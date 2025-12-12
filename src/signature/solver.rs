use miden_assembly_syntax::ast::{Block, InvocationTarget, Op};

use crate::{callgraph::CallGraph, frontend::Workspace};

use super::{
    ProcSignature, Range, SignatureMap,
    domain::{Provenance, ProvenanceStack},
    effects::{InstructionEffect, stack_effect},
};

const MAX_ITERATIONS: usize = 8;

pub fn infer_signatures(workspace: &Workspace, cg: &CallGraph) -> SignatureMap {
    let mut sigs = SignatureMap::default();
    for (name, node) in cg.nodes.iter().enumerate() {
        let _ = name;
        sigs.signatures
            .insert(node.name.clone(), ProcSignature::Unknown);
    }

    // Fixed-point iteration over all nodes
    let mut current_iteration = 0;
    let mut changed = true;
    while changed && current_iteration < MAX_ITERATIONS {
        changed = false;
        current_iteration += 1;
        for node in cg.nodes.iter() {
            if let Some(proc) = workspace.lookup_proc(&node.name) {
                let module_path = node.module_path.as_ref();
                let sig = analyze_proc(proc.body(), module_path, &sigs, workspace);
                if sigs
                    .signatures
                    .get(&node.name)
                    .map(|s| s != &sig)
                    .unwrap_or(true)
                {
                    sigs.signatures.insert(node.name.clone(), sig);
                    changed = true;
                }
            }
        }
    }

    sigs
}

enum OpResult {
    Ok { accessed_existing: bool },
    Unknown,
}

fn analyze_proc(
    body: &Block,
    module_path: &str,
    sigs: &SignatureMap,
    workspace: &Workspace,
) -> ProcSignature {
    let mut stack = ProvenanceStack::default();
    let mut next_new = 0u32;
    let mut unbounded_inputs = false;
    let mut unbounded_outputs = false;

    match analyze_block(
        body,
        &mut stack,
        module_path,
        sigs,
        workspace,
        &mut next_new,
        &mut unbounded_inputs,
        &mut unbounded_outputs,
    ) {
        OpResult::Ok { .. } => {
            let (outputs_min, outputs_max) = stack.new_count_bounds();
            ProcSignature::Known {
                inputs: Range {
                    min: stack.required,
                    max: if unbounded_inputs {
                        None
                    } else {
                        Some(stack.required)
                    },
                },
                outputs: Range {
                    min: outputs_min,
                    max: if unbounded_outputs { None } else { outputs_max },
                },
                slots: Vec::new(),
                side_effects: false, // TODO: Implement side-effect analysis
            }
        }
        OpResult::Unknown => ProcSignature::Unknown,
    }
}

fn analyze_block(
    block: &Block,
    stack: &mut ProvenanceStack,
    module_path: &str,
    sigs: &SignatureMap,
    workspace: &Workspace,
    next_new: &mut u32,
    unbounded_inputs: &mut bool,
    unbounded_outputs: &mut bool,
) -> OpResult {
    let mut accessed_existing = false;
    for op in block.iter() {
        match op {
            Op::Inst(inst) => {
                // Handle calls explicitly to use current signatures
                match inst.inner() {
                    miden_assembly_syntax::ast::Instruction::Exec(target)
                    | miden_assembly_syntax::ast::Instruction::Call(target)
                    | miden_assembly_syntax::ast::Instruction::SysCall(target) => {
                        if apply_call_effect(target, module_path, sigs, stack, next_new, workspace)
                            .is_unknown()
                        {
                            return OpResult::Unknown;
                        }
                    }
                    miden_assembly_syntax::ast::Instruction::DynExec
                    | miden_assembly_syntax::ast::Instruction::DynCall => return OpResult::Unknown,
                    _ => match stack_effect(inst.inner()) {
                        InstructionEffect::Known {
                            pops,
                            pushes,
                            required: req,
                        } => {
                            // Only apply required when instruction does not pop;
                            // popping will drive required via underflow accounting.
                            if pops == 0 && req > stack.required {
                                stack.required = req;
                            }
                            if pops == 0 && req as usize > stack.len() {
                                // Seed missing stack slots to satisfy the required depth so that
                                // we don't over-count inputs via underflow on later pops.
                                let target = req as usize;
                                while stack.len() < target {
                                    let idx = stack.len() as u32;
                                    stack.push(Provenance::Input(idx));
                                }
                                stack.required = stack.required.max(req);
                            }
                            if pops == 0 && req > 0 {
                                accessed_existing = true;
                            }
                            for _ in 0..pops {
                                let _ = stack.pop();
                            }
                            for _ in 0..pushes {
                                stack.push(Provenance::New(*next_new));
                                *next_new += 1;
                            }
                        }
                        InstructionEffect::Unknown => return OpResult::Unknown,
                    },
                }
            }
            Op::If {
                then_blk, else_blk, ..
            } => {
                let _ = stack.pop(); // condition

                let mut then_stack = stack.clone();
                let mut else_stack = stack.clone();

                let then_res = analyze_block(
                    then_blk,
                    &mut then_stack,
                    module_path,
                    sigs,
                    workspace,
                    next_new,
                    unbounded_inputs,
                    unbounded_outputs,
                );
                let else_res = analyze_block(
                    else_blk,
                    &mut else_stack,
                    module_path,
                    sigs,
                    workspace,
                    next_new,
                    unbounded_inputs,
                    unbounded_outputs,
                );
                if then_res.is_unknown() || else_res.is_unknown() {
                    return OpResult::Unknown;
                }

                if then_stack.len() != else_stack.len() {
                    return OpResult::Unknown;
                }

                let mut merged = Vec::with_capacity(then_stack.len());
                for (a, b) in then_stack
                    .clone_slots()
                    .into_iter()
                    .zip(else_stack.clone_slots())
                {
                    let merged_slot = if a == b {
                        a
                    } else if matches!(a, Provenance::New(_)) || matches!(b, Provenance::New(_)) {
                        Provenance::Rewritten
                    } else {
                        Provenance::Unknown
                    };
                    merged.push(merged_slot);
                }
                stack.required = stack
                    .required
                    .max(then_stack.required.max(else_stack.required));
                stack.replace_slots(merged);
                accessed_existing = accessed_existing
                    || matches!(
                        then_res,
                        OpResult::Ok {
                            accessed_existing: true
                        }
                    )
                    || matches!(
                        else_res,
                        OpResult::Ok {
                            accessed_existing: true
                        }
                    );
            }
            Op::Repeat { count, body, .. } => {
                for _ in 0..*count {
                    if analyze_block(
                        body,
                        stack,
                        module_path,
                        sigs,
                        workspace,
                        next_new,
                        unbounded_inputs,
                        unbounded_outputs,
                    )
                    .is_unknown()
                    {
                        return OpResult::Unknown;
                    }
                }
            }
            Op::While { body, .. } => {
                // while.true: pop initial condition, optional body, then each iteration pops a fresh condition
                let _ = stack.pop(); // initial condition
                let entry_stack = stack.clone(); // state if loop exits immediately
                let mut body_stack = stack.clone(); // state entering body
                let body_res = analyze_block(
                    body,
                    &mut body_stack,
                    module_path,
                    sigs,
                    workspace,
                    next_new,
                    unbounded_inputs,
                    unbounded_outputs,
                );
                if body_res.is_unknown() {
                    return OpResult::Unknown;
                }
                // Body must leave a condition for the next iteration check
                if body_stack.len() == 0 {
                    return OpResult::Unknown;
                }
                let cond_prov = body_stack.pop();

                // If loop changes height, conservatively unknown
                if entry_stack.len() != body_stack.len() {
                    return OpResult::Unknown;
                }
                let mut merged = Vec::with_capacity(entry_stack.len());
                for (a, b) in entry_stack
                    .clone_slots()
                    .into_iter()
                    .zip(body_stack.clone_slots())
                {
                    let merged_slot = if a == b {
                        a
                    } else if matches!(a, Provenance::New(_)) || matches!(b, Provenance::New(_)) {
                        Provenance::Rewritten
                    } else {
                        Provenance::Unknown
                    };
                    merged.push(merged_slot);
                }
                let combined_required = entry_stack.required.max(body_stack.required);
                stack.required = stack.required.max(combined_required);
                stack.replace_slots(merged);

                if matches!(
                    cond_prov,
                    Provenance::Input(_) | Provenance::Unknown | Provenance::Rewritten
                ) {
                    *unbounded_inputs = true;
                }
                // If the body accessed existing slots and we had to consume a condition, we may need additional inputs
                if let OpResult::Ok {
                    accessed_existing: true,
                } = body_res
                {
                    if entry_stack.len() == 0 {
                        stack.required = stack.required.max(
                            entry_stack
                                .required
                                .saturating_add(body_stack.required.max(1)),
                        );
                    }
                }
                if body_stack.len() > entry_stack.len() {
                    *unbounded_outputs = true;
                }
            }
        }
    }
    OpResult::Ok { accessed_existing }
}

fn apply_call_effect(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut ProvenanceStack,
    next_new: &mut u32,
    workspace: &Workspace,
) -> OpResult {
    let callee = match target {
        InvocationTarget::Symbol(ident) => format!("{module_path}::{}", ident.as_str()),
        InvocationTarget::Path(path) => path.to_string(),
        InvocationTarget::MastRoot(_) => return OpResult::Unknown,
    };
    let (inputs, outputs) = match sigs.signatures.get(&callee) {
        Some(ProcSignature::Known {
            inputs, outputs, ..
        }) => {
            let out = match outputs.max {
                Some(max) if max == outputs.min => max,
                _ => return OpResult::Unknown,
            };
            (inputs.min, out)
        }
        _ => return OpResult::Unknown,
    };

    // If this is a local call, ensure the target exists to avoid resolving stale sigs
    if workspace.lookup_proc(&callee).is_none() {
        return OpResult::Unknown;
    }

    for _ in 0..inputs {
        let _ = stack.pop();
    }
    for _ in 0..outputs {
        stack.push(Provenance::New(*next_new));
        *next_new += 1;
    }
    OpResult::Ok {
        accessed_existing: true,
    }
}

impl OpResult {
    fn is_unknown(&self) -> bool {
        matches!(self, OpResult::Unknown)
    }
}
