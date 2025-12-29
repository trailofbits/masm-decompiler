use miden_assembly_syntax::ast::{Block, Instruction, InvocationTarget, Op, Procedure};

use crate::{callgraph::CallGraph, frontend::Workspace};

use super::{ProcSignature, SignatureMap, domain::ProvenanceStack, effects::InstructionEffect};

pub fn infer_signatures(workspace: &Workspace, callgraph: &CallGraph) -> SignatureMap {
    let mut signatures = SignatureMap::default();

    // Iterate over call graph nodes in bottom up order, starting with
    // call-graph leaves.
    for node in callgraph.iter() {
        if let Some(proc) = workspace.lookup_proc(&node.name) {
            let module_path = node.module_path.as_ref();
            let analysis = Analysis::new(module_path, &signatures, workspace);
            let signature = analysis.visit_proc(proc);
            signatures.insert(node.name.clone(), signature);
        }
    }
    signatures
}

/// The result of analyzing a single operation.
enum OpResult {
    Known,
    Unknown,
}

impl OpResult {
    /// Check if the result is unknown.
    fn is_unknown(&self) -> bool {
        matches!(self, OpResult::Unknown)
    }
}

struct Analysis<'a> {
    signatures: &'a SignatureMap,
    workspace: &'a Workspace,
    /// Fully-qualified path to the analyzed module
    module_path: &'a str,
}

impl<'a> Analysis<'a> {
    pub fn new(
        module_path: &'a str,
        signatures: &'a SignatureMap,
        workspace: &'a Workspace,
    ) -> Self {
        Analysis {
            module_path,
            signatures,
            workspace,
        }
    }

    pub fn visit_proc(&self, procedure: &Procedure) -> ProcSignature {
        let mut stack = ProvenanceStack::default();
        match self.visit_block(procedure.body(), &mut stack) {
            OpResult::Known => ProcSignature::from(&stack),
            OpResult::Unknown => ProcSignature::Unknown,
        }
    }

    fn visit_block(&self, block: &Block, stack: &mut ProvenanceStack) -> OpResult {
        for op in block.iter() {
            let op_result = self.visit_op(op, stack);
            if op_result.is_unknown() {
                return OpResult::Unknown;
            }
        }
        OpResult::Known
    }

    fn visit_op(&self, op: &Op, stack: &mut ProvenanceStack) -> OpResult {
        match op {
            Op::Inst(inst) => self.visit_inst(inst.inner(), stack),
            Op::If {
                then_blk, else_blk, ..
            } => self.visit_if(then_blk, else_blk, stack),
            Op::Repeat { count, body, .. } => self.visit_repeat(*count, body, stack),
            Op::While { body, .. } => self.visit_while(body, stack),
        }
    }

    fn visit_inst(&self, inst: &Instruction, stack: &mut ProvenanceStack) -> OpResult {
        use Instruction::*;

        match inst {
            // Handle calls explicitly
            Exec(target) => self.visit_call(target, stack),
            // TODO: Handle call and syscall
            Call(..) | SysCall(..) | DynCall | DynExec => return OpResult::Unknown,
            _ => match InstructionEffect::from(inst) {
                InstructionEffect::Known {
                    pops,
                    pushes,
                    required_depth,
                } => {
                    stack.apply(pops, pushes, required_depth);
                    OpResult::Known
                }
                InstructionEffect::Unknown => return OpResult::Unknown,
            },
        }
    }

    fn visit_call(&self, target: &InvocationTarget, stack: &mut ProvenanceStack) -> OpResult {
        let callee = match target {
            InvocationTarget::Symbol(ident) => format!("{}::{}", self.module_path, ident.as_str()),
            InvocationTarget::Path(path) => path.to_string(),
            InvocationTarget::MastRoot(_) => return OpResult::Unknown,
        };
        // If the callee signature is not found, this procedure is part
        // of an SCC. In this case we bail and return unknown.
        let Some(signature) = self.signatures.get(&callee) else {
            return OpResult::Unknown;
        };
        // Procedures are visited in bottom-up order in the call graph, so
        // either callee signatures are known or inference failed. If inference
        // failed we cannot determine stack effects for the caller either and so
        // we bail here.
        let InstructionEffect::Known {
            pops,
            pushes,
            required_depth,
        } = signature.into()
        else {
            return OpResult::Unknown;
        };
        stack.apply(pops, pushes, required_depth);
        OpResult::Known
    }

    fn visit_if(
        &self,
        then_block: &Block,
        else_block: &Block,
        stack: &mut ProvenanceStack,
    ) -> OpResult {
        stack.pop(); // Pop condition.

        let mut then_stack = stack.clone();
        let mut else_stack = stack.clone();

        let then_result = self.visit_block(then_block, &mut then_stack);
        let else_result = self.visit_block(else_block, &mut else_stack);
        if then_result.is_unknown() || else_result.is_unknown() {
            return OpResult::Unknown;
        }

        // We bail on branches with different stack effects.
        if then_stack.current_depth != else_stack.current_depth {
            return OpResult::Unknown;
        }
        *stack = then_stack.merge(&else_stack);
        OpResult::Known
    }

    fn visit_repeat(&self, count: u32, body: &Block, stack: &mut ProvenanceStack) -> OpResult {
        for _ in 0..count {
            let body_result = self.visit_block(body, stack);
            if body_result.is_unknown() {
                return OpResult::Unknown;
            }
        }
        OpResult::Known
    }

    fn visit_while(&self, body: &Block, stack: &mut ProvenanceStack) -> OpResult {
        stack.pop(); // Pop initial condition.

        let entry_stack = stack.clone(); // State if loop exits immediately.
        let mut body_stack = stack.clone(); // State entering loop body.
        let body_result = self.visit_block(body, &mut body_stack);
        if body_result.is_unknown() {
            return OpResult::Unknown;
        }
        // We require that the body leaves a condition for the next iteration
        // check. Otherwise we bail.
        if body_stack.current_depth <= 0 {
            return OpResult::Unknown;
        }
        body_stack.pop();

        // We also require that the while-loop body is stack neutral after the
        // condition is popped. Otherwise we bail.
        if entry_stack.current_depth != body_stack.current_depth {
            return OpResult::Unknown;
        }
        *stack = entry_stack.merge(&body_stack);
        OpResult::Known
    }
}
