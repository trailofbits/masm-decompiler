//! Proptest strategies for generating valid MASM programs.
//!
//! These strategies generate `miden_assembly_syntax` AST types directly to test
//! signature inference. This ensures that tests exercise the real stack effect
//! computation logic in `src/signature/effects.rs`.
//!
//! Generated programs satisfy the requirements for successful signature inference:
//!
//! 1. No conditional blocks with different stack effects between branches
//! 2. No while loops with non-neutral stack effects (after condition pop)
//! 3. Only calls to procedures satisfying constraints 1-3
//! 4. Call graphs are DAGs (no SCCs) with configurable depth

use masm_decompiler::signature::StackEffect;
use miden_assembly_syntax::PathBuf;
use miden_assembly_syntax::ast::{
    Block, Ident, Immediate, Instruction, InvocationTarget, Op, Procedure, ProcedureName,
    Visibility,
};
use miden_assembly_syntax::debuginfo::{SourceSpan, Span};
use miden_assembly_syntax::parser::{IntValue, PushValue};
use miden_assembly_syntax::prettier::PrettyPrint;
use proptest::prelude::*;

// ============================================================================
// Instruction strategies
// ============================================================================

/// Returns a list of truly stack-neutral instructions (pops 0, pushes 0).
fn neutral_instructions() -> Vec<Instruction> {
    vec![Instruction::Nop]
}

/// Returns a list of producing instructions (pops 0, pushes 1).
/// Only includes Push instructions since Dup requires values on the stack.
fn producing_instructions() -> Vec<Instruction> {
    vec![
        Instruction::Push(Immediate::Value(Span::unknown(PushValue::Int(
            IntValue::U8(0),
        )))),
        Instruction::Push(Immediate::Value(Span::unknown(PushValue::Int(
            IntValue::U8(1),
        )))),
    ]
}

/// Returns a list of consuming instructions (pops 1, pushes 0).
/// Only includes Drop since binary ops like Add/Sub have effect (2,1) not (1,0).
fn consuming_instructions() -> Vec<Instruction> {
    vec![Instruction::Drop]
}

/// Strategy for selecting a stack-neutral instruction.
pub fn neutral_instruction_strategy() -> impl Strategy<Value = Instruction> {
    let instructions = neutral_instructions();
    (0..instructions.len()).prop_map(move |index| instructions[index].clone())
}

/// Strategy for selecting a producing instruction (net effect +1).
pub fn producing_instruction_strategy() -> impl Strategy<Value = Instruction> {
    let instructions = producing_instructions();
    (0..instructions.len()).prop_map(move |index| instructions[index].clone())
}

/// Strategy for selecting a consuming instruction (net effect -1).
pub fn consuming_instruction_strategy() -> impl Strategy<Value = Instruction> {
    let instructions = consuming_instructions();
    (0..instructions.len()).prop_map(move |index| instructions[index].clone())
}

/// Wraps an `Instruction` in an `Op::Inst` with an unknown source span.
fn instruction_to_op(instruction: Instruction) -> Op {
    Op::Inst(Span::unknown(instruction))
}

// ============================================================================
// Op strategies
// ============================================================================

/// Strategy for generating an `Op` along with its stack effect.
///
/// This strategy can generate any type of operation (instruction, if, while,
/// repeat, or exec call) based on the configuration. The returned effect
/// allows callers to compensate with padding instructions if needed.
pub fn op_with_effect_strategy(config: StrategyConfig) -> BoxedStrategy<(Op, StackEffect)> {
    let can_generate_call = config.max_calls > 0 && !config.callees.is_empty();
    let can_generate_control_flow = config.control_flow_depth > 0;

    if !can_generate_control_flow && !can_generate_call {
        // Base case: generate a single instruction op
        any_instruction_strategy()
    } else if !can_generate_control_flow {
        // Can only generate instructions or calls
        prop_oneof![
            // Weight 3: Simple instruction
            3 => any_instruction_strategy(),
            // Weight 1: Exec call
            1 => exec_call_strategy(config.clone()),
        ]
        .boxed()
    } else {
        // Can include control flow structures and possibly calls
        let nested_config = config.decrement_control_flow_depth();

        let mut strategies: Vec<(u32, BoxedStrategy<(Op, StackEffect)>)> = vec![
            // Weight 4: Simple instruction (most common)
            (4, any_instruction_strategy()),
            // Weight 2: Balanced if-else with neutral effect
            (2, balanced_if_strategy(nested_config.clone())),
            // Weight 1: Neutral while loop (net effect -1)
            (1, neutral_while_strategy(nested_config.clone())),
            // Weight 1: Repeat loop with count 1
            (1, repeat_strategy(1, nested_config.clone())),
        ];

        // Weight 1: Exec call (only if we have callees and calls remaining)
        if can_generate_call {
            strategies.push((1, exec_call_strategy(config.clone())));
        }

        prop::strategy::Union::new_weighted(strategies).boxed()
    }
}

/// Strategy for generating any single instruction with its effect.
fn any_instruction_strategy() -> BoxedStrategy<(Op, StackEffect)> {
    prop_oneof![
        // Neutral instructions (effect 0)
        2 => neutral_instruction_strategy().prop_map(|instruction| {
            (instruction_to_op(instruction), StackEffect::known(0, 0))
        }),
        // Producing instructions (effect +1)
        1 => producing_instruction_strategy().prop_map(|instruction| {
            (instruction_to_op(instruction), StackEffect::known(0, 1))
        }),
        // Consuming instructions (effect -1)
        1 => consuming_instruction_strategy().prop_map(|instruction| {
            (instruction_to_op(instruction), StackEffect::known(1, 0))
        }),
    ]
    .boxed()
}

/// Strategy for generating an exec call with its effect.
fn exec_call_strategy(config: StrategyConfig) -> BoxedStrategy<(Op, StackEffect)> {
    assert!(
        !config.callees.is_empty(),
        "exec_call_strategy requires at least one callee"
    );

    let callees = config.callees.clone();
    (0..callees.len())
        .prop_map(move |index| {
            let callee = &callees[index];
            let op = callee.to_exec_op();
            let effect = StackEffect::known(callee.pops, callee.pushes);
            (op, effect)
        })
        .boxed()
}

/// Strategy for a single instruction `Op` with the specified net effect.
fn instruction_strategy(net_effect: isize) -> BoxedStrategy<Op> {
    if net_effect > 0 {
        producing_instruction_strategy()
            .prop_map(instruction_to_op)
            .boxed()
    } else if net_effect < 0 {
        consuming_instruction_strategy()
            .prop_map(instruction_to_op)
            .boxed()
    } else {
        neutral_instruction_strategy()
            .prop_map(instruction_to_op)
            .boxed()
    }
}

/// Strategy for generating a balanced if-else conditional `Op` with random effect.
///
/// Both branches have the same randomly chosen stack effect. The condition
/// consumes one element, so the overall effect is (branch_pops + 1, branch_pushes).
fn balanced_if_strategy(config: StrategyConfig) -> BoxedStrategy<(Op, StackEffect)> {
    // Generate random branch effect (0-2 pops, 0-2 pushes)
    (0usize..=2, 0usize..=2)
        .prop_flat_map(move |(branch_pops, branch_pushes)| {
            let config = config.clone();
            let then_strategy =
                block_with_effect_strategy(branch_pops, branch_pushes, config.clone());
            let else_strategy = block_with_effect_strategy(branch_pops, branch_pushes, config);

            (then_strategy, else_strategy).prop_map(move |(then_block, else_block)| {
                let op = Op::If {
                    span: SourceSpan::default(),
                    then_blk: then_block,
                    else_blk: else_block,
                };
                // Condition pops 1, plus branch effect
                (op, StackEffect::known(branch_pops + 1, branch_pushes))
            })
        })
        .boxed()
}

/// Strategy for generating a while loop operation.
///
/// The loop body must push exactly 1 value (the next condition), making the
/// overall net effect: -1 (pops 1 for the initial condition).
fn neutral_while_strategy(config: StrategyConfig) -> BoxedStrategy<(Op, StackEffect)> {
    // Body must push 1 value for the next loop condition.
    block_with_effect_strategy(0, 1, config)
        .prop_map(|body| {
            let op = Op::While {
                span: SourceSpan::default(),
                body,
            };
            // Initial condition pops 1, body pushes 1 for next condition, final condition pops 1
            // Net effect: -1 (pops 1, pushes 0)
            (op, StackEffect::known(1, 0))
        })
        .boxed()
}

/// Strategy for generating a repeat loop operation with random body effect.
///
/// The body has a randomly chosen effect, and the overall effect is the body
/// effect multiplied by the repeat count.
fn repeat_strategy(max_count: usize, config: StrategyConfig) -> BoxedStrategy<(Op, StackEffect)> {
    // Generate random body effect (0-2 pops, 0-2 pushes)
    (0usize..=2, 0usize..=2, 1usize..=max_count)
        .prop_flat_map(move |(body_pops, body_pushes, count)| {
            let config = config.clone();
            block_with_effect_strategy(body_pops, body_pushes, config).prop_map(move |body| {
                let op = Op::Repeat {
                    span: SourceSpan::default(),
                    count: count as u32,
                    body,
                };
                // Effect is body effect multiplied by count
                // For simplicity, we compute the aggregate effect
                let total_pops = body_pops * count;
                let total_pushes = body_pushes * count;
                (op, StackEffect::known(total_pops, total_pushes))
            })
        })
        .boxed()
}

// ============================================================================
// Block strategies
// ============================================================================

/// Strategy for generating a block with a target stack effect.
///
/// The generated block will have the specified number of pops and pushes.
/// Uses `op_with_effect_strategy` to generate operations, then compensates
/// with padding instructions to achieve the exact target effect.
pub fn block_with_effect_strategy(
    target_pops: usize,
    target_pushes: usize,
    config: StrategyConfig,
) -> BoxedStrategy<Block> {
    // Generate a main operation using op_with_effect_strategy
    op_with_effect_strategy(config.clone())
        .prop_flat_map(move |(main_op, op_effect)| {
            let config = config.clone();
            let StackEffect::Known {
                pops: op_pops,
                pushes: op_pushes,
                ..
            } = op_effect
            else {
                panic!("op_with_effect_strategy should return known effects");
            };

            // Calculate padding needed to achieve target effect
            // We need: padding_before + op_effect + padding_after = target_effect
            //
            // The op consumes op_pops and produces op_pushes.
            // We need the block to consume target_pops and produce target_pushes.
            //
            // Strategy:
            // 1. If op needs more inputs than target provides (op_pops > target_pops),
            //    push (op_pops - target_pops) values before the op
            // 2. If op produces more than target wants (op_pushes > target_pushes),
            //    drop (op_pushes - target_pushes) values after the op
            // 3. If op needs fewer inputs than target provides (op_pops < target_pops),
            //    drop (target_pops - op_pops) values before the op
            // 4. If op produces fewer than target wants (op_pushes < target_pushes),
            //    push (target_pushes - op_pushes) values after the op

            let (push_before, drop_before) = if op_pops > target_pops {
                (op_pops - target_pops, 0)
            } else {
                (0, target_pops - op_pops)
            };

            let (push_after, drop_after) = if op_pushes > target_pushes {
                (0, op_pushes - target_pushes)
            } else {
                (target_pushes - op_pushes, 0)
            };

            // Generate padding instructions
            let push_before_strategy =
                prop::collection::vec(producing_instruction_strategy(), push_before..=push_before);
            let drop_before_strategy =
                prop::collection::vec(consuming_instruction_strategy(), drop_before..=drop_before);
            let push_after_strategy =
                prop::collection::vec(producing_instruction_strategy(), push_after..=push_after);
            let drop_after_strategy =
                prop::collection::vec(consuming_instruction_strategy(), drop_after..=drop_after);

            // Generate optional neutral instructions
            let neutral_strategy = prop::collection::vec(
                neutral_instruction_strategy(),
                0..=config.max_neutral_instructions,
            );

            (
                push_before_strategy,
                drop_before_strategy,
                neutral_strategy,
                push_after_strategy,
                drop_after_strategy,
            )
                .prop_map(
                    move |(push_before, drop_before, neutral, push_after, drop_after)| {
                        let mut ops = Vec::new();

                        // Add padding before the main op
                        ops.extend(push_before.into_iter().map(instruction_to_op));
                        ops.extend(drop_before.into_iter().map(instruction_to_op));

                        // Add the main operation
                        ops.push(main_op.clone());

                        // Add neutral instructions for variety
                        ops.extend(neutral.into_iter().map(instruction_to_op));

                        // Add padding after the main op
                        ops.extend(push_after.into_iter().map(instruction_to_op));
                        ops.extend(drop_after.into_iter().map(instruction_to_op));

                        Block::new(SourceSpan::default(), ops)
                    },
                )
        })
        .boxed()
}

/// Strategy for generating a block with a specific net effect.
pub fn block_with_net_effect_strategy(
    net_effect: isize,
    config: StrategyConfig,
) -> BoxedStrategy<Block> {
    let (pops, pushes) = if net_effect >= 0 {
        (0, net_effect as usize)
    } else {
        ((-net_effect) as usize, 0)
    };
    block_with_effect_strategy(pops, pushes, config)
}

/// Computes the aggregate `StackEffect` for a block.
pub fn compute_block_effect(block: &Block) -> StackEffect {
    let mut effect = StackEffect::known(0, 0);
    for op in block.iter() {
        let op_effect = compute_op_effect(op);
        effect = effect.then(op_effect);
    }
    effect
}

/// Computes the `StackEffect` for a single operation.
pub fn compute_op_effect(op: &Op) -> StackEffect {
    match op {
        Op::Inst(instruction) => StackEffect::from(instruction.inner()),
        Op::If {
            then_blk, else_blk, ..
        } => {
            let condition_pop = StackEffect::known(1, 0);
            let then_effect = compute_block_effect(then_blk);
            let else_effect = compute_block_effect(else_blk);
            // For generated conditionals, both branches have the same effect
            assert_eq!(then_effect, else_effect);
            condition_pop.then(then_effect)
        }
        Op::While { body, .. } => {
            let condition_pop = StackEffect::known(1, 0);
            let body_effect = compute_block_effect(body);
            // For stack-neutral while loops, body pushes 1 for the next condition
            condition_pop.then(body_effect).then(condition_pop)
        }
        Op::Repeat { count, body, .. } => {
            let body_effect = compute_block_effect(body);
            let mut total_effect = StackEffect::known(0, 0);
            for _ in 0..*count {
                total_effect = total_effect.then(body_effect);
            }
            total_effect
        }
    }
}

// ============================================================================
// Procedure strategies
// ============================================================================

/// Strategy for a valid procedure name.
pub fn procedure_name_strategy() -> impl Strategy<Value = ProcedureName> {
    "[a-z]{8}".prop_map(|suffix| {
        let name = format!("proc_{suffix}");
        ProcedureName::new(&name).expect("valid procedure name")
    })
}

/// A callable procedure with its name and stack effect.
#[derive(Debug, Clone)]
pub struct CallableProcedure {
    /// The procedure name (local) or fully qualified path (cross-module)
    pub name: String,
    /// The module containing this procedure (None for local calls)
    pub module: Option<String>,
    /// Number of stack elements consumed
    pub pops: usize,
    /// Number of stack elements produced
    pub pushes: usize,
}

impl CallableProcedure {
    pub fn new_local(name: &ProcedureName, pops: usize, pushes: usize) -> Self {
        Self {
            name: name.to_string(),
            module: None,
            pops,
            pushes,
        }
    }

    pub fn new_external(name: &str, module: &str, pops: usize, pushes: usize) -> Self {
        Self {
            name: name.to_string(),
            module: Some(module.to_string()),
            pops,
            pushes,
        }
    }

    /// Net stack effect (pushes - pops)
    pub fn net_effect(&self) -> isize {
        self.pushes as isize - self.pops as isize
    }

    /// Creates an exec instruction op for this procedure
    pub fn to_exec_op(&self) -> Op {
        let target = if let Some(ref module) = self.module {
            let path_str = format!("{}::{}", module, self.name);
            let path_buf: PathBuf = path_str.parse().expect("valid path");
            let path: std::sync::Arc<miden_assembly_syntax::Path> = path_buf.into();
            InvocationTarget::Path(Span::unknown(path))
        } else {
            let ident = Ident::new(&self.name).expect("valid ident");
            InvocationTarget::Symbol(ident)
        };
        let instruction = Instruction::Exec(target);
        Op::Inst(Span::unknown(instruction))
    }
}

/// Configuration for strategy generation.
///
/// Controls the complexity of generated code including control flow nesting,
/// number of exec calls, and available callees.
#[derive(Debug, Clone)]
pub struct StrategyConfig {
    /// Maximum number of neutral instructions in blocks
    pub max_neutral_instructions: usize,
    /// Maximum depth of control flow nesting
    pub control_flow_depth: usize,
    /// Maximum number of exec calls allowed
    pub max_calls: usize,
    /// Procedures that can be called
    pub callees: Vec<CallableProcedure>,
}

impl Default for StrategyConfig {
    fn default() -> Self {
        Self {
            max_neutral_instructions: 3,
            control_flow_depth: 1,
            max_calls: 2,
            callees: vec![],
        }
    }
}

impl StrategyConfig {
    pub fn with_callees(mut self, callees: Vec<CallableProcedure>) -> Self {
        self.callees = callees;
        self
    }

    pub fn with_control_flow_depth(mut self, depth: usize) -> Self {
        self.control_flow_depth = depth;
        self
    }

    pub fn with_max_calls(mut self, max_calls: usize) -> Self {
        self.max_calls = max_calls;
        self
    }

    /// Returns a config with decremented control flow depth.
    fn decrement_control_flow_depth(&self) -> Self {
        Self {
            control_flow_depth: self.control_flow_depth.saturating_sub(1),
            ..self.clone()
        }
    }
}

/// Strategy for generating a procedure with configurable effects and optional calls.
///
/// The config's callees and max_calls control whether exec calls may be generated.
/// Calls are handled internally by `block_with_effect_strategy` via `op_with_effect_strategy`.
pub fn procedure_strategy(
    name: ProcedureName,
    target_pops: usize,
    target_pushes: usize,
    config: StrategyConfig,
) -> BoxedStrategy<Procedure> {
    block_with_effect_strategy(target_pops, target_pushes, config)
        .prop_map(move |body| {
            Procedure::new(
                SourceSpan::default(),
                Visibility::Private,
                name.clone(),
                0,
                body,
            )
        })
        .boxed()
}

// ============================================================================
// Module representation
// ============================================================================

/// A module with procedures (generates MASM source strings).
#[derive(Debug, Clone)]
pub struct Module {
    pub name: String,
    pub uses: Vec<String>,
    pub procedures: Vec<Procedure>,
}

impl Module {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            uses: vec![],
            procedures: vec![],
        }
    }

    pub fn with_use(mut self, use_declaration: impl Into<String>) -> Self {
        self.uses.push(use_declaration.into());
        self
    }

    pub fn with_procedure(mut self, procedure: Procedure) -> Self {
        self.procedures.push(procedure);
        self
    }

    pub fn name(&self) -> String {
        self.name.clone()
    }

    /// Converts the module to MASM source code.
    pub fn to_masm(&self) -> String {
        let use_declarations = self
            .uses
            .iter()
            .map(|use_path| format!("use {}", use_path))
            .collect::<Vec<_>>()
            .join("\n");

        let procedure_declarations = self
            .procedures
            .iter()
            .map(|procedure| procedure.to_pretty_string())
            .collect::<Vec<_>>()
            .join("\n\n");

        if use_declarations.is_empty() {
            procedure_declarations
        } else {
            format!("{}\n\n{}", use_declarations, procedure_declarations)
        }
    }

    pub fn to_source_pair(&self) -> (String, String) {
        (self.name(), self.to_masm())
    }

    /// Returns callable procedure info for all procedures in this module.
    pub fn callable_procedures(&self) -> Vec<CallableProcedure> {
        self.procedures
            .iter()
            .map(|procedure| {
                let effect = compute_block_effect(procedure.body());
                let StackEffect::Known { pops, pushes, .. } = effect else {
                    panic!("callable stack effect should be known")
                };
                CallableProcedure::new_external(
                    &procedure.name().to_string(),
                    &self.name,
                    pops,
                    pushes,
                )
            })
            .collect()
    }
}

/// Strategy for a valid module name.
pub fn module_name_strategy() -> impl Strategy<Value = String> {
    "[a-z]{8}".prop_map(|suffix| format!("mod_{suffix}"))
}

/// Strategy for a module with procedures that can call each other locally.
pub fn module_strategy(procedure_count: usize, config: StrategyConfig) -> BoxedStrategy<Module> {
    module_with_external_calls_strategy(procedure_count, vec![], config)
}

// ============================================================================
// Call graph strategies
// ============================================================================

/// A DAG of modules for testing call graph traversal.
#[derive(Debug, Clone)]
pub struct CallGraph {
    pub modules: Vec<Module>,
}

impl CallGraph {
    pub fn new(modules: Vec<Module>) -> Self {
        Self { modules }
    }

    pub fn to_source_pairs(&self) -> Vec<(String, String)> {
        self.modules
            .iter()
            .map(|module| module.to_source_pair())
            .collect()
    }
}

/// Strategy for a module that can call procedures from external modules.
pub fn module_with_external_calls_strategy(
    procedure_count: usize,
    external_callees: Vec<CallableProcedure>,
    config: StrategyConfig,
) -> BoxedStrategy<Module> {
    module_procedures_with_external_calls_strategy(
        procedure_count,
        vec![],
        external_callees.clone(),
        config,
    )
    .prop_flat_map(move |procedures| {
        let external_modules: Vec<String> = external_callees
            .iter()
            .filter_map(|callee| callee.module.clone())
            .collect::<std::collections::HashSet<_>>()
            .into_iter()
            .collect();

        module_name_strategy().prop_map(move |name| {
            let mut module = Module::new(name);
            for external_module in &external_modules {
                module = module.with_use(format!("{}::*", external_module));
            }
            for procedure in &procedures {
                module = module.with_procedure(procedure.clone());
            }
            module
        })
    })
    .boxed()
}

/// Recursive strategy for procedures with external call capability.
fn module_procedures_with_external_calls_strategy(
    remaining_count: usize,
    local_callees: Vec<CallableProcedure>,
    external_callees: Vec<CallableProcedure>,
    config: StrategyConfig,
) -> BoxedStrategy<Vec<Procedure>> {
    if remaining_count == 0 {
        return Just(vec![]).boxed();
    }

    let procedure_index = local_callees.len();
    let name =
        ProcedureName::new(&format!("proc_{}", procedure_index)).expect("valid procedure name");

    let effect_strategy = (0usize..=2, 0usize..=2);

    // Clone everything needed for the chained closures upfront
    let local_callees_for_first = local_callees.clone();
    let local_callees_for_second = local_callees;
    let external_callees_for_first = external_callees.clone();
    let external_callees_for_second = external_callees;
    let config_for_first = config.clone();
    let config_for_second = config;

    effect_strategy
        .prop_flat_map(move |(target_pops, target_pushes)| {
            let name = name.clone();
            let mut all_callees = local_callees_for_first.clone();
            all_callees.extend(external_callees_for_first.clone());

            let procedure_config = StrategyConfig {
                max_neutral_instructions: config_for_first.max_neutral_instructions,
                control_flow_depth: config_for_first.control_flow_depth,
                max_calls: config_for_first.max_calls,
                callees: all_callees,
            };

            procedure_strategy(name.clone(), target_pops, target_pushes, procedure_config)
                .prop_map(move |procedure| (procedure, target_pops, target_pushes))
        })
        .prop_flat_map(move |(procedure, pops, pushes)| {
            let mut new_local_callees = local_callees_for_second.clone();
            new_local_callees.push(CallableProcedure::new_local(procedure.name(), pops, pushes));

            module_procedures_with_external_calls_strategy(
                remaining_count - 1,
                new_local_callees,
                external_callees_for_second.clone(),
                config_for_second.clone(),
            )
            .prop_map(move |mut rest| {
                let mut result = vec![procedure.clone()];
                result.append(&mut rest);
                result
            })
        })
        .boxed()
}

/// Strategy for a DAG of modules with specified depth.
///
/// Depth 1 = single level of leaf modules (only local calls)
/// Depth N = modules at level N can call procedures from levels 1..N-1
pub fn call_graph_strategy(depth: usize, procedures_per_module: usize) -> BoxedStrategy<CallGraph> {
    assert!(depth >= 1);

    let config = StrategyConfig::default();

    if depth == 1 {
        prop::collection::vec(module_strategy(procedures_per_module, config), 1..=2)
            .prop_map(CallGraph::new)
            .boxed()
    } else {
        call_graph_strategy(depth - 1, procedures_per_module)
            .prop_flat_map(move |lower_graph| {
                let external_callees: Vec<CallableProcedure> = lower_graph
                    .modules
                    .iter()
                    .flat_map(|module| module.callable_procedures())
                    .collect();

                let new_config = StrategyConfig::default();

                prop::collection::vec(
                    module_with_external_calls_strategy(
                        procedures_per_module,
                        external_callees,
                        new_config,
                    ),
                    1..=2,
                )
                .prop_map(move |new_modules| {
                    let mut all_modules = lower_graph.modules.clone();
                    all_modules.extend(new_modules);
                    CallGraph::new(all_modules)
                })
            })
            .boxed()
    }
}
