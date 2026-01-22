//! SSA intermediate representation.

use std::collections::HashSet;

use miden_assembly_syntax::ast::{Immediate, ImmFelt, ImmU32, Instruction};
use miden_assembly_syntax::parser::PushValue;

pub mod lift;
pub mod stack;

pub use stack::SsaStack;

/// Index expression used for SSA subscripts.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum IndexExpr {
    /// Constant index value.
    Const(usize),
    /// Loop counter reference.
    LoopVar(usize),
    /// Sum of two index expressions.
    Add(Box<IndexExpr>, Box<IndexExpr>),
    /// Product of two index expressions.
    Mul(Box<IndexExpr>, Box<IndexExpr>),
}

/// Optional SSA subscript attached to a variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Subscript {
    /// No subscript.
    None,
    /// Subscript defined by an index expression.
    Expr(IndexExpr),
}

/// SSA variable identifier with an optional subscript.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var {
    /// Unique variable index within the arena.
    pub index: usize,
    /// SSA subscript for renaming, if any.
    pub subscript: Subscript,
}

impl Var {
    /// Create a new variable with no subscript.
    pub const fn new(index: usize) -> Self {
        Self {
            index,
            subscript: Subscript::None,
        }
    }

    /// Return a copy of this variable with a new subscript.
    pub fn with_subscript(&self, subscript: Subscript) -> Self {
        let mut result = self.clone();
        result.subscript = subscript;
        result
    }
}

/// Allocator for unique SSA variable IDs.
#[derive(Debug, Clone, Default)]
pub struct VarArena {
    /// Next available variable index.
    next_id: usize,
}

impl VarArena {
    /// Create a new arena starting at index 0.
    pub const fn new() -> Self {
        Self { next_id: 0 }
    }

    /// Allocate a fresh SSA variable.
    pub fn new_var(&mut self) -> Var {
        let v = Var::new(self.next_id);
        self.next_id += 1;
        v
    }

    /// Return the next variable index without allocating.
    pub fn next_id(&self) -> usize {
        self.next_id
    }
}

/// SSA expression tree.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    /// Boolean true literal.
    True,
    /// Variable reference.
    Var(Var),
    /// Constant literal.
    Constant(Constant),
    /// Binary operator application.
    Binary(BinOp, Box<Expr>, Box<Expr>),
    /// Unary operator application.
    Unary(UnOp, Box<Expr>),
    /// Placeholder for unknown expressions.
    Unknown,
}

/// Binary operator used in expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    /// Addition.
    Add,
    /// Subtraction.
    Sub,
    /// Multiplication.
    Mul,
    /// Division.
    Div,
    /// Bitwise and.
    And,
    /// Bitwise or.
    Or,
    /// Bitwise xor.
    Xor,
    /// Equality comparison.
    Eq,
    /// Inequality comparison.
    Neq,
    /// Less-than comparison.
    Lt,
    /// Less-than-or-equal comparison.
    Lte,
    /// Greater-than comparison.
    Gt,
    /// Greater-than-or-equal comparison.
    Gte,
}

/// Unary operator used in expressions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// Logical not.
    Not,
    /// Arithmetic negation.
    Neg,
}

/// Constant literal used in expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constant {
    /// Field element literal.
    Felt(u64),
    /// Word literal (4 felts).
    Word([u64; 4]),
    /// Named constant identifier.
    Defined(String),
}

impl From<miden_assembly_syntax::ast::ImmFelt> for Constant {
    /// Convert a felt immediate into a constant.
    fn from(imm: miden_assembly_syntax::ast::ImmFelt) -> Self {
        match imm {
            miden_assembly_syntax::ast::Immediate::Value(span) => {
                Constant::Felt(span.inner().as_int())
            }
            miden_assembly_syntax::ast::Immediate::Constant(id) => {
                Constant::Defined(id.to_string())
            }
        }
    }
}

impl From<miden_assembly_syntax::parser::PushValue> for Constant {
    /// Convert a push literal into a constant.
    fn from(val: miden_assembly_syntax::parser::PushValue) -> Self {
        match val {
            miden_assembly_syntax::parser::PushValue::Int(int) => match int {
                miden_assembly_syntax::parser::IntValue::U8(v) => Constant::Felt(v as u64),
                miden_assembly_syntax::parser::IntValue::U16(v) => Constant::Felt(v as u64),
                miden_assembly_syntax::parser::IntValue::U32(v) => Constant::Felt(v as u64),
                miden_assembly_syntax::parser::IntValue::Felt(f) => Constant::Felt(f.as_int()),
            },
            miden_assembly_syntax::parser::PushValue::Word(w) => Constant::Word([
                w.0[0].as_int(),
                w.0[1].as_int(),
                w.0[2].as_int(),
                w.0[3].as_int(),
            ]),
        }
    }
}

impl From<Constant> for Expr {
    /// Convert a constant into an expression.
    fn from(constant: Constant) -> Self {
        Expr::Constant(constant)
    }
}

impl From<PushValue> for Expr {
    /// Convert a push literal into an expression.
    fn from(value: PushValue) -> Self {
        Expr::Constant(Constant::from(value))
    }
}

impl From<&PushValue> for Expr {
    /// Convert a push literal reference into an expression.
    fn from(value: &PushValue) -> Self {
        Expr::from(*value)
    }
}

impl From<&Immediate<PushValue>> for Expr {
    /// Convert a push immediate into an expression.
    fn from(imm: &Immediate<PushValue>) -> Self {
        match imm {
            Immediate::Value(span) => Expr::from(span.inner()),
            Immediate::Constant(id) => Expr::Constant(Constant::Defined(id.to_string())),
        }
    }
}

impl From<&ImmFelt> for Expr {
    /// Convert a felt immediate into an expression.
    fn from(imm: &ImmFelt) -> Self {
        match imm {
            Immediate::Value(span) => Expr::Constant(Constant::Felt(span.inner().as_int())),
            Immediate::Constant(id) => Expr::Constant(Constant::Defined(id.to_string())),
        }
    }
}

impl From<&ImmU32> for Expr {
    /// Convert a u32 immediate into an expression.
    fn from(imm: &ImmU32) -> Self {
        match imm {
            Immediate::Value(span) => Expr::Constant(Constant::Felt(u64::from(*span.inner()))),
            Immediate::Constant(id) => Expr::Constant(Constant::Defined(id.to_string())),
        }
    }
}

/// Stack operation capturing explicit pops and pushes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackOp {
    /// Instruction that produced this stack operation.
    pub inst: miden_assembly_syntax::ast::Instruction,
    /// Variables popped from the stack.
    pub pops: Vec<Var>,
    /// Variables pushed onto the stack.
    pub pushes: Vec<Var>,
}

/// SSA representation of a memory load.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemLoad {
    /// Address operands for the load.
    pub address: Vec<Var>,
    /// Output variables produced by the load.
    pub outputs: Vec<Var>,
}

/// SSA representation of a memory store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemStore {
    /// Address operands for the store.
    pub address: Vec<Var>,
    /// Values written by the store.
    pub values: Vec<Var>,
}

/// SSA representation of an advice load.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdvLoad {
    /// Output variables produced by the load.
    pub outputs: Vec<Var>,
}

/// SSA representation of an advice store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdvStore {
    /// Values consumed by the store.
    pub values: Vec<Var>,
}

/// SSA representation of a local load.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalLoad {
    /// Local variable index.
    pub index: u16,
    /// Output variables produced by the load.
    pub outputs: Vec<Var>,
}

/// SSA representation of a local store.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalStore {
    /// Local variable index.
    pub index: u16,
    /// Values written to the local.
    pub values: Vec<Var>,
}

/// SSA representation of a call-like instruction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    /// Fully-qualified target name.
    pub target: String,
    /// Input arguments popped from the stack.
    pub args: Vec<Var>,
    /// Output results pushed onto the stack.
    pub results: Vec<Var>,
}

/// SSA representation of a named intrinsic operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Intrinsic {
    /// Intrinsic name.
    pub name: String,
    /// Input arguments popped from the stack.
    pub args: Vec<Var>,
    /// Output results pushed onto the stack.
    pub results: Vec<Var>,
}

/// Intermediate representation used for SSA.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    /// Assignment to a new SSA variable.
    Assign {
        dest: Var,
        expr: Expr,
    },
    /// Side-effect-free expression used as a statement.
    Expr(Expr),
    /// Branch condition marker.
    Branch(Expr),
    /// Raw instruction placeholder.
    Inst(Instruction),
    /// No-op placeholder.
    Nop,
    /// Stack operation with explicit pops/pushes.
    StackOp(StackOp),
    /// Memory load operation.
    MemLoad(MemLoad),
    /// Memory store operation.
    MemStore(MemStore),
    /// Advice stack load.
    AdvLoad(AdvLoad),
    /// Advice stack store.
    AdvStore(AdvStore),
    /// Local variable load.
    LocalLoad(LocalLoad),
    /// Local variable store.
    LocalStore(LocalStore),
    /// Call to a known procedure.
    Call(Call),
    /// Exec call to a known procedure.
    Exec(Call),
    /// Syscall to a known procedure.
    SysCall(Call),
    /// Dynamic call with unknown target.
    DynCall {
        args: Vec<Var>,
        results: Vec<Var>,
    },
    /// Named intrinsic operation.
    Intrinsic(Intrinsic),
    /// Phi-node merging multiple sources.
    Phi {
        var: Var,
        sources: Vec<Var>,
    },
    /// Repeat loop with a known iteration count.
    Repeat {
        loop_var: Var,
        loop_count: usize,
        body: Vec<Stmt>,
    },
    /// If/else conditional.
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    /// Switch statement over a selector expression.
    Switch {
        expr: Expr,
        cases: Vec<(Constant, Vec<Stmt>)>,
        default: Vec<Stmt>,
    },
    /// For loop with explicit init/step.
    For {
        init: Box<Stmt>,
        cond: Expr,
        step: Box<Stmt>,
        body: Vec<Stmt>,
    },
    /// While loop with a condition expression.
    While {
        cond: Expr,
        body: Vec<Stmt>,
    },
    /// Break out of a loop.
    Break,
    /// Continue to the next loop iteration.
    Continue,
    /// Placeholder for unknown operations.
    Unknown,
    /// Return the given values (top of stack order).
    Return(Vec<Var>),
}

impl Expr {
    /// Return the set of variables referenced by this expression.
    pub fn used_vars(&self) -> HashSet<Var> {
        match self {
            Expr::Var(v) => HashSet::from([v.clone()]),
            Expr::Binary(_, left, right) => {
                let mut vars = left.used_vars();
                vars.extend(right.used_vars());
                vars
            }
            Expr::Unary(_, expr) => expr.used_vars(),
            _ => HashSet::new(),
        }
    }
}

impl Stmt {
    /// Return variables used by this statement.
    pub fn used_vars(&self) -> HashSet<Var> {
        match self {
            Stmt::Assign { expr, .. } => expr.used_vars(),
            Stmt::Expr(expr) => expr.used_vars(),
            Stmt::Branch(expr) => expr.used_vars(),
            Stmt::StackOp(op) => op.pops.iter().cloned().collect(),
            Stmt::MemLoad(mem) => mem.address.iter().cloned().collect(),
            Stmt::MemStore(mem) => mem
                .address
                .iter()
                .chain(mem.values.iter())
                .cloned()
                .collect(),
            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                call.args.iter().cloned().collect()
            }
            Stmt::DynCall { args, .. } => args.iter().cloned().collect(),
            Stmt::Intrinsic(intr) => intr.args.iter().cloned().collect(),
            Stmt::AdvLoad(_) => HashSet::new(),
            Stmt::AdvStore(store) => store.values.iter().cloned().collect(),
            Stmt::LocalLoad(_) => HashSet::new(),
            Stmt::LocalStore(store) => store.values.iter().cloned().collect(),
            Stmt::Phi { sources, .. } => sources.iter().cloned().collect(),
            Stmt::Repeat { body, .. } => body.iter().flat_map(|s| s.used_vars()).collect(),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let mut vars = cond.used_vars();
                for s in then_body {
                    vars.extend(s.used_vars());
                }
                for s in else_body {
                    vars.extend(s.used_vars());
                }
                vars
            }
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                let mut vars = expr.used_vars();
                for (_, body) in cases {
                    for s in body {
                        vars.extend(s.used_vars());
                    }
                }
                for s in default {
                    vars.extend(s.used_vars());
                }
                vars
            }
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => {
                let mut vars = init.used_vars();
                vars.extend(cond.used_vars());
                vars.extend(step.used_vars());
                for s in body {
                    vars.extend(s.used_vars());
                }
                vars
            }
            Stmt::While { cond, body } => {
                let mut vars = cond.used_vars();
                for s in body {
                    vars.extend(s.used_vars());
                }
                vars
            }
            Stmt::Return(vals) => vals.iter().cloned().collect(),
            Stmt::Inst(_)
            | Stmt::Nop
            | Stmt::Break
            | Stmt::Continue
            | Stmt::Unknown => HashSet::new(),
        }
    }
}
