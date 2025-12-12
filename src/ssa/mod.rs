//! SSA IR skeleton.
//!
//! This keeps the crate layout aligned with `rewasm` while inference/SSA lowering is implemented.

pub mod lower;
pub mod out_of_ssa;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var {
    pub index: u32,
    pub subscript: u32,
}

impl Var {
    pub const fn new(index: u32, subscript: u32) -> Self {
        Self { index, subscript }
    }

    pub const fn no_sub(index: u32) -> Self {
        Self {
            index,
            subscript: 0,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    True,
    Var(Var),
    Constant(Constant),
    BinOp(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
    Xor,
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constant {
    Felt(u64),
    Word([u64; 4]),
    Defined(String),
}

impl From<miden_assembly_syntax::ast::ImmFelt> for Constant {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StackOp {
    pub inst: miden_assembly_syntax::ast::Instruction,
    pub pops: Vec<Var>,
    pub pushes: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemLoad {
    pub address: Vec<Var>,
    pub outputs: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemStore {
    pub address: Vec<Var>,
    pub values: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdvLoad {
    pub outputs: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AdvStore {
    pub values: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalLoad {
    pub index: u16,
    pub outputs: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LocalStore {
    pub index: u16,
    pub values: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Call {
    pub target: String,
    pub args: Vec<Var>,
    pub results: Vec<Var>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Intrinsic {
    pub name: String,
    pub args: Vec<Var>,
    pub results: Vec<Var>,
}

pub type LocalId = u32;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Assign {
        dst: Var,
        expr: Expr,
    },
    /// Return the given values (top of stack order).
    Return(Vec<Var>),
    Expr(Expr),
    Instr(miden_assembly_syntax::ast::Instruction),
    StackOp(StackOp),
    MemLoad(MemLoad),
    MemStore(MemStore),
    AdvLoad(AdvLoad),
    AdvStore(AdvStore),
    LocalLoad(LocalLoad),
    LocalStore(LocalStore),
    Call(Call),
    Exec(Call),
    SysCall(Call),
    DynCall {
        args: Vec<Var>,
        results: Vec<Var>,
    },
    Intrinsic(Intrinsic),
    Phi {
        var: Var,
        sources: Vec<Var>,
    },
    Branch(Expr),
    /// Lowering marker for repeat.N: initialize the synthetic loop counter.
    RepeatInit {
        local: LocalId,
        count: u32,
    },
    /// Lowering marker for repeat.N: branch on the synthetic loop counter.
    RepeatCond {
        local: LocalId,
        count: u32,
    },
    /// Lowering marker for repeat.N: increment the synthetic loop counter.
    RepeatStep {
        local: LocalId,
    },
    For {
        init: Box<Stmt>,
        cond: Expr,
        step: Box<Stmt>,
        body: Vec<Stmt>,
    },
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    Switch {
        expr: Expr,
        cases: Vec<(Constant, Vec<Stmt>)>,
        default: Vec<Stmt>,
    },
    While {
        cond: Expr,
        body: Vec<Stmt>,
    },
    Break,
    Continue,
    Unknown,
    Nop,
}
