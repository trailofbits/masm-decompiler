use miden_assembly_syntax::ast::{Block, Instruction, Op, Procedure};

use crate::ssa::{BinOp, Constant, Expr, Stmt, Var};

use super::{BasicBlock, Cfg, Edge, NodeId};

#[derive(Debug)]
pub enum CfgError {
    EmptyProcedure,
}

pub fn build_cfg_for_proc(proc: &Procedure) -> Result<Cfg, CfgError> {
    let mut builder = Builder::new();
    if proc.body().is_empty() {
        return Err(CfgError::EmptyProcedure);
    }
    let entry_id = builder.new_block();
    builder.build_block(proc.body(), entry_id);
    Ok(builder.cfg)
}

struct Builder {
    cfg: Cfg,
}

impl Builder {
    fn new() -> Self {
        Self {
            cfg: Cfg::default(),
        }
    }

    /// Create a new variable.
    fn new_var(&mut self) -> Var {
        self.cfg.arena.new_var()
    }

    /// Create a new basic block.
    fn new_block(&mut self) -> NodeId {
        let id = self.cfg.nodes.len();
        self.cfg.nodes.push(BasicBlock::default());
        id
    }

    /// Add an edge between two basic blocks.
    fn add_edge(&mut self, from: NodeId, to: NodeId, edge: Edge) {
        self.cfg.nodes[from].next.push(edge);
        let prev_edge = match edge {
            Edge::Unconditional { back_edge, .. } => Edge::Unconditional {
                node: from,
                back_edge,
            },
            Edge::Conditional {
                back_edge,
                true_branch,
                ..
            } => Edge::Conditional {
                node: from,
                back_edge,
                true_branch,
            },
        };
        self.cfg.nodes[to].prev.push(prev_edge);
    }

    /// Build CFG for a block starting at `current`, returning the last block ID.
    fn build_block(&mut self, block: &Block, mut current_id: NodeId) -> NodeId {
        for op in block.iter() {
            match op {
                Op::Inst(inst) => {
                    current_id = self.build_inst(inst.inner(), current_id);
                }
                Op::If {
                    then_blk, else_blk, ..
                } => {
                    current_id = self.build_if(then_blk, else_blk, current_id);
                }
                Op::Repeat { count, body, .. } => {
                    current_id = self.build_repeat(*count, body, current_id);
                }
                Op::While { body, .. } => {
                    current_id = self.build_while(body, current_id);
                }
            }
        }
        current_id
    }

    /// Build an instruction in the current block.
    fn build_inst(&mut self, inst: &Instruction, current_id: NodeId) -> NodeId {
        self.cfg.nodes[current_id]
            .code
            .push(Stmt::Inst(inst.clone()));

        current_id
    }

    /// If statements are lifted into a CFG structure with explicit header,
    /// then, else, and join blocks.
    fn build_if(&mut self, then_body: &Block, else_body: &Block, preheader_id: NodeId) -> NodeId {
        let header_id = self.new_block();
        let then_id = self.new_block();
        let else_id = self.new_block();
        let join_id = self.new_block();

        self.add_edge(
            preheader_id,
            header_id,
            Edge::Unconditional {
                node: header_id,
                back_edge: false,
            },
        );

        // Create branch header with condition. The condition is unknown in this
        // phase, and is filled in with the correct value during SSA lifting.
        self.cfg.nodes[header_id]
            .code
            .push(Stmt::Branch(Expr::Unknown));
        self.add_edge(
            header_id,
            then_id,
            Edge::Conditional {
                node: then_id,
                back_edge: false,
                true_branch: true,
            },
        );
        self.add_edge(
            header_id,
            else_id,
            Edge::Conditional {
                node: else_id,
                back_edge: false,
                true_branch: false,
            },
        );

        // Build then body.
        let then_exit_id = self.build_block(then_body, then_id);
        self.add_edge(
            then_exit_id,
            join_id,
            Edge::Unconditional {
                node: join_id,
                back_edge: false,
            },
        );

        // Build else body.
        let else_exit_id = self.build_block(else_body, else_id);
        self.add_edge(
            else_exit_id,
            join_id,
            Edge::Unconditional {
                node: join_id,
                back_edge: false,
            },
        );

        join_id
    }

    // While loops are lifted into a CFG structure with explicit loop header, body, and exit blocks.
    fn build_while(&mut self, body: &Block, preheader_id: NodeId) -> NodeId {
        let header_id = self.new_block();
        let body_id = self.new_block();
        let exit_id = self.new_block();

        self.add_edge(
            preheader_id,
            header_id,
            Edge::Unconditional {
                node: header_id,
                back_edge: false,
            },
        );

        // Create loop header with condition. The condition is unknown in this
        // phase, and is filled in with the correct value during SSA lifting.
        self.cfg.nodes[header_id]
            .code
            .push(Stmt::Branch(Expr::Unknown));
        self.add_edge(
            header_id,
            body_id,
            Edge::Conditional {
                node: body_id,
                back_edge: false,
                true_branch: true,
            },
        );
        self.add_edge(
            header_id,
            exit_id,
            Edge::Conditional {
                node: exit_id,
                back_edge: false,
                true_branch: false,
            },
        );

        // Build loop body.
        let body_exit_id = self.build_block(body, body_id);
        self.add_edge(
            body_exit_id,
            header_id,
            Edge::Unconditional {
                node: header_id,
                back_edge: true,
            },
        );

        exit_id
    }

    /// Repeat loops are lifted into a CFG structure with explicit loop header, body, and exit blocks.
    fn build_repeat(&mut self, count: u32, body: &Block, preheader_id: NodeId) -> NodeId {
        let header_id = self.new_block();
        let body_id = self.new_block();
        let exit_id = self.new_block();

        let phi_var = self.new_var();
        let step_var = self.new_var();

        // We need to introduce a loop counter variable here to distinguish
        // repeat loops from while loops during SSA lifting.
        let init_var = self.new_var();
        self.cfg.nodes[preheader_id].code.push(Stmt::Assign {
            dest: init_var.clone(),
            expr: Expr::Constant(Constant::Felt(0)),
        });
        self.add_edge(
            preheader_id,
            header_id,
            Edge::Unconditional {
                node: header_id,
                back_edge: false,
            },
        );

        // Create loop header with phi and condition.
        self.cfg.nodes[header_id].code.push(Stmt::Phi {
            var: phi_var.clone(),
            sources: vec![init_var, step_var.clone()],
        });
        self.cfg.nodes[header_id]
            .code
            .push(Stmt::Branch(Expr::BinOp(
                BinOp::Lt,
                Box::new(Expr::Var(phi_var.clone())),
                Box::new(Expr::Constant(Constant::Felt(count as u64))),
            )));

        self.add_edge(
            header_id,
            body_id,
            Edge::Conditional {
                node: body_id,
                back_edge: false,
                true_branch: true,
            },
        );
        self.add_edge(
            header_id,
            exit_id,
            Edge::Conditional {
                node: exit_id,
                back_edge: false,
                true_branch: false,
            },
        );

        // Build loop body and increment loop counter.
        let body_exit_id = self.build_block(body, body_id);
        self.cfg.nodes[body_exit_id].code.push(Stmt::Assign {
            dest: step_var,
            expr: Expr::BinOp(
                BinOp::Add,
                Box::new(Expr::Var(phi_var)),
                Box::new(Expr::Constant(Constant::Felt(1))),
            ),
        });
        self.add_edge(
            body_exit_id,
            header_id,
            Edge::Unconditional {
                node: header_id,
                back_edge: true,
            },
        );

        exit_id
    }
}
