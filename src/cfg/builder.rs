use miden_assembly_syntax::ast::{Block, Op, Procedure};

use super::{BasicBlock, Cfg, Edge, EdgeCond, EdgeType, NodeId};

#[derive(Debug)]
pub enum CfgBuildError {
    EmptyProcedure,
}

pub fn build_cfg_for_proc(proc: &Procedure) -> Result<Cfg, CfgBuildError> {
    let mut builder = Builder::new();
    if proc.body().is_empty() {
        return Err(CfgBuildError::EmptyProcedure);
    }
    let exit = builder.build_block(proc.body(), builder.entry);
    builder.finalize(exit);
    Ok(builder.cfg)
}

struct Builder {
    cfg: Cfg,
    entry: NodeId,
    next_cond_idx: u32,
}

impl Builder {
    fn new() -> Self {
        let mut cfg = Cfg::default();
        let entry = cfg.nodes.len();
        cfg.nodes.push(BasicBlock::default());
        Self { cfg, entry, next_cond_idx: 0 }
    }

    fn finalize(&mut self, exit: NodeId) {
        // No special exit handling needed yet; ensure exit has no dangling prev/next symmetry issues.
        let _ = exit;
    }

    fn new_block(&mut self) -> NodeId {
        let id = self.cfg.nodes.len();
        self.cfg.nodes.push(BasicBlock::default());
        id
    }

    fn add_edge(&mut self, from: NodeId, to: NodeId, cond: EdgeCond, back_edge: bool) {
        self.cfg.nodes[from].next.push(Edge { cond, node: to, back_edge });
        self.cfg.nodes[to].prev.push(Edge { cond, node: from, back_edge });
    }

    /// Build CFG for a block starting at `current`, returning the last block ID.
    fn build_block(&mut self, block: &Block, mut current: NodeId) -> NodeId {
        for op in block.iter() {
            match op {
                Op::Inst(inst) => {
                    self.cfg.nodes[current].code.push(crate::ssa::Stmt::Instr(inst.inner().clone()));
                }
                Op::If { then_blk, else_blk, .. } => {
                    let then_id = self.new_block();
                    let else_id = self.new_block();
                    let join_id = self.new_block();

                    let cond_idx = self.next_cond_idx;
                    self.next_cond_idx += 1;
                    self.add_edge(
                        current,
                        then_id,
                        EdgeCond { expr_index: cond_idx, edge_type: EdgeType::Conditional(true) },
                        false,
                    );
                    self.add_edge(
                        current,
                        else_id,
                        EdgeCond { expr_index: cond_idx, edge_type: EdgeType::Conditional(false) },
                        false,
                    );

                    let then_exit = self.build_block(then_blk, then_id);
                    let else_exit = self.build_block(else_blk, else_id);

                    self.add_edge(then_exit, join_id, EdgeCond::unconditional(), false);
                    self.add_edge(else_exit, join_id, EdgeCond::unconditional(), false);

                    current = join_id;
                }
                Op::Repeat { count, body, .. } => {
                    for _ in 0..*count {
                        current = self.build_block(body, current);
                    }
                }
                Op::While { body, .. } => {
                    // Loop structure: current -> body (true), current -> exit (false), body -> current (back edge)
                    let body_id = self.new_block();
                    let exit_id = self.new_block();

                    let cond_idx = self.next_cond_idx;
                    self.next_cond_idx += 1;
                    self.add_edge(
                        current,
                        body_id,
                        EdgeCond { expr_index: cond_idx, edge_type: EdgeType::Conditional(true) },
                        false,
                    );
                    self.add_edge(
                        current,
                        exit_id,
                        EdgeCond { expr_index: cond_idx, edge_type: EdgeType::Conditional(false) },
                        false,
                    );

                    let body_exit = self.build_block(body, body_id);
                    self.add_edge(body_exit, current, EdgeCond::unconditional(), true);

                    current = exit_id;
                }
            }
        }
        current
    }
}
