//! Dead code elimination for structured code.
//!
//! This module eliminates dead assignments from structured code using the
//! forward liveness analysis in `used_vars`.
//!
//! ## Algorithm
//!
//! 1. Run forward liveness analysis to identify dead statement paths
//! 2. Collect indices of dead `Assign` statements
//! 3. Remove statements at those indices (in reverse order to preserve indices)
//! 4. Iterate until a fixed point is reached (eliminating dead code may
//!    create new dead code when uses are removed)

use log::trace;
use std::collections::HashSet;

use crate::ir::Stmt;

use super::used_vars::{PathSegment, StmtPath, analyze_liveness};

const MAX_ELIMINATION_PASSES: usize = 100;

/// Eliminate dead code from structured statements.
///
/// This pass removes assignments whose results are never used.
/// It iterates until a fixed point is reached (no more eliminations possible).
pub fn eliminate_dead_code(stmts: &mut Vec<Stmt>) {
    for pass in 0..MAX_ELIMINATION_PASSES {
        let result = analyze_liveness(stmts);

        if result.dead_paths.is_empty() {
            trace!("DCE converged after {pass} passes");
            break;
        }

        trace!(
            "DCE pass {pass}: {} dead paths identified",
            result.dead_paths.len()
        );

        // Collect and remove dead statements.
        let changed = eliminate_at_paths(stmts, &result.dead_paths, &mut Vec::new());
        if !changed {
            break;
        }
    }
}

/// Eliminate statements at the specified paths.
///
/// Only `Assign` statements are eliminated; other statements have side effects.
/// Returns true if any statements were eliminated.
fn eliminate_at_paths(
    stmts: &mut Vec<Stmt>,
    dead_paths: &HashSet<StmtPath>,
    current_path: &mut StmtPath,
) -> bool {
    // Collect indices of statements to remove at this level.
    let mut indices_to_remove: Vec<usize> = Vec::new();
    let mut changed = false;

    for (i, stmt) in stmts.iter_mut().enumerate() {
        current_path.push(PathSegment::Index(i));

        match stmt {
            Stmt::Assign { .. } => {
                if dead_paths.contains(current_path) {
                    trace!("eliminating dead assignment at {:?}", current_path);
                    indices_to_remove.push(i);
                    changed = true;
                }
            }

            Stmt::Repeat { body, .. } => {
                current_path.push(PathSegment::Repeat);
                changed |= eliminate_at_paths(body, dead_paths, current_path);
                current_path.pop();
            }

            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                current_path.push(PathSegment::Then);
                changed |= eliminate_at_paths(then_body, dead_paths, current_path);
                current_path.pop();

                current_path.push(PathSegment::Else);
                changed |= eliminate_at_paths(else_body, dead_paths, current_path);
                current_path.pop();
            }

            Stmt::While { body, .. } => {
                current_path.push(PathSegment::While);
                changed |= eliminate_at_paths(body, dead_paths, current_path);
                current_path.pop();
            }

            // Other statements are not eliminated (side effects or not definitions).
            _ => {}
        }

        current_path.pop();
    }

    // Remove collected indices in reverse order to preserve earlier indices.
    for i in indices_to_remove.into_iter().rev() {
        stmts.remove(i);
    }

    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BinOp, Constant, Expr, IndexExpr, LoopVar, Var};

    fn var_with_subscript(stack_depth: usize, sub: i64) -> Var {
        Var {
            stack_depth,
            subscript: IndexExpr::Const(sub),
        }
    }

    #[test]
    fn test_eliminate_simple_dead_assign() {
        // v_0 = 1;  // DEAD
        // v_1 = 2;  // LIVE
        // return v_1;
        let mut stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        eliminate_dead_code(&mut stmts);

        assert_eq!(stmts.len(), 2);
        assert!(matches!(&stmts[0], Stmt::Assign { dest, .. } if dest.stack_depth == 1));
        assert!(matches!(&stmts[1], Stmt::Return(_)));
    }

    #[test]
    fn test_eliminate_redefined_before_use() {
        // v_0 = 1;  // DEAD - redefined before use
        // v_0 = 2;  // LIVE
        // return v_0;
        let mut stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        eliminate_dead_code(&mut stmts);

        assert_eq!(stmts.len(), 2);
        // The second assignment (v_0 = 2) should remain.
        assert!(matches!(
            &stmts[0],
            Stmt::Assign {
                expr: Expr::Constant(Constant::Felt(2)),
                ..
            }
        ));
        assert!(matches!(&stmts[1], Stmt::Return(_)));
    }

    #[test]
    fn test_preserve_used_before_redefine() {
        // v_0 = 1;      // LIVE - used before redefinition
        // v_1 = v_0;    // LIVE
        // v_0 = 2;      // DEAD - never used after
        // return v_1;
        let mut stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Var(var_with_subscript(0, 0)),
            },
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        eliminate_dead_code(&mut stmts);

        // v_0 = 1 and v_1 = v_0 should remain, v_0 = 2 should be eliminated.
        assert_eq!(stmts.len(), 3);
        assert!(
            matches!(&stmts[0], Stmt::Assign { dest, expr: Expr::Constant(Constant::Felt(1)), .. } if dest.stack_depth == 0)
        );
        assert!(matches!(&stmts[1], Stmt::Assign { dest, .. } if dest.stack_depth == 1));
        assert!(matches!(&stmts[2], Stmt::Return(_)));
    }

    #[test]
    fn test_eliminate_chain_of_dead() {
        // v_0 = 1;        // DEAD (after iteration, v_1 is dead so v_0 becomes dead)
        // v_1 = v_0 + 1;  // DEAD
        // v_2 = 3;        // LIVE
        // return v_2;
        let mut stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var(var_with_subscript(0, 0))),
                    Box::new(Expr::Constant(Constant::Felt(1))),
                ),
            },
            Stmt::Assign {
                dest: var_with_subscript(2, 2),
                expr: Expr::Constant(Constant::Felt(3)),
            },
            Stmt::Return(vec![var_with_subscript(2, 2)]),
        ];

        eliminate_dead_code(&mut stmts);

        // Both v_0 and v_1 should be eliminated through iteration.
        assert_eq!(stmts.len(), 2);
        assert!(matches!(&stmts[0], Stmt::Assign { dest, .. } if dest.stack_depth == 2));
        assert!(matches!(&stmts[1], Stmt::Return(_)));
    }

    #[test]
    fn test_eliminate_in_nested_if() {
        // if cond {
        //   v_0 = 1;  // DEAD
        //   v_1 = 2;  // LIVE
        // } else {
        //   v_2 = 3;  // DEAD
        // }
        // return v_1;
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::True,
                then_body: vec![
                    Stmt::Assign {
                        dest: var_with_subscript(0, 0),
                        expr: Expr::Constant(Constant::Felt(1)),
                    },
                    Stmt::Assign {
                        dest: var_with_subscript(1, 1),
                        expr: Expr::Constant(Constant::Felt(2)),
                    },
                ],
                else_body: vec![Stmt::Assign {
                    dest: var_with_subscript(2, 2),
                    expr: Expr::Constant(Constant::Felt(3)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        eliminate_dead_code(&mut stmts);

        assert_eq!(stmts.len(), 2);
        if let Stmt::If {
            then_body,
            else_body,
            ..
        } = &stmts[0]
        {
            assert_eq!(then_body.len(), 1); // Only v_1 assignment remains
            assert_eq!(else_body.len(), 0); // v_2 assignment removed
        } else {
            panic!("Expected If statement");
        }
    }

    #[test]
    fn test_eliminate_in_loop_with_symbolic_subscript() {
        // repeat.4 {
        //   v_(3-i) = const;  // Defines v_3, v_2, v_1, v_0
        // }
        // return v_0;  // Only v_0 is used

        let loop_var = LoopVar::new(0); // Outermost loop has depth 0

        let subscript_expr = IndexExpr::Add(
            Box::new(IndexExpr::Const(3)),
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(-1)),
                Box::new(IndexExpr::LoopVar(0)),
            )),
        );

        let var_in_loop = Var {
            stack_depth: 0,
            subscript: subscript_expr,
        };

        let mut stmts = vec![
            Stmt::Repeat {
                loop_var,
                loop_count: 4,
                body: vec![Stmt::Assign {
                    dest: var_in_loop.clone(),
                    expr: Expr::Constant(Constant::Felt(42)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        eliminate_dead_code(&mut stmts);

        // The loop should still exist because v_0 (when i=3) is used by return.
        assert_eq!(stmts.len(), 2);
        if let Stmt::Repeat { body, .. } = &stmts[0] {
            assert_eq!(body.len(), 1); // Assignment still exists
        } else {
            panic!("Expected Repeat statement");
        }
    }

    #[test]
    fn test_preserve_stores() {
        // MemStore is a side effect and should be preserved.
        use crate::ir::MemStore;

        let mut stmts = vec![Stmt::MemStore(MemStore {
            address: vec![var_with_subscript(0, 0)],
            values: vec![var_with_subscript(1, 1)],
        })];

        eliminate_dead_code(&mut stmts);

        // Store should be preserved.
        assert_eq!(stmts.len(), 1);
        assert!(matches!(&stmts[0], Stmt::MemStore(_)));
    }

    #[test]
    fn test_preserve_calls() {
        // Calls have side effects and should be preserved even if results unused.
        use crate::ir::Call;

        let mut stmts = vec![Stmt::Call(Call {
            target: "foo".to_string(),
            args: vec![],
            results: vec![var_with_subscript(0, 0)], // Result unused
        })];

        eliminate_dead_code(&mut stmts);

        // Call should be preserved.
        assert_eq!(stmts.len(), 1);
        assert!(matches!(&stmts[0], Stmt::Call(_)));
    }

    #[test]
    fn test_if_both_branches_live() {
        // if cond {
        //   v_0 = 1;  // LIVE
        // } else {
        //   v_0 = 2;  // LIVE
        // }
        // return v_0;
        let mut stmts = vec![
            Stmt::If {
                cond: Expr::True,
                then_body: vec![Stmt::Assign {
                    dest: var_with_subscript(0, 0),
                    expr: Expr::Constant(Constant::Felt(1)),
                }],
                else_body: vec![Stmt::Assign {
                    dest: var_with_subscript(0, 0),
                    expr: Expr::Constant(Constant::Felt(2)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        eliminate_dead_code(&mut stmts);

        // Both branches should be preserved.
        assert_eq!(stmts.len(), 2);
        if let Stmt::If {
            then_body,
            else_body,
            ..
        } = &stmts[0]
        {
            assert_eq!(then_body.len(), 1);
            assert_eq!(else_body.len(), 1);
        } else {
            panic!("Expected If statement");
        }
    }
}
