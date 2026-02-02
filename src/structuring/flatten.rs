//! Control flow flattening pass.
//!
//! This pass converts a CFG with branch markers (`IfBranch`, `WhileBranch`, `RepeatBranch`)
//! and conditional edges into a flat sequence of structured statements (`If`, `While`, `Repeat`).
//!
//! ## Algorithm
//!
//! The pass processes CFG nodes in **post-order** (inner structures first, then outer).
//! For each node containing a branch marker:
//!
//! 1. **`IfBranch`** → `Stmt::If`: Identifies then/else targets from conditional edges,
//!    finds the join node where branches reconverge, collects code from each region,
//!    and builds a structured `If` statement.
//!
//! 2. **`WhileBranch`** → `Stmt::While`: Identifies body and exit targets, collects
//!    loop body code (following edges until a back-edge to the header), and builds
//!    a `While` statement from the body.
//!
//! 3. **`RepeatBranch`** → `Stmt::Repeat`: Similar to while, but uses the iteration
//!    count from the condition and creates a `Repeat` statement with a loop variable.
//!
//! After all regions are collapsed, the CFG is linearized into a single statement sequence.
//!
//! ## Transformations
//!
//! **If-then-else region:**
//! ```text
//! [header: IfBranch(cond)] --true--> [then_block] ---> [join]
//!                          --false-> [else_block] -/
//! ```
//! becomes:
//! ```text
//! if (cond) { then_code } else { else_code }
//! ```
//!
//! **While loop:**
//! ```text
//! [header: WhileBranch(cond)] --true--> [body] --back-edge--> [header]
//!                             --false-> [exit]
//! ```
//! becomes:
//! ```text
//! while (cond) { body_code; }
//! ```
//!
//! **Repeat loop:**
//! ```text
//! [header: RepeatBranch(N)] --true--> [body] --back-edge--> [header]
//!                           --false-> [exit]
//! ```
//! becomes:
//! ```text
//! repeat(N) { body_code }
//! ```

use std::collections::HashSet;

use crate::cfg::{Cfg, Edge, NodeId};
use crate::ssa::{Condition, Expr, Stmt, Var};

/// Flatten a CFG into a sequence of structured statements.
///
/// This function processes the CFG in post-order, collapsing control flow
/// regions into structured statements. Post-order ensures inner structures
/// (nested ifs/loops) are collapsed before outer ones. After this pass, the
/// result is a flat sequence with no CFG edges - all control flow is represented
/// by `If`, `While`, and `Repeat` statements.
pub fn flatten_control_flow(mut cfg: Cfg) -> Vec<Stmt> {
    if cfg.nodes.is_empty() {
        return Vec::new();
    }

    let post_order = compute_post_order(&cfg);

    // Process in post-order (inner structures first, then outer).
    for &node in post_order.iter() {
        if node >= cfg.nodes.len() || cfg.nodes[node].code.is_empty() {
            continue;
        }

        // Check for branch markers and collapse accordingly.
        let branch_type = find_branch_type(&cfg.nodes[node].code);
        match branch_type {
            Some(BranchType::If) => collapse_if(&mut cfg, node),
            Some(BranchType::While) => collapse_while(&mut cfg, node),
            Some(BranchType::Repeat(count, loop_var)) => {
                collapse_repeat(&mut cfg, node, count, loop_var)
            }
            None => {}
        }
    }

    // Linearize the CFG into a single sequence.
    linearize(cfg)
}

#[derive(Debug, Clone)]
enum BranchType {
    If,
    While,
    Repeat(usize, Option<Var>),
}

/// Find the branch type from a node's code.
fn find_branch_type(code: &[Stmt]) -> Option<BranchType> {
    for stmt in code.iter().rev() {
        match stmt {
            Stmt::IfBranch(_) => return Some(BranchType::If),
            Stmt::WhileBranch(_) => return Some(BranchType::While),
            Stmt::RepeatBranch(Condition::Count { count, loop_var }) => {
                return Some(BranchType::Repeat(*count, loop_var.clone()));
            }
            _ => {}
        }
    }
    None
}

/// Collapse an if-then-else region into a `Stmt::If`.
fn collapse_if(cfg: &mut Cfg, header: NodeId) {
    // Find the condition expression and remove the IfBranch.
    let (cond, branch_idx) = extract_if_condition(&cfg.nodes[header].code);

    // Find then and else branches.
    let (then_node, else_node) = match find_conditional_targets(&cfg.nodes[header].next) {
        Some(targets) => targets,
        None => return,
    };

    // Find the join node (common successor of then and else).
    let join_node = find_join_node(cfg, then_node, else_node);

    // Collect code from then and else regions.
    let then_code = collect_region_code(cfg, then_node, join_node);
    let else_code = collect_region_code(cfg, else_node, join_node);

    // Build the If statement.
    let if_stmt = Stmt::If {
        cond,
        then_body: then_code,
        else_body: else_code,
    };

    // Remove the branch marker and insert the If statement.
    if let Some(idx) = branch_idx {
        cfg.nodes[header].code.remove(idx);
    }
    cfg.nodes[header].code.push(if_stmt);

    // Rewire edges: header now connects directly to join (or has no successors).
    cfg.nodes[header].next.clear();
    if let Some(join) = join_node {
        cfg.nodes[header].next.push(Edge::Unconditional {
            node: join,
            back_edge: false,
        });
        // Update join's predecessors.
        cfg.nodes[join]
            .prev
            .retain(|e| e.node() != then_node && e.node() != else_node);
        cfg.nodes[join].prev.push(Edge::Unconditional {
            node: header,
            back_edge: false,
        });
    }

    // Clear the collapsed nodes.
    clear_node(cfg, then_node);
    clear_node(cfg, else_node);
}

/// Collapse a while loop region into a `Stmt::While`.
fn collapse_while(cfg: &mut Cfg, header: NodeId) {
    // Find the condition expression and remove the WhileBranch.
    let (cond, branch_idx) = extract_while_condition(&cfg.nodes[header].code);

    // Find body and exit nodes.
    let (body_node, exit_node) = match find_conditional_targets(&cfg.nodes[header].next) {
        Some(targets) => targets,
        None => return,
    };

    // Collect code from the loop body.
    let body = collect_loop_body_code(cfg, header, body_node);

    // Build the While statement.
    let while_stmt = Stmt::While { cond, body };

    // Remove the branch marker and insert the While statement.
    if let Some(idx) = branch_idx {
        cfg.nodes[header].code.remove(idx);
    }
    cfg.nodes[header].code.push(while_stmt);

    // Rewire edges: header now connects directly to exit.
    cfg.nodes[header].next.clear();
    cfg.nodes[header].next.push(Edge::Unconditional {
        node: exit_node,
        back_edge: false,
    });

    // Update exit's predecessors.
    cfg.nodes[exit_node].prev.retain(|e| {
        e.node() != header
            || !matches!(
                e,
                Edge::Conditional {
                    true_branch: false,
                    ..
                }
            )
    });
    cfg.nodes[exit_node].prev.push(Edge::Unconditional {
        node: header,
        back_edge: false,
    });

    // Clear the body node.
    clear_node(cfg, body_node);
}

/// Collapse a repeat loop region into a `Stmt::Repeat`.
fn collapse_repeat(cfg: &mut Cfg, header: NodeId, count: usize, loop_var: Option<Var>) {
    // Find body and exit nodes.
    let (body_node, exit_node) = match find_conditional_targets(&cfg.nodes[header].next) {
        Some(targets) => targets,
        None => return,
    };

    // Collect code from the loop body.
    let body_code = collect_loop_body_code(cfg, header, body_node);

    // Get the loop variable from the condition (or create a dummy).
    let loop_var = loop_var.unwrap_or_else(|| Var::new(0));

    // Build the Repeat statement.
    let repeat_stmt = Stmt::Repeat {
        loop_var: loop_var.clone(),
        loop_count: count,
        body: body_code,
    };

    // Remove branch markers from header.
    cfg.nodes[header]
        .code
        .retain(|s| !matches!(s, Stmt::RepeatBranch(_)));
    cfg.nodes[header].code.push(repeat_stmt);

    // Rewire edges: header now connects directly to exit.
    cfg.nodes[header].next.clear();
    cfg.nodes[header].next.push(Edge::Unconditional {
        node: exit_node,
        back_edge: false,
    });

    // Update exit's predecessors.
    cfg.nodes[exit_node].prev.retain(|e| {
        e.node() != header
            || !matches!(
                e,
                Edge::Conditional {
                    true_branch: false,
                    ..
                }
            )
    });
    cfg.nodes[exit_node].prev.push(Edge::Unconditional {
        node: header,
        back_edge: false,
    });

    // Clear the body node.
    clear_node(cfg, body_node);
}

/// Extract the condition expression from an IfBranch.
fn extract_if_condition(code: &[Stmt]) -> (Expr, Option<usize>) {
    for (idx, stmt) in code.iter().enumerate().rev() {
        if let Stmt::IfBranch(Condition::Stack(expr)) = stmt {
            return (expr.clone(), Some(idx));
        }
    }
    (Expr::Unknown, None)
}

/// Extract the condition expression from a WhileBranch.
fn extract_while_condition(code: &[Stmt]) -> (Expr, Option<usize>) {
    for (idx, stmt) in code.iter().enumerate().rev() {
        if let Stmt::WhileBranch(Condition::Stack(expr)) = stmt {
            return (expr.clone(), Some(idx));
        }
    }
    (Expr::Unknown, None)
}

/// Find the true and false branch targets from conditional edges.
fn find_conditional_targets(edges: &[Edge]) -> Option<(NodeId, NodeId)> {
    let mut true_target = None;
    let mut false_target = None;

    for edge in edges {
        if let Edge::Conditional {
            node, true_branch, ..
        } = edge
        {
            if *true_branch {
                true_target = Some(*node);
            } else {
                false_target = Some(*node);
            }
        }
    }

    match (true_target, false_target) {
        (Some(t), Some(f)) => Some((t, f)),
        _ => None,
    }
}

/// Find the join node where then and else branches meet.
fn find_join_node(cfg: &Cfg, then_node: NodeId, else_node: NodeId) -> Option<NodeId> {
    // The join is the common successor of then and else.
    let then_succs: HashSet<_> = cfg.nodes[then_node].next.iter().map(|e| e.node()).collect();
    let else_succs: HashSet<_> = cfg.nodes[else_node].next.iter().map(|e| e.node()).collect();

    then_succs.intersection(&else_succs).next().copied()
}

/// Collect code from a region (for if branches).
fn collect_region_code(cfg: &mut Cfg, start: NodeId, end: Option<NodeId>) -> Vec<Stmt> {
    if Some(start) == end {
        return Vec::new();
    }

    let mut code = std::mem::take(&mut cfg.nodes[start].code);

    // Follow unconditional edges to collect more code (handles already-collapsed nested structures).
    let mut current = start;
    loop {
        let edges = &cfg.nodes[current].next;
        if edges.len() != 1 {
            break;
        }
        let next = edges[0].node();
        if Some(next) == end {
            break;
        }
        // Don't follow back-edges.
        if edges[0].back_edge() {
            break;
        }

        code.extend(std::mem::take(&mut cfg.nodes[next].code));
        current = next;
    }

    code
}

/// Collect code from a loop body.
fn collect_loop_body_code(cfg: &mut Cfg, header: NodeId, body_start: NodeId) -> Vec<Stmt> {
    let mut code = std::mem::take(&mut cfg.nodes[body_start].code);

    // Follow the body chain until we hit a back-edge to header.
    let mut current = body_start;
    loop {
        let edges = &cfg.nodes[current].next;
        if edges.is_empty() {
            break;
        }

        // Check if any edge is a back-edge to header.
        let has_back_edge = edges.iter().any(|e| e.back_edge() && e.node() == header);
        if has_back_edge {
            break;
        }

        // Follow unconditional forward edges.
        if edges.len() == 1 && !edges[0].back_edge() {
            let next = edges[0].node();
            code.extend(std::mem::take(&mut cfg.nodes[next].code));
            current = next;
        } else {
            break;
        }
    }

    code
}

/// Clear a node's code and edges.
fn clear_node(cfg: &mut Cfg, node: NodeId) {
    cfg.nodes[node].code.clear();
    cfg.nodes[node].next.clear();
    cfg.nodes[node].prev.clear();
}

/// Compute post-order traversal of the CFG.
fn compute_post_order(cfg: &Cfg) -> Vec<NodeId> {
    let mut visited = HashSet::new();
    let mut post_order = Vec::new();

    fn visit(cfg: &Cfg, node: NodeId, visited: &mut HashSet<NodeId>, post_order: &mut Vec<NodeId>) {
        if !visited.insert(node) {
            return;
        }
        for edge in &cfg.nodes[node].next {
            if !edge.back_edge() {
                visit(cfg, edge.node(), visited, post_order);
            }
        }
        post_order.push(node);
    }

    if !cfg.nodes.is_empty() {
        visit(cfg, 0, &mut visited, &mut post_order);
    }

    post_order
}

/// Linearize the CFG into a single sequence of statements.
fn linearize(cfg: Cfg) -> Vec<Stmt> {
    let mut result = Vec::new();
    let mut visited = HashSet::new();
    let mut stack = vec![0usize];

    while let Some(node) = stack.pop() {
        if node >= cfg.nodes.len() || !visited.insert(node) {
            continue;
        }

        result.extend(cfg.nodes[node].code.iter().cloned());

        // Add successors in reverse order so they're processed in order.
        for edge in cfg.nodes[node].next.iter().rev() {
            if !edge.back_edge() {
                stack.push(edge.node());
            }
        }
    }

    result
}
