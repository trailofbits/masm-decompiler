//! Symbolic stack for lifting.
//!
//! This module provides a symbolic stack that tracks variables during lifting,
//! modeled after the provenance stack used in signature inference.

use std::collections::VecDeque;

use crate::ir::Var;

/// Symbolic stack tracking variables during lifting.
///
/// The stack grows to the right (back). Variables are created with their
/// birth depth set to the stack depth at the time of creation.
#[derive(Debug, Clone, Default)]
pub struct SymbolicStack {
    /// Stack contents, bottom to top.
    stack: VecDeque<Var>,
}

impl SymbolicStack {
    /// Create a new empty stack.
    pub fn new() -> Self {
        Self {
            stack: VecDeque::new(),
        }
    }

    /// Return the current stack depth.
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Check if the stack is empty.
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Push a new variable onto the stack.
    ///
    /// The variable's stack_depth should be set to the current stack depth
    /// before pushing (i.e., the depth at which it is born).
    pub fn push(&mut self, var: Var) {
        self.stack.push_back(var);
    }

    /// Pop a variable from the top of the stack.
    ///
    /// # Panics
    ///
    /// Panics if the stack is empty.
    pub fn pop(&mut self) -> Var {
        self.stack.pop_back().expect("stack underflow")
    }

    /// Pop multiple variables from the stack, returning them in pop order
    /// (top of stack first).
    pub fn pop_n(&mut self, n: usize) -> Vec<Var> {
        let mut result = Vec::with_capacity(n);
        for _ in 0..n {
            result.push(self.pop());
        }
        result
    }

    /// Peek at the variable at the given depth from the top (0 = top).
    pub fn peek(&self, depth: usize) -> Option<&Var> {
        if depth >= self.stack.len() {
            return None;
        }
        self.stack.get(self.stack.len() - 1 - depth)
    }

    /// Get the top n variables without removing them (top of stack first).
    pub fn top_n(&self, n: usize) -> Vec<Var> {
        let len = self.stack.len();
        if n > len {
            return self.stack.iter().rev().cloned().collect();
        }
        self.stack.iter().skip(len - n).rev().cloned().collect()
    }

    /// Ensure the stack has at least the given depth by pushing input variables.
    ///
    /// Returns the variables that were created to satisfy the depth requirement.
    pub fn ensure_depth(&mut self, required_depth: usize) -> Vec<Var> {
        let mut inputs = Vec::new();
        while self.stack.len() < required_depth {
            // Input variables are pushed at the front (bottom of stack).
            // Their stack_depth is 0, 1, 2, ... from bottom.
            let depth = self.stack.len();
            let var = Var::new(depth);
            self.stack.push_front(var.clone());
            inputs.push(var);
        }
        inputs
    }

    /// Apply a stack effect: pop `pops` values, push `pushes` new variables.
    ///
    /// The `required_depth` is ensured before popping. Returns the popped
    /// variables and the newly pushed variables.
    pub fn apply(
        &mut self,
        pops: usize,
        pushes: usize,
        required_depth: usize,
    ) -> (Vec<Var>, Vec<Var>) {
        self.ensure_depth(required_depth);

        // Pop values (top of stack first).
        let popped = self.pop_n(pops);

        // Push new variables with their birth depth.
        let mut pushed = Vec::with_capacity(pushes);
        for _ in 0..pushes {
            let depth = self.stack.len();
            let var = Var::new(depth);
            self.stack.push_back(var.clone());
            pushed.push(var);
        }

        (popped, pushed)
    }

    /// Duplicate the variable at the given depth from top onto the top.
    pub fn dup(&mut self, depth: usize) {
        if let Some(var) = self.peek(depth).cloned() {
            // Duplication creates a reference to the same variable,
            // not a new variable.
            self.stack.push_back(var);
        }
    }

    /// Swap the top element with the element at the given depth.
    pub fn swap(&mut self, depth: usize) {
        let len = self.stack.len();
        if depth > 0 && depth < len {
            let top_idx = len - 1;
            let other_idx = len - 1 - depth;
            self.stack.swap(top_idx, other_idx);
        }
    }

    /// Move the element at the given depth to the top.
    pub fn movup(&mut self, depth: usize) {
        let len = self.stack.len();
        if depth > 0 && depth < len {
            let idx = len - 1 - depth;
            if let Some(var) = self.stack.remove(idx) {
                self.stack.push_back(var);
            }
        }
    }

    /// Move the top element down to the given depth.
    pub fn movdn(&mut self, depth: usize) {
        let len = self.stack.len();
        if depth > 0 && depth < len {
            if let Some(var) = self.stack.pop_back() {
                let idx = len - 1 - depth;
                self.stack.insert(idx, var);
            }
        }
    }

    /// Get an iterator over the stack from bottom to top.
    pub fn iter(&self) -> impl Iterator<Item = &Var> {
        self.stack.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_pop() {
        let mut stack = SymbolicStack::new();
        stack.push(Var::new(0));
        stack.push(Var::new(1));
        assert_eq!(stack.len(), 2);

        let v = stack.pop();
        assert_eq!(v.stack_depth, 1);
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn test_ensure_depth() {
        let mut stack = SymbolicStack::new();
        let inputs = stack.ensure_depth(3);
        assert_eq!(stack.len(), 3);
        assert_eq!(inputs.len(), 3);
        // Inputs are created with depths 0, 1, 2 from bottom.
        assert_eq!(inputs[0].stack_depth, 0);
        assert_eq!(inputs[1].stack_depth, 1);
        assert_eq!(inputs[2].stack_depth, 2);
    }

    #[test]
    fn test_apply() {
        let mut stack = SymbolicStack::new();
        // Start with 2 inputs.
        stack.ensure_depth(2);

        // Apply add: pops 2, pushes 1.
        let (popped, pushed) = stack.apply(2, 1, 2);
        assert_eq!(popped.len(), 2);
        assert_eq!(pushed.len(), 1);
        assert_eq!(stack.len(), 1);
        // The new variable is born at depth 0.
        assert_eq!(pushed[0].stack_depth, 0);
    }

    #[test]
    fn test_dup() {
        let mut stack = SymbolicStack::new();
        stack.push(Var::new(0));
        stack.push(Var::new(1));
        stack.dup(1); // Duplicate the element at depth 1 (second from top).
        assert_eq!(stack.len(), 3);
        let top = stack.pop();
        assert_eq!(top.stack_depth, 0); // Same variable as the one at depth 1.
    }

    #[test]
    fn test_swap() {
        let mut stack = SymbolicStack::new();
        stack.push(Var::new(0));
        stack.push(Var::new(1));
        stack.swap(1);
        assert_eq!(stack.peek(0).unwrap().stack_depth, 0);
        assert_eq!(stack.peek(1).unwrap().stack_depth, 1);
    }
}
