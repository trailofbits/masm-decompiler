//! Stack utilities used during SSA lifting.

use std::collections::VecDeque;

use super::Var;

/// Symbolic stack used during SSA lifting.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct SsaStack {
    /// Current stack contents, bottom to top.
    stack: VecDeque<Var>,
    /// Minimum required depth inferred from pops.
    required_depth: usize,
}

impl SsaStack {
    /// Build a stack from entry inputs.
    pub fn from_inputs(inputs: Vec<Var>) -> Self {
        let required_depth = inputs.len();
        let mut stack = VecDeque::with_capacity(required_depth);
        for value in inputs {
            stack.push_back(value);
        }
        Self {
            stack,
            required_depth,
        }
    }

    /// Build a stack from explicit parts.
    pub fn from_parts(stack: VecDeque<Var>, required_depth: usize) -> Self {
        Self {
            stack,
            required_depth,
        }
    }

    /// Return the current stack depth.
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    /// Return the maximum required stack depth.
    pub fn required_depth(&self) -> usize {
        self.required_depth
    }

    /// Ensure the stack meets a minimum depth using synthesized inputs.
    pub fn ensure_depth<F>(&mut self, required_depth: usize, mut make_input: F)
    where
        F: FnMut() -> Var,
    {
        while self.stack.len() < required_depth {
            let value = make_input();
            self.stack.push_front(value);
            self.required_depth += 1;
        }
    }

    /// Pop a fixed number of values, padding with inputs as needed.
    pub fn pop_many<F>(&mut self, pops: usize, required_depth: usize, mut make_input: F) -> Vec<Var>
    where
        F: FnMut() -> Var,
    {
        let needed = required_depth.max(pops);
        self.ensure_depth(needed, &mut make_input);
        let mut out = Vec::with_capacity(pops);
        for _ in 0..pops {
            if let Some(value) = self.stack.pop_back() {
                out.push(value);
            } else {
                let value = make_input();
                self.required_depth += 1;
                out.push(value);
            }
        }
        out
    }

    /// Push a fixed number of new locals.
    pub fn push_many<F>(&mut self, pushes: usize, mut make_local: F) -> Vec<Var>
    where
        F: FnMut() -> Var,
    {
        let mut vars = Vec::with_capacity(pushes);
        for _ in 0..pushes {
            let value = make_local();
            self.stack.push_back(value.clone());
            vars.push(value);
        }
        vars
    }

    /// Peek a value at a depth from the top of stack.
    pub fn peek_from_top(&self, depth: usize) -> Option<Var> {
        let idx = self.stack.len().checked_sub(depth + 1)?;
        self.stack.get(idx).cloned()
    }

    /// Peek a contiguous range from the top of stack.
    pub fn peek_range_from_top(&self, offset: usize, count: usize) -> Option<Vec<Var>> {
        let len = self.stack.len();
        let start = len.checked_sub(offset + count)?;
        let mut out = Vec::with_capacity(count);
        for i in 0..count {
            out.push(self.stack.get(start + i)?.clone());
        }
        Some(out)
    }

    /// Permute the top `count` values using the provided permutation function.
    pub fn permute_top<F, I>(
        &mut self,
        count: usize,
        mut make_input: I,
        mut permute: F,
    ) -> (Vec<Var>, Vec<Var>)
    where
        F: FnMut(&mut Vec<Var>),
        I: FnMut() -> Var,
    {
        if count == 0 {
            return (Vec::new(), Vec::new());
        }
        self.ensure_depth(count, &mut make_input);
        let mut segment = self.peek_range_from_top(0, count).unwrap_or_else(Vec::new);
        let pops = segment.clone();
        permute(&mut segment);
        let pushes = segment.clone();
        let len = self.stack.len();
        let start = len - count;
        for (idx, value) in segment.iter().enumerate() {
            if let Some(slot) = self.stack.get_mut(start + idx) {
                *slot = value.clone();
            }
        }
        (pops, pushes)
    }

    /// Pad the stack to a target length with new values.
    pub fn pad_to_len<F>(&mut self, len: usize, mut make_value: F)
    where
        F: FnMut() -> Var,
    {
        while self.stack.len() < len {
            self.stack.push_back(make_value());
        }
    }

    /// Truncate the stack to a target length.
    pub fn truncate(&mut self, len: usize) {
        while self.stack.len() > len {
            self.stack.pop_back();
        }
    }

    /// Get a value by absolute index from the bottom.
    pub fn get(&self, index: usize) -> Option<Var> {
        self.stack.get(index).cloned()
    }

    /// Iterate over stack values from bottom to top.
    pub fn iter(&self) -> impl Iterator<Item = &Var> {
        self.stack.iter()
    }
}
