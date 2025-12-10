//! Pretty-printing helpers.
//!
//! This will grow to match the `rewasm` `fmt` module; for now it just exposes a stub writer.

use crate::ssa::Stmt;

#[derive(Default)]
pub struct CodeWriter {
    output: String,
    indent: usize,
}

impl CodeWriter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn write_stmt(&mut self, stmt: &Stmt) {
        self.output.push_str(&format!("{:?}", stmt));
        self.output.push('\n');
    }

    pub fn indent(&mut self) {
        self.indent += 1;
    }

    pub fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    pub fn finish(self) -> String {
        self.output
    }
}
