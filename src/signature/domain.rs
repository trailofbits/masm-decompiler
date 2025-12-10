use std::collections::HashMap;

/// Shape of a stack slot; currently coarse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SlotShape {
    Unknown,
    Felt,
    Word(u8),
    Tuple(u8),
}

/// Inclusive range with optional upper bound (None = unbounded).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Range {
    pub min: u32,
    pub max: Option<u32>,
}

impl Range {
    pub const fn exact(v: u32) -> Self {
        Self {
            min: v,
            max: Some(v),
        }
    }

    pub const fn unknown() -> Self {
        Self { min: 0, max: None }
    }

    pub fn add(&self, other: &Range) -> Range {
        Range {
            min: self.min.saturating_add(other.min),
            max: match (self.max, other.max) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProcSignature {
    Known {
        inputs: Range,
        outputs: Range,
        slots: Vec<SlotShape>,
        side_effects: bool,
    },
    Unknown,
}

impl ProcSignature {
    pub fn unknown() -> Self {
        ProcSignature::Unknown
    }
}

/// Provenance of a stack slot during abstract interpretation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Provenance {
    Input(u32),
    New(u32),
    Rewritten,
    Unknown,
}

#[derive(Debug, Default)]
pub struct SignatureMap {
    pub signatures: HashMap<String, ProcSignature>,
}

/// Small helper around a Vec<Provenance> with required-depth tracking.
#[derive(Debug, Default, Clone)]
pub struct ProvenanceStack {
    stack: Vec<Provenance>,
    pub required: u32,
}

impl ProvenanceStack {
    pub fn pop(&mut self) -> Provenance {
        if let Some(v) = self.stack.pop() {
            v
        } else {
            self.required = self.required.saturating_add(1);
            Provenance::Input(self.required - 1)
        }
    }

    pub fn push(&mut self, prov: Provenance) {
        self.stack.push(prov);
    }

    pub fn new_count_bounds(&self) -> (u32, Option<u32>) {
        let min = self
            .stack
            .iter()
            .filter(|p| matches!(p, Provenance::New(_)))
            .count() as u32;
        let max = self
            .stack
            .iter()
            .filter(|p| matches!(p, Provenance::New(_) | Provenance::Rewritten))
            .count() as u32;
        (min, Some(max))
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }

    pub fn clone_slots(&self) -> Vec<Provenance> {
        self.stack.clone()
    }

    pub fn replace_slots(&mut self, slots: Vec<Provenance>) {
        self.stack = slots;
    }
}
