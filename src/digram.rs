use crate::symbol::{Symbol, SymbolPair};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Digram {
    rule_id: usize,
    left_symbol: Symbol,
    left_index: usize,
    right_symbol: Symbol,
    right_index: usize,
}

impl Digram {
    pub fn new(rule_id: usize, left: (Symbol, usize), right: (Symbol, usize)) -> Self {
        Self {
            rule_id,
            left_symbol: left.0,
            left_index: left.1,
            right_symbol: right.0,
            right_index: right.1,
        }
    }

    pub fn get_left_id(&self) -> usize {
        self.left_index
    }

    pub fn get_right_id(&self) -> usize {
        self.right_index
    }

    pub fn get_rule_id(&self) -> usize {
        self.rule_id
    }

    pub fn get_left_symbol(&self) -> Symbol {
        self.left_symbol
    }

    pub fn get_right_symbol(&self) -> Symbol {
        self.right_symbol
    }

    pub fn pair(&self) -> SymbolPair {
        SymbolPair(self.left_symbol, self.right_symbol)
    }
}
