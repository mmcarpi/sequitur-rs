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

    pub fn overlap(&self, other: &Digram) -> bool {
        (self.rule_id == other.rule_id)
            && ((self.right_index == other.left_index && self.left_symbol == other.right_symbol)
                || (other.right_index == self.left_index && other.left_symbol == self.right_symbol))
    }
}

#[cfg(test)]
mod test_symbol {
    use super::*;
    #[test]
    fn test_overlap() {
        let a = Symbol::Char('a');
        let b = Symbol::Char('b');

        let d1 = Digram::new(0, (a, 0), (a, 1));
        let d2 = Digram::new(0, (a, 1), (a, 2));

        assert!(d1.overlap(&d1));
        assert!(d1.overlap(&d2));
        assert!(d2.overlap(&d1));

        let d3 = Digram::new(0, (a, 2), (b, 3));
        assert!(!d2.overlap(&d3));
        assert!(!d3.overlap(&d2));

        let d1 = Digram::new(0, (a, 0), (a, 1));
        let d2 = Digram::new(0, (a, 2), (a, 3));

        assert!(!d1.overlap(&d2));
    }
}
