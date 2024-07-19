use std::{char, fmt};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Symbol {
    Char(char),
    Rule(usize),
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Symbol::Char(c) => write!(f, "{}", c),
            Symbol::Rule(r) => write!(f, "R{}", r),
        }
    }
}

#[derive(Eq, PartialEq, Hash, Debug)]
pub struct SymbolPair(pub Symbol, pub Symbol);

impl fmt::Display for SymbolPair {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}
