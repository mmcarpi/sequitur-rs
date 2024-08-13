use std::fmt;

use crate::digram::Digram;
use crate::dll::Dll;
use crate::symbol::Symbol;

#[derive(Eq, PartialEq, Hash, Copy, Clone, Debug)]
pub struct RuleUsage {
    rule_id: usize,
    index: usize,
}

impl RuleUsage {
    pub fn new(rule_id: usize, index: usize) -> Self {
        Self { rule_id, index }
    }

    pub fn get_rule_id(&self) -> usize {
        self.rule_id
    }

    pub fn get_index(&self) -> usize {
        self.index
    }
}

pub struct Rule {
    pub rhs: Dll<Symbol>,
    id: usize,
}

impl Rule {
    pub fn new(id: usize) -> Self {
        Self {
            rhs: Dll::new(),
            id,
        }
    }

    pub fn get_id(&self) -> usize {
        self.id
    }

    pub fn push(&mut self, s: Symbol) -> (usize, Option<Digram>) {
        let idx = self.rhs.push(s);
        (idx, self.digram_ending_at(idx))
    }

    pub fn digram_ending_at(&self, idx: usize) -> Option<Digram> {
        let curr_node = self.rhs[idx];
        match curr_node.get_prev() {
            Some(prev) => Some(Digram::new(
                self.id,
                (self.rhs[prev].get_symbol(), prev),
                (curr_node.get_symbol(), curr_node.get_addr()),
            )),
            None => None,
        }
    }

    pub fn digram_starting_at(&self, idx: usize) -> Option<Digram> {
        let curr_node = self.rhs[idx];
        match curr_node.get_next() {
            Some(next) => Some(Digram::new(
                self.id,
                (curr_node.get_symbol(), curr_node.get_addr()),
                (self.rhs[next].get_symbol(), next),
            )),
            None => None,
        }
    }

    pub fn rhs_to_vec(&self) -> Vec<Symbol> {
        self.rhs.to_vec()
    }

    pub fn is_digram(&self) -> Option<Digram> {
        match self.rhs.len() {
            2 => {
                let left = self.rhs.get_head_content().unwrap();
                let right = self.rhs.get_tail_content().unwrap();
                Some(Digram::new(self.id, left, right))
            }
            _ => None,
        }
    }
}

impl fmt::Display for Rule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::new();
        s.push('[');

        let mut head = self.rhs.get_head();
        while let Some(idx) = head {
            s.push_str(&format!(" {}", self.rhs[idx].get_symbol()));
            head = self.rhs[idx].get_next();
        }
        s.push(' ');
        s.push(']');
        write!(f, "{}", s)
    }
}
