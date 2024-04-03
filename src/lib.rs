type Link = usize;

enum Node {
    Guard { prev: Link, next: Link },
    Elem { elem: usize, prev: Link, next: Link },
}

impl Node {
    fn get_prev(&self) -> Link {
        match self {
            Node::Guard { prev, .. } => *prev,
            Node::Elem { prev, .. } => *prev,
        }
    }

    fn get_next(&self) -> Link {
        match self {
            Node::Guard { next, .. } => *next,
            Node::Elem { next, .. } => *next,
        }
    }

    fn set_prev(&self, new_prev: Link) -> Node {
        match self {
            Node::Guard { next, .. } => Node::Guard {
                prev: new_prev,
                next: *next,
            },
            Node::Elem { elem, next, .. } => Node::Elem {
                elem: *elem,
                prev: new_prev,
                next: *next,
            },
        }
    }

    fn set_next(&self, new_next: Link) -> Node {
        match self {
            Node::Guard { prev, .. } => Node::Guard {
                prev: *prev,
                next: new_next,
            },
            Node::Elem { elem, prev, .. } => Node::Elem {
                elem: *elem,
                prev: *prev,
                next: new_next,
            },
        }
    }

    fn set_elem(&self, new_elem: usize) -> Node {
        Node::Elem {
            elem: new_elem,
            next: self.get_next(),
            prev: self.get_prev(),
        }
    }

    fn get_elem(&self) -> usize {
        match self {
            Node::Elem { elem, .. } => *elem,
            Node::Guard { .. } => panic!("Tried to get_elem from guard node"),
        }
    }
}

type RuleLabel = usize;
type Digram = (usize, usize);
type Elem = usize;

use std::collections::{HashMap, HashSet};

pub struct Sequitur {
    node: Vec<Option<Node>>,
    memo: Vec<usize>,
    rule: Vec<(Link, usize)>,
    digram: HashMap<Digram, usize>,
    drule: HashMap<Digram, usize>,
    rule_start: usize,
}

impl Sequitur {
    pub fn new() -> Self {
        Sequitur {
            node: Vec::new(),
            memo: Vec::new(),
            rule: Vec::new(),
            digram: HashMap::new(),
            drule: HashMap::new(),
            rule_start: 256,
        }
    }

    pub fn len(&self) -> usize {
        self.node.len() - self.memo.len()
    }

    fn insert_new_node(&mut self, pos: usize, node: Node) {
        self.node[pos] = Some(node);
    }

    fn next_free_pos(&mut self) -> usize {
        match self.memo.pop() {
            Some(free_pos) => free_pos,
            None => {
                self.node.push(None);
                self.node.len() - 1
            }
        }
    }

    fn new_rule(&mut self) -> RuleLabel {
        let free_pos = self.next_free_pos();
        let rule_label = self.rule_start + self.rule.len(); // This may overflow but it is what it is
        self.rule.push((free_pos, 1));
        self.insert_new_node(
            free_pos,
            Node::Guard {
                next: free_pos,
                prev: free_pos,
            },
        );
        rule_label
    }

    fn is_rule(&self, rule: RuleLabel) -> Option<Link> {
        match rule < self.rule_start {
            true => None,
            false => Some(rule - self.rule_start),
        }
    }

    pub fn rule_push_back(&mut self, rule: RuleLabel, elem: Elem) -> Option<Link> {
        match self.is_rule(rule) {
            None => None,
            Some(rule_idx) => {
                let pos = self.rule[rule_idx].0;
                match &self.node[pos] {
                    Some(node) => match &self.node[node.get_prev()] {
                        Some(_other_node) => match self.insert_after(node.get_prev(), elem) {
                            Some(new_pos) => {
                                self.node[pos] =
                                    Some(self.node[pos].as_ref().unwrap().set_prev(new_pos));
                                Some(new_pos)
                            }
                            None => None,
                        },
                        None => self.insert_after(pos, elem),
                    },
                    None => None,
                }
            }
        }
    }

    pub fn debug(&self) {
        println!("Rules:");
        for r in 0..self.rule.len() {
            println!("{:?}", self.fetch_rule(r));
        }

        println!("");
        println!("Digrams:");
        for (d, p) in self.digram.iter() {
            Sequitur::debug_digram_pos(*d, *p, self.drule.get(d).is_some());
        }
    }

    pub fn fetch_rule(&self, rule: RuleLabel) -> Vec<(Elem, Elem, Elem, Elem)> {
        let mut v = vec![];

        let mut curr_node_add = self.rule[rule].0;
        let start_node = curr_node_add;
        while let Some(node) = &self.node[curr_node_add] {
            match node {
                Node::Guard { prev, next } => v.push((curr_node_add, 666 as usize, *next, *prev)),
                Node::Elem { elem, prev, next } => v.push((curr_node_add, *elem, *next, *prev)),
            }
            curr_node_add = node.get_next();
            if curr_node_add == start_node {
                break;
            }
        }
        return v;
    }

    fn char_to_str(val: usize) -> String {
        if val < 97 {
            format!("R_{:06}", val)
        } else {
            format!("{:6}", val)
            // format!("{}", char::from_u32(val as u32).unwrap())
        }
    }

    fn debug_digram_pos(digram: Digram, pos: usize, is_rule: bool) {
        println!(
            "digram={}    pos={:6} [{}]",
            format!(
                "{},{}",
                Sequitur::char_to_str(digram.0),
                Sequitur::char_to_str(digram.1),
            ),
            pos,
            if is_rule { '*' } else { '-' }
        );
    }

    fn ensure_rule_usage(&mut self, rule: RuleLabel) {}

    fn remove_digram(&mut self, digram: Digram) {
        for elem in vec![digram.0, digram.1] {
            match self.is_rule(elem) {
                Some(rule_idx) => {
                    todo!("Some case");
                }
                None => { /* Do nothing */ }
            }
        }
        self.digram.remove(&digram);
    }

    fn ensure_digram_uniqueness(&mut self, digram: Digram, pointer: Vec<Link>) {
        // TODO: /* Do nothing */ should perhaps be unreachable
        // Acho que uma sacada bem legal é o seguinte
        // A gente popa o primeiro cara
        // E com uma referência para o segundo altera o valor dele para a rule

        // Keep the information that a new rule was created for this digram
        let new_rule = self.new_rule();
        println!("Inserting {:?}", digram);
        self.drule.insert(digram, new_rule);

        // Push the data for this digram
        // TODO: Reuse some already created rule
        self.rule_push_back(new_rule, digram.0);
        self.rule_push_back(new_rule, digram.1);

        // Now we remove the nodes
        // TODO: Perhaps write it for both nodes before trying to generalize

        println!("Before poping");
        self.debug();
        let mut new_pointers: Vec<Link> = vec![];
        let mut old_digrams = vec![];
        for &p in &pointer {
            let old_node: Node = self.pop_and_fix(p);
            let old_next_node: Node = self.pop_and_fix(old_node.get_next());

            match self.node[old_node.get_prev()]
                .as_ref()
                .expect("Node should exist")
            {
                Node::Elem { elem, .. } => old_digrams.push((*elem, old_node.get_elem())),
                _else => {}
            }

            match self.node[old_next_node.get_next()]
                .as_ref()
                .expect("Node should exist")
            {
                Node::Elem { elem, .. } => old_digrams.push((old_next_node.get_elem(), *elem)),
                _else => {}
            }

            new_pointers.push(old_node.get_prev());
        }

        println!("\nAfter poping\n");
        println!("old_digrams={:?}", old_digrams);
        println!("\nnew_pointers={:?}", new_pointers);

        for &digram in &old_digrams {
            self.remove_digram(digram);
        }

        self.debug();

        let mut final_pointers = vec![];
        for &p in &new_pointers {
            final_pointers.push(self.insert_after_and_fix(p, new_rule));
            // TODO: Use insert after p to add a new node with the rule
            // self.node[p] = Some(
            //     self.node[p]
            //         .as_ref()
            //         .expect("Node is the second element of a old digram")
            //         .set_elem(new_rule),
            // );
        }

        println!("\nAfter new_pointers update\n");
        self.debug();

        let mut new_digrams = HashSet::new();

        for &p in &final_pointers {
            match self.node[p]
                .as_ref()
                .expect("Node is the second element of a old digram")
            {
                Node::Elem {
                    elem: curr_elem,
                    prev,
                    next,
                } => {
                    match self.node[*prev].as_ref().expect("Node should exist") {
                        Node::Elem {
                            elem: prev_elem, ..
                        } => {
                            //self.add_digram((*prev_elem, *curr_elem), *prev);
                            new_digrams.insert(((*prev_elem, *curr_elem), *prev));
                        }
                        _else => { /* We do not care */ }
                    }

                    match self.node[*next].as_ref().expect("Node should exist") {
                        Node::Elem {
                            elem: next_elem, ..
                        } => {
                            //self.add_digram((*curr_elem, *next_elem), p);
                            new_digrams.insert(((*curr_elem, *next_elem), p));
                        }
                        _else => { /* We do not care */ }
                    }
                }
                _else => { /* Do nothing */ }
            }
        }

        println!("\nBefore exiting poping\n");
        self.debug();
        println!("new_digrams={:?}", new_digrams);

        for &(new_digram, digram_pos) in &new_digrams {
            self.add_digram(new_digram, digram_pos);
        }

        println!("\nBefore trully exiting poping\n");
        self.debug();

        // // Now we change self.node[node.next] the next
        // self.node[curr_node_add] = Some(self.node[curr_node_add].as_ref().unwrap().set_elem(new_rule));

        // // Now we add the newly created digrams and their start positions
        // let curr_node = self.node[curr_node_add].as_ref().expect("Node should exist");
        // let prev_node_add = curr_node.get_prev();
        // let next_node_add = curr_node.get_next();

        // //// Notice that neither prev_node nor next_node must must exist
        // if let Some(prev_node) = self.node[prev_node_add].as_ref() {
        //     match prev_node {
        //         Node::Elem { elem, .. } => {
        //             self.digram.insert((*elem, new_rule), prev_node_add);
        //         },
        //         _else => { /* Do nothing */ },
        //     }
        // }

        // if let Some(next_node) = self.node[next_node_add].as_ref() {
        //     match next_node {
        //         Node::Elem { elem, .. } => {
        //             self.digram.insert((new_rule, *elem), curr_node_add);
        //         },
        //         _else => { /* Do nothing */ },
        //     }
        // }

        // let prev_node = node.prev;
        // self.digram.insert((new_rule, self.node[prev_node].elem), p);
        // todo!("^^^^^^^^^^^^^^^^^^^^^^^^^");

        //todo!("Ensure digram uniqueness");
    }

    fn get_digrams(&self) -> HashSet<(usize, usize)> {
        // let drule : HashSet<(Elem, Elem)> = self.drule.keys().map(
        //     |&(d0, d1)| (d0, d1)
        // ).collect();

        let digram: HashSet<(Elem, Elem)> = self.digram.keys().map(|&(d0, d1)| (d0, d1)).collect();

        digram
        // (drule.union(&digram)).map(
        //    |&(d0, d1)| (d0, d1)).collect()
    }

    fn add_digram(&mut self, digram: Digram, pos: usize) {
        //Sequitur::debug_digram_pos(digram, pos);

        match self.digram.get(&digram) {
            Some(prev_pos) => {
                self.ensure_digram_uniqueness(digram, vec![*prev_pos, pos]);
            }
            None => {
                self.digram.insert(digram, pos);
            }
        }

        // match self.drule.contains_key(&digram) {
        //     true => {
        //         todo!("Rule already created");
        //     }
        //     false => match self.digram.remove(&digram) {
        //         Some(prev_pos) => {
        //             self.ensure_digram_uniqueness(digram, vec![pos, prev_pos]);
        //         }
        //         None => {
        //             self.digram.insert(digram, pos);
        //         }
        //     },
        // }
    }

    pub fn compress(&mut self, input: &[u8]) -> Vec<usize> {
        if input.len() == 0 {
            return Vec::new();
        }

        let s = self.new_rule();
        let mut cprev: usize = input[0] as usize;
        let mut pos = self.rule_push_back(s, cprev).unwrap();

        for cat in &input[1..] {
            // self.debug();
            // println!("-------------");
            let cat: usize = *cat as usize;
            let digram = (cprev as usize, cat as usize);
            let next_pos = self.rule_push_back(s, cat);

            self.add_digram(digram, pos);
            pos = next_pos.unwrap();
            cprev = cat;
        }

        //todo!("compress");
        vec![]
    }

    pub fn pos_exists(&self, pos: usize) -> Option<Link> {
        match pos < self.node.len() && self.node[pos].is_some() {
            true => Some(pos),
            false => None,
        }
    }

    fn insert_after_and_fix(&mut self, pos: usize, elem: Elem) -> Link {
        let free_pos = self.next_free_pos();
        let next_node_add = self.node[pos].as_ref().unwrap().get_next();
        match &self.node[next_node_add] {
            Some(_next_node) => {
                self.node[pos] = Some(self.node[pos].as_ref().unwrap().set_next(free_pos));
                self.node[next_node_add] = Some(
                    self.node[next_node_add]
                        .as_ref()
                        .unwrap()
                        .set_prev(free_pos),
                );
                self.node[free_pos] = Some(Node::Elem {
                    elem: elem,
                    next: next_node_add,
                    prev: pos,
                });
            }
            None => {
                self.node[pos] = Some(self.node[pos].as_ref().unwrap().set_next(free_pos));
                self.node[free_pos] = Some(Node::Elem {
                    elem: elem,
                    next: pos,
                    prev: pos,
                });
                self.node[pos] = Some(self.node[pos].as_ref().unwrap().set_prev(free_pos));
            }
        }
        return free_pos;
    }

    pub fn insert_after(&mut self, pos: usize, elem: Elem) -> Option<Link> {
        match self.pos_exists(pos) {
            Some(pos) => Some(self.insert_after_and_fix(pos, elem)),
            None => None,
        }
    }

    fn pop_and_fix(&mut self, pos: usize) -> Node {
        let node = self.node[pos].take().expect("Should be a bug!");
        let next_node_add = node.get_next();
        let prev_node_add = node.get_prev();
        self.memo.push(pos);
        match &self.node[next_node_add] {
            None => panic!("Node at position {} .next is invalid.", pos),
            Some(_next_node) => match &self.node[prev_node_add] {
                None => panic!("Node at position {} .prev is invalid.", pos),
                Some(_prev_node) => {
                    self.node[prev_node_add] = Some(
                        self.node[prev_node_add]
                            .as_ref()
                            .unwrap()
                            .set_next(next_node_add),
                    );
                    self.node[next_node_add] = Some(
                        self.node[next_node_add]
                            .as_ref()
                            .unwrap()
                            .set_prev(prev_node_add),
                    );
                    node
                }
            },
        }
    }

    pub fn pop_at(&mut self, pos: usize) -> Option<Elem> {
        // Make so it pops the node
        match self.pos_exists(pos) {
            Some(pos) => match self.pop_and_fix(pos) {
                Node::Elem { elem, .. } => Some(elem),
                _else => None,
            },
            None => None,
        }
    }
}

#[cfg(test)]
mod sequitur_tests {
    use super::*;

    #[test]
    fn add_rule() {
        let mut s = Sequitur::new();
        let rule1 = s.new_rule();
        let rule2 = s.new_rule();
        assert_eq!(rule1, s.rule_start);
        assert_eq!(rule2, s.rule_start + 1);
        assert_eq!(s.len(), 2);
    }

    #[test]
    fn add_rule_and_add_items() {
        let n: usize = 10;
        let mut seq = Sequitur::new();
        let s = seq.new_rule();
        let mut v = vec![s];

        for i in 0..n {
            let e = i;
            assert_eq!(seq.rule_push_back(s, e), Some(i + 1));
            v.push(e);
        }

        //assert_eq!(seq.fetch_rule(s), v);
    }

    #[test]
    fn pop_and_fix() {
        let mut seq = Sequitur::new();
        let s = seq.new_rule();
        let input = "abcdb".as_bytes();
        // let input = "abcdbcabcd".as_bytes();
        let mut v = vec![s];
        seq.debug();
        for b in input.iter() {
            seq.rule_push_back(s, (*b).into()).unwrap();
            v.push((*b).into());
        }

        //assert_eq!(v, seq.fetch_rule(s));
        seq.debug();
        // println!("{}", seq.node[1].as_ref().unwrap().elem);
        seq.pop_at(1);
        seq.debug();
        seq.pop_at(2);
        seq.debug();
        // TODO: Check if sequence is implemented correctly
        //println!("{}", seq.node[2].as_ref().unwrap().elem);
        //assert_eq!(true, false);
    }

    #[test]
    fn basic_digram_check() {
        let mut seq = Sequitur::new();
        let s = seq.new_rule();
        let input = "abac".as_bytes();

        let mut i = input.iter().peekable();
        let mut pos =
            seq.rule_push_back(s, (**i.peek().expect("input should not be empty.")).into());
        //TODO: Rewrite compress loop in this way
        for (&a, &b) in input.iter().zip(i.skip(1)) {
            let (a, b) = (a.into(), b.into());
            println!("{:?} {:?}", a, b);
            let next_pos = seq.rule_push_back(s, b);
            seq.add_digram((a, b), pos.unwrap());
            pos = next_pos;
        }

        let r: HashSet<(usize, usize)> = seq.get_digrams();

        assert_eq!(
            r,
            HashSet::from([
                ('a' as usize, 'b' as usize),
                ('b' as usize, 'a' as usize),
                ('a' as usize, 'c' as usize),
            ])
        );
    }

    #[test]
    fn small_digram_check() {
        let mut seq = Sequitur::new();
        let input = "abab".as_bytes();

        let compressed = seq.compress(input);
        let digramset: HashSet<Digram> = seq.get_digrams();

        println!("digramset={:?}", digramset);

        assert_eq!(
            digramset,
            HashSet::from([
                (seq.rule_start + 1, seq.rule_start + 1),
                (97 as usize, 98 as usize),
            ])
        );
    }

    #[test]
    fn medium_digram_check() {
        let mut seq = Sequitur::new();
        let input = "abacabde".as_bytes();

        let compressed = seq.compress(input);
        let digramset: HashSet<Digram> = seq.get_digrams();

        println!("digramset={:?}", digramset);
        seq.debug();
        assert_eq!(
            digramset,
            HashSet::from([
                (257, 97),  // Aa
                (97, 99),   // ac
                (99, 257),  // cA
                (100, 101), // de
                (98, 100),  // bd
                (97, 98),   // ab
            ])
        );
    }

    //#[test]
    fn compress() {
        let mut s = Sequitur::new();

        let input1 = "abcdbcabcd".as_bytes();
        let output1: Vec<usize> = vec![
            257,
            256,
            260,
            258,
            260,
            256,
            256,
            258,
            256,
            'b' as usize,
            'c' as usize,
            256,
            256,
            260,
            256,
            'a' as usize,
            258,
            'd' as usize,
            256,
            256,
        ];
        assert_eq!(s.compress(&input1), output1);
    }
}
