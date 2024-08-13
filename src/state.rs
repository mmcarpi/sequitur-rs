use crate::digram::Digram;
use crate::rule::{Rule, RuleUsage};
use crate::symbol::{Symbol, SymbolPair};

use std::collections::HashMap;
use std::collections::HashSet;

pub struct Grammar {
    rules: HashMap<usize, Rule>,
    count: usize,
}

impl Grammar {
    fn new() -> Self {
        Self {
            rules: HashMap::new(),
            count: 0,
        }
    }

    pub fn add_rule(&mut self) -> usize {
        let new_rule = Rule::new(self.count);
        self.rules.insert(self.count, new_rule);
        self.count += 1;
        self.count - 1
    }
}

pub struct State {
    digrams: HashMap<SymbolPair, Digram>,
    rtable: HashMap<SymbolPair, usize>,
    inv_rtable: HashMap<usize, SymbolPair>,
    rule_usage: HashMap<usize, HashSet<RuleUsage>>,
}

impl State {
    fn new() -> Self {
        Self {
            digrams: HashMap::new(),
            rtable: HashMap::new(),
            inv_rtable: HashMap::new(),
            rule_usage: HashMap::new(),
        }
    }

    pub fn insert_digram(&mut self, digram: Digram) {
        //println!("INSERT {}", digram.pair());
        self.digrams.insert(digram.pair(), digram);
    }

    pub fn remove_digram(&mut self, digram: Digram) -> Option<Digram> {
        //println!("REMOVE {}", digram.pair());
        self.digrams.remove(&digram.pair())
    }

    pub fn insert_rule_usage(&mut self, rule_id: usize, rule_usage: RuleUsage) {
        if let Some(rule_usage_set) = self.rule_usage.get_mut(&rule_id) {
            rule_usage_set.insert(rule_usage);
        } else {
            self.rule_usage.insert(rule_id, HashSet::from([rule_usage]));
        }
    }
}

pub fn show_state(state: &State) {
    //println!("DIGRAMS: {{");
    for (pair, _digram) in state.digrams.iter() {
        //println!("{}", &pair);
    }
    //println!("}}");

    //println!("RTABLE: {{");
    for (pair, rule_id) in state.rtable.iter() {
        //println!("{} -> {}", &pair, rule_id);
    }
    //println!("}}");

    //println!("USAGE: {{");
    for (rule_id, rule_usage_set) in state.rule_usage.iter() {
        //println!("R{} <- {:#?}", rule_id, rule_usage_set);
    }
    //println!("}}");
}

pub fn show_rules(grammar: &Grammar) {
    //println!("RULES: {{");

    for (rule_id, rule) in grammar.rules.iter() {
        //println!("R{} -> {}", &rule_id, &rule);
    }
    //println!("}}");
}

pub fn insert_rule_usage(
    grammar: &mut Grammar,
    state: &mut State,
    rule_id: usize,
    rule_usage: RuleUsage,
) {
    //println!("insert_rule_usage({}, {:?})", rule_id, rule_usage);
    if let Some(rule_usage_set) = state.rule_usage.get_mut(&rule_id) {
        rule_usage_set.insert(rule_usage);
    } else {
        state
            .rule_usage
            .insert(rule_id, HashSet::from([rule_usage]));
    }
}

pub fn remove_rule_usage(
    grammar: &mut Grammar,
    state: &mut State,
    rule_id: usize,
    rule_usage: RuleUsage,
) {
    //println!("remove_rule_usage({}, {:?})", rule_id, rule_usage);
    let mut rule_usage_set = state
        .rule_usage
        .remove(&rule_id)
        .expect("rule_usage_set not found!");

    if rule_usage_set.len() == 2 {
        rule_usage_set.remove(&rule_usage);
        for last_usage in rule_usage_set.into_iter() {
            expand_rule(grammar, state, rule_id, last_usage);
            if let Some(pair) = state.inv_rtable.remove(&rule_id) {
                state.rtable.remove(&pair);
            }

            if let Some(pair) = state.inv_rtable.remove(&last_usage.get_rule_id()) {
                state.rtable.remove(&pair);
            }
        }
    } else {
        rule_usage_set.remove(&rule_usage);
        state.rule_usage.insert(rule_id, rule_usage_set);
    }
}

pub fn expand_rule(
    grammar: &mut Grammar,
    state: &mut State,
    rule_id: usize,
    last_usage: RuleUsage,
) {
    //println!("expand_rule({},\n            {:?})", rule_id, last_usage);
    let mut old_rule = grammar
        .rules
        .remove(&rule_id)
        .expect(&format!("old_rule Rule({}) not found!", rule_id));

    let target_rule = grammar
        .rules
        .get_mut(&last_usage.get_rule_id())
        .expect(&format!("target_rule Rule({}) not found!", rule_id));

    if let Some(digram) = target_rule.digram_starting_at(last_usage.get_index()) {
        state.remove_digram(digram);
    }

    if let Some(digram) = target_rule.digram_ending_at(last_usage.get_index()) {
        state.remove_digram(digram);
    }
    //println!("loop start");
    let index_after_last_usage = target_rule.rhs[last_usage.get_index()].get_next();
    let mut tail = old_rule.rhs.get_tail();
    while let Some(prev) = tail {
        let node = old_rule.rhs.pop(prev);
        tail = node.get_prev();

        if let Some(node_prev) = tail {
            let pnode = old_rule.rhs[node_prev];
            state.remove_digram(Digram::new(
                old_rule.get_id(),
                (pnode.get_symbol(), pnode.get_addr()),
                (node.get_symbol(), node.get_addr()),
            ));
        }

        let nidx = target_rule
            .rhs
            .push_after(last_usage.get_index(), node.get_symbol());

        if let Symbol::Rule(other_rule) = node.get_symbol() {
            let rule_usage_set = state
                .rule_usage
                .get_mut(&other_rule)
                .expect("rule_usage_set not found");
            rule_usage_set.remove(&RuleUsage::new(old_rule.get_id(), node.get_addr()));
            rule_usage_set.insert(RuleUsage::new(target_rule.get_id(), nidx));
        }

        if let Some(digram) = target_rule.digram_starting_at(nidx) {
            if Some(digram.get_right_id()) != index_after_last_usage {
                //println!("INSERTING DIGRAM -> {:?}", digram);
                state.insert_digram(digram);
            }
        }
    }

    let popped_node = target_rule.rhs.pop(last_usage.get_index());

    let next_digram = match popped_node.get_next() {
        Some(idx) => target_rule.digram_ending_at(idx),
        _ => None,
    };

    let prev_digram = match popped_node.get_prev() {
        Some(idx) => target_rule.digram_starting_at(idx),
        _ => None,
    };

    let last_digram = match index_after_last_usage {
        Some(idx) => target_rule.digram_ending_at(idx),
        _ => None,
    };

    if let Some(new_digram) = next_digram {
        //println!("next_digram -> {:?}", new_digram);
        insert_digram(grammar, state, new_digram);
    }

    if let Some(new_digram) = prev_digram {
        //println!("prev_digram -> {:?}", new_digram);
        insert_digram(grammar, state, new_digram);
    }

    if let Some(new_digram) = last_digram {
        //println!("last_digram -> {:?}", new_digram);
        insert_digram(grammar, state, new_digram);
    }
}

pub fn insert_digram(grammar: &mut Grammar, state: &mut State, new_digram: Digram) {
    //println!("insert_digram({:?})", new_digram);
    match state.remove_digram(new_digram) {
        Some(old_digram) => {
            if !old_digram.overlap(&new_digram) {
                check_rule_existence(grammar, state, old_digram, new_digram);
            } else {
                state.insert_digram(old_digram);
            }
        }
        None => {
            state.insert_digram(new_digram);
        }
    }
}

pub fn check_rule_existence(
    grammar: &mut Grammar,
    state: &mut State,
    old_digram: Digram,
    new_digram: Digram,
) {
    // println!(
    //     "check_rule_existence({:?},\n                     {:?})",
    //     old_digram, new_digram
    // );
    match state.rtable.get(&new_digram.pair()) {
        Some(rule_id) => {
            replace_digram(grammar, state, new_digram, Symbol::Rule(*rule_id));
            state.insert_digram(old_digram);
        }
        None => {
            create_new_rule(grammar, state, old_digram, new_digram);
        }
    }
}

pub fn push(grammar: &mut Grammar, state: &mut State, rule_id: usize, symbol: Symbol) {
    let rule = grammar
        .rules
        .get_mut(&rule_id)
        .expect(&format!("Rule {} not found!", rule_id));

    let (idx, option_digram) = rule.push(symbol);

    if let Symbol::Rule(other_rule) = symbol {
        insert_rule_usage(grammar, state, other_rule, RuleUsage::new(rule_id, idx));
    }

    if let Some(new_digram) = option_digram {
        insert_digram(grammar, state, new_digram);
    }
}

pub fn create_new_rule(
    grammar: &mut Grammar,
    state: &mut State,
    old_digram: Digram,
    new_digram: Digram,
) {
    // println!(
    //     "create_new_rule({:?},\n                {:?})",
    //     old_digram, new_digram
    // );
    let new_rule_idx = grammar.add_rule();

    push(grammar, state, new_rule_idx, new_digram.get_left_symbol());
    push(grammar, state, new_rule_idx, new_digram.get_right_symbol());
    state.rtable.insert(new_digram.pair(), new_rule_idx);
    state.inv_rtable.insert(new_rule_idx, new_digram.pair());

    replace_digrams(
        grammar,
        state,
        old_digram,
        new_digram,
        Symbol::Rule(new_rule_idx),
    );
}

pub fn replace_digrams(
    grammar: &mut Grammar,
    state: &mut State,
    old_digram: Digram,
    new_digram: Digram,
    symbol: Symbol,
) {
    println!("begin_replace_digrams!");
    replace_digram(grammar, state, old_digram, symbol);
    replace_digram(grammar, state, new_digram, symbol);
    println!("end_replace_digrams!");
}

pub fn replace_digram(grammar: &mut Grammar, state: &mut State, digram: Digram, symbol: Symbol) {
    println!("replace_digram({:?},\n               {:?})", digram, symbol);
    let rule = grammar.rules.get_mut(&digram.get_rule_id()).unwrap();
    let rule_id = rule.get_id();

    let digram_right_id = digram.get_right_id();
    let rnode = rule.rhs[digram_right_id];

    let digram_left_id = digram.get_left_id();
    let lnode = rule.rhs[digram_left_id];

    if let Some(digram) = rule.digram_starting_at(digram_right_id) {
        state.remove_digram(digram);
    }

    if let Some(digram) = rule.digram_ending_at(digram_left_id) {
        state.remove_digram(digram);
    }

    rule.rhs.pop(digram_right_id);
    let nidx = rule.rhs.push_after(digram_left_id, symbol);
    rule.rhs.pop(digram_left_id);

    if let Symbol::Rule(other_rule_id) = symbol {
        state.insert_rule_usage(other_rule_id, RuleUsage::new(rule_id, nidx));
    }

    let new_left_digram = rule.digram_ending_at(nidx);
    let new_right_digram = rule.digram_starting_at(nidx);

    if let Symbol::Rule(other_rule_id) = rnode.get_symbol() {
        remove_rule_usage(
            grammar,
            state,
            other_rule_id,
            RuleUsage::new(rule_id, rnode.get_addr()),
        );
    }

    if let Some(new_digram) = new_left_digram {
        insert_digram(grammar, state, new_digram);
    }

    if let Symbol::Rule(other_rule_id) = lnode.get_symbol() {
        remove_rule_usage(
            grammar,
            state,
            other_rule_id,
            RuleUsage::new(rule_id, lnode.get_addr()),
        );
    }

    if let Some(new_digram) = new_right_digram {
        insert_digram(grammar, state, new_digram)
    }
}

#[cfg(test)]
mod test_state {
    use super::*;
    #[test]
    fn test_replace_digram_01() {
        let mut grammar = Grammar::new();
        let mut state = State::new();
        let s = grammar.add_rule();

        let a = Symbol::Char('a');
        let b = Symbol::Char('b');
        let r1 = Symbol::Rule(1);

        push(&mut grammar, &mut state, s, a);
        push(&mut grammar, &mut state, s, b);

        assert_eq!(state.digrams.len(), 1);

        push(&mut grammar, &mut state, s, a);
        push(&mut grammar, &mut state, s, b);
        assert_eq!(
            state
                .digrams
                .values()
                .map(|x| x.pair())
                .collect::<HashSet<SymbolPair>>(),
            HashSet::from([SymbolPair(a, b), SymbolPair(r1, r1)])
        );

        assert_eq!(*state.rtable.get(&SymbolPair(a, b)).unwrap(), 1);
        assert_eq!(state.rule_usage.get(&0), None);
        assert_eq!(
            *state.rule_usage.get(&1).unwrap(),
            HashSet::from([RuleUsage::new(0, 1), RuleUsage::new(0, 3)])
        );
        assert_eq!(grammar.rules.len(), 2);
        assert_eq!(grammar.rules.get(&0).unwrap().rhs_to_vec(), vec![r1, r1]);
        assert_eq!(grammar.rules.get(&1).unwrap().rhs_to_vec(), vec![a, b]);
    }

    #[test]
    fn test_replace_digram_02() {
        let mut state = State::new();
        let mut grammar = Grammar::new();

        let s = grammar.add_rule();

        let a = Symbol::Char('a');
        let b = Symbol::Char('b');
        let c = Symbol::Char('c');
        let d = Symbol::Char('d');
        let r1 = Symbol::Rule(1);
        let input = vec![a, b, c, d, b, c];

        for symbol in input.into_iter() {
            push(&mut grammar, &mut state, s, symbol);
        }

        assert_eq!(
            state
                .digrams
                .values()
                .map(|x| x.pair())
                .collect::<HashSet<SymbolPair>>(),
            HashSet::from([
                SymbolPair(a, r1),
                SymbolPair(b, c),
                SymbolPair(r1, d),
                SymbolPair(d, r1)
            ])
        );

        assert_eq!(*state.rtable.get(&SymbolPair(b, c)).unwrap(), 1);
        assert_eq!(state.rule_usage.get(&1).unwrap().len(), 2);

        assert_eq!(
            grammar.rules.get(&s).unwrap().rhs_to_vec(),
            vec![a, r1, d, r1]
        );

        assert_eq!(
            grammar.rules.get(&(s + 1)).unwrap().rhs_to_vec(),
            vec![b, c]
        )
    }

    #[test]
    fn test_expand_rule() {
        let mut grammar = Grammar::new();
        let mut state = State::new();
        let s = grammar.add_rule();

        let a = Symbol::Char('a');
        let b = Symbol::Char('b');
        let c = Symbol::Char('c');
        let d = Symbol::Char('d');
        let input = vec![a, b, c, d, b, c, a, b, c, d];

        for (i, symbol) in input.into_iter().enumerate() {
            push(&mut grammar, &mut state, s, symbol);
        }

        assert_eq!(grammar.rules.len(), 3);
    }

    #[test]
    fn test_overlap() {
        let mut grammar = Grammar::new();
        let mut state = State::new();

        let s = grammar.add_rule();

        let a = Symbol::Char('a');
        let r = Symbol::Rule(s + 1);
        push(&mut grammar, &mut state, s, a);
        push(&mut grammar, &mut state, s, a);
        push(&mut grammar, &mut state, s, a);
        assert_eq!(grammar.rules.get(&s).unwrap().rhs_to_vec(), vec![a, a, a]);
        push(&mut grammar, &mut state, s, a);
        assert_eq!(grammar.rules.get(&s).unwrap().rhs_to_vec(), vec![r, r]);
    }
}
