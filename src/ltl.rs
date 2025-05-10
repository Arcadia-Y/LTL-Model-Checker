use std::{collections::HashSet, vec};

// LTL formulas with extended operators
#[derive(Debug)]
pub enum LTLE {
    True,
    Atom(String),
    Not(Box<LTLE>),
    And(Box<LTLE>, Box<LTLE>),
    Or(Box<LTLE>, Box<LTLE>),
    Impl(Box<LTLE>, Box<LTLE>),
    Next(Box<LTLE>),
    Even(Box<LTLE>),
    Always(Box<LTLE>),
    Until(Box<LTLE>, Box<LTLE>),
}

// LTL formulas with only basic operators
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum LTL {
    True,
    Atom(String),
    Not(Box<LTL>),
    And(Box<LTL>, Box<LTL>),
    Next(Box<LTL>),
    Until(Box<LTL>, Box<LTL>),
}

pub fn negate(x: LTL) -> LTL {
    match x {
        LTL::Not(x) => *x,
        _ => LTL::Not(Box::new(x)),
    }
}

// reduce an LTLE formula to LTL
pub fn reduce_ltl(x: LTLE) -> LTL {
    match x {
        LTLE::True => LTL::True,
        LTLE::Atom(s) => LTL::Atom(s),
        LTLE::Not(x) => negate(reduce_ltl(*x)),
        LTLE::And(x, y) => LTL::And(Box::new(reduce_ltl(*x)), Box::new(reduce_ltl(*y))),
        LTLE::Or(x, y) => 
            LTL::Not(Box::new(LTL::And(
                Box::new(negate(reduce_ltl(*x))),
                Box::new(negate(reduce_ltl(*y))),
            ))),
        LTLE::Impl(x, y) => 
            LTL::Not(Box::new(LTL::And(
                Box::new(reduce_ltl(*x)),
                Box::new(negate(reduce_ltl(*y))),
            ))),
        LTLE::Next(x) => LTL::Next(Box::new(reduce_ltl(*x))),
        LTLE::Even(x) => LTL::Until(Box::new(LTL::True), Box::new(reduce_ltl(*x))),
        LTLE::Always(x) =>
            LTL::Not(Box::new(LTL::Until(
                Box::new(LTL::True),
                Box::new(negate(reduce_ltl(*x))),
            ))),
        LTLE::Until(x, y) => LTL::Until(Box::new(reduce_ltl(*x)), Box::new(reduce_ltl(*y))),
    }
}

impl<'a> LTL {
    // get the atoms of an LTL formula
    pub fn get_atoms(&self) -> HashSet<String> {
        let mut res = HashSet::new();
        self.get_atoms_aux(&mut res);
        res
    }

    fn get_atoms_aux(&self, set: &mut HashSet<String>) {
        match self {
            LTL::True => {}
            LTL::Atom(s) => {
                set.insert(s.clone());
            }
            LTL::Not(x) => x.get_atoms_aux(set),
            LTL::And(x, y) => {
                x.get_atoms_aux(set);
                y.get_atoms_aux(set);
            }
            LTL::Next(x) => x.get_atoms_aux(set),
            LTL::Until(x, y) => {
                x.get_atoms_aux(set);
                y.get_atoms_aux(set);
            }
        }
    }

    // get the closure of an LTL formula
    // only subformulas that don't start with negation are included
    pub fn get_closure(&self) -> Vec<& LTL> {
        let mut res = vec!();
        let mut set = HashSet::new();
        self.get_closure_aux(&mut res, &mut set);
        res
    }

    fn update_closure<'b>(&'a self, vec: &'b mut Vec<&'a LTL>, set: &'b mut HashSet<&'a LTL>) {
        if !set.contains(self) {
            vec.push(self);
            set.insert(self);
        }
    }

    fn get_closure_aux<'b>(&'a self, vec: &'b mut Vec<&'a LTL>, set: &'b mut HashSet<&'a LTL>) {
        match self {
            LTL::True | LTL::Atom(_) => {
                self.update_closure(vec, set);
            }
            LTL::Not(x) => x.get_closure_aux(vec, set),
            LTL::And(x, y) => {
                x.get_closure_aux(vec, set);
                y.get_closure_aux(vec, set);
                self.update_closure(vec, set);
            }
            LTL::Next(x) => {
                x.get_closure_aux(vec, set);
                self.update_closure(vec, set);
            }
            LTL::Until(x, y) => {
                x.get_closure_aux(vec, set);
                y.get_closure_aux(vec, set);
                self.update_closure(vec, set);
            }
        }
    }
}

// An elementary set B of an LTL
// atoms = B ∩ AP
// set is a map from positive sub-formulas of the LTL formulas to their truth values in B
#[derive(Debug, Clone)]
pub struct ElemSet<'a> {
    pub atoms: HashSet<String>,
    pub set: HashSet<&'a LTL>,
}

impl<'a> ElemSet<'a> {
    // check whether an elementary set contains an LTL formula
    // it will handle the negation case
    pub fn has(&self, x: &LTL) -> bool {
        match x {
            LTL::True => true,
            LTL::Not(y) => !self.has(y),
            _ => self.set.contains(x)
        }
    }
}

// get the elementary sets of a closure
pub fn get_elem_sets<'a>(cl: &'a Vec<&LTL>) -> Vec<ElemSet<'a>> {
    let mut res = vec!();
    let cur = ElemSet {
        atoms: HashSet::new(),
        set: HashSet::new(),
    };
    get_elem_sets_aux(cl, cur, &mut res);
    res
}

fn eval_truth_value(e: &ElemSet, x: &LTL) -> bool {
    match x {
        LTL::True => true,
        LTL::Not(x) => !eval_truth_value(e, x),
        _ => e.set.contains(x)
    }
}

fn get_elem_sets_aux<'a>(cl: &'a [&LTL], mut cur: ElemSet<'a>, res: &mut Vec<ElemSet<'a>>) {
    if cl.is_empty() {
        res.push(cur);
        return;
    }
    let x = cl[0];
    match x {
        LTL::True => get_elem_sets_aux(&cl[1..], cur, res),
        LTL::Atom(s) => {
            let mut other = cur.clone();
            // x is false
            get_elem_sets_aux(&cl[1..], cur, res);
            // x is true
            other.atoms.insert(s.clone());
            other.set.insert(x);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Not(_) => {
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::And(a, b) => {
            if eval_truth_value(&cur, a) && eval_truth_value(&cur, b) {
                cur.set.insert(x);
            }
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::Next(_) => {
            let mut other = cur.clone();
            // x is false
            get_elem_sets_aux(&cl[1..], cur, res);
            // x is true
            other.set.insert(x);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Until(a, b) => {
            if eval_truth_value(&cur, b) {
                // b is true
                cur.set.insert(x);
                get_elem_sets_aux(&cl[1..], cur, res);
            } else {
                // b is false
                if eval_truth_value(&cur, a) {
                    // a is true
                    let mut other = cur.clone();
                    // x is false
                    get_elem_sets_aux(&cl[1..], cur, res);
                    // x is true
                    other.set.insert(x);
                    get_elem_sets_aux(&cl[1..], other, res);
                } else {
                    // a is false
                    get_elem_sets_aux(&cl[1..], cur, res);
                }
            }
        }
    }
}

// Check if (x, y) satisfies one-step relation in the construction of the GNBA's transition relation
pub fn step_relation(clos:&Vec<&LTL>, x: &ElemSet, y: &ElemSet) -> bool {
    for a in clos {
        match a {
            LTL::Next(b) => {
                let a_in_x = x.has(a);
                let b_in_y = y.has(&**b);
                if a_in_x && !b_in_y || !a_in_x && b_in_y {
                    return false;
                }
            }
            LTL::Until(a1, a2) => {
                let lval = x.has(a);
                let rval = x.has(&**a2) || (x.has(&**a1) && y.has(a));
                if lval && !rval || !lval && rval {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use chumsky::Parser;
    use super::*;
    use crate::parser::ltl_parser;

    #[test]
    fn test_ltl() {
        let parser = ltl_parser();
        let input = "a U (!a /\\ b)";
        let result = parser.parse(input).unwrap();
        println!("{:?}", result);
        let ltl = reduce_ltl(result);
        println!("{:?}", ltl);
        let closure = ltl.get_closure();
        println!("{:?}", closure);
        let elem_sets = get_elem_sets(&closure);
        println!("{:?}", elem_sets.len());
    }
}