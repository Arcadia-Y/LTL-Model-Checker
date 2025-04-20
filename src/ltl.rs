use std::{collections::{HashMap, HashSet}, vec};

use chumsky::prelude::*;

// LTL formulas with extended operators
#[derive(Debug)]
pub enum LTLE<'a> {
    True,
    Atom(&'a str),
    Not(Box<LTLE<'a>>),
    And(Box<LTLE<'a>>, Box<LTLE<'a>>),
    Or(Box<LTLE<'a>>, Box<LTLE<'a>>),
    Impl(Box<LTLE<'a>>, Box<LTLE<'a>>),
    Next(Box<LTLE<'a>>),
    Even(Box<LTLE<'a>>),
    Always(Box<LTLE<'a>>),
    Until(Box<LTLE<'a>>, Box<LTLE<'a>>),
}

pub fn ltl_parser<'a>() -> impl Parser<'a, &'a str, LTLE<'a>> {
    recursive(|expr| {
        let ident = regex("[a-z]+").padded();

        let atom = (text::keyword("true").map(|_| LTLE::True))
            .or(ident.map(|s| LTLE::Atom(s)))
            .or(expr.delimited_by(just('('), just(')')))
            .padded();  
    
        let op = |c| just(c).padded();
        let op2 = |c1: char, c2: char| just(c1).then(just(c2)).padded();
    
        let unary = choice((
            op('!').to(LTLE::Not as fn(_) -> _),
            op('X').to(LTLE::Next as fn(_) -> _),
            op('G').to(LTLE::Always as fn(_) -> _),
            op('F').to(LTLE::Even as fn(_) -> _),
        ))
            .or_not()
            .then(atom)
            .map(|(lhs, rhs)| match lhs {
                Some(op) => op(Box::new(rhs)),
                None => rhs,
            });
    
        let binary = unary.clone().foldl(
            choice((
                op2('/', '\\').to(LTLE::And as fn(_, _) -> _),
                op2('\\', '/').to(LTLE::Or as fn(_, _) -> _),
                op2('-', '>').to(LTLE::Impl as fn(_, _) -> _),
                op('U').to(LTLE::Until as fn(_, _) -> _),
            ))
            .then(unary)
            .repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        );

        binary
    })
}

// LTL formulas with only basic operators
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum LTL<'a> {
    True,
    Atom(&'a str),
    Not(Box<LTL<'a>>),
    And(Box<LTL<'a>>, Box<LTL<'a>>),
    Next(Box<LTL<'a>>),
    Until(Box<LTL<'a>>, Box<LTL<'a>>),
}

fn negate(x: LTL) -> LTL {
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

impl<'a> LTL<'a> {
    // get the closure of an LTL formula
    // only subformulas that don't start with negation are included
    pub fn get_closure(&self) -> Vec<& LTL> {
        let mut res = vec!();
        let mut set = HashSet::new();
        self.get_closure_aux(&mut res, &mut set);
        res
    }

    fn update_closure<'b>(&'a self, vec: &'b mut Vec<&'a LTL<'a>>, set: &'b mut HashSet<&'a LTL<'a>>) {
        if !set.contains(self) {
            vec.push(self);
            set.insert(self);
        }
    }

    fn get_closure_aux<'b>(&'a self, vec: &'b mut Vec<&'a LTL<'a>>, set: &'b mut HashSet<&'a LTL<'a>>) {
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
// set is a map from sub-formulas of the LTL formulas to their truth values in B
#[derive(Debug, Clone)]
pub struct ElemSet<'a> {
    atoms: HashSet<&'a str>,
    set: HashMap<&'a LTL<'a>, bool>,
}

// get the elementary sets of a closure
pub fn get_elem_sets<'a>(cl: &'a Vec<& LTL<'a>>) -> Vec<ElemSet<'a>> {
    let mut res = vec!();
    let cur = ElemSet {
        atoms: HashSet::new(),
        set: HashMap::new(),
    };
    get_elem_sets_aux(cl, cur, &mut res);
    res
}

fn eval_truth_value(e: &ElemSet, x: &LTL) -> bool {
    match x {
        LTL::True => true,
        LTL::Not(x) => !eval_truth_value(e, x),
        _ => *e.set.get(x).unwrap()
    }
}

fn get_elem_sets_aux<'a>(cl: &'a [&LTL<'a>], mut cur: ElemSet<'a>, res: &mut Vec<ElemSet<'a>>) {
    if cl.is_empty() {
        res.push(cur);
        return;
    }
    let x = cl[0];
    match x {
        LTL::True => get_elem_sets_aux(&cl[1..], cur, res),
        LTL::Atom(s) => {
            let mut other = cur.clone();
            cur.set.insert(x, false);
            get_elem_sets_aux(&cl[1..], cur, res);
            other.atoms.insert(s);
            other.set.insert(x, true);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Not(_) => {
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::And(a, b) => {
            cur.set.insert(x, eval_truth_value(&cur, a) && eval_truth_value(&cur, b));
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::Next(x) => {
            let mut other = cur.clone();
            cur.set.insert(x, false);
            get_elem_sets_aux(&cl[1..], cur, res);
            other.set.insert(x, true);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Until(a, b) => {
            if eval_truth_value(&cur, b) {
                // b is true
                cur.set.insert(x, true);
                get_elem_sets_aux(&cl[1..], cur, res);
            } else {
                // b is false
                if eval_truth_value(&cur, a) {
                    // a is true
                    let mut other = cur.clone();
                    cur.set.insert(x, false);
                    get_elem_sets_aux(&cl[1..], cur, res);
                    other.set.insert(x, true);
                    get_elem_sets_aux(&cl[1..], other, res);
                } else {
                    // a is false
                    cur.set.insert(x, false);
                    get_elem_sets_aux(&cl[1..], cur, res);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        println!("{:?}", elem_sets);
    }
}