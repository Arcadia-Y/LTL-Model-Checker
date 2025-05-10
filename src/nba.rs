use std::{collections::HashSet, vec};

use crate::ltl::{step_relation, ElemSet, LTL};

// GNBA with natural numbers as states and A as alphabet
#[derive(Debug)]
pub struct GNBA<A> {
    state_num: usize,
    initial: Vec<usize>,
    // q -> [(A, δ(q, a))]
    transition: Vec<Vec<(A, Vec<usize>)>>,
    accept: Vec<HashSet<usize>>,
}

// Construct a GNBA from an LTL formula
pub fn elem_sets_to_gnba(phi:&LTL, clos:&Vec<&LTL>, elem_sets: &Vec<ElemSet>) -> GNBA<HashSet<String>> {
    let state_num = elem_sets.len();

    let mut initial = vec!();
    for i in 0..state_num {
        if elem_sets[i].has(phi) {
            initial.push(i);
        }
    }

    let mut transition = vec!();
    for i in 0..state_num {
        let x = &elem_sets[i];
        let mut dest = vec!();
        for j in 0..state_num {
            let y = &elem_sets[j];
            if step_relation(&clos, x, y) {
                dest.push(j);
            }
        }
        transition.push(vec![(x.atoms.clone(), dest)]);
    }

    let mut accept = vec!();
    for a in clos {
        match a {
            LTL::Until(_, a2) => {
                let mut f = HashSet::new();
                for i in 0..state_num {
                    let x = &elem_sets[i];
                    if !(x.has(a) && !x.has(a2)) {
                        f.insert(i);
                    }
                }
                accept.push(f);
            }
            _ => {}
        }
    }
    if accept.is_empty() {
        // formula does not contain any U, all states are accepting states
        accept.push(HashSet::from_iter(0..state_num));
    }

    GNBA {
        state_num,
        initial,
        transition,
        accept,
    }
}

// NBA with natural numbers as states and A as alphabet
// specialized for LTL model checking
#[derive(Debug)]
pub struct NBA<A> {
    pub state_num: usize,
    pub initial: Vec<usize>,
    // q -> [(A, δ(q, a))]
    pub transition: Vec<Vec<(A, Vec<usize>)>>,
    pub accept: HashSet<usize>,
}

// transform a GNBA to an NBA
pub fn gnba_to_nba<A: Clone>(gnba: &GNBA<A>) -> NBA<A> {
    let k = gnba.accept.len();
    let n = gnba.state_num;
    // (q,j) is encoded as q + j * n
    let initial = gnba.initial.clone();
    let state_num = gnba.state_num * k;
    let accept = gnba.accept[0].clone();

    let mut transition = vec!();
    for j in 0..k {
        let fj = &gnba.accept[j];
        for i in 0..n {
            let ts_func = &gnba.transition[i];
            let mut res = vec!();
            for (a, ts) in ts_func {
                let dest: Vec<usize>;
                if fj.contains(&i) {
                    dest = ts.iter().map(|x: &usize| *x + (j+1) % k * n).collect();
                } else {
                    dest = ts.iter().map(|x: &usize| *x + j * n).collect();
                }
                res.push((a.clone(), dest));
            }
            transition.push(res);
        }
    }

    NBA {
        state_num,
        initial,
        transition,
        accept,
    }
}

#[cfg(test)]
mod tests {
    use chumsky::Parser;
    use crate::{ltl::*, parser::ltl_parser};
    use super::*;

    #[test]
    fn test_elem_sets_to_nba() {
        let parser = ltl_parser();
        let input = "F a";
        let result = parser.parse(input).unwrap();
        let ltl = reduce_ltl(result);
        let closure = ltl.get_closure();
        println!("{:?}", closure);
        let elem_sets = get_elem_sets(&closure);
        println!("{:?}", elem_sets);
        let gnba = elem_sets_to_gnba(&ltl, &closure, &elem_sets);
        println!("{:?}", gnba);
        let nba = gnba_to_nba(&gnba);
        println!("{:?}", nba);
    }

    #[test]
    fn test_gnba_to_nba() {
        let gnba = GNBA {
            state_num: 3,
            initial: vec![0],
            transition: vec![
                vec![(String::from("true"), vec![0]), 
                    (String::from("crit1"), vec![1]),
                    (String::from("crit2"), vec![2])],
                vec![(String::from("true"), vec![0])],
                vec![(String::from("true"), vec![0])],
            ],
            accept: vec![
                HashSet::from([1]),
                HashSet::from([2]),
            ],
        };
        println!("{:?}", gnba);
        let nba = gnba_to_nba(&gnba);
        println!("{:?}", nba);
    }
}   