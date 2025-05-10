use std::{collections::HashSet, rc::Rc};
use crate::nba::NBA;

// Transition System with natural numbers as states
// Since actions are currently useless, we ignore them for now
// AP is the type of atomic propositions
#[derive(Debug)]
pub struct TS<AP> {
    pub state_num: usize,
    pub transition: Rc<Vec<Vec<usize>>>,
    pub initial: Rc<Vec<usize>>,
    pub prop: Vec<AP>,
}

// construct a product TS of a TS and an NBA 
// with `atoms` as AP of the NBA and `init_set` as initial states of the TS
pub fn ts_nba_prod<A: PartialEq>(ts: &TS<A>, nba: &NBA<A>) -> TS<usize> {
    let sn = ts.state_num;
    let qn = nba.state_num;
    // (s, q) is encoded as s * qn + q
    let pair = |s: usize, q: usize| s * qn + q;
    let state_num = sn * qn;

    let mut transition = vec![Vec::new(); state_num];
    for s in 0..sn {
        for t in &ts.transition[s] {
            let lt = &ts.prop[*t];
            for q in 0..qn {
                nba.transition[q].iter()
                    .filter(|(a, _)| a == lt)
                    .for_each(|(_, ps)| {
                        for p in ps {
                            transition[pair(s, q)].push(pair(*t, *p));
                        }
                    });
            }
        }
    }

    let mut initial = Vec::new();
    for s in &*ts.initial {
        let ls = &ts.prop[*s];
        let mut qset = HashSet::new();
        for i in &nba.initial {
            nba.transition[*i].iter()
                .filter(|(a, _)| a == ls)
                .for_each(|(_, qs)| qset.extend(qs));
        }
        for q in qset {
            initial.push(pair(*s, q));
        }
    }

    let mut prop = Vec::with_capacity(state_num);
    for _ in 0..sn {
        for q in 0..qn {
            prop.push(q);
        }
    }
    
    TS {
        state_num,
        transition: Rc::new(transition),
        initial: Rc::new(initial),
        prop,
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, rc::Rc};
    use crate::{nba::NBA, ts::{ts_nba_prod, TS}};

    #[test]
    fn test_ts_nba_prod() {
        let red = String::from("red");
        let green = String::from("green");
        let ts = TS {
            state_num: 2,
            initial: Rc::new(vec![0]),
            transition: Rc::new(vec![vec![1], vec![0]]),
            prop: vec![red.clone(),
                       green.clone()],
        };
        let nba = NBA {
            state_num: 3,
            initial: vec![0],
            accept: HashSet::from([1]),
            transition: vec![
                vec![(red.clone(), vec![0, 1]), (green.clone(), vec![0])],
                vec![(red.clone(), vec![1]), (green.clone(), vec![2])],
                vec![(red.clone(), vec![2]), (green.clone(), vec![2])],
            ],
        };
        let prod = ts_nba_prod(&ts, &nba);
        println!("{:?}", prod);
    }

}