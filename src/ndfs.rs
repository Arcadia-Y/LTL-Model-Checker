use std::{collections::HashSet, vec};
use crate::ts::TS;

// data structures for nested DFS
pub struct NDFS<'a> {
    ts: &'a TS<usize>,
    accept: &'a HashSet<usize>, // NBA accepting states
    outer_visited: Vec<bool>,
    inner_visited: Vec<bool>,
}

impl<'a> NDFS<'a> {
    pub fn new(ts: &'a TS<usize>, accept: &'a HashSet<usize>) -> Self {
        let state_num = ts.state_num;
        NDFS {
            ts,
            accept,
            inner_visited: vec![false; state_num],
            outer_visited: vec![false; state_num],
        }
    }

    // return whether there's a reachable cycle with an accepting state
    pub fn run(&mut self) -> bool {
        for i in &*self.ts.initial {
            if !self.outer_visited[*i] {
                if self.reachable_cycle(*i) {
                    return true;
                }
            }
        }
        false
    }

    // outrer DFS
    fn reachable_cycle(&mut self, s: usize) -> bool {
        self.outer_visited[s] = true;
        for t in &self.ts.transition[s] {
            if !self.outer_visited[*t] {
                if self.reachable_cycle(*t) {
                    return true;
                }
            }
        }
        // outer DFS finished for s
        if self.accept.contains(&self.ts.prop[s]) {
            // inner DFS
            if self.cycle_check(s, s) {
                return true;
            }
        }
        false
    }

    // inner DFS
    // all inner DFS shares the same visited set
    // this is a key trick to improve performance
    fn cycle_check(&mut self, s: usize, v: usize) -> bool {
        self.inner_visited[v] = true;   
        for t in &self.ts.transition[v] {
            if *t == s {
                return true;
            }
            if !self.inner_visited[*t] {
                if self.cycle_check(s, *t) {
                    return true;
                }
            }
        }
        false
    }

}
