use std::{collections::HashSet, vec};
use crate::ts::TS;

// data structures for nested DFS
pub struct NDFS<'a> {
    ts: &'a TS<usize>,
    accept: &'a HashSet<usize>, // NBA accepting states
    outer_visited: Vec<bool>,
    inner_visited: Vec<bool>,
    state_cnt: usize, // the number of states in the NBA
    trace: Vec<usize>, // the trace of the counterexample
}

impl<'a> NDFS<'a> {
    pub fn new(ts: &'a TS<usize>, accept: &'a HashSet<usize>, state_cnt: usize) -> Self {
        let state_num = ts.state_num;
        NDFS {
            ts,
            accept,
            inner_visited: vec![false; state_num],
            outer_visited: vec![false; state_num],
            state_cnt,
            trace: vec![],
        }
    }

    // return the trace of the counterexample
    pub fn get_trace(&self) -> &Vec::<usize> {
        &self.trace
    }

    // track down the trace for the counterexample
    fn track(&mut self, s: usize) {
        self.trace.push(s / self.state_cnt);
    }

    // return whether there's a reachable cycle with an accepting state
    pub fn run(&mut self) -> bool {
        for i in &*self.ts.initial {
            if !self.outer_visited[*i] {
                if self.reachable_cycle(*i) {
                    self.track(*i);
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
                    self.track(*t);
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
                self.track(*t);
                return true;
            }
            if !self.inner_visited[*t] {
                if self.cycle_check(s, *t) {
                    self.track(*t);
                    return true;
                }
            }
        }
        false
    }

}
