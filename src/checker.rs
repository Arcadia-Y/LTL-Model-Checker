use crate::{ltl::*, nba::*, ndfs, ts::*, CliArgs};
use std::{collections::HashSet, rc::Rc};

// Checker Arguments
pub struct CheckerArg {
    res: bool,
    gnba: bool,
    nba: bool,
    prod: bool,
    trace: bool,
}

impl CheckerArg {
    pub fn new() -> Self {
        CheckerArg {
            res: false,
            gnba: false,
            nba: false,
            prod: false,
            trace: false,
        }
    }
}

impl From<&CliArgs> for CheckerArg {
    fn from(args: &CliArgs) -> Self {
        CheckerArg {
            res: true,
            gnba: args.gnba,
            nba: args.nba,
            prod: args.prod,
            trace: args.trace,
        }
    }
}
pub struct Checker<'a> {
    ts: &'a TS<HashSet<String>>,
    args: CheckerArg,
}

impl<'a> Checker<'a> {
    // return a Checker without output
    pub fn new(ts: &'a TS<HashSet<String>>) -> Self {
        Checker {
            ts,
            args: CheckerArg::new(),
        }
    }

    pub fn with_args(ts: &'a TS<HashSet<String>>, args: CheckerArg) -> Self {
        Checker { ts, args }
    }

    fn show_trace(&self, trace: &Vec<usize>) {
        print!("Counterexample: ");
        for i in trace.iter().rev() {
            print!("{} ", i);
        }
        println!();
    }

    // return the NBA of the negated ltl and its atoms
    fn ltl_to_nba(&self, ltle: LTLE) -> (NBA<HashSet<String>>, HashSet<String>) {
        let ltl = negate(reduce_ltl(ltle));
        let atoms = ltl.get_atoms();
        let closure = ltl.get_closure();
        let elem_sets = get_elem_sets(&closure);
        let gnba = ltl_to_gnba(&ltl, &closure, &elem_sets);
        if self.args.gnba {
            println!("GNBA: {:?}", gnba);
        }
        let nba = gnba_to_nba(&gnba);
        if self.args.nba {
            println!("NBA: {:?}", nba);
        }
        (nba, atoms)
    }

    // check whether a TS satisfies an LTL formula
    pub fn check(&self, ltle: LTLE) -> bool {
        let (nba, atoms) = self.ltl_to_nba(ltle);
        // construct a new TS with the scoped prop
        let ts_new = TS {
            state_num: self.ts.state_num,
            transition: self.ts.transition.clone(),
            initial: self.ts.initial.clone(),
            prop: self.ts.prop.iter().map(|x| x.intersection(&atoms).cloned().collect()).collect(),
        };
        let ts_nba = ts_nba_prod(&ts_new, &nba);
        if self.args.prod {
            println!("Product TS: {:?}", ts_nba);
        }
        let mut ndfs = ndfs::NDFS::new(&ts_nba, &nba.accept, nba.state_num);
        let res = !ndfs.run();
        if self.args.res {
            println!("{}", res as u8);
        }
        if self.args.trace && !res {
            self.show_trace(ndfs.get_trace());
        }
        res
    }

    // check whether a state in a TS satisfies an LTL formula
    pub fn check_state(&self, s: usize, ltle: LTLE) -> bool {
        let (nba, atoms) = self.ltl_to_nba(ltle);
        // construct a new TS with the scoped prop and s as the only initial state
        let ts_new = TS {
            state_num: self.ts.state_num,
            transition: self.ts.transition.clone(),
            initial: Rc::new(vec![s]),
            prop: self.ts.prop.iter().map(|x| x.intersection(&atoms).cloned().collect()).collect(),
        };
        let ts_nba = ts_nba_prod(&ts_new, &nba);
        if self.args.prod {
            println!("Product TS: {:?}", ts_nba);
        }
        let mut ndfs = ndfs::NDFS::new(&ts_nba, &nba.accept, nba.state_num);
        let res = !ndfs.run();
        if self.args.res {
            println!("{}", res as u8);
        }
        if self.args.trace && !res {
            self.show_trace(ndfs.get_trace());
        }
        res
    }
}
