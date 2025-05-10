use crate::{ltl::*, nba::*, ndfs, ts::*};
use std::{collections::HashSet, rc::Rc};

impl TS<HashSet<String>> {
    // check whether a TS satisfies an LTL formula
    pub fn check(&self, ltle: LTLE) -> bool {
        let ltl = negate(reduce_ltl(ltle));
        let atoms = ltl.get_atoms();
        let closure = ltl.get_closure();
        let elem_sets = get_elem_sets(&closure);
        let gnba = elem_sets_to_gnba(&ltl, &closure, &elem_sets);
        let nba = gnba_to_nba(&gnba);
        // construct a new TS with the scoped prop
        let ts_new = TS {
            state_num: self.state_num,
            transition: self.transition.clone(),
            initial: self.initial.clone(),
            prop: self.prop.iter().map(|x| x.intersection(&atoms).cloned().collect()).collect(),
        };
        let ts_nba = ts_nba_prod(&ts_new, &nba,);
        let mut ndfs = ndfs::NDFS::new(&ts_nba, &nba.accept);
        ndfs.run()
    }

    // check whether a state in a TS satisfies an LTL formula
    pub fn check_state(&self, s: usize, ltle: LTLE) -> bool {
        let ltl = negate(reduce_ltl(ltle));
        let atoms = ltl.get_atoms();
        let closure = ltl.get_closure();
        let elem_sets = get_elem_sets(&closure);
        let gnba = elem_sets_to_gnba(&ltl, &closure, &elem_sets);
        let nba = gnba_to_nba(&gnba);
        // construct a new TS with the scoped prop and s as the only initial state
        let ts_new = TS {
            state_num: self.state_num,
            transition: self.transition.clone(),
            initial: Rc::new(vec![s]),
            prop: self.prop.iter().map(|x| x.intersection(&atoms).cloned().collect()).collect(),
        };
        let ts_nba = ts_nba_prod(&ts_new, &nba);
        let mut ndfs = ndfs::NDFS::new(&ts_nba, &nba.accept);
        ndfs.run()
    }
}
