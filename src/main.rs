use std::env;
use parser::{read_ltl, read_ts};

mod ltl;
mod ts;
mod nba;
mod parser;
mod ndfs;
mod checker;

fn main() {
    let args: Vec<String> = env::args().collect();
    assert_eq!(args.len(), 3, "Usage: {} <ts_file> <ltl_file>", args[0]);
    let ts_path = &args[1];
    let ltl_path = &args[2];
    // Read TS and LTL from files
    let ts = read_ts(ts_path);
    let (ts_tasks, state_tasks) = read_ltl(ltl_path);
    // Check each LTL formula against the TS
    for l in ts_tasks {
        println!("{}", ts.check(l) as u8);
    }
    for (s, l) in state_tasks {
        println!("{}", ts.check_state(s, l) as u8);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use crate::{ltl::LTLE, parser::{read_ltl, read_ts}, ts::TS};

    fn get_check_res(ts:&TS<HashSet<String>>, ts_tasks: Vec<LTLE>, state_tasks: Vec<(usize, LTLE)>) -> Vec<u8> {
        let mut res = vec!();
        for l in ts_tasks {
            res.push(ts.check(l) as u8);
        }
        for (s, l) in state_tasks {
            res.push(ts.check_state(s,l) as u8);
        }
        res
    }

    #[test]
    fn test_checker1() {
        let ts = read_ts("testcases/ts1.txt");
        let (ts_tasks, state_tasks) = read_ltl("testcases/ltl1.txt");
        assert_eq!(get_check_res(&ts, ts_tasks, state_tasks), vec![1, 1, 0, 0]);
        let (ts_tasks, state_tasks) = read_ltl("testcases/ltl2.txt");
        assert_eq!(get_check_res(&ts, ts_tasks, state_tasks), vec![1; 8]);
        let (ts_tasks, state_tasks) = read_ltl("testcases/ltl3.txt");
        assert_eq!(get_check_res(&ts, ts_tasks, state_tasks), vec![1, 0, 0, 0, 1, 1, 0, 1, 1, 1]);
    }

}
