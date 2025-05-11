mod ltl;
mod ts;
mod nba;
mod parser;
mod ndfs;
mod checker;

use checker::Checker;
use parser::{read_ltl, read_ts};
use clap::Parser;
use checker::CheckerArg;

#[derive(Parser, Debug)]
#[command(name = "ltl-checker", version = "0.1.0", about = "An LTL model checker")]
pub struct CliArgs {
    /// Path to the transition system file
    ts_file: String,
    /// Path to the LTL formulas file
    ltl_file: String,
    /// Output the counterexample trace
    #[arg(short, long, action = clap::ArgAction::SetTrue)]
    trace: bool,
    /// Output the GNBA of LTL formulas
    #[arg(short, long, action = clap::ArgAction::SetTrue)]
    gnba: bool,
    /// Output the NBA of LTL formulas
    #[arg(short, long, action = clap::ArgAction::SetTrue)]
    nba: bool,
    /// Output the product TS for checking
    #[arg(short, long, action = clap::ArgAction::SetTrue)]
    prod: bool,
}

fn main() {
    let args = CliArgs::parse();
    // Read TS and LTL from files
    let ts = read_ts(&args.ts_file);
    let (ts_tasks, state_tasks) = read_ltl(&args.ltl_file);
    let checker = Checker::with_args(&ts, CheckerArg::from(&args));
    // Check each LTL formula against the TS
    for l in ts_tasks {
        checker.check(l);
    }
    for (s, l) in state_tasks {
        checker.check_state(s, l);
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;
    use crate::{checker::Checker, ltl::LTLE, parser::{read_ltl, read_ts}, ts::TS, CliArgs};

    fn get_check_res(ts:&TS<HashSet<String>>, ts_tasks: Vec<LTLE>, state_tasks: Vec<(usize, LTLE)>) -> Vec<u8> {
        let checker = Checker::new(ts);
        let mut res = vec!();
        for l in ts_tasks {
            res.push(checker.check(l) as u8);
        }
        for (s, l) in state_tasks {
            res.push(checker.check_state(s,l) as u8);
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
