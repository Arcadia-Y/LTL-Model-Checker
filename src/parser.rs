use chumsky::prelude::*;
use crate::{ltl::*, ts::TS};
use std::{collections::HashSet, fs::File, io::{BufRead, BufReader}, rc::Rc};

pub fn ltl_parser<'a>() -> impl Parser<'a, &'a str, LTLE> {
    recursive(|expr| {
        let ident = regex("[a-z]+").padded();

        let atom = (text::keyword("true").map(|_| LTLE::True))
            .or(ident.map(|s: &str| LTLE::Atom(s.to_string())))
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

// Read Atomic Props and the TS from a file
pub fn read_ts(file_path: &str) -> TS<HashSet<String>> {
    let file = File::open(file_path).expect("Failed to open the file.");
    let reader = BufReader::new(file);
    let mut lines = reader.lines().map(|l| l.expect("Failed to read line"));
    
    // Parse first line: S and T (states and transitions)
    let first_line = lines.next().expect("File is empty");
    let mut iter = first_line.split_whitespace();
    let state_num: usize = iter.next().expect("Missing state count")
        .parse().expect("Invalid state count");
    let transition_count: usize = iter.next().expect("Missing transition count")
        .parse().expect("Invalid transition count");
    
    // Parse second line: initial states
    let initial_line = lines.next().expect("Missing initial states line");
    let initial: Vec<usize> = initial_line.split_whitespace()
        .map(|s| s.parse().expect("Invalid initial state"))
        .collect();
    
    // Parse third line: actions (we're ignoring them)
    let _actions_line = lines.next().expect("Missing actions line");
    
    let props_line = lines.next().expect("Missing propositions line");
    let props: Vec<String> = props_line.split_whitespace()
        .map(|s| s.to_string())
        .collect();
    
    let mut transition: Vec<Vec<usize>> = vec![Vec::new(); state_num];
    
    // Parse transitions
    for _ in 0..transition_count {
        let trans_line = lines.next().expect("Missing transition line");
        let parts: Vec<usize> = trans_line.split_whitespace()
            .map(|s| s.parse().expect("Invalid transition value"))
            .collect();
        
        if parts.len() >= 3 {
            let from = parts[0];
            let _action = parts[1]; // We're not using action for now
            let to = parts[2];
            transition[from].push(to);
        }
    }
    
    // Parse state labels
    let mut prop_map: Vec<HashSet<String>> = Vec::with_capacity(state_num);
    
    for _ in 0..state_num {
        let label_line = lines.next().expect("Missing state label line");
        let mut state_props = HashSet::new();
        
        // If line contains just -1, the set is empty
        if label_line.trim() != "-1" {
            for index in label_line.split_whitespace() {
                let i: usize = index.parse().expect("Invalid index");
                state_props.insert(props[i].clone());
            }
        }
        prop_map.push(state_props);
    }
    
    let ts = TS {
        state_num,
        transition: Rc::new(transition),
        initial: Rc::new(initial),
        prop: prop_map,
    };
    ts
}

pub fn read_ltl(file_path: &str) -> (Vec<LTLE>, Vec<(usize, LTLE)>) {
    let file = File::open(file_path).expect("Failed to open the file.");
    let reader = BufReader::new(file);
    let lines:Vec<String> = reader.lines().map(|l| l.expect("Failed to read line")).collect();
    
    // parse the first line
    let first_line = &lines[0];
    let mut iter = first_line.split_whitespace();
    let a: usize = iter.next().expect("Missing line count A")
        .parse().expect("Invalid line count A");
    let b: usize = iter.next().expect("Missing line count B")
        .parse().expect("Invalid line count B");
    // check number of lines
    assert_eq!(lines.len(), a + b + 1, "Invalid number of lines");
    
    let parser = ltl_parser();
    // Parse LTL formulas for the TS
    let mut reta = Vec::with_capacity(a);
    for i in 1..a+1 {
        let ltl_line = &lines[i];
        let ltl = parser.parse(ltl_line).into_output()
            .expect("Invalid LTL formula");
        reta.push(ltl);
    }
    // Parse LTL formulas for states
    let mut retb = Vec::with_capacity(b);
    for i in a+1..a+b+1 {
        let ltl_line = lines[i].trim();
        let (num, ltl_str) = ltl_line.split_at(ltl_line.find(' ').expect("Missing space"));
        let index: usize = num.parse().expect("Invalid index");
        let ltl = parser.parse(ltl_str).into_output()
            .expect("Invalid LTL formula");
        retb.push((index, ltl));
    }
    (reta, retb)
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_read_ts() {
        let ts = super::read_ts("testcases/ts1.txt");
        println!("{:?}", ts);
    }

    #[test]
    fn test_read_ltl() {
        let (a, b) = super::read_ltl("testcases/ltl1.txt");
        println!("{:?}", a);
        println!("{:?}", b);
    }
}
