
# LTL Model Checker Documentation

## 1. Linear Temporal Logic (LTL)

LTL formulas are used to specify properties of sequences of states.

### Data Structures: `LTLE` and `LTL`

The project defines two enums for LTL formulas:
*   `LTLE` (LTL Extended): Represents LTL formulas with a richer set of operators, including `Or`, `Implies`, `Eventually (F)`, and `Always (G)`.
*   `LTL`: Represents LTL formulas in a reduced form, using only `True`, `Atom`, `Not`, `And`, `Next (X)`, and `Until (U)`.

````rust
// filepath: src/ltl.rs
// LTL formulas with extended operators
#[derive(Debug)]
pub enum LTLE {
    True,
    Atom(String),
    Not(Box<LTLE>),
    And(Box<LTLE>, Box<LTLE>),
    Or(Box<LTLE>, Box<LTLE>),
    Impl(Box<LTLE>, Box<LTLE>),
    Next(Box<LTLE>),
    Even(Box<LTLE>), // Eventually (F)
    Always(Box<LTLE>), // Always (G)
    Until(Box<LTLE>, Box<LTLE>),
}

// LTL formulas with only basic operators
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum LTL {
    True,
    Atom(String),
    Not(Box<LTL>),
    And(Box<LTL>, Box<LTL>),
    Next(Box<LTL>),
    Until(Box<LTL>, Box<LTL>),
}
````

### `reduce_ltl`: Converting `LTLE` to `LTL`

The `reduce_ltl` function converts an `LTLE` formula into an equivalent `LTL` formula by expressing extended operators in terms of the basic ones. For example:
*   $\varphi_1 \lor \varphi_2 \equiv \neg (\neg \varphi_1 \land \neg \varphi_2)$
*   $\varphi_1 \rightarrow \varphi_2 \equiv \neg (\varphi_1 \land \neg \varphi_2)$ (or $\neg \varphi_1 \lor \varphi_2$)
*   $F \varphi \equiv \text{true} U \varphi$
*   $G \varphi \equiv \neg F \neg \varphi \equiv \neg (\text{true} U \neg \varphi)$

```rust
// filepath: src/ltl.rs

pub fn negate(x: LTL) -> LTL {
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
```


### `get_atoms`: Extracting Atomic Propositions

This method collects all unique atomic propositions (strings) present in an `LTL` formula.

```rust
// filepath: src/ltl.rs

impl<'a> LTL {
    // get the atoms of an LTL formula
    pub fn get_atoms(&self) -> HashSet<String> {
        let mut res = HashSet::new();
        self.get_atoms_aux(&mut res);
        res
    }

    fn get_atoms_aux(&self, set: &mut HashSet<String>) {
        match self {
            LTL::True => {}
            LTL::Atom(s) => {
                set.insert(s.clone());
            }
            LTL::Not(x) => x.get_atoms_aux(set),
            LTL::And(x, y) => {
                x.get_atoms_aux(set);
                y.get_atoms_aux(set);
            }
            LTL::Next(x) => x.get_atoms_aux(set),
            LTL::Until(x, y) => {
                x.get_atoms_aux(set);
                y.get_atoms_aux(set);
            }
        }
    }

```


### `get_closure`: Computing the Closure

The closure of an LTL formula $\varphi$, denoted $cl(\varphi)$, is the set of all subformulas of $\varphi$. To improve space efficiency, only subformulas that do not start with negation are explicitly included, as negations are handled by the `has` method of `ElemSet`. This is crucial for constructing the states of the GNBA.

```rust
// filepath: src/ltl.rs

    // get the closure of an LTL formula
    // only subformulas that don't start with negation are included
    pub fn get_closure(&self) -> Vec<& LTL> {
        let mut res = vec!();
        let mut set = HashSet::new();
        self.get_closure_aux(&mut res, &mut set);
        res
    }

    fn update_closure<'b>(&'a self, vec: &'b mut Vec<&'a LTL>, set: &'b mut HashSet<&'a LTL>) {
        if !set.contains(self) {
            vec.push(self);
            set.insert(self);
        }
    }

    fn get_closure_aux<'b>(&'a self, vec: &'b mut Vec<&'a LTL>, set: &'b mut HashSet<&'a LTL>) {
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
```

### `ElemSet`: Elementary Sets

An elementary set $B$ for an LTL formula $\varphi$ is a subset of $cl(\varphi)$ that is maximally consistent. It represents a "snapshot" of truth values for subformulas at a particular state.
It contains:
*   `atoms`: The set of atomic propositions true in this elementary set.
*   `set`: The set of (positive) subformulas from the closure that are true in this elementary set.

````rust
// filepath: src/ltl.rs

// An elementary set B of an LTL
// atoms = B ∩ AP
// set is a map from positive sub-formulas of the LTL formulas to their truth values in B
#[derive(Debug, Clone)]
pub struct ElemSet<'a> {
    pub atoms: HashSet<String>,
    pub set: HashSet<&'a LTL>,
}

impl<'a> ElemSet<'a> {
    // check whether an elementary set contains an LTL formula
    // it will handle the negation case
    pub fn has(&self, x: &LTL) -> bool {
        match x {
            LTL::True => true,
            LTL::Not(y) => !self.has(y),
            _ => self.set.contains(x)
        }
    }
}

````

### `get_elem_sets`: Generating Elementary Sets

This function recursively generates all valid elementary sets for a given closure. A set is valid if it satisfies consistency rules for LTL operators (e.g., $\varphi_1 \land \varphi_2$ is in the set iff both $\varphi_1$ and $\varphi_2$ are in the set).

````rust
// filepath: src/ltl.rs

// get the elementary sets of a closure
pub fn get_elem_sets<'a>(cl: &'a Vec<&LTL>) -> Vec<ElemSet<'a>> {
    let mut res = vec!();
    let cur = ElemSet {
        atoms: HashSet::new(),
        set: HashSet::new(),
    };
    get_elem_sets_aux(cl, cur, &mut res);
    res
}

fn eval_truth_value(e: &ElemSet, x: &LTL) -> bool {
    match x {
        LTL::True => true,
        LTL::Not(x) => !eval_truth_value(e, x),
        _ => e.set.contains(x)
    }
}

fn get_elem_sets_aux<'a>(cl: &'a [&LTL], mut cur: ElemSet<'a>, res: &mut Vec<ElemSet<'a>>) {
    if cl.is_empty() {
        res.push(cur);
        return;
    }
    let x = cl[0];
    match x {
        LTL::True => get_elem_sets_aux(&cl[1..], cur, res),
        LTL::Atom(s) => {
            let mut other = cur.clone();
            // x is false
            get_elem_sets_aux(&cl[1..], cur, res);
            // x is true
            other.atoms.insert(s.clone());
            other.set.insert(x);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Not(_) => { // Negations are handled by consistency of positive subformulas
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::And(a, b) => {
            if eval_truth_value(&cur, a) && eval_truth_value(&cur, b) {
                cur.set.insert(x);
            }
            get_elem_sets_aux(&cl[1..], cur, res);
        }
        LTL::Next(_) => { // Next formulas can be true or false independently of current atoms
            let mut other = cur.clone();
            // x is false
            get_elem_sets_aux(&cl[1..], cur, res);
            // x is true
            other.set.insert(x);
            get_elem_sets_aux(&cl[1..], other, res);
        }
        LTL::Until(a, b) => { // phi U psi
            if eval_truth_value(&cur, b) { // psi is true
                cur.set.insert(x); // Then phi U psi is true
                get_elem_sets_aux(&cl[1..], cur, res);
            } else { // psi is false
                if eval_truth_value(&cur, a) { // phi is true
                    let mut other = cur.clone();
                    // x (phi U psi) is false (consistent with psi false, phi true)
                    get_elem_sets_aux(&cl[1..], cur, res);
                    // x (phi U psi) is true (consistent with psi false, phi true)
                    other.set.insert(x);
                    get_elem_sets_aux(&cl[1..], other, res);
                } else { // phi is false (and psi is false)
                    // x (phi U psi) must be false
                    get_elem_sets_aux(&cl[1..], cur, res);
                }
            }
        }
    }
}

````

### `step_relation`: One-Step Relation for GNBA Construction

This function checks if a transition from elementary set `x` to elementary set `y` is valid according to LTL semantics. This is used to define transitions in the GNBA.
*   For $X \psi \in cl(\varphi)$: $X \psi \in x \iff \psi \in y$.
*   For $\psi_1 U \psi_2 \in cl(\varphi)$: $\psi_1 U \psi_2 \in x \iff (\psi_2 \in x) \lor (\psi_1 \in x \land \psi_1 U \psi_2 \in y)$.

````rust
// filepath: src/ltl.rs

// Check if (x, y) satisfies one-step relation in the construction of the GNBA's transition relation
pub fn step_relation(clos:&Vec<&LTL>, x: &ElemSet, y: &ElemSet) -> bool {
    for a in clos {
        match a {
            LTL::Next(b) => {
                let a_in_x = x.has(a);
                let b_in_y = y.has(&**b);
                if a_in_x && !b_in_y || !a_in_x && b_in_y {
                    return false;
                }
            }
            LTL::Until(a1, a2) => {
                let lval = x.has(a); // (a1 U a2) in x
                let rval = x.has(&**a2) || (x.has(&**a1) && y.has(a)); // a2 in x OR (a1 in x AND (a1 U a2) in y)
                if lval && !rval || !lval && rval {
                    return false;
                }
            }
            _ => {}
        }
    }
    true
}

````

## 2. Automata (GNBA and NBA)

Automata are used to represent the LTL formula. The model checking problem is then reduced to an emptiness check on the product of the TS and the automaton for the negated formula.

### Data Structures: `GNBA` and `NBA`

*   `GNBA` (Generalized Büchi Automaton): An automaton with multiple acceptance sets. A run is accepting if it visits states from each acceptance set infinitely often.
    *   `state_num`: Number of states.
    *   `initial`: List of initial states.
    *   `transition`: Transition function. For each state, a list of (alphabet symbol, destination states) tuples.
    *   `accept`: A vector of `HashSet<usize>`, where each `HashSet` is an acceptance set.
*   `NBA` (Büchi Automaton): An automaton with a single acceptance set. A run is accepting if it visits some state from the acceptance set infinitely often.
    *   Fields are similar to `GNBA`, but `accept` is a single `HashSet<usize>`.

````rust
// filepath: src/nba.rs

// GNBA with natural numbers as states and A as alphabet
#[derive(Debug)]
pub struct GNBA<A> {
    state_num: usize,
    initial: Vec<usize>,
    // q -> [(A, δ(q, a))]
    transition: Vec<Vec<(A, Vec<usize>)>>,
    accept: Vec<HashSet<usize>>,
}

// NBA with natural numbers as states and A as alphabet
#[derive(Debug)]
pub struct NBA<A> {
    pub state_num: usize,
    pub initial: Vec<usize>,
    // q -> [(A, δ(q, a))]
    pub transition: Vec<Vec<(A, Vec<usize>)>>,
    pub accept: HashSet<usize>,
}

````

### `ltl_to_gnba`: Constructing GNBA from LTL

This function constructs a GNBA for a given LTL formula $\varphi$.
*   **States**: The states of the GNBA are the elementary sets of $\varphi$.
*   **Initial States**: Elementary sets $B$ such that $\varphi \in B$.
*   **Transitions**: A transition exists from state $B_i$ (representing `elem_sets[i]`) to $B_j$ on an input alphabet symbol $\alpha$ (a set of atomic propositions) if $B_i.\text{atoms} = \alpha$ and the `step_relation(clos, &elem_sets[i], &elem_sets[j])` holds. In this implementation, the alphabet symbol is directly taken from `elem_sets[i].atoms`.
*   **Acceptance Sets**: For each subformula of the form $\psi_1 U \psi_2$ in $cl(\varphi)$, there is an acceptance set $F_k = \{ B \mid \neg(\psi_1 U \psi_2) \in B \lor \psi_2 \in B \}$. (This is equivalent to $B \notin F_k \implies (\psi_1 U \psi_2 \in B \land \neg \psi_2 \in B)$). If there are no `Until` subformulas, all states form a single acceptance set.

````rust
// filepath: src/nba.rs

// Construct a GNBA from an LTL formula
pub fn ltl_to_gnba(phi:&LTL, clos:&Vec<&LTL>, elem_sets: &Vec<ElemSet>) -> GNBA<HashSet<String>> {
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
                    // States where the Until obligation is met or the Until formula is false
                    // F_i = { B | B |= neg(psi1 U psi2) or B |= psi2 }
                    // which is equivalent to { B | not (B |= (psi1 U psi2) and B |= not psi2) }
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

````

### `gnba_to_nba`: Converting GNBA to NBA

This function converts a GNBA to an equivalent NBA using the standard "counting" construction.
If the GNBA has $n$ states and $k$ acceptance sets $F_0, \dots, F_{k-1}$, the NBA will have $n \times k$ states.
A state in the NBA is a pair $(q, j)$, where $q$ is a GNBA state and $j \in \{0, \dots, k-1\}$ is a counter indicating the next acceptance set $F_j$ to be visited.
*   **NBA States**: $(q, j)$ where $q$ is a GNBA state, $j \in [0, k-1]$. Encoded as $q + j \times n$.
*   **NBA Initial States**: $(q_0, 0)$ for each initial state $q_0$ of the GNBA.
*   **NBA Transitions**: If GNBA has transition $q \xrightarrow{\alpha} q'$, then NBA has:
    *   $(q, j) \xrightarrow{\alpha} (q', j)$ if $q \notin F_j$.
    *   $(q, j) \xrightarrow{\alpha} (q', (j+1) \pmod k)$ if $q \in F_j$.
*   **NBA Acceptance Set**: States $(q, 0)$ where $q \in F_0$ (or any other fixed index, typically 0). The implementation uses `gnba.accept[0]` for the NBA's acceptance set, and states are of the form `q` (original GNBA state index) if they are in `gnba.accept[0]`. The product states are `q + j * n`. The NBA acceptance set consists of states `s` (which is `q + 0 * n`) such that `q` is in `gnba.accept[0]`.

````rust
// filepath: src/nba.rs

// transform a GNBA to an NBA
pub fn gnba_to_nba<A: Clone>(gnba: &GNBA<A>) -> NBA<A> {
    let k = gnba.accept.len();
    let n = gnba.state_num;
    // (q,j) is encoded as q + j * n
    let initial = gnba.initial.clone(); // Initial states are (q_init, 0)
    let state_num = gnba.state_num * k;
    // NBA accepting states are (q, 0) where q is in F_0 of GNBA.
    // Here, it means states with index q (from 0 to n-1) if q is in gnba.accept[0].
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
        initial, // These are GNBA initial states, implicitly becoming (q_initial, 0) in the product TS * NBA
        transition,
        accept,
    }
}

````

## 3. Transition Systems (TS)

A Transition System models the behavior of the system being checked.

### Data Structure: `TS`

*   `state_num`: Number of states.
*   `transition`: Adjacency list representation of transitions. `transition[i]` is a list of states reachable from state `i`.
*   `initial`: List of initial states.
*   `prop`: For each state `s`, `prop[s]` stores the set of atomic propositions true at state `s`. The type `AP` is generic.

````rust
// filepath: src/ts.rs

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

````

### `ts_nba_prod`: Product of a TS and an NBA

This function constructs the product automaton $TS \otimes \mathcal{A}$.
*   **States**: Pairs $(s, q)$ where $s$ is a TS state and $q$ is an NBA state. Encoded as $s \times q_n + q$, where $q_n$ is `nba.state_num`.
*   **Initial States**: $(s_0, q')$ such that $s_0$ is an initial state of $TS$, and there's a transition $q_0 \xrightarrow{L(s_0)} q'$ in the NBA, where $q_0$ is an initial state of the NBA and $L(s_0)$ is the set of propositions true at $s_0$.
*   **Transitions**: If $s \to s'$ is a transition in $TS$ and $q \xrightarrow{L(s')} q'$ is a transition in the NBA, then $(s, q) \to (s', q')$ is a transition in the product.
*   **Acceptance States (for NDFS)**: The `prop` field of the product TS stores the NBA state component `q` for each product state $(s,q)$. This is used by NDFS in conjunction with `nba.accept` to identify accepting states in the product.

````rust
// filepath: src/ts.rs

// construct a product TS of a TS and an NBA 
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

    // The 'prop' of the product state (s,q) is q itself.
    // This is used by NDFS to check against nba.accept.
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
        prop, // prop[pair(s,q)] = q
    }
}

````

## 4. Nested Depth-First Search (NDFS)

NDFS is an algorithm for detecting accepting cycles in a Büchi automaton (here, the product $TS \otimes \mathcal{A}$).

### Data Structure: `NDFS`

*   `ts`: The product automaton $TS \otimes \mathcal{A}$.
*   `accept`: The acceptance set of the NBA $\mathcal{A}$ (used to identify accepting states in the product).
*   `outer_visited`: Marks states visited by the first (outer) DFS.
*   `inner_visited`: Marks states visited by the second (inner) DFS.
*   `state_cnt`: The number of states in the original NBA
*   `trace`: The trace of the states in the original TS for the counterexample

````rust
// filepath: src/ndfs.rs

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

````

### `run` and DFS methods: Cycle Detection

The `run` method along with two other methods implements the NDFS algorithm. It shares the same core idea with the NDFS algorithm on textbook. However, we implement both DFS in the recursive form, which is more concise and easier to understand than the stack form.
Besides, we track down the trace in the original TS if we successfully find a a reachable cycle with an accepting state


````rust
// filepath: src/ndfs.rs

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
````

## 5. Parsing

The parser.rs file contains functions to parse input files.

### `ltl_parser`: LTL Formula Parser

Uses the `chumsky` parser combinator library to parse LTL formulas from strings into `LTLE` enum variants.

````rust
// filepath: src/parser.rs

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
                op2('/', '\\').to(LTLE::And as fn(_, _) -> _), // /\
                op2('\\', '/').to(LTLE::Or as fn(_, _) -> _),  // \/
                op2('-', '>').to(LTLE::Impl as fn(_, _) -> _), // ->
                op('U').to(LTLE::Until as fn(_, _) -> _),
            ))
            .then(unary)
            .repeated(),
            |lhs, (op, rhs)| op(Box::new(lhs), Box::new(rhs)),
        );

        binary
    })
}

````

### `read_ts`: Transition System Parser

Reads a file describing a transition system (number of states, transitions, initial states, atomic propositions, and state labels) and constructs a `TS<HashSet<String>>` object.

````rust
// filepath: src/parser.rs

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
            for index_str in label_line.split_whitespace() {
                let i: usize = index_str.parse().expect("Invalid index");
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

````

### `read_ltl`: LTL Formulas Parser

Reads a file containing LTL formulas. The file specifies a number of formulas to check against the whole TS and a number of formulas to check against specific states of the TS.

````rust
// filepath: src/parser.rs

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
        let (num_str, ltl_str_with_space) = ltl_line.split_at(ltl_line.find(' ').expect("Missing space"));
        let index: usize = num_str.parse().expect("Invalid index");
        let ltl = parser.parse(ltl_str_with_space.trim_start()).into_output()
            .expect("Invalid LTL formula");
        retb.push((index, ltl));
    }
    (reta, retb)
}

````

## 6. Model Checking Logic

The checker.rs file implements the core model checking algorithm.

### `check` and `check_state` methods

These methods, implemented for `Checker`, orchestrate the model checking workflow:
1.  Negate the input LTL formula (`ltle`) and reduce it.
2.  Get atoms, closure, and elementary sets for the negated formula.
3.  Construct GNBA and then NBA for the negated formula.
4.  Create a new TS (`ts_new`) where atomic propositions are scoped to those relevant to the LTL formula. For `check_state`, the initial states of `ts_new` are also restricted to the specified state `s`.
5.  Construct the product $TS_{new} \otimes NBA$.
6.  Run NDFS on the product.
7.  The result is `!ndfs.run()`: if NDFS finds an accepting cycle (meaning $\neg \varphi$ is satisfiable), then $\varphi$ is false. Otherwise, $\varphi$ is true.

````rust
// filepath: src/checker.rs
impl<'a> Checker<'a> {
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
````
