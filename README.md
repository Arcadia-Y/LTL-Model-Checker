# LTL-Model-Checker

This is a Linear Temporal Logic (LTL) model checker. More specifically, given a transition system (TS) and an LTL formula, it can check whether the TS (or an arbitrary state of the TS) satisfies the formula.

See [this document](Input_Format.pdf) for input format.
We'll output the checking results line by line corresponding to the input. Each line is either `1` for `true` or `0` for `false`.

## How to Compile and Run
This project is built with Rust. If you don't have Rust installed, you can install it by following the official instructions at [rust-lang.org](https://www.rust-lang.org/tools/install).

This project was developed and tested with Rust version 1.86.0.
It is recommended to use a similar version or manage your Rust toolchain using `rustup`.

To compile the project, navigate to the project's root directory and run:
```sh
cargo build
```
For a release build (optimized), use:
```sh
cargo build --release
```

After successful compilation, the executable will be located in the `target/debug/` directory (or `target/release/` for a release build).

To run the program :
```sh
./target/debug/ltl-checker <ts_file> <ltl_file>
```
Or for a release build:
```sh
./target/release/ltl-checker <ts_file> <ltl_file>
```

Alternatively, you can compile and run the project in one step using:
```sh
cargo run -- <ts_file> <ltl_file>
```
For a release build:
```sh
cargo run --release -- <ts_file> <ltl_file>
```

## Workflow Overview
The model checking process follows these general steps for each LTL formula $\varphi$ to be checked against a transition system $TS$:

1.  **Parse Inputs:** Read the transition system $TS$ from the TS file and the LTL formulas from the LTL file.
2.  **Negate and Reduce Formula:** Construct the negation $\neg \varphi$ and transform it into a "reduced" LTL form, which uses a minimal set of LTL operators.
3.  **Compute Closure and Elementary Sets:**
    *   Calculate the closure of $\neg \varphi$, which is the set of all subformulas of $\neg \varphi$ (and their negations, handled implicitly).
    *   Generate the elementary sets of LTL formulas based on the closure.
4.  **Construct GNBA:** Build a Generalized Büchi Automaton (GNBA) that accepts all infinite words satisfying $\neg \varphi$. The states of this GNBA correspond to the elementary sets.
5.  **Convert GNBA to NBA:** Transform the GNBA into an equivalent Büchi Automaton (NBA) $\mathcal{A}$.
6.  **Construct Product Automaton:** Compute the product $TS \otimes \mathcal{A}$. This product automaton's states are pairs of states $(s, q)$ where $s$ is a state in $TS$ and $q$ is a state in $\mathcal{A}$.
7.  **Nested DFS:** Run a nested depth-first search (NDFS) algorithm on $TS \otimes \mathcal{A}$ to check if there is an accepting cycle reachable from an initial state.
    *   If such a cycle exists, it means there is a path in $TS$ that satisfies $\neg \varphi$. Therefore, $TS \not\models \varphi$.
    *   If no such cycle exists, the language of $TS \otimes \mathcal{A}$ is empty, meaning no path in $TS$ satisfies $\neg \varphi$. Therefore, $TS \models \varphi$.
8.  **Output Result:** Print `1` if $TS \models \varphi$ and `0` otherwise.

If checking a formula $\varphi$ for a specific state $s_0$ in $TS$, the process is similar, but the initial state of the TS in the product automaton construction is restricted to only $s_0$.
<!-- Our overall workflow is as follows: We first parse input to get the transition system $TS$ and LTL formulas. Then for each formula $\varphi$, we
- construct $\neg \varphi$ and transform it into the reduced form
- construct its elementary set
- construct a GNBA for $\neg \varphi$
- transform the GNBA into an NBA $\mathcal{A}$
- construct $TS \otimes \mathcal{A}$ within the scope of $\varphi$ (and possibly the specific state $s$ to check)
- run the nested DFS on $TS \otimes \mathcal{A}$ to check whether $TS \models \varphi$ -->

## Code Structure
The project is organized into several Rust modules within the src directory:

*   `main.rs`: The entry point of the program. Parses command-line arguments and orchestrates the reading of input files and the checking process.
*   `ltl.rs`: Defines LTL data structures, functions for LTL formula manipulation (reduction, negation), and logic for computing closures and elementary sets.
*   `nba.rs`: Implements Generalized Büchi Automata and Büchi Automata. Contains the logic for converting an LTL formula to a GNBA and for converting a GNBA to an NBA.
*   `ts.rs`: Defines the Transition System data structure and the algorithm for constructing the product of a TS and an NBA.
*   `ndfs.rs`: Implements the Nested DFS algorithm for detecting accepting cycles in the product automaton.
*   `parser.rs`: Contains parsers for LTL formulas and for the input files describing transition systems and LTL tasks.
*   `checker.rs`: Contains the main model checking logic, tying together the components from other modules to verify LTL formulas against transition systems.


See [document.md](document.md) for more implementation details.
