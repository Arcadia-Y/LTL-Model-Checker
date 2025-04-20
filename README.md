# LTL-Checker

This is a Linear Temporal Logic (LTL) model checker. More specifically, given a transition system (TS) and an LTL formula, it can check whether the TS (or an arbitrary state of the TS) satisfies the formula.

See [this document](Input_Format.pdf) for input format.

## Workflow Overview
Our overall workflow is as follows: We first parse input to get the transition system $TS$ and LTL formulas. Then for each formula $\varphi$, we
- construct $\neg \varphi$ and transform it into the reduced form
- construct its elementary set
- construct a GNBA for $\neg \varphi$
- transform the GNBA into an NBA $\mathcal{A}$
- construct $TS \otimes \mathcal{A}$
- run the nested DFS on $TS \otimes \mathcal{A}$ to check whether $TS \models \varphi$
