

# using e-peg inside a smt solver

normal smt solver egraph doesn't share equivalent terms, but we gotta


would be nice to be able to use the same e-peg/egraph for smt & eqsat

smt is harder, because need to backtrack merges & have conflict clauses still make sense

idea for smt is to either:
- sometimes store multiple theory vars per equiv class
  (more than one = merged classes)
or
- one per class & tell the theory solver `a := b` & use a until backtracked
  & make the theory solver deal with it
  (e.g. by setting b's value to a reference to a, or by rewriting domain values in terms of a)
  TODO: think about propagation

complicates theories storing non-backtracked info

TODO: how does conflict analysis work with this?
need to add `a = b` as a premise somehow?
/ whatever caused `a = b` (congruence, transitivity, etc)


theory solver can either register theory vars with us or use TermSet

todo: figure out a safe theory interface (that doesn't expose EquivClass or that makes it impossible to store EquivClass)


# reading list

https://ths.rwth-aachen.de/wp-content/uploads/sites/4/teaching/theses/neuberger_bachelor.pdf (GENERATION OF INFEASIBLE SUBSETS IN LESS-LAZY SMT-SOLVING FOR THE THEORY OF UNINTERPRETED FUNCTIONS)
https://hal.inria.fr/hal-01442691/document (Congruence Closure with Free Variables)
https://link.springer.com/article/10.1007/s10703-017-0283-x (NP-completeness of small conflict set generation for congruence closure
)
https://sci-hub.tw/10.1023/B:JARS.0000009518.26415.49 (Abstract Congruence Closure)
https://arxiv.org/pdf/2004.03082.pdf (egg: Easy, Efficient, and Extensible E-graphs): meh
http://fmv.jku.at/master/Sperl-MasterThesis-2016.pdf (Bit-Vector Rewriting using Union-Find with Offsets)
https://sci-hub.tw/10.1145/3299869.3319880 (Efficient Subgraph Matching: Harmonizing Dynamic Programming, Adaptive Matching Order, and Failing Set Together)
https://homepages.dcc.ufmg.br/~hbarbosa/papers/hosmt_report.pdf (Extending SMT Solvers to Higher-Order Logic (Technical Report))


## smt integration

https://sci-hub.tw/10.1007/978-3-319-94144-8_7 - Chronological backtracking
https://hal.archives-ouvertes.fr/hal-01935591/document https://github.com/witan-org/witan - Centralizing equality reasoning in MCSAT
http://profs.sci.univr.it/~bonacina/talks/FroCoS2019keynoteSpeech-slides.pdf - Conflict-Driven Reasoning in Unions of Theories


