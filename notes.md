
# reading list

https://ths.rwth-aachen.de/wp-content/uploads/sites/4/teaching/theses/neuberger_bachelor.pdf (GENERATION OF INFEASIBLE SUBSETS IN LESS-LAZY SMT-SOLVING FOR THE THEORY OF UNINTERPRETED FUNCTIONS)
https://hal.inria.fr/hal-01442691/document (Congruence Closure with Free Variables)
https://link.springer.com/article/10.1007/s10703-017-0283-x (NP-completeness of small conflict set generation for congruence closure
)
https://sci-hub.tw/10.1023/B:JARS.0000009518.26415.49 (Abstract Congruence Closure)
http://fmv.jku.at/master/Sperl-MasterThesis-2016.pdf (Bit-Vector Rewriting using Union-Find with Offsets)
https://sci-hub.tw/10.1145/3299869.3319880 (Efficient Subgraph Matching: Harmonizing Dynamic Programming, Adaptive Matching Order, and Failing Set Together)
https://homepages.dcc.ufmg.br/~hbarbosa/papers/hosmt_report.pdf (Extending SMT Solvers to Higher-Order Logic (Technical Report))
http://leodemoura.github.io/files/ematching.pdf

## read

https://arxiv.org/pdf/2004.03082.pdf (egg: Easy, Efficient, and Extensible E-graphs): nothing useful

## smt integration

https://sci-hub.tw/10.1007/978-3-319-94144-8_7 - Chronological backtracking
https://hal.archives-ouvertes.fr/hal-01935591/document https://github.com/witan-org/witan - Centralizing equality reasoning in MCSAT
http://profs.sci.univr.it/~bonacina/talks/FroCoS2019keynoteSpeech-slides.pdf - Conflict-Driven Reasoning in Unions of Theories

# TODO


- delayed merges
- normalization:
  e.g. normalize `a = b` by choosing which goes on which side (order a & b?)
  or alternatively could also check for `b = a` in find?
- shostak
- AC

detect (on merges?):
- injective fns, check if a contains same head fn
  `f(x) = f(y) => x = y`
  - other fundeps?
- x = equality that's false, check for propagating like `f(a) != f(b) => a != b`
  - make new term for `a != b`? or could check if it already exists i guess? but idk, hard to propagate if created in the future
  - maybe need to sort/index members for this one? need to check if same symbol is in both children of bp
  - or just do dynamic ackermannization?
- disjointness of constructors (or store a Maybe Term per equiv class for if it's known to be a constructor?)


