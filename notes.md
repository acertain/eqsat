

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
