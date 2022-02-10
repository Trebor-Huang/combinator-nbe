# Normalization by Evaluation, for combinators

- `combinator.agda` defines the basic concepts. We work in a language
with the combinators `𝕂` `𝕊`, and the natural numbers `O` `S`, together
with a recursion combinator `ℝ`.
- `reduce.agda` describes how to reduce combinators with reductions,
basically a big-step semantics. Note that we have to add the Agda pragma
`{-# TERMINATING #-}`, because it's not obvious that such a reduction
terminates.
- `nbe.agda` uses normalization by evaluation. Apart from being slightly faster
(I cannot measure accurately, but it seems to be around 2x faster), it also
convinces Agda that the process terminates.

- `nbe.py` gives a quick implementation in python, stripped of all the
proofs. It is basically just 10 lines!

# Normalization by Evaluation, for simply typed lambda calculus

I eventually got around to implement NbE for STLC. Please note that
since I'm working on a case-insensitive filesystem, you might need to
adjust the file cases according to this Readme.

- `Equivalence.agda` defines handy tools.
- `STLC.agda` defines simply typed lambda calculus, demonstrates how to
translate it into combinators, and defines relevant basic concepts.
- `Substitution.agda` proves various substitution lemmas.
- `NbE.agda` implements normalization by evaluation.

--------

The files have plenty of comments, and are intended to be read in
the order as listed.
