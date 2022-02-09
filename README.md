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

There's also a folder with the complete beta-eta normalization for simply
typed lambda calculus. However since my filesystem is case insensitive, you
may need to adjust some of the filenames.
