
/-
# TODO

Add cslib to deps

It looks like mathlib has recently [deprecated FinEncoding](https://github.com/leanprover-community/mathlib4/blob/9ef14c7b82f8a45f8dfc03dace26d6bb25023bac/Mathlib/Computability/Encoding.lean#L211-L214) / changed Encoding to unbundle the alphabet.

I'm not sure I agree with this change, but I also am not sure I like how it was before - I think it would have made more sense to make FinEncoding be a `class`. This would have made it possible to write conjectures like "Integer Factorization is in P" succinctly as something like `IsPolytime PNat.factorMultiset`.

Maybe this is a good opportunity to remake this?

We would also probably want to have a way of making TMs with different output/input alphabets, so this might have to wait on more development on that side.
-/
