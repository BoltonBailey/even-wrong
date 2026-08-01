/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
-- NOTE: unlike the rest of this repository, this file is deliberately *not* a `module`.
-- It depends on `VCVio`, which has not been converted to the module system, and Lean
-- forbids a `module` from importing a non-`module`. Consequently `EvenWrong.lean` cannot
-- import this file either; it is built by its own `EvenWrongProbEval` target in the
-- lakefile. Re-modulize this file once VCVio is modulized upstream.

import Mathlib
import VCVio.OracleComp.ProbComp
import EvenWrong.Games.Minesweeper

/-!

# Probabilistically evaluables

This file contains the definition for a monad-like type transformation `ProbEval`
which encapsulates probabilistic computations (defined using VCVio's `ProbComp`)
that return the same value more than half of the time.

Note: We could actually maybe do *any ProbComp with a gap from the highest probability to the
second highest probability*. Because we can then just sample enough that we identify the top
values and the gaps.

The concept of this structure
is that it's useful as an encapsulation for actions that arise in probabilistic tests.

Here are some examples of uses of this structure:

* The Miller-Rabin test can be written as a `ℕ → ProbComp Bool`
  that returns `true` if the number is probably prime and `false` if it is composite
  with soundness bound 75%.
* The Schwartz-Zippel test can be written as a `Polynomial → Polynomial → ProbComp Bool`
  that returns `true` if the two polynomials are probably equal and `false` if they are not.
* A `ProbComp Cell` could be written that returns the best cell to reveal in a minesweeper board,
  by statistically upper or lower bounding the equity of each other cell.

-/

/--
Probabilistic evaluables
-/
structure ProbEval (α : Type) where
  /-- The value associated with the evaluation
  (TODO: should this be included, or does this ruin the computational properties) -/
  val : α
  /-- A probabilistic computation we can run to obtain val -/
  comp : ProbComp α
  /-- A bound on the probability of correct evalaution -/
  bound_correct : NNRat
  /-- The bound must be at least 1/2 to guarantee ability to boost -/
  bound_correct_le : 1/2 < bound_correct
  /-- The soundness condition:
  the probability that `comp` does not return `val` is at most `bound`. -/
  soundness : bound_correct ≤ Pr[= val | comp]


/--
A probabilistic computation that involves repeating a
ProbEval some number of times and taking the plurality value.

This allows us to produce a new ProbEval with a much smaller error bound.
-/
def ProbEval.repeat {α} (p : ProbEval α) (repetitions : Nat) : ProbComp α :=
  sorry

/--
A probabilistic computation that involves repeating a
ProbEval some number of times and taking the plurality value.

We choose the number of repetitions to guarantee that the error bound is reduced to the given bound.

This allows us to produce a new ProbEval with a much smaller error bound.
-/
def ProbEval.boost {α} (p : ProbEval α) (bound : NNRat) : ProbComp α :=
  sorry

/--
The pure constructor for ProbEval, which just returns a fixed value with probability 1.
-/
def ProbEval.pure {α} (x : α) : ProbEval α := sorry

/--
The bind constructor for ProbEval, which composes two ProbEvals together.

Note that this is **not** constructed using the monadic bind of `ProbComp`,
because then the soundness would be the product of the individual soundness bounds,
which is not good enough to guarantee that the result is above 1/2.

Instead, we must first boost the ProbEvals before composing.

Note that unfortunately, this seems to mean that monad laws won't hold.

Can we fix this somehow?

On another level,
really what we want to do is do the whole computation
and then best decide how to boost parts of it

(perhaps by making a soundness budget that parts of the computation
for example,
we could let the first call take 1/2 the budget,
then the next 2 calls take the next 1/4, then the next 4 cals take 1/8, etc.
so that we can guarantee the final soundness is at most the given bound
and amortized each call takes about the polynomial buudget fraction in the number of calls.
)
-/
def ProbEval.bind {α β} (p : ProbEval α) (f : α → ProbEval β) : ProbEval β :=
  sorry

/-! ## The examples from the module docstring

Each of the three examples above is stated below as a challenge: the `ProbEval` itself is the
object to be constructed, and the accompanying theorems pin down *which* value it evaluates to
(its `val`) and *how good* its soundness bound is (its `bound_correct`). The `soundness` field of
`ProbEval` already carries the probabilistic content, so no separate probability statement is
needed.
-/

/-! ### Miller-Rabin primality testing -/

/--
A single round of the Miller-Rabin test on `n`, as a probabilistic evaluable.

Miller-Rabin never rejects a prime, and rejects a composite with probability at least `3/4`, so
one round already clears the `1/2` threshold that `ProbEval` demands.
-/
def millerRabin (n : ℕ) : ProbEval Bool :=
  sorry

/-- Miller-Rabin evaluates to `true` on exactly the primes. -/
theorem millerRabin_val_eq_true_iff (n : ℕ) :
    (millerRabin n).val = true ↔ n.Prime :=
  sorry

/-- A single round of Miller-Rabin achieves soundness bound `3/4`. -/
theorem millerRabin_bound_correct (n : ℕ) :
    (millerRabin n).bound_correct = 3 / 4 :=
  sorry

/-! ### Schwartz-Zippel polynomial identity testing -/

section SchwartzZippel

variable {R : Type} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ}

/--
Polynomial identity testing for `p` and `q` by the Schwartz-Zippel lemma, as a probabilistic
evaluable: evaluate `p - q` at a point drawn uniformly from `S ^ n` and report whether the
results agree.

The statement is for multivariate polynomials, which is where Schwartz-Zippel has content; the
univariate case is `n = 1`. By `MvPolynomial.schwartz_zippel_totalDegree`, a nonzero difference of
total degree at most `d` vanishes at such a point with probability at most `d / #S`, so the
hypothesis `2 * d < #S` is exactly what pushes the soundness bound above `1/2`.
-/
def schwartzZippel (p q : MvPolynomial (Fin n) R) (S : Finset R) (d : ℕ)
    (hd : (p - q).totalDegree ≤ d) (hS : 2 * d < S.card) : ProbEval Bool :=
  sorry

/-- The Schwartz-Zippel test evaluates to `true` exactly when the two polynomials are equal. -/
theorem schwartzZippel_val_eq_true_iff (p q : MvPolynomial (Fin n) R) (S : Finset R) (d : ℕ)
    (hd : (p - q).totalDegree ≤ d) (hS : 2 * d < S.card) :
    (schwartzZippel p q S d hd hS).val = true ↔ p = q :=
  sorry

/-- The Schwartz-Zippel test achieves the soundness bound supplied by the Schwartz-Zippel lemma. -/
theorem schwartzZippel_bound_correct (p q : MvPolynomial (Fin n) R) (S : Finset R) (d : ℕ)
    (hd : (p - q).totalDegree ≤ d) (hS : 2 * d < S.card) :
    (schwartzZippel p q S d hd hS).bound_correct = 1 - (d : ℚ≥0) / (S.card : ℚ≥0) :=
  sorry

end SchwartzZippel

/-! ### Minesweeper: choosing the best cell to open -/

section Minesweeper

open Minesweeper

variable {h w : ℕ}

/--
A statistical minesweeper solver, as a probabilistic evaluable: it returns a cell that is optimal
to open, found by bounding the equity of each candidate cell from above and below by sampling
rather than by computing `Board.openingEquity` exactly.
-/
def bestOpening (board : Board h w) : ProbEval (Fin h × Fin w) :=
  sorry

/-- The cell returned is one that can actually be opened. -/
theorem bestOpening_val_mem (board : Board h w) (hb : board.unrevealedCells ≠ []) :
    (bestOpening board).val ∈ board.unrevealedCells :=
  sorry

/-- The cell returned maximises the expected equity over all cells that can be opened. -/
theorem openingEquity_le_bestOpening (board : Board h w) (hb : board.unrevealedCells ≠ [])
    (c : Fin h × Fin w) (hc : c ∈ board.unrevealedCells) :
    board.openingEquity c.1 c.2 ≤
      board.openingEquity (bestOpening board).val.1 (bestOpening board).val.2 :=
  sorry

end Minesweeper
