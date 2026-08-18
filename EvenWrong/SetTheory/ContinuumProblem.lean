/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The continuum problem

Entry #71 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Hilbert's first problem. Gödel and Cohen showed that the continuum hypothesis is independent of
ZFC, so neither it nor its negation is provable — which makes this module an unusually pure
instance of what `EvenWrong` is for. Both `ContinuumProblem.continuum_hypothesis` and
`ContinuumProblem.not_continuum_hypothesis` are well-formed Lean statements, and *neither* can ever
receive a solution in `NotWrong`. The live mathematical question is not the binary one but which
additional axioms (Woodin's Ω-logic, forcing axioms, `V = Ultimate L`) should settle it, and
those are statements about models rather than statements of Lean's own set theory.

Lean's `Cardinal` lives in a fixed universe, so `CH` here is the statement for `Type 0` cardinals.
-/

@[expose] public section

namespace ContinuumProblem

open Cardinal

/-- The continuum hypothesis: there is no cardinal strictly between `ℵ₀` and `𝔠`. -/
def CH : Prop :=
  ∀ c : Cardinal.{0}, ℵ₀ ≤ c → c < 𝔠 → c = ℵ₀

/-- The generalised continuum hypothesis: for every infinite cardinal, nothing sits strictly
between it and its power. -/
def GCH : Prop :=
  ∀ a c : Cardinal.{0}, ℵ₀ ≤ a → a < c → c < 2 ^ a → False

/-! ## Challenges

Both of the first two statements are unprovable, and a solution to either would be a
soundness bug rather than a mathematical result. They are recorded because the `EvenWrong`
convention is that a statement earns its place by being well-formed, not by being provable.
-/

/-- **The continuum hypothesis.** Unprovable in ZFC (Cohen). -/
theorem continuum_hypothesis : CH := by
  sorry

/-- **The negation of the continuum hypothesis.** Also unprovable in ZFC (Gödel). -/
theorem not_continuum_hypothesis : ¬CH := by
  sorry

/-- The generalised continuum hypothesis implies the continuum hypothesis. Unlike the two
statements above, this one *is* provable, and is the real challenge on this page. -/
theorem ch_of_gch (h : GCH) : CH := by
  sorry

/-- Cantor's theorem, the one part of the continuum problem that is settled: `𝔠` is strictly
larger than `ℵ₀`, so the question is about what lies between rather than whether they differ. -/
theorem aleph0_lt_continuum : ℵ₀ < 𝔠 := by
  sorry

/-- `𝔠` is `2 ^ ℵ₀`, the identification that makes `CH` a statement about the power set of `ℕ`. -/
theorem continuum_eq_two_pow : 𝔠 = 2 ^ ℵ₀ := by
  sorry

/-- König's theorem gives the one nontrivial ZFC constraint on the value of `𝔠`: its cofinality is
uncountable, so `𝔠 ≠ ℵ_ω`. Every other value consistent with monotonicity is consistent
(Easton), which is the precise sense in which ZFC says almost nothing here. -/
theorem aleph0_lt_cof_continuum : ℵ₀ < (𝔠 : Cardinal.{0}).ord.cof := by
  sorry

end ContinuumProblem
