/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# Hadwiger's conjecture

Entry #57 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Hadwiger's conjecture is the far-reaching generalisation of the four colour theorem: a graph with
no `K_{t+1}` minor is `t`-colourable. The cases `t ≤ 3` are classical, `t = 4` is equivalent to the
four colour theorem (Wagner), `t = 5` was proved by Robertson–Seymour–Thomas modulo the four colour
theorem, and every `t ≥ 6` is open.

Mathlib has no theory of graph minors, so we define the one notion we need — a complete minor via
branch sets — from scratch.
-/

@[expose] public section

namespace Hadwiger

open SimpleGraph

variable {V : Type*}

/-- `G` has a `K t` *minor* when there are `t` pairwise disjoint, nonempty, connected vertex sets
(the *branch sets*), any two of which are joined by an edge of `G`. Contracting each branch set to
a single vertex produces a complete graph on `t` vertices. -/
def HasCompleteMinor (G : SimpleGraph V) (t : ℕ) : Prop :=
  ∃ B : Fin t → Set V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i, (G.induce (B i)).Connected) ∧
    (Pairwise fun i j => Disjoint (B i) (B j)) ∧
    (∀ i j, i ≠ j → ∃ u ∈ B i, ∃ v ∈ B j, G.Adj u v)

/-- The *Hadwiger number* of `G`: the largest `t` for which `G` has a `K t` minor. -/
noncomputable def hadwigerNumber (G : SimpleGraph V) : ℕ∞ :=
  ⨆ t ∈ {t : ℕ | HasCompleteMinor G t}, (t : ℕ∞)

/-! ## Challenges -/

/-- **Hadwiger's conjecture.** A graph with no `K_{t+1}` minor is `t`-colourable. -/
theorem hadwiger (G : SimpleGraph V) (t : ℕ) (h : ¬HasCompleteMinor G (t + 1)) :
    G.chromaticNumber ≤ t := by
  sorry

/-- The equivalent "chromatic number is at most the Hadwiger number" phrasing. -/
theorem chromaticNumber_le_hadwigerNumber (G : SimpleGraph V) :
    G.chromaticNumber ≤ hadwigerNumber G := by
  sorry

/-- The trivial direction, and the sanity check for the definition: a `K t` minor forces at least
`t` colours. Unlike the conjecture itself this is provable. -/
theorem le_chromaticNumber_of_hasCompleteMinor (G : SimpleGraph V) (t : ℕ)
    (h : HasCompleteMinor G t) : (t : ℕ∞) ≤ G.chromaticNumber := by
  sorry

/-- The case `t = 4`: Wagner showed this is equivalent to the four colour theorem. -/
theorem hadwiger_four (G : SimpleGraph V) (h : ¬HasCompleteMinor G 5) :
    G.chromaticNumber ≤ 4 := by
  sorry

/-- The case `t = 6`, the first case that neither follows from the four colour theorem nor from
the Robertson–Seymour–Thomas argument, and hence the first genuinely open one. -/
theorem hadwiger_six (G : SimpleGraph V) (h : ¬HasCompleteMinor G 7) :
    G.chromaticNumber ≤ 6 := by
  sorry

/-- The *linear Hadwiger* relaxation: even a bound of the form `C * t` on the chromatic number of
graphs with no `K_{t+1}` minor is open. The best known bounds are `O(t log log t)`
(Delcourt–Postle), improving the classical `O(t √(log t))` of Kostochka and Thomason. -/
theorem hadwiger_linear :
    ∃ C : ℝ, ∀ (V : Type) (G : SimpleGraph V) (t : ℕ),
      ¬HasCompleteMinor G (t + 1) → G.chromaticNumber ≤ (⌈C * t⌉₊ : ℕ∞) := by
  sorry

/-- The case `t = 5` (Robertson–Seymour–Thomas), the last case that is a theorem. Their proof is
conditional on the four colour theorem, so a Lean proof would have to go through it. -/
theorem hadwiger_five (G : SimpleGraph V) (h : ¬HasCompleteMinor G 6) :
    G.chromaticNumber ≤ 5 := by
  sorry

/-- The case `t = 2`: a graph with no `K₃` minor is a forest, hence `2`-colourable. This is the
easy end of the conjecture and a good test that the definition of `HasCompleteMinor` is right. -/
theorem hadwiger_two (G : SimpleGraph V) (h : ¬HasCompleteMinor G 3) :
    G.chromaticNumber ≤ 2 := by
  sorry

end Hadwiger
