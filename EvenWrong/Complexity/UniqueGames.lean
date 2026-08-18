/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib
public import EvenWrong.Complexity.Basic

/-!
# The Unique Games Conjecture

Entry #73 of the [open-problem tier list](https://github.com/evand/open-math-problems), listed
there without a Lean statement.

A unique game is a constraint satisfaction problem in which every constraint is a bijection between
the label sets of its two endpoints, so an assignment to one endpoint determines the other.
Khot conjectured that distinguishing near-satisfiable instances from badly unsatisfiable ones is
`NP`-hard. If true it pins down the exact approximability of Max-Cut, Vertex Cover and every
constraint satisfaction problem at once, via Raghavendra's theorem.
The related 2-to-2 games conjecture was proved by Khot–Minzer–Safra in 2018, which is the strongest
evidence in favour; the conjecture itself is open.

Instances are finite objects, so they carry a bit-string encoding and the reduction in the
statement is a `PolyTimeMap` in the sense of `EvenWrong.Complexity.Basic`.
-/

@[expose] public section

namespace UniqueGames

open Complexity

variable {n k : ℕ}

/-- A unique game with `n` variables and label set `Fin k`: for each ordered pair of variables,
either no constraint or a bijection of the labels that the assignment must respect. -/
structure Instance (n k : ℕ) where
  /-- The constraint on an ordered pair of variables, if any. -/
  constraint : Fin n → Fin n → Option (Equiv.Perm (Fin k))

/-- A permutation of the label set encodes as the list of its values. -/
instance (k : ℕ) : Encoding (Equiv.Perm (Fin k)) :=
  ⟨fun π => ((List.finRange k).map fun i => selfDelimit (encode (π i))).flatten⟩

/-- An instance encodes as its table of constraints. -/
instance (n k : ℕ) : Encoding (Instance n k) :=
  ⟨fun I => ((List.finRange n).flatMap fun u =>
    (List.finRange n).map fun v => selfDelimit (encode (I.constraint u v))).flatten⟩

/-- Instances of arbitrary size with a fixed label set, the target type of the reduction. -/
def Instances (k : ℕ) : Type :=
  Σ n : ℕ, Instance n k

instance (k : ℕ) : Encoding (Instances k) :=
  ⟨fun I => pair (encode I.1) (encode I.2)⟩

open scoped Classical in
/-- The constraints actually present in an instance. -/
noncomputable def constraints (I : Instance n k) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun p => (I.constraint p.1 p.2).isSome

open scoped Classical in
/-- The constraints satisfied by an assignment. -/
noncomputable def satisfied (I : Instance n k) (A : Fin n → Fin k) : Finset (Fin n × Fin n) :=
  (constraints I).filter fun p => ∃ π, I.constraint p.1 p.2 = some π ∧ A p.2 = π (A p.1)

/-- The *value* of an instance: the largest fraction of constraints any assignment satisfies. -/
noncomputable def value (I : Instance n k) : ℝ :=
  ⨆ A : Fin n → Fin k, ((satisfied I A).card : ℝ) / (constraints I).card

/-! ## Challenges -/

/-- **The Unique Games Conjecture.** For every gap `(1 - ε, δ)` there is a label set size `k` such
that every `NP` language reduces, in polynomial time, to distinguishing unique games of value at
least `1 - ε` from those of value at most `δ`. -/
theorem unique_games (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ L : Language, InNP L →
      ∃ F : Bits → Instances k, PolyTimeMap F ∧
        ∀ x : Bits, (x ∈ L → 1 - ε ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ) := by
  sorry

/-- The conjecture is widely doubted as well as widely used; this is its "even wrong" companion.
A refutation would most likely take the form of a subexponential algorithm strong enough to rule
out the reduction, in the spirit of Arora–Barak–Steurer. -/
theorem not_unique_games :
    ¬∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ k : ℕ, ∀ L : Language, InNP L →
      ∃ F : Bits → Instances k, PolyTimeMap F ∧
        ∀ x : Bits, (x ∈ L → 1 - ε ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ) := by
  sorry

/-- Exactly satisfiable unique games are easy: propagating labels along constraints decides
satisfiability in polynomial time. This is why the conjecture must be about the *gap* version, and
it is a provable statement that pins the definitions down. -/
theorem decidable_perfect_completeness :
    PolyTimeDecidable fun I : Instances 2 => value I.2 = 1 := by
  sorry

/-- The value of an instance lies in `[0, 1]`. -/
theorem value_mem_Icc (I : Instance n k) (h : (constraints I).Nonempty) :
    value I ∈ Set.Icc (0 : ℝ) 1 := by
  sorry

/-- With a single label everything is satisfiable, so the conjecture is vacuous for `k = 1`: the
label set must grow as the gap sharpens. -/
theorem value_eq_one_of_one_label (I : Instance n 1) (h : (constraints I).Nonempty) :
    value I = 1 := by
  sorry

/-- Khot–Minzer–Safra proved the 2-to-2 games conjecture, which gives the unique games gap with
imperfect completeness `1/2` rather than `1 - ε`. This is the strongest evidence for the
conjecture, and the natural formalisation target on this page. -/
theorem khot_minzer_safra (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, ∀ L : Language, InNP L →
      ∃ F : Bits → Instances k, PolyTimeMap F ∧
        ∀ x : Bits, (x ∈ L → 1 / 2 ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ) := by
  sorry

/-- Monotonicity in the label set: a gap reduction with label set `Fin k` gives one with any
larger label set, by padding the permutations with fixed points. This is provable, and it is what
makes "there exists `k`" the right quantifier in the conjecture. -/
theorem unique_games_mono (ε δ : ℝ) (k k' : ℕ) (hkk : k ≤ k') (L : Language) (hL : InNP L)
    (h : ∃ F : Bits → Instances k, PolyTimeMap F ∧
      ∀ x : Bits, (x ∈ L → 1 - ε ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ)) :
    ∃ F : Bits → Instances k', PolyTimeMap F ∧
      ∀ x : Bits, (x ∈ L → 1 - ε ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ) := by
  sorry

/-- The gap is vacuous when the two thresholds cross: for `1 - ε ≤ δ` the distinguishing problem is
trivial, so the conjecture has content only in the range where `δ < 1 - ε`. -/
theorem unique_games_trivial_of_le (ε δ : ℝ) (hεδ : 1 - ε ≤ δ) (k : ℕ) (L : Language)
    (hL : InP L) :
    ∃ F : Bits → Instances k, PolyTimeMap F ∧
      ∀ x : Bits, (x ∈ L → 1 - ε ≤ value (F x).2) ∧ (x ∉ L → value (F x).2 ≤ δ) := by
  sorry

end UniqueGames
