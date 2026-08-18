/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The Caccetta–Häggkvist conjecture

Entry #66 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Caccetta and Häggkvist conjectured that a digraph on `n` vertices in which every vertex has
out-degree at least `k` contains a directed cycle of length at most `⌈n / k⌉`. The case `k = n / 3`,
asking for a directed triangle, is the one usually quoted; the best known constant there is
`0.3465` (Hladký–Kráľ–Norin), still short of `1/3`.

Mathlib's `Digraph` carries no cycle theory, so we work directly with an irreflexive relation and
spell out what a directed cycle is: a `k`-periodic walk that is injective on one period.
-/

@[expose] public section

namespace CaccettaHaggkvist

variable {V : Type*}

/-- `r` has a directed cycle of length exactly `k`: a `k`-periodic sequence of vertices, injective
on a period, each step following an arc of `r`. -/
def HasDirectedCycleOfLength (r : V → V → Prop) (k : ℕ) : Prop :=
  0 < k ∧ ∃ c : ℕ → V,
    (∀ i, r (c i) (c (i + 1))) ∧ (∀ i, c (i + k) = c i) ∧ Set.InjOn c (Set.Iio k)

/-- The directed girth is at most `m`: some directed cycle has length at most `m`. -/
def HasDirectedCycleOfLengthLE (r : V → V → Prop) (m : ℕ) : Prop :=
  ∃ k ≤ m, HasDirectedCycleOfLength r k

open scoped Classical in
/-- The out-degree of `v` under `r`. -/
noncomputable def outDegree [Fintype V] (r : V → V → Prop) (v : V) : ℕ :=
  (Finset.univ.filter fun w => r v w).card

/-! ## Challenges -/

/-- **The Caccetta–Häggkvist conjecture.** Minimum out-degree `k` on `n` vertices forces a directed
cycle of length at most `⌈n / k⌉`. -/
theorem caccetta_haggkvist [Fintype V] (r : V → V → Prop) (hirr : ∀ v, ¬r v v) (k : ℕ)
    (hk : 0 < k) (hdeg : ∀ v, k ≤ outDegree r v) :
    HasDirectedCycleOfLengthLE r ⌈(Fintype.card V : ℚ) / k⌉₊ := by
  sorry

/-- The flagship case: out-degree at least `n / 3` forces a directed triangle. -/
theorem caccetta_haggkvist_triangle [Fintype V] (r : V → V → Prop) (hirr : ∀ v, ¬r v v)
    (hdeg : ∀ v, (Fintype.card V : ℚ) / 3 ≤ outDegree r v) :
    HasDirectedCycleOfLengthLE r 3 := by
  sorry

/-- The Seymour second-neighbourhood conjecture, a close relative: some vertex has at least as many
vertices at distance two as at distance one. It implies the triangle case of Caccetta–Häggkvist. -/
theorem seymour_second_neighbourhood (hfin : Finite V) (r : V → V → Prop) (hirr : ∀ v, ¬r v v)
    (hasym : ∀ u v, r u v → ¬r v u) :
    ∃ v : V, Nat.card {w | r v w} ≤ Nat.card {w | (∃ u, r v u ∧ r u w) ∧ ¬r v w ∧ w ≠ v} := by
  sorry

/-- The `k = 1` case is the easy one and fixes the shape of the statement: out-degree at least one
everywhere forces a directed cycle at all (of length at most `n`). -/
theorem caccetta_haggkvist_one [Fintype V] (r : V → V → Prop) (hirr : ∀ v, ¬r v v)
    (hdeg : ∀ v, 1 ≤ outDegree r v) :
    HasDirectedCycleOfLengthLE r (Fintype.card V) := by
  sorry

/-- The best currently known constant for the triangle case, due to Hladký, Kráľ and Norin:
out-degree at least `0.3465 n` suffices. This is a theorem rather than a conjecture, and the
quantitative target a solution should aim at first. -/
theorem hladky_kral_norin [Fintype V] (r : V → V → Prop) (hirr : ∀ v, ¬r v v)
    (hdeg : ∀ v, (0.3465 : ℚ) * Fintype.card V ≤ outDegree r v) :
    HasDirectedCycleOfLengthLE r 3 := by
  sorry

/-- A digraph with no arcs at all has no directed cycles, so some out-degree hypothesis is
genuinely needed. -/
theorem not_hasDirectedCycle_bot (m : ℕ) :
    ¬HasDirectedCycleOfLengthLE (fun _ _ : V => False) m := by
  sorry

end CaccettaHaggkvist
