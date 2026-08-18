/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The cycle double cover and Berge–Fulkerson conjectures

Entry #62 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Szekeres and Seymour conjectured that every bridgeless graph carries a family of cycles covering
each edge exactly twice. Berge and Fulkerson conjectured the matching analogue for cubic graphs:
six perfect matchings covering each edge exactly twice. Both would follow from, and are close
cousins of, Tutte's nowhere-zero flow conjectures; all are open, and all reduce to the case of
snarks.
-/

@[expose] public section

namespace CycleDoubleCover

open SimpleGraph

variable {V : Type*}

/-- A graph is *bridgeless* when no single edge disconnects it. Bridgeless-ness is necessary:
a bridge lies on no cycle at all, so it can never be covered twice. -/
def Bridgeless (G : SimpleGraph V) : Prop :=
  ∀ e ∈ G.edgeSet, ¬G.IsBridge e

/-- A *closed walk family*: a multiset of closed walks in `G`, packaged with their basepoints. -/
abbrev CycleFamily (G : SimpleGraph V) : Type _ :=
  Multiset (Σ v : V, G.Walk v v)

open scoped Classical in
/-- The number of times an edge is used by a family of closed walks. -/
noncomputable def multiplicity (G : SimpleGraph V) (C : CycleFamily G) (e : Sym2 V) : ℕ :=
  (C.map fun c => c.2.edges.count e).sum

open scoped Classical in
/-- `C` is a *cycle double cover* of `G`: every member is a cycle, and every edge of `G` is used
by exactly two of them. -/
def IsCycleDoubleCover (G : SimpleGraph V) (C : CycleFamily G) : Prop :=
  (∀ c ∈ C, c.2.IsCycle) ∧ ∀ e ∈ G.edgeSet, multiplicity G C e = 2

/-! ## Challenges -/

/-- **The cycle double cover conjecture** (Szekeres, Seymour). -/
theorem cycle_double_cover (hfin : Finite V) (G : SimpleGraph V) (h : Bridgeless G) :
    ∃ C : CycleFamily G, IsCycleDoubleCover G C := by
  sorry

/-- Bridgelessness is necessary: a graph with a bridge admits no cycle double cover. This is the
provable half, and pins down the hypothesis. -/
theorem not_isCycleDoubleCover_of_isBridge (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hbr : G.IsBridge e) (C : CycleFamily G) : ¬IsCycleDoubleCover G C := by
  sorry

/-- The *strong* cycle double cover conjecture (Goddyn): the cover can be chosen to contain any
prescribed cycle. -/
theorem strong_cycle_double_cover (hfin : Finite V) (G : SimpleGraph V) (h : Bridgeless G)
    {v : V} (c₀ : G.Walk v v) (hc₀ : c₀.IsCycle) :
    ∃ C : CycleFamily G, IsCycleDoubleCover G C ∧ (⟨v, c₀⟩ : Σ v : V, G.Walk v v) ∈ C := by
  sorry

open scoped Classical in
/-- **The Berge–Fulkerson conjecture.** Every bridgeless cubic graph has six perfect matchings
covering each edge exactly twice. -/
theorem berge_fulkerson [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hbr : Bridgeless G) :
    ∃ M : Fin 6 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e ∈ G.edgeSet, (Finset.univ.filter fun i => e ∈ (M i).edgeSet).card = 2 := by
  sorry

open scoped Classical in
/-- The Fan–Raspaud weakening of Berge–Fulkerson: three perfect matchings with empty common
intersection. Even this is open. -/
theorem fan_raspaud [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : G.IsRegularOfDegree 3) (hbr : Bridgeless G) :
    ∃ M : Fin 3 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
      ∀ e ∈ G.edgeSet, ∃ i, e ∉ (M i).edgeSet := by
  sorry

/-- Berge–Fulkerson implies the cycle double cover conjecture for cubic graphs: the complements of
the six matchings, taken in pairs, give the required cycles. -/
theorem cdc_of_berge_fulkerson
    (hbf : ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → Bridgeless G →
        ∃ M : Fin 6 → G.Subgraph, (∀ i, (M i).IsPerfectMatching) ∧
          ∀ e ∈ G.edgeSet, Nat.card {i | e ∈ (M i).edgeSet} = 2) :
    ∀ (V : Type) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
      G.IsRegularOfDegree 3 → Bridgeless G →
        ∃ C : CycleFamily G, IsCycleDoubleCover G C := by
  sorry

end CycleDoubleCover
