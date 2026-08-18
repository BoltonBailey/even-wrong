/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The reconstruction conjecture

Entry #61 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Kelly and Ulam conjectured that a finite graph on at least three vertices is determined, up to
isomorphism, by its multiset of one-vertex-deleted subgraphs (its *deck*). Verified for all graphs
on at most eleven vertices and for many classes (trees, disconnected graphs, regular graphs), it is
open in general. Harary's *edge* reconstruction conjecture is the analogue for edge-deleted
subgraphs, and is known for graphs with more than `n log₂ n` edges (Müller).

The deck is a multiset, so a hypomorphism is stated as a vertex bijection together with, for each
vertex, an isomorphism of the corresponding deleted subgraphs.
-/

@[expose] public section

namespace Reconstruction

open SimpleGraph

variable {V W : Type*}

/-- `G` and `H` are *hypomorphic* when there is a bijection of their vertices matching up the
vertex-deleted subgraphs: deleting `v` from `G` gives the same graph as deleting `σ v` from `H`.
This is exactly the statement that `G` and `H` have the same deck. -/
def IsHypomorphic (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∃ σ : V ≃ W, ∀ v : V, Nonempty (G.induce {v}ᶜ ≃g H.induce {σ v}ᶜ)

/-- `G` and `H` are *edge hypomorphic* when there is a bijection of their edge sets matching up
the edge-deleted subgraphs. -/
def IsEdgeHypomorphic (G H : SimpleGraph V) : Prop :=
  ∃ σ : G.edgeSet ≃ H.edgeSet,
    ∀ e : G.edgeSet, Nonempty (G.deleteEdges {(e : Sym2 V)} ≃g H.deleteEdges {(σ e : Sym2 V)})

/-! ## Challenges -/

/-- **The reconstruction conjecture** (Kelly–Ulam). Finite graphs on at least three vertices are
determined by their decks. -/
theorem reconstruction [Fintype V] (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (h : IsHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/-- **The edge reconstruction conjecture** (Harary). Finite graphs with at least four edges are
determined by their edge decks. -/
theorem edge_reconstruction {G H : SimpleGraph V}
    (hE : 4 ≤ Nat.card G.edgeSet) (h : IsEdgeHypomorphic G H) : Nonempty (G ≃g H) := by
  sorry

/-- On two vertices reconstruction *fails*: `K₂` and its complement have the same deck (two
isolated vertices), which is why the hypothesis `3 ≤ card V` cannot be dropped. This is the
counterexample that fixes the shape of the conjecture. -/
theorem not_reconstruction_two :
    ∃ G H : SimpleGraph (Fin 2), IsHypomorphic G H ∧ IsEmpty (G ≃g H) := by
  sorry

/-- Kelly's lemma, the basic tool: the number of copies of any graph strictly smaller than `G` is
reconstructible from the deck. This is a theorem, and the natural first target. -/
theorem kelly_lemma (G : SimpleGraph V) (H : SimpleGraph W) (h : IsHypomorphic G H)
    (F : SimpleGraph (Fin 3)) :
    Nat.card {s : Finset V // Nonempty (F ≃g G.induce (s : Set V))} =
      Nat.card {s : Finset W // Nonempty (F ≃g H.induce (s : Set W))} := by
  sorry

/-- Disconnected graphs are reconstructible (Kelly). Along with trees this is the best-known
special case. -/
theorem reconstruction_of_disconnected [Fintype V] (hV : 3 ≤ Fintype.card V)
    (G : SimpleGraph V) (H : SimpleGraph W) (h : IsHypomorphic G H) (hG : ¬G.Connected) :
    Nonempty (G ≃g H) := by
  sorry

/-- Edge reconstruction implies vertex reconstruction is *not* known; the two conjectures are
related the other way round, by Greenwell's theorem: reconstruction implies edge reconstruction
for graphs with at least four edges. -/
theorem edge_reconstruction_of_reconstruction
    (hrec : ∀ (V W : Type) (_ : Fintype V), 3 ≤ Fintype.card V →
      ∀ (G : SimpleGraph V) (H : SimpleGraph W), IsHypomorphic G H → Nonempty (G ≃g H)) :
    ∀ (V : Type) (_ : Fintype V) (G H : SimpleGraph V), 4 ≤ Nat.card G.edgeSet →
      IsEdgeHypomorphic G H → Nonempty (G ≃g H) := by
  sorry

end Reconstruction
