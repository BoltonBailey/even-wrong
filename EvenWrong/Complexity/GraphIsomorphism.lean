/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib
public import EvenWrong.Complexity.Basic

/-!
# Graph isomorphism in polynomial time

Entry #76 of the [open-problem tier list](https://github.com/evand/open-math-problems), listed
there without a Lean statement.

Graph isomorphism is the flagship problem that is neither known to be in `P` nor believed to be
`NP`-complete: it sits in `NP ∩ coAM`, so `NP`-completeness would collapse the polynomial
hierarchy. Babai's 2015 algorithm runs in quasipolynomial time `exp((log n)^{O(1)})`, which is the
best known, and whether the exponent can be brought down to a constant is open.

Graphs are presented by their adjacency matrices, encoded row-major as `n²` bits, so that
membership in the language is a statement about bit strings and the machine model of
`EvenWrong.Complexity.Basic` applies directly.
-/

@[expose] public section

namespace GraphIsomorphism

open Complexity

/-- A graph on `n` vertices, presented by its adjacency matrix. -/
abbrev Graph (n : ℕ) := Fin n → Fin n → Bool

/-- Row-major encoding of an adjacency matrix as `n ^ 2` bits. -/
instance (n : ℕ) : Encoding (Graph n) :=
  ⟨fun G => (List.finRange n).flatMap fun u => (List.finRange n).map fun v => G u v⟩

/-- Encoding of a graph of unspecified size: its vertex count, then its adjacency matrix. -/
instance : Encoding (Σ n : ℕ, Graph n) :=
  ⟨fun G => pair (encode G.1) (encode G.2)⟩

/-- Two graphs on the same vertex set are isomorphic when a permutation of the vertices carries one
adjacency matrix to the other. -/
def IsIsomorphic {n : ℕ} (G H : Graph n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ u v, G u v = H (σ u) (σ v)

/-- The graph isomorphism language: encoded pairs of isomorphic graphs of equal size. -/
def isoLanguage : Language :=
  {x | ∃ (n : ℕ) (G H : Graph n),
    IsIsomorphic G H ∧ x = pair (encode (⟨n, G⟩ : Σ n, Graph n)) (encode (⟨n, H⟩ : Σ n, Graph n))}

/-- The graph automorphism language: encoded graphs with a nontrivial automorphism. It is
polynomial-time equivalent to isomorphism. -/
def autLanguage : Language :=
  {x | ∃ (n : ℕ) (G : Graph n), (∃ σ : Equiv.Perm (Fin n), σ ≠ 1 ∧ ∀ u v, G u v = G (σ u) (σ v)) ∧
    x = encode (⟨n, G⟩ : Σ n, Graph n)}

/-! ## Challenges -/

/-- **Is graph isomorphism in `P`?** -/
theorem inP_isoLanguage : InP isoLanguage := by
  sorry

/-- Graph isomorphism is in `NP`: the witness is the permutation. This is provable and is the
sanity check that the encoding is usable. -/
theorem inNP_isoLanguage : InNP isoLanguage := by
  sorry

/-- Graph isomorphism is *not* expected to be `NP`-complete, since that would collapse the
polynomial hierarchy (Boppana–Håstad–Zachos). This statement is the "even wrong" companion to
`GraphIsomorphism.inP_isoLanguage`: a solution to either would be a major result, and most
researchers expect both to be unprovable at present. -/
theorem not_npComplete_isoLanguage : ¬NPComplete isoLanguage := by
  sorry

/-- Isomorphism and automorphism are polynomial-time equivalent, the classical self-reducibility
argument. -/
theorem polyTimeReducible_aut_iso : PolyTimeReducible autLanguage isoLanguage := by
  sorry

/-- The reverse reduction. -/
theorem polyTimeReducible_iso_aut : PolyTimeReducible isoLanguage autLanguage := by
  sorry

/-- Babai's quasipolynomial algorithm, the state of the art. Stating it needs a runtime bound
finer than "polynomial", so it is phrased as the existence of a machine whose time bound on inputs
of length `m` is `exp((log m) ^ c)`. -/
theorem babai :
    ∃ c : ℕ, ∃ f : Bits → Bits, (∀ x, x ∈ isoLanguage ↔ f x = [true]) ∧
      ∃ M : Cslib.Turing.SingleTapeTM.TimeComputable f,
        ∀ m : ℕ, (M.timeBound m : ℝ) ≤ Real.exp ((Real.log m) ^ c) := by
  sorry

/-- Isomorphism of graphs is an equivalence relation, which the language definition implicitly
assumes. -/
theorem isIsomorphic_equivalence (n : ℕ) : Equivalence (IsIsomorphic (n := n)) := by
  sorry

/-- The adjacency-matrix encoding is injective on graphs of a fixed size, so `isoLanguage` really
is the isomorphism problem and not an artefact of the encoding. -/
theorem encode_graph_injective (n : ℕ) : Function.Injective (encode : Graph n → Bits) := by
  sorry

end GraphIsomorphism
