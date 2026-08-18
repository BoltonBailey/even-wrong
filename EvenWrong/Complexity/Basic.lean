/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib
public import Cslib.Computability.Machines.Turing.SingleTape.Deterministic

/-!
# Scaffolding for complexity-theoretic challenges

Several entries on the [open-problem tier list](https://github.com/evand/open-math-problems) are
statements about polynomial-time computation. This module fixes a single machine model for all of
them, so that the individual challenge files state mathematics rather than re-litigate the model.

The model is `cslib`'s single-tape deterministic Turing machine over the alphabet `Bool`, together
with `Cslib.Turing.SingleTapeTM.PolyTimeComputable`. On top of it we define:

* `Encoding`, a class of concrete bit-string encodings, so that challenges may talk about
  polynomial-time maps between structured types rather than only between bit strings;
* `InP` and `InNP`, the two complexity classes needed downstream — `NP` through the verifier
  characterisation, which avoids committing to a nondeterministic machine model;
* `PolyTimeReducible`, `NPHard` and `NPComplete`;
* `Negligible`, for the cryptographic statements.

Nothing here is itself an open problem; it is the shared vocabulary for
`EvenWrong.Complexity.OneWayFunctions`, `EvenWrong.Complexity.GraphIsomorphism` and
`EvenWrong.Complexity.UniqueGames`.
-/

@[expose] public section

namespace Complexity

open Cslib.Turing

/-- Bit strings, the universal input type. -/
abbrev Bits := List Bool

/-- A *language* is a set of bit strings. -/
abbrev Language := Set Bits

/-! ## Encodings -/

/-- A concrete bit-string encoding of a type. Encodings are data, not a property: two different
encodings of the same type give literally different languages, and complexity statements are only
meaningful relative to a fixed one. -/
class Encoding (α : Type*) where
  /-- The encoding function. -/
  encode : α → Bits

export Encoding (encode)

/-- Self-delimiting form of a bit string: double every bit, then append the marker `10`, which
cannot occur at an even offset inside the doubled part. -/
def selfDelimit (x : Bits) : Bits :=
  x.flatMap (fun b => [b, b]) ++ [true, false]

/-- Pairing of bit strings: a self-delimiting copy of the first followed by the second. -/
def pair (x y : Bits) : Bits :=
  selfDelimit x ++ y

instance : Encoding Bool := ⟨fun b => [b]⟩

instance : Encoding ℕ := ⟨Nat.bits⟩

instance (n : ℕ) : Encoding (Fin n) := ⟨fun i => Nat.bits i⟩

instance {α β : Type*} [Encoding α] [Encoding β] : Encoding (α × β) :=
  ⟨fun p => pair (encode p.1) (encode p.2)⟩

instance {α : Type*} [Encoding α] : Encoding (List α) :=
  ⟨fun l => (l.map fun a => selfDelimit (encode a)).flatten⟩

instance {α : Type*} [Encoding α] : Encoding (Option α) :=
  ⟨fun o => o.elim [false] (fun a => true :: encode a)⟩

instance {α β : Type*} [Encoding α] [Encoding β] : Encoding (α ⊕ β) :=
  ⟨fun s => s.elim (fun a => false :: encode a) (fun b => true :: encode b)⟩

/-- Bit strings encode as themselves. Declared last so that it takes priority over the generic
`List` instance, which would otherwise apply to `Bits = List Bool` as well. -/
instance : Encoding Bits := ⟨id⟩

/-! ## Polynomial time -/

/-- A bit-string function is *polynomial-time computable* when some single-tape Turing machine
computes it within a polynomial number of steps. -/
def PolyTime (f : Bits → Bits) : Prop :=
  Nonempty (SingleTapeTM.PolyTimeComputable f)

/-- A map between encoded types is polynomial-time computable when it is so on encodings. -/
def PolyTimeMap {α β : Type*} [Encoding α] [Encoding β] (F : α → β) : Prop :=
  ∃ f : Bits → Bits, PolyTime f ∧ ∀ a : α, f (encode a) = encode (F a)

/-- A predicate on an encoded type is polynomial-time decidable when its indicator is. -/
def PolyTimeDecidable {α : Type*} [Encoding α] (p : α → Prop) : Prop :=
  ∃ f : Bits → Bits, PolyTime f ∧ ∀ a : α, p a ↔ f (encode a) = [true]

/-! ## P and NP -/

/-- `L ∈ P`: some polynomial-time machine answers membership. -/
def InP (L : Language) : Prop :=
  ∃ f : Bits → Bits, PolyTime f ∧ ∀ x, x ∈ L ↔ f x = [true]

/-- `L ∈ NP`, via the verifier characterisation: membership has a polynomially-bounded witness
checkable in polynomial time. Using verifiers rather than nondeterministic machines keeps the
definition inside the deterministic model fixed above. -/
def InNP (L : Language) : Prop :=
  ∃ (p : Polynomial ℕ) (R : Language), InP R ∧
    ∀ x, x ∈ L ↔ ∃ w : Bits, w.length ≤ p.eval x.length ∧ pair x w ∈ R

/-- Polynomial-time many-one reducibility. -/
def PolyTimeReducible (L₁ L₂ : Language) : Prop :=
  ∃ f : Bits → Bits, PolyTime f ∧ ∀ x, x ∈ L₁ ↔ f x ∈ L₂

@[inherit_doc] scoped infix:50 " ≤ₚ " => PolyTimeReducible

/-- `L` is `NP`-hard: everything in `NP` reduces to it. -/
def NPHard (L : Language) : Prop :=
  ∀ L' : Language, InNP L' → PolyTimeReducible L' L

/-- `L` is `NP`-complete. -/
def NPComplete (L : Language) : Prop :=
  InNP L ∧ NPHard L

/-! ## Negligible functions -/

/-- A function is *negligible* when it eventually falls below every inverse polynomial. This is the
security threshold used in `EvenWrong.Complexity.OneWayFunctions`. -/
def Negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in Filter.atTop, |f n| ≤ 1 / (n : ℝ) ^ c

/-! ## Sanity checks

The definitions above are only as good as the encodings they rest on. These challenges pin the
encodings down; a solution to a downstream complexity challenge that exploited a non-injective
encoding would be caught here.
-/

/-- The pairing of bit strings can be parsed: it determines both components. -/
theorem pair_injective : Function.Injective (Function.uncurry pair) := by
  sorry

/-- Bit-string encodings of pairs are injective when the component encodings are. -/
theorem encode_prod_injective {α β : Type*} [Encoding α] [Encoding β]
    (hα : Function.Injective (encode : α → Bits)) (hβ : Function.Injective (encode : β → Bits)) :
    Function.Injective (encode : α × β → Bits) := by
  sorry

/-- Bit-string encodings of lists are injective when the entry encoding is. -/
theorem encode_list_injective {α : Type*} [Encoding α]
    (hα : Function.Injective (encode : α → Bits)) :
    Function.Injective (encode : List α → Bits) := by
  sorry

/-- `P ⊆ NP`, the trivial inclusion, and a check that the verifier definition is not accidentally
too strong. -/
theorem inNP_of_inP {L : Language} (h : InP L) : InNP L := by
  sorry

/-- **P ≠ NP**, entry #2 of the tier list. It already has a Lean statement in
`formal-conjectures`; it is restated here because everything else in this directory is calibrated
against it. -/
theorem p_ne_np : ∃ L : Language, InNP L ∧ ¬InP L := by
  sorry

/-- Polynomial-time reducibility is transitive, which is what makes `NPHard` well-behaved. -/
theorem polyTimeReducible_trans {L₁ L₂ L₃ : Language} (h₁ : PolyTimeReducible L₁ L₂)
    (h₂ : PolyTimeReducible L₂ L₃) : PolyTimeReducible L₁ L₃ := by
  sorry

/-- `P` is closed downwards under reduction. -/
theorem inP_of_polyTimeReducible {L₁ L₂ : Language} (h : PolyTimeReducible L₁ L₂) (h₂ : InP L₂) :
    InP L₁ := by
  sorry

end Complexity
