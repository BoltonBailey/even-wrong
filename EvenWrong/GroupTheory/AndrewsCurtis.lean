/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The Andrews–Curtis conjecture

Entry #41 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

A *balanced presentation* of the trivial group has as many relators as generators. Andrews and
Curtis conjectured that any such presentation can be reduced to the trivial one by a sequence of
elementary moves: inverting a relator, multiplying one relator by another, and conjugating a
relator. Most experts expect the conjecture to be false, and several families of potential
counterexamples (Akbulut–Kirby, Miller–Schupp) are known but unresolved; recent reinforcement
learning attacks have trivialised some of them.

Everything happens inside `FreeGroup (Fin n)`, so the statement is fully self-contained.
-/

@[expose] public section

namespace AndrewsCurtis

open FreeGroup

variable {n : ℕ}

/-- The elementary Andrews–Curtis moves on an `n`-tuple of elements of the free group of rank `n`:
invert a coordinate, multiply one coordinate by another, or conjugate a coordinate. -/
inductive Move : (Fin n → FreeGroup (Fin n)) → (Fin n → FreeGroup (Fin n)) → Prop
  /-- Replace the `i`-th relator by its inverse. -/
  | inv (r : Fin n → FreeGroup (Fin n)) (i : Fin n) :
      Move r (Function.update r i (r i)⁻¹)
  /-- Replace the `i`-th relator by its product with a different relator. -/
  | mul (r : Fin n → FreeGroup (Fin n)) (i j : Fin n) (hij : i ≠ j) :
      Move r (Function.update r i (r i * r j))
  /-- Conjugate the `i`-th relator by an arbitrary word. -/
  | conj (r : Fin n → FreeGroup (Fin n)) (i : Fin n) (w : FreeGroup (Fin n)) :
      Move r (Function.update r i (w * r i * w⁻¹))

/-- Two tuples are *Andrews–Curtis equivalent* when one can be transformed into the other by a
finite sequence of elementary moves. -/
def ACEquiv (r s : Fin n → FreeGroup (Fin n)) : Prop :=
  Relation.ReflTransGen Move r s

/-- A tuple *presents the trivial group* when its normal closure is the whole free group; the
presentation `⟨x₁, …, xₙ | r₁, …, rₙ⟩` is then a balanced presentation of the trivial group. -/
def PresentsTrivial (r : Fin n → FreeGroup (Fin n)) : Prop :=
  Subgroup.normalClosure (Set.range r) = ⊤

/-! ## Challenges -/

/-- **The Andrews–Curtis conjecture.** Every balanced presentation of the trivial group is
Andrews–Curtis equivalent to the trivial presentation `(x₁, …, xₙ)`. -/
theorem andrews_curtis (r : Fin n → FreeGroup (Fin n)) (hr : PresentsTrivial r) :
    ACEquiv r (fun i => FreeGroup.of i) := by
  sorry

/-- The expected answer is that the conjecture is **false**. This is the "even wrong" companion:
a counterexample is a balanced presentation of the trivial group that no sequence of moves
trivialises. At most one of this statement and `AndrewsCurtis.andrews_curtis` can be solved. -/
theorem exists_counterexample :
    ∃ (n : ℕ) (r : Fin n → FreeGroup (Fin n)),
      PresentsTrivial r ∧ ¬ACEquiv r (fun i => FreeGroup.of i) := by
  sorry

/-- The moves preserve the property of presenting the trivial group, so the conjecture is at least
consistent. This is the provable sanity check on the definitions. -/
theorem presentsTrivial_of_move {r s : Fin n → FreeGroup (Fin n)} (h : Move r s)
    (hr : PresentsTrivial r) : PresentsTrivial s := by
  sorry

/-- Andrews–Curtis equivalence is symmetric: each move can be undone by moves of the same kind. -/
theorem acEquiv_symm {r s : Fin n → FreeGroup (Fin n)} (h : ACEquiv r s) : ACEquiv s r := by
  sorry

/-- The trivial presentation does present the trivial group, so the target of the conjecture is
legitimate. -/
theorem presentsTrivial_of : PresentsTrivial (fun i : Fin n => FreeGroup.of i) := by
  sorry

/-- The rank-one case is easy: a single relator normally generating `FreeGroup (Fin 1) ≃ ℤ` must be
a generator, hence is already trivialised. -/
theorem andrews_curtis_one (r : Fin 1 → FreeGroup (Fin 1)) (hr : PresentsTrivial r) :
    ACEquiv r (fun i => FreeGroup.of i) := by
  sorry

/-- The Akbulut–Kirby presentations `⟨x, y | x^n = y^{n+1}, xyx = yxy⟩`, the best known family of
candidate counterexamples. The case `n = 3` was trivialised by hand in 2015; the general case is
open. -/
theorem akbulut_kirby (n : ℕ) (hn : 2 ≤ n) :
    ACEquiv
      (fun i : Fin 2 =>
        if i = 0 then FreeGroup.of (0 : Fin 2) ^ n * (FreeGroup.of (1 : Fin 2) ^ (n + 1))⁻¹
        else FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) *
          (FreeGroup.of (1 : Fin 2) * FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2))⁻¹)
      (fun i => FreeGroup.of i) := by
  sorry

end AndrewsCurtis
