/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib
public import EvenWrong.Complexity.Basic

/-!
# Existence of one-way functions

Entry #14 of the [open-problem tier list](https://github.com/evand/open-math-problems), listed
there without a Lean statement.

A one-way function is easy to evaluate and hard to invert. Their existence is the minimal
assumption of symmetric cryptography — it is equivalent to the existence of pseudorandom
generators, pseudorandom functions, and secure signature schemes — and is where Impagliazzo's five
worlds separate: `P ≠ NP` alone does not deliver them.

The adversaries here are *deterministic* polynomial-time machines, which is what the machine model
in `EvenWrong.Complexity.Basic` supplies. That is a weaker security requirement than the textbook
one, which quantifies over probabilistic polynomial-time adversaries; a randomised version would
need a probabilistic machine model with a runtime bound, which `VCVio`'s `ProbComp` does not yet
carry. Closing that gap is future work for the model, not for these statements.
-/

@[expose] public section

namespace OneWayFunctions

open Complexity Filter

/-- The advantage of `g` at inverting `f` on inputs of length `n`: the fraction of `n`-bit inputs
`x` for which `g (f x)` is a valid preimage of `f x`. Inverting means finding *some* preimage, not
recovering `x` itself. -/
noncomputable def inversionAdvantage (f g : Bits → Bits) (n : ℕ) : ℝ :=
  ((Finset.univ.filter fun x : Fin n → Bool =>
      f (g (f (List.ofFn x))) = f (List.ofFn x)).card : ℝ) / 2 ^ n

/-- `f` is *one-way*: polynomial-time computable, but no polynomial-time adversary inverts it with
non-negligible probability over a uniformly random input. -/
def IsOneWay (f : Bits → Bits) : Prop :=
  PolyTime f ∧ ∀ g : Bits → Bits, PolyTime g → Negligible (inversionAdvantage f g)

/-- `f` is *weakly one-way*: every polynomial-time adversary fails on at least an inverse
polynomial fraction of inputs. -/
def IsWeaklyOneWay (f : Bits → Bits) : Prop :=
  PolyTime f ∧ ∃ c : ℕ, ∀ g : Bits → Bits, PolyTime g →
    ∀ᶠ n in atTop, inversionAdvantage f g n ≤ 1 - 1 / (n : ℝ) ^ c

/-- `f` is length-preserving, the normalisation under which one-wayness is usually stated. -/
def IsLengthPreserving (f : Bits → Bits) : Prop :=
  ∀ x, (f x).length = x.length

/-! ## Challenges -/

/-- **Do one-way functions exist?** The A-tier question, and the dividing line between
Impagliazzo's Minicrypt and Pessiland. -/
theorem exists_oneWay : ∃ f : Bits → Bits, IsOneWay f := by
  sorry

/-- The negation, as an "even wrong" companion: we live in Pessiland or better-behaved. Exactly
one of this and `OneWayFunctions.exists_oneWay` is true, and neither is expected to be resolved. -/
theorem not_exists_oneWay : ¬∃ f : Bits → Bits, IsOneWay f := by
  sorry

/-- One-way functions imply `P ≠ NP`: inverting `f` is an `NP` search problem, so a polynomial-time
decision procedure for `NP` would invert it. This is a real implication, provable from the
definitions here, and the most tractable challenge on this page. -/
theorem p_ne_np_of_exists_oneWay (h : ∃ f : Bits → Bits, IsOneWay f) :
    ∃ L : Language, InNP L ∧ ¬InP L := by
  sorry

/-- The converse fails to be known: `P ≠ NP` is not known to imply one-way functions, and the gap
between them is exactly Pessiland. Recording it as a challenge makes the separation explicit — a
solution would be a major result, and a refutation would be an oracle separation made uniform. -/
theorem exists_oneWay_of_p_ne_np (h : ∃ L : Language, InNP L ∧ ¬InP L) :
    ∃ f : Bits → Bits, IsOneWay f := by
  sorry

/-- Yao's amplification theorem: a weak one-way function can be hardened into a one-way function by
direct product. This is known, and is a self-contained formalisation target. -/
theorem exists_oneWay_of_exists_weaklyOneWay (h : ∃ f : Bits → Bits, IsWeaklyOneWay f) :
    ∃ f : Bits → Bits, IsOneWay f := by
  sorry

/-- One-way functions can be taken length-preserving without loss of generality. -/
theorem exists_lengthPreserving_oneWay (h : ∃ f : Bits → Bits, IsOneWay f) :
    ∃ f : Bits → Bits, IsOneWay f ∧ IsLengthPreserving f := by
  sorry

/-- A one-way function is in particular weakly one-way, the easy direction of the amplification
theorem and a check that the two definitions are compatible. -/
theorem isWeaklyOneWay_of_isOneWay {f : Bits → Bits} (h : IsOneWay f) : IsWeaklyOneWay f := by
  sorry

/-- No function is one-way against unbounded adversaries: dropping `PolyTime g` from the definition
makes it vacuous, since `g` can brute-force a preimage. This is the guardrail that shows the
polynomial-time restriction is carrying the whole statement. -/
theorem not_isOneWay_of_unbounded (f : Bits → Bits) :
    ¬(∀ g : Bits → Bits, Negligible (inversionAdvantage f g)) := by
  sorry

/-- One-wayness survives composition with a polynomial-time injection on the output side: if `f`
is one-way and `h` is a polynomial-time injection, then `h ∘ f` is one-way. This is the closure
property every construction in symmetric cryptography leans on. -/
theorem isOneWay_comp {f h : Bits → Bits} (hf : IsOneWay f) (hh : PolyTime h)
    (hinj : Function.Injective h) : IsOneWay (h ∘ f) := by
  sorry

end OneWayFunctions
