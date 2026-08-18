/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The Lindelöf Hypothesis

Entry #20 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

The Lindelöf hypothesis asserts that `ζ(1/2 + it)` grows slower than any fixed positive power of
`t`. It is implied by the Riemann hypothesis and is strictly weaker than it, but is still open;
the best unconditional exponents come from the Bombieri–Iwaniec–Huxley and, more recently,
Guth–Maynard machinery.

We package the statement through the *Lindelöf `μ` function*, the standard convexity-theoretic
device: `μ σ` is the least exponent `c` for which `ζ(σ + it) = O(|t| ^ c)`. The hypothesis is
exactly `μ (1/2) = 0`.
-/

@[expose] public section

namespace Lindelof

open Complex

/-- The set of admissible growth exponents on the vertical line `Re s = σ`: those `c ≥ 0` for
which `ζ(σ + it)` is `O(|t| ^ c)` as `|t| → ∞`. -/
def growthExponents (σ : ℝ) : Set ℝ :=
  {c : ℝ | 0 ≤ c ∧ ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| → ‖riemannZeta (σ + t * I)‖ ≤ C * |t| ^ c}

/-- The Lindelöf `μ` function: the infimum of the exponents `c` with `ζ(σ + it) = O(|t| ^ c)`. -/
noncomputable def mu (σ : ℝ) : ℝ :=
  sInf (growthExponents σ)

/-! ## Challenges -/

/-- **The Lindelöf hypothesis**, in its `μ`-function form: the zeta function has no growth at all
on the critical line, beyond `|t| ^ ε` for every `ε > 0`. -/
theorem mu_half : mu (1 / 2) = 0 := by
  sorry

/-- **The Lindelöf hypothesis**, in its `ε`-form: for every positive `ε` the function
`ζ(1/2 + it)` is `O(|t| ^ ε)`. This is the shape the hypothesis is usually quoted in, and it is
equivalent to `Lindelof.mu_half`. -/
theorem lindelof_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε := by
  sorry

/-- The two forms above say the same thing. Proving this reduces one challenge to the other. -/
theorem mu_half_iff :
    mu (1 / 2) = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ t : ℝ, 1 ≤ |t| → ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * |t| ^ ε := by
  sorry

/-- The exponent set is nonempty and bounded below, so `mu` is not the junk value of `sInf` on the
empty set. This is the sanity check that makes `Lindelof.mu_half` meaningful. -/
theorem growthExponents_nonempty (σ : ℝ) (hσ : 1 / 2 ≤ σ) : (growthExponents σ).Nonempty := by
  sorry

/-- The classical convexity ("Phragmén–Lindelöf") bound `μ (1/2) ≤ 1/4`, due to Lindelöf himself.
Unlike the hypothesis this is a theorem, and it is the natural first target here. -/
theorem mu_half_le_quarter : mu (1 / 2) ≤ 1 / 4 := by
  sorry

/-- `μ` is nonnegative everywhere: `ζ` does not decay on vertical lines. -/
theorem mu_nonneg (σ : ℝ) : 0 ≤ mu σ := by
  sorry

/-- To the right of the critical strip there is no growth: `ζ` is bounded on `Re s = σ > 1`. -/
theorem mu_eq_zero_of_one_lt (σ : ℝ) (hσ : 1 < σ) : mu σ = 0 := by
  sorry

/-- The Riemann hypothesis implies the Lindelöf hypothesis. This is the classical implication
(via the Borel–Carathéodory / Hadamard three-circles argument), and is the one direction of the
relationship between the two that is actually a theorem — Lindelöf does *not* imply RH. -/
theorem rh_imp_lindelof
    (rh : ∀ s : ℂ, riemannZeta s = 0 → ¬(s.re < 0 ∨ 1 < s.re) → s.re = 1 / 2) :
    mu (1 / 2) = 0 := by
  sorry

/-- The Lindelöf hypothesis is equivalent to a statement about zero density: for every `σ > 1/2`,
the number of zeros of `ζ` with real part above `σ` and imaginary part in `[T, T+1]` is
`o(log T)`. This is Backlund's criterion. -/
theorem lindelof_iff_zero_density :
    mu (1 / 2) = 0 ↔
      ∀ σ : ℝ, 1 / 2 < σ → ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
        ∀ s : Finset ℂ, (∀ z ∈ s, riemannZeta z = 0 ∧ σ < z.re ∧ T ≤ z.im ∧ z.im ≤ T + 1) →
          (s.card : ℝ) ≤ ε * Real.log T := by
  sorry

end Lindelof
