/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
This file is for some problems from
https://thequantummilkman.substack.com/p/bit-commitment-from-factor-counting

TODO need nore TM API to develop some of this.
TODO probably best to reuse VCVio when it becomes available.

-/

@[expose] public section

namespace SumsOfIID

open scoped ENNReal

/-! ## Sums of independent copies -/

/-- The distribution of `X + Y` for independent `X ~ μ` and `Y ~ ν`: the convolution of `μ`
and `ν`. -/
noncomputable def conv (μ ν : PMF ℝ) : PMF ℝ :=
  μ.bind fun x => ν.map (x + ·)

/-- The distribution of a sum of `n` independent copies of `μ`. The empty sum is `0`. -/
noncomputable def convPow (μ : PMF ℝ) : ℕ → PMF ℝ
  | 0 => PMF.pure 0
  | n + 1 => conv μ (convPow μ n)

/-- A distribution is *positive* when every point of its support is a positive real. -/
def PosSupport (μ : PMF ℝ) : Prop :=
  ∀ x ∈ μ.support, 0 < x

/-! ## Statistical distance -/

/-- The statistical (total variation) distance between two discrete distributions: half the sum of
the absolute differences of the point masses. -/
noncomputable def statDist (μ ν : PMF ℝ) : ℝ :=
  (∑' x : ℝ, |(μ x).toReal - (ν x).toReal|) / 2

/-- Statistical distance agrees with the `sup`-over-events description: it is the largest
difference in probability that any event can exhibit. -/
theorem statDist_eq_iSup (μ ν : PMF ℝ) :
    statDist μ ν = ⨆ s : Set ℝ, |(μ.toMeasure s).toReal - (ν.toMeasure s).toReal| := by
  sorry

/-- Statistical distance never exceeds `1`. -/
theorem statDist_le_one (μ ν : PMF ℝ) : statDist μ ν ≤ 1 := by
  sorry

/-! ## The quantity under study -/

/-- The statistical distance between `X₁ + X₂` and `X₃ + X₄ + X₅` for i.i.d. `Xᵢ ~ μ`. -/
noncomputable def gap (μ : PMF ℝ) : ℝ :=
  statDist (convPow μ 2) (convPow μ 3)

/-- The set of statistical distances between a sum of two and a sum of three i.i.d. copies,
as the common distribution ranges over the positive discrete distributions. -/
def gaps : Set ℝ :=
  {d | ∃ μ : PMF ℝ, PosSupport μ ∧ gap μ = d}

/-- The minimum (infimum) statistical distance between `X₁ + X₂` and `X₃ + X₄ + X₅` over all
i.i.d. positive-real-valued discrete distributions. -/
noncomputable def minDistance : ℝ :=
  sInf gaps

/-! ## Challenges -/

/-- Rescaling the distribution by a positive constant rescales both sums, so it does not change
the statistical distance between them. In particular the problem is scale-invariant, and no
normalization of `μ` (e.g. of its mean) loses generality. -/
theorem gap_map_mul (μ : PMF ℝ) (hμ : PosSupport μ) {c : ℝ} (hc : 0 < c) :
    gap (μ.map (c * ·)) = gap μ := by
  sorry

/-- For a *fixed* positive distribution, a sum of two copies and a sum of three copies are never
equal in distribution, so their statistical distance is strictly positive.

Sketch: the Laplace transform `L t = 𝔼[exp (-t * X)]` satisfies `L t ^ 2 = L t ^ 3` for all
`t > 0` if the two sums agree, hence `L t = 1`, hence `X = 0` almost surely, contradicting
`PosSupport`. -/
theorem statDist_pos (μ : PMF ℝ) (hμ : PosSupport μ) : 0 < gap μ := by
  sorry

/-- **The main challenge.** The infimum is *not* attained in the limit either: there is a uniform
positive lower bound on the statistical distance between a sum of two and a sum of three i.i.d.
positive copies.

This does not follow from `statDist_pos`, which gives a bound depending on `μ`. It is the
"even wrong" half of the problem: an explicit family of heavy-tailed distributions driving the
distance to `0` would refute it. -/
theorem minDistance_pos : 0 < minDistance := by
  sorry

/-- Complementary to `minDistance_pos`: the infimum is bounded away from the trivial upper bound
`1`, witnessed by a suitably heavy-tailed distribution (see the module docstring). -/
theorem exists_gap_lt_half : ∃ μ : PMF ℝ, PosSupport μ ∧ gap μ < 1 / 2 := by
  sorry

/-- Is the infimum attained? An optimal distribution would have to be heavy-tailed, and it is not
clear that the optimization is closed; a solution either exhibits a minimizer or shows there is
none. -/
theorem exists_minimizer : ∃ μ : PMF ℝ, PosSupport μ ∧ gap μ = minDistance := by
  sorry

end SumsOfIID
