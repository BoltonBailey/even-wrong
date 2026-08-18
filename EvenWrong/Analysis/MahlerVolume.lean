/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The Mahler volume conjecture

Entry #84 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

The Mahler volume `|K| · |K°|` of a convex body is an affine invariant. Its *maximum* over
symmetric bodies is the ball (the Blaschke–Santaló inequality, a theorem). Mahler conjectured that
its *minimum* is attained by the cube — equivalently the cross-polytope — with value `4^d / d!`.
The conjecture is known in the plane (Mahler) and in dimension three (Iriyeh–Shibata, 2020), and
Bourgain–Milman gives the bound up to an exponential factor.

There is also a non-symmetric version, with the simplex conjectured extremal and value
`(d+1)^{d+1} / (d!)^2`.
-/

@[expose] public section

namespace Mahler

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

variable {d : ℕ}

/-- The *polar body* of `K`: the points whose inner product with everything in `K` is at most one.
For a symmetric convex body containing the origin in its interior this is again such a body. -/
def polarBody (K : Set (EuclideanSpace ℝ (Fin d))) : Set (EuclideanSpace ℝ (Fin d)) :=
  {y | ∀ x ∈ K, ⟪x, y⟫ ≤ 1}

/-- The *Mahler volume* of `K`, the product of the volumes of `K` and of its polar. It is invariant
under invertible linear maps, which is what makes the extremal problem well posed. -/
noncomputable def mahlerVolume (K : Set (EuclideanSpace ℝ (Fin d))) : ℝ≥0∞ :=
  volume K * volume (polarBody K)

/-- A *symmetric convex body*: compact, convex, centrally symmetric, with the origin in its
interior. -/
structure IsSymmetricBody (K : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  /-- The body is convex. -/
  convex : Convex ℝ K
  /-- The body is compact. -/
  isCompact : IsCompact K
  /-- The body is symmetric about the origin. -/
  symmetric : ∀ x ∈ K, -x ∈ K
  /-- The body has nonempty interior, normalised so that the origin is an interior point. -/
  zero_mem_interior : 0 ∈ interior K

/-! ## Challenges -/

/-- **Mahler's conjecture** for symmetric bodies: the cube minimises the Mahler volume, with value
`4^d / d!`. -/
theorem mahler_symmetric (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsSymmetricBody K) :
    (4 ^ d / (Nat.factorial d) : ℝ≥0∞) ≤ mahlerVolume K := by
  sorry

/-- The conjectured minimiser is genuinely a minimiser: the cube `[-1, 1]^d` attains the value
`4^d / d!`, its polar being the cross-polytope. This computation fixes the constant. -/
theorem mahlerVolume_cube :
    mahlerVolume {x : EuclideanSpace ℝ (Fin d) | ∀ i, |x i| ≤ 1} =
      (4 ^ d / (Nat.factorial d) : ℝ≥0∞) := by
  sorry

/-- The planar case, proved by Mahler. -/
theorem mahler_two (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsSymmetricBody K) :
    (8 : ℝ≥0∞) ≤ mahlerVolume K := by
  sorry

/-- The three-dimensional case, proved by Iriyeh and Shibata in 2020 — the most recent case to
fall, and the natural formalisation target. -/
theorem mahler_three (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsSymmetricBody K) :
    (32 / 3 : ℝ≥0∞) ≤ mahlerVolume K := by
  sorry

/-- The Bourgain–Milman theorem: the Mahler volume is bounded below by `c^d / d!` for an absolute
constant `c > 0`. This is the known result that the conjecture sharpens to `c = 4`. -/
theorem bourgain_milman :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ (d : ℕ) (K : Set (EuclideanSpace ℝ (Fin d))), IsSymmetricBody K →
      c ^ d / (Nat.factorial d) ≤ mahlerVolume K := by
  sorry

/-- The Blaschke–Santaló inequality, the matching upper bound: the Euclidean ball maximises the
Mahler volume. Unlike the conjecture, this direction is a theorem. -/
theorem blaschke_santalo (K : Set (EuclideanSpace ℝ (Fin d))) (hK : IsSymmetricBody K) :
    mahlerVolume K ≤ mahlerVolume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
  sorry

/-- **Mahler's conjecture** in the non-symmetric case: among convex bodies with centroid at the
origin the simplex is extremal, with Mahler volume `(d+1)^{d+1} / (d!)^2`. -/
theorem mahler_nonsymmetric (K : Set (EuclideanSpace ℝ (Fin d))) (hconv : Convex ℝ K)
    (hcomp : IsCompact K) (hint : 0 ∈ interior K)
    (hcentroid : ∫ x in K, x ∂volume = 0) :
    (((d + 1) ^ (d + 1) : ℕ) / ((Nat.factorial d) ^ 2 : ℕ) : ℝ≥0∞) ≤ mahlerVolume K := by
  sorry

/-- The Mahler volume is a linear invariant: applying an invertible linear map to `K` applies its
inverse transpose to the polar, and the two determinant factors cancel. This is the sanity check
that the extremal problem is affine-invariant. -/
theorem mahlerVolume_comp_linearEquiv (K : Set (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :
    mahlerVolume (f '' K) = mahlerVolume K := by
  sorry

end Mahler
