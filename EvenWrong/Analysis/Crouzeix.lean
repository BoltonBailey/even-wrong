/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# Crouzeix's conjecture

Entry #47 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Crouzeix conjectured that the numerical range of a matrix is a `2`-spectral set: for every
polynomial `p`,
`‖p(A)‖ ≤ 2 · sup { |p z| : z ∈ W(A) }`,
where `W(A) = { ⟪x, A x⟫ : ‖x‖ = 1 }` is the field of values. The constant `2` would be optimal.
Crouzeix and Palencia proved the bound with `1 + √2`, which remains the best known.

We state it for continuous linear endomorphisms of a finite-dimensional complex inner product
space, which is where `Polynomial.aeval` and the operator norm are both available.
-/

@[expose] public section

namespace Crouzeix

open scoped ComplexInnerProductSpace

variable {n : ℕ}

/-- The *numerical range* (field of values) of an operator: the set of values `⟪x, A x⟫` over unit
vectors `x`. It is a compact convex set containing the spectrum. -/
def numericalRange (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : Set ℂ :=
  {z : ℂ | ∃ x : EuclideanSpace ℂ (Fin n), ‖x‖ = 1 ∧ z = ⟪x, A x⟫}

/-- The supremum of `|p|` over the numerical range of `A`. -/
noncomputable def supOnNumericalRange (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (p : Polynomial ℂ) : ℝ :=
  ⨆ z ∈ numericalRange A, ‖p.eval z‖

/-! ## Challenges -/

/-- **Crouzeix's conjecture.** The numerical range is a `2`-spectral set. -/
theorem crouzeix (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ 2 * supOnNumericalRange A p := by
  sorry

/-- The Crouzeix–Palencia theorem: the bound holds with `1 + √2`. This is known, and is the
natural first target — a solution here is a genuine formalisation of a hard analysis result rather
than a resolution of the conjecture. -/
theorem crouzeix_palencia (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ (1 + Real.sqrt 2) * supOnNumericalRange A p := by
  sorry

/-- The constant `2` cannot be improved: there are matrices and polynomials for which the ratio
approaches `2`. This is the "even wrong" guardrail on the conjecture. -/
theorem two_is_optimal :
    ∀ c : ℝ, c < 2 → ∃ (n : ℕ) (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
      (p : Polynomial ℂ), c * supOnNumericalRange A p < ‖Polynomial.aeval A p‖ := by
  sorry

/-- The `2 × 2` case is a theorem (Crouzeix): the conjecture holds, with constant `2`, for
matrices of order two. -/
theorem crouzeix_two (A : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ 2 * supOnNumericalRange A p := by
  sorry

/-- The numerical range is convex (the Toeplitz–Hausdorff theorem). This is the structural fact
that makes the conjecture plausible and is a prerequisite for any proof of it. -/
theorem convex_numericalRange (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    Convex ℝ (numericalRange A) := by
  sorry

/-- The numerical range contains the spectrum, so the right-hand side of Crouzeix's inequality
dominates the spectral radius of `p(A)`. -/
theorem spectrum_subset_numericalRange
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
    spectrum ℂ A ⊆ numericalRange A := by
  sorry

/-- For normal operators the bound holds with constant `1` (the numerical range is then the convex
hull of the spectrum, and the spectral theorem applies). This is the easy case and a useful test of
the definitions. -/
theorem crouzeix_of_isStarNormal (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hA : IsStarNormal A) (p : Polynomial ℂ) :
    ‖Polynomial.aeval A p‖ ≤ supOnNumericalRange A p := by
  sorry

end Crouzeix
