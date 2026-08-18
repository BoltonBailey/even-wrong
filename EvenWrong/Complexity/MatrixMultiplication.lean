/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The matrix multiplication exponent

Entry #74 of the [open-problem tier list](https://github.com/evand/open-math-problems), listed
there without a Lean statement.

The exponent `ω` is the infimum of the exponents achievable by matrix multiplication algorithms.
Strassen's seven multiplications for `2 × 2` matrices gave `ω ≤ log₂ 7 ≈ 2.807`; the laser method
and its refinements have pushed the record to about `2.371`. Whether `ω = 2` is the central open
problem of algebraic complexity.

The right notion of "number of multiplications" is the tensor rank of the matrix multiplication
tensor, spelled out here as the existence of a bilinear algorithm.
-/

@[expose] public section

namespace MatMul

variable {n r : ℕ}

/-- A *bilinear algorithm* of rank `r` for `n × n` matrix multiplication over `ℚ`: `r` products of
linear forms in the entries of `X` and of `Y`, recombined linearly into `X * Y`. The coefficient
matrices `a i`, `b i` and `c i` are the three factors of a rank-one term of the matrix
multiplication tensor. -/
def IsBilinearAlgorithm (a b c : Fin r → Matrix (Fin n) (Fin n) ℚ) : Prop :=
  ∀ X Y : Matrix (Fin n) (Fin n) ℚ,
    X * Y = ∑ i, ((∑ p, ∑ q, a i p q * X p q) * (∑ p, ∑ q, b i p q * Y p q)) • c i

/-- The tensor rank of `n × n` matrix multiplication: the least number of multiplications in a
bilinear algorithm. -/
noncomputable def rank (n : ℕ) : ℕ :=
  sInf {r | ∃ a b c : Fin r → Matrix (Fin n) (Fin n) ℚ, IsBilinearAlgorithm a b c}

/-- The achievable exponents: those `w` for which the tensor rank of `n × n` multiplication is
`O(n ^ w)`. -/
def exponents : Set ℝ :=
  {w : ℝ | ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (rank n : ℝ) ≤ C * (n : ℝ) ^ w}

/-- The matrix multiplication exponent `ω`. -/
noncomputable def omega : ℝ :=
  sInf exponents

/-! ## Challenges -/

/-- **Is `ω = 2`?** The central conjecture: matrix multiplication is essentially as cheap as
reading the input. -/
theorem omega_eq_two : omega = 2 := by
  sorry

/-- The trivial lower bound `2 ≤ ω`, which holds because the output has `n ^ 2` entries. This is
provable and pins down half of the conjecture. -/
theorem two_le_omega : 2 ≤ omega := by
  sorry

/-- Strassen's algorithm: `2 × 2` matrices can be multiplied with seven multiplications. This is a
finite, checkable identity, and the most concrete challenge here. -/
theorem rank_two_le_seven : rank 2 ≤ 7 := by
  sorry

/-- Winograd's matching lower bound: seven multiplications are necessary for `2 × 2`. Together with
`MatMul.rank_two_le_seven` this determines `rank 2 = 7`. -/
theorem seven_le_rank_two : 7 ≤ rank 2 := by
  sorry

/-- Strassen's consequence: `ω ≤ log₂ 7`. -/
theorem omega_le_logb_seven : omega ≤ Real.logb 2 7 := by
  sorry

/-- The current record, from the refined laser method (Alman–Duan–Vassilevska Williams–Xu–Xu–Zhou
and successors): `ω < 2.372`. -/
theorem omega_lt : omega < 2.372 := by
  sorry

/-- The rank of `3 × 3` matrix multiplication is unknown; it lies between `19` and `23`. Settling
either bound would be a real advance, and the statement is finite. -/
theorem rank_three_bounds : 19 ≤ rank 3 ∧ rank 3 ≤ 23 := by
  sorry

/-- The naive algorithm gives `rank n ≤ n ^ 3`, so `exponents` is nonempty and `omega` is not the
junk value of `sInf ∅`. -/
theorem rank_le_cube (n : ℕ) : rank n ≤ n ^ 3 := by
  sorry

/-- Tensor rank is submultiplicative under the Kronecker product, which is why a single good
algorithm bootstraps into an exponent at all. -/
theorem rank_mul_le (m n : ℕ) : rank (m * n) ≤ rank m * rank n := by
  sorry

end MatMul
