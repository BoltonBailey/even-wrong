/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# NotWrong.Games.ProblemFourteen

Solutions to the self-contained equity challenges posed in `EvenWrong.Games.ProblemFourteen`
(paired by `comparator/ProblemFourteen.json`).

This module does **not** import `EvenWrong`. The only definition the challenge statements
depend on is the equity recursion `e`, which is re-declared here verbatim from
`EvenWrong.Games.ProblemFourteen` so that `comparator` can match the declarations.

The theorems solved here are exactly the ones whose proofs are independent of the
(`SOS`-dependent) barrier development: the lower bound `sub_le_e`, nonnegativity
`zero_le_e`, strict positivity on the diagonal `e_pos_of_pos`, the swapped-deck bound
`pos_e_swap_add`, and the two structural unfoldings `e_succ_succ` and
`e_eq_zero_of_inner_nonpos`.
-/

@[expose] public section

/-! ## Definition re-declared from `EvenWrong` (comparator-friendly) -/

/-- The equity `e r b` of a deck with `r` red and `b` black cards. -/
def e : ℕ → ℕ → ℚ
| 0, _ => 0
| r, 0 => r
| r+1, b+1 => max 0 ((r+1)/(r+b+2) * (e r (b+1) + 1) + (b+1)/(r+b+2) * (e (r+1) b - 1))

/-! ## The proofs -/

/-- For a deck with `n` red cards and `m` black cards, the expected payoff is at least `n - m`. -/
theorem sub_le_e (n m : ℕ) : n - m ≤ e n m := by
  induction n generalizing m with
  | zero => simp [e]
  | succ n ih =>
    induction m with
    | zero => simp [e]
    | succ m ihm =>
      simp only [e]
      apply le_trans _ (le_max_right 0 _)
      have hn := ih (m + 1)
      push_cast at *
      have h1 : (0 : ℚ) ≤ (n + 1) / (n + m + 2) := by positivity
      have h2 : (0 : ℚ) ≤ (m + 1) / (n + m + 2) := by positivity
      have key1 : e n (m + 1) + 1 ≥ (n : ℚ) - m := by linarith
      have key2 : e (n + 1) m - 1 ≥ (n : ℚ) - m := by linarith
      have hsum : (n + 1 : ℚ) / (n + m + 2) + (m + 1) / (n + m + 2) = 1 := by
        field_simp; ring
      calc (n : ℚ) + 1 - (m + 1)
          = (n - m) * ((n + 1) / (n + m + 2) + (m + 1) / (n + m + 2)) := by rw [hsum]; ring
        _ = (n + 1) / (n + m + 2) * (n - m) + (m + 1) / (n + m + 2) * (n - m) := by ring
        _ ≤ (n + 1) / (n + m + 2) * (e n (m + 1) + 1) +
            (m + 1) / (n + m + 2) * (e (n + 1) m - 1) := by
            apply add_le_add <;> apply mul_le_mul_of_nonneg_left _ ‹_› <;> linarith

/-- The expected payoff is always nonnegative. -/
theorem zero_le_e (n m : ℕ) : 0 ≤ e n m := by
  induction n generalizing m with
  | zero => simp [e]
  | succ n ih =>
    induction m with
    | zero => simp only [e]; positivity
    | succ m ihm =>
      simp only [e]
      exact le_max_left _ _

/-- For a deck with a positive equal amount of cards of each color, the expected payoff is
strictly positive. -/
theorem e_pos_of_pos (n : ℕ) (hn : 0 < n) : 0 < e n n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [e]
  apply lt_of_lt_of_le _ (le_max_right 0 _)
  have h1 : (0 : ℚ) ≤ e k (k + 1) := zero_le_e k (k + 1)
  have h2 : (1 : ℚ) ≤ e (k + 1) k := by
    have := sub_le_e (k + 1) k; push_cast at this; linarith
  have hcoeff : (k + 1 : ℚ) / (↑k + ↑k + 2) = 1 / 2 := by field_simp; ring
  rw [hcoeff]; nlinarith

/-- For one deck with `n` red cards and `m` black cards, and another deck with `m` red cards and
`n` black cards, the total expected payoff is positive. -/
theorem pos_e_swap_add (n m : ℕ) (hn : 0 < n + m) : 0 < e n m + e m n := by
  rcases lt_trichotomy n m with h | rfl | h
  case inl =>
    have hcast : (n : ℚ) + 1 ≤ m := by exact_mod_cast h
    linarith [sub_le_e m n, zero_le_e n m]
  case inr.inl =>
    linarith [e_pos_of_pos n (by omega)]
  case inr.inr =>
    have hcast : (m : ℚ) + 1 ≤ n := by exact_mod_cast h
    linarith [sub_le_e n m, zero_le_e m n]

/-- Unfolded recursion: for `r, b ≥ 1` (here in the `r+1, b+1` form), `e` satisfies the
optimality equation with `N = r + b + 2`. -/
theorem e_succ_succ (r b : ℕ) :
    e (r + 1) (b + 1) =
      max 0 ((r + 1) / (r + b + 2) * (e r (b + 1) + 1)
        + (b + 1) / (r + b + 2) * (e (r + 1) b - 1)) := by
  simp only [e]

/-- Reduction: if the "continue" value is `≤ 0`, the equity is exactly `0`. -/
theorem e_eq_zero_of_inner_nonpos (r b : ℕ)
    (h : (r + 1) / (r + b + 2) * (e r (b + 1) + 1)
        + (b + 1) / (r + b + 2) * (e (r + 1) b - 1) ≤ 0) :
    e (r + 1) (b + 1) = 0 :=
  (e_succ_succ r b).trans (max_eq_left h)
