/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# Zaremba's conjecture

Entry #93 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Zaremba conjectured that every denominator `n` admits a numerator `a`, coprime to `n`, whose
continued fraction expansion `a / n = [0; q₁, …, q_r]` uses only small partial quotients — five
suffices. The motivation is numerical: such fractions are the good lattice points for
quasi-Monte-Carlo integration. Bourgain and Kontorovich proved a density version (almost all `n`
work, with bound 50, later improved), but no single `n` is known to fail and the full statement is
open.

We compute partial quotients directly by the Euclidean algorithm rather than through Mathlib's
`GenContFract`, which keeps everything inside `ℕ`.
-/

@[expose] public section

namespace Zaremba

/-- The partial quotients of `a / b`, computed by the Euclidean algorithm: `partQuots a b` is the
list `[⌊a/b⌋, …]` obtained by repeatedly replacing `(a, b)` with `(b, a % b)`. For `a < b` the
first entry is `0`, matching the convention `a / b = [0; q₁, q₂, …]`. -/
def partQuots : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, b + 1 => (a / (b + 1)) :: partQuots (b + 1) (a % (b + 1))
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/-- The partial quotients occurring after the leading `⌊a/b⌋`; these are the ones Zaremba's
conjecture bounds. -/
def tailQuots (a b : ℕ) : List ℕ :=
  (partQuots a b).tail

/-- `n` is *`A`-good* when some numerator coprime to `n` has all partial quotients at most `A`. -/
def IsGood (A n : ℕ) : Prop :=
  ∃ a : ℕ, a < n ∧ Nat.Coprime a n ∧ ∀ q ∈ tailQuots a n, q ≤ A

/-! ## Challenges -/

/-- **Zaremba's conjecture.** Every denominator is `5`-good. -/
theorem zaremba (n : ℕ) (hn : 0 < n) : IsGood 5 n := by
  sorry

/-- The weak form: *some* absolute bound works, uniformly in `n`. Even this is open, and it is the
statement that quasi-Monte-Carlo applications actually need. -/
theorem zaremba_weak : ∃ A : ℕ, ∀ n : ℕ, 0 < n → IsGood A n := by
  sorry

/-- Hensley's sharpening: `A = 2` suffices for all sufficiently large `n`. The bound `2` is best
possible, since `IsGood 1` fails for all but finitely many `n` (only Fibonacci-like denominators
have all partial quotients equal to `1`). -/
theorem hensley : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsGood 2 n := by
  sorry

open scoped Classical in
/-- Bourgain–Kontorovich: the `A`-good denominators have density one for some absolute `A`. This
is a theorem, and the strongest thing currently known in the direction of the conjecture. -/
theorem bourgain_kontorovich :
    ∃ A : ℕ, Filter.Tendsto
      (fun N : ℕ => (((Finset.range N).filter (fun n => IsGood A n)).card : ℝ) / (N : ℝ))
      Filter.atTop (nhds 1) := by
  sorry

/-! ## Sanity checks

These pin down `partQuots` so that a solution cannot satisfy the challenges by exploiting a
mis-stated definition.
-/

/-- The partial quotients of a fraction reconstruct it: folding the continued fraction back gives
`a / b` in lowest terms. -/
theorem partQuots_spec (a b : ℕ) (hb : 0 < b) (hab : Nat.Coprime a b) :
    ((partQuots a b).foldr (fun q r => (q : ℚ) + (if r = 0 then 0 else 1 / r)) 0)
      = (a : ℚ) / b := by
  sorry

/-- The expansion terminates, and its length is the number of Euclidean division steps. -/
theorem partQuots_length_pos (a b : ℕ) (hb : 0 < b) : 0 < (partQuots a b).length := by
  sorry

/-- A worked instance: `1/2 = [0; 2]`. -/
theorem partQuots_one_two : partQuots 1 2 = [0, 2] := by
  sorry

/-- Denominators that are `1`-good are exactly the ones with a Fibonacci numerator, which is why
Zaremba's constant cannot be taken below `2`. -/
theorem not_isGood_one : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬IsGood 1 n := by
  sorry

end Zaremba
