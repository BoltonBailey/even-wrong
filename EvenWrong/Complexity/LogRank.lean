/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The log-rank conjecture

Entry #77 of the [open-problem tier list](https://github.com/evand/open-math-problems), listed
there without a Lean statement.

Lovász and Saks conjectured that the deterministic communication complexity of a Boolean matrix is
polylogarithmic in its rank: `D(f) ≤ (log rank f) ^ O(1)`. The rank lower bound
`D(f) ≥ log rank f` is elementary, so the conjecture says the two measures are polynomially
related. The best upper bound is Lovett's `O(√rank · log rank)`, and the best lower bound is
Göös–Pitassi–Watson's `Ω((log rank)²)`, so the truth is not even known up to constants.

Communication complexity is not in Mathlib, so protocols are defined here as binary trees whose
internal nodes record whose turn it is and what that party announces.
-/

@[expose] public section

namespace LogRank

variable {X Y : Type*}

/-- A deterministic two-party communication protocol: a binary tree in which each internal node is
owned by Alice (who knows `x`) or Bob (who knows `y`) and is labelled by the bit its owner
announces. Leaves carry the output. -/
inductive Protocol (X Y : Type*) where
  /-- Output a value and stop. -/
  | leaf (b : Bool) : Protocol X Y
  /-- Alice announces `m x`; the protocol continues in the corresponding subtree. -/
  | alice (m : X → Bool) (l r : Protocol X Y) : Protocol X Y
  /-- Bob announces `m y`; the protocol continues in the corresponding subtree. -/
  | bob (m : Y → Bool) (l r : Protocol X Y) : Protocol X Y

/-- The function a protocol computes. -/
def Protocol.eval : Protocol X Y → X → Y → Bool
  | .leaf b, _, _ => b
  | .alice m l r, x, y => if m x then l.eval x y else r.eval x y
  | .bob m l r, x, y => if m y then l.eval x y else r.eval x y

/-- The cost of a protocol: the depth of the tree, that is, the worst-case number of bits
exchanged. -/
def Protocol.cost : Protocol X Y → ℕ
  | .leaf _ => 0
  | .alice _ l r => 1 + max l.cost r.cost
  | .bob _ l r => 1 + max l.cost r.cost

/-- The deterministic communication complexity of `f`: the least cost of a protocol computing it. -/
noncomputable def commComplexity (f : X → Y → Bool) : ℕ :=
  sInf {c | ∃ P : Protocol X Y, P.eval = f ∧ P.cost ≤ c}

/-- The communication matrix of `f`, over the rationals. -/
def commMatrix [Fintype X] [Fintype Y] (f : X → Y → Bool) : Matrix X Y ℚ :=
  Matrix.of fun x y => if f x y then 1 else 0

/-- The rank of the communication matrix. -/
noncomputable def commRank [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y → Bool) : ℕ :=
  (commMatrix f).rank

/-! ## Challenges -/

/-- **The log-rank conjecture.** Deterministic communication complexity is polylogarithmic in the
rank of the communication matrix. -/
theorem log_rank :
    ∃ c C : ℝ, 0 < C ∧ ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (f : X → Y → Bool),
      (commComplexity f : ℝ) ≤ C * (Real.logb 2 (commRank f + 1)) ^ c := by
  sorry

/-- The rank lower bound, the elementary half of the relationship: a protocol of cost `c` cuts the
communication matrix into at most `2 ^ c` monochromatic rectangles, so the rank is at most `2 ^ c`.
This is provable, and is the natural first target. -/
theorem logb_commRank_le_commComplexity (X Y : Type) [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y → Bool) :
    Real.logb 2 (commRank f) ≤ commComplexity f := by
  sorry

/-- The trivial upper bound in terms of the rank; the conjecture asks to improve it to
polylogarithmic. -/
theorem commComplexity_le_commRank (X Y : Type) [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (f : X → Y → Bool) :
    commComplexity f ≤ commRank f + 1 := by
  sorry

/-- Lovett's theorem, the current record upper bound: `D(f) = O(√rank · log rank)`. -/
theorem lovett :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
      (f : X → Y → Bool),
      (commComplexity f : ℝ) ≤ C * Real.sqrt (commRank f) * Real.logb 2 (commRank f + 1) := by
  sorry

/-- Göös–Pitassi–Watson: the exponent in the conjecture must be at least `2`, so the sharper guess
`D(f) = O(log rank)` is false. This is the "even wrong" guardrail on the exponent. -/
theorem goos_pitassi_watson :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ (X Y : Type) (_ : Fintype X) (_ : Fintype Y)
      (_ : DecidableEq X) (_ : DecidableEq Y) (f : X → Y → Bool),
      N ≤ commRank f ∧ c * (Real.logb 2 (commRank f)) ^ 2 ≤ (commComplexity f : ℝ) := by
  sorry

/-- On a finite domain the infimum defining `commComplexity` is attained, since Alice can always
announce all of `x`. This fixes the meaning of the `sInf`. -/
theorem exists_protocol_of_commComplexity (hX : Finite X) (hY : Finite Y) (f : X → Y → Bool) :
    ∃ P : Protocol X Y, P.eval = f ∧ P.cost = commComplexity f := by
  sorry

/-- The equality function on `n`-bit strings has full rank and communication complexity `n + 1`:
the standard example where the two measures are exponentially far apart in the *other* direction
from what the conjecture bounds. -/
theorem commComplexity_eq_fun (n : ℕ) :
    commComplexity (fun x y : Fin n → Bool => decide (x = y)) = n + 1 := by
  sorry

end LogRank
