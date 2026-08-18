/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# The Chowla and Sarnak conjectures

Entry #22 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Both conjectures say that the Liouville function `λ` (equivalently the Möbius function `μ`) is
"random": it correlates with nothing. Chowla asks for no correlation with shifts of itself;
Sarnak asks for no correlation with any *deterministic* sequence, meaning one produced by a
topological dynamical system of zero entropy. Tao proved the logarithmically-averaged two-point
case of Chowla, and Chowla is known to imply Sarnak.
-/

@[expose] public section

namespace Chowla

open Filter Topology

/-- The Liouville function `λ n = (-1) ^ Ω n`, where `Ω n` counts prime factors with multiplicity.
It is the completely multiplicative function taking value `-1` at every prime. -/
def liouville (n : ℕ) : ℤ :=
  (-1) ^ ArithmeticFunction.cardFactors n

/-! ## Chowla's conjecture -/

/-- The `k`-point correlation average of the Liouville function along the shifts `h`, up to `N`. -/
noncomputable def correlation {k : ℕ} (h : Fin k → ℕ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, ∏ i, (liouville (n + h i) : ℝ)) / N

/-- **Chowla's conjecture.** For any number of distinct shifts, the Liouville function has
vanishing correlation: `λ` looks like a random `±1` sequence to every finite window. -/
theorem chowla {k : ℕ} (hk : 0 < k) (h : Fin k → ℕ) (hinj : Function.Injective h) :
    Tendsto (correlation h) atTop (𝓝 0) := by
  sorry

/-- The two-point case `k = 2`, the first genuinely open instance: `λ(n) λ(n+1)` averages to zero.
Tao proved the logarithmically-averaged version of exactly this statement. -/
theorem chowla_two (h : ℕ) (hh : 0 < h) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, (liouville n * liouville (n + h) : ℝ)) / N)
      atTop (𝓝 0) := by
  sorry

/-- The one-point case `k = 1` is *not* open: it is equivalent to the prime number theorem, and so
is a warm-up rather than a challenge. -/
theorem chowla_one :
    Tendsto (fun N => (∑ n ∈ Finset.range N, (liouville n : ℝ)) / N) atTop (𝓝 0) := by
  sorry

/-- Tao's theorem: the logarithmically averaged two-point Chowla conjecture holds. Unlike the
statements above this one is known, and is the state of the art on Chowla. -/
theorem chowla_two_logarithmic (h : ℕ) (hh : 0 < h) :
    Tendsto
      (fun N => (∑ n ∈ Finset.Ico 1 N, (liouville n * liouville (n + h) : ℝ) / n) /
        Real.log N)
      atTop (𝓝 0) := by
  sorry

/-! ## Sarnak's conjecture

A sequence is *deterministic* when it is produced by sampling a continuous observable along an
orbit of a topological dynamical system with zero entropy. Sarnak's conjecture is that the Möbius
function is asymptotically orthogonal to every such sequence.
-/

/-- A sequence `a : ℕ → ℝ` is *deterministic* if it arises as `a n = f (T^[n] x)` for a continuous
observable `f` on a compact metric space carrying a zero-entropy continuous self-map `T`. -/
def IsDeterministic (a : ℕ → ℝ) : Prop :=
  ∃ (X : Type) (_ : MetricSpace X) (_ : CompactSpace X) (T : X → X) (f : X → ℝ) (x : X),
    Continuous T ∧ Continuous f ∧ Dynamics.coverEntropy T Set.univ = 0 ∧
      ∀ n, a n = f (T^[n] x)

/-- **Sarnak's conjecture.** The Möbius function is asymptotically orthogonal to every
deterministic sequence. -/
theorem sarnak (a : ℕ → ℝ) (ha : IsDeterministic a) :
    Tendsto (fun N => (∑ n ∈ Finset.range N, (ArithmeticFunction.moebius n : ℝ) * a n) / N)
      atTop (𝓝 0) := by
  sorry

/-- Chowla implies Sarnak. This implication is a theorem (Sarnak; Tao), so it is the challenge on
this page most likely to be within reach: it reduces one open problem to the other rather than
resolving either. -/
theorem chowla_imp_sarnak
    (hchowla : ∀ (k : ℕ), 0 < k → ∀ h : Fin k → ℕ, Function.Injective h →
      Tendsto (correlation h) atTop (𝓝 0)) :
    ∀ a : ℕ → ℝ, IsDeterministic a →
      Tendsto (fun N => (∑ n ∈ Finset.range N, (ArithmeticFunction.moebius n : ℝ) * a n) / N)
        atTop (𝓝 0) := by
  sorry

/-- The Liouville and Möbius functions agree on squarefree numbers, which is why the two
conjectures may be stated with either. -/
theorem liouville_eq_moebius_of_squarefree (n : ℕ) (hn : Squarefree n) :
    liouville n = ArithmeticFunction.moebius n := by
  sorry

end Chowla
