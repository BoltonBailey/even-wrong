/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!
# Falconer's distance conjecture

Entry #45 of [Evan Daniel's open-problem tier list](https://github.com/evand/open-math-problems),
listed there without a Lean statement.

Falconer's conjecture is the continuous analogue of the Erdős distinct distances problem: a compact
set in `ℝ^d` of Hausdorff dimension greater than `d / 2` should determine a set of distances of
positive Lebesgue measure. The threshold `d / 2` is sharp, as Falconer's own example shows. The best
known threshold in the plane is `5/4` (Guth–Iosevich–Ou–Wang), against the conjectured `1`.

Mathlib supplies `dimH`, so the statement transcribes directly.
-/

@[expose] public section

namespace Falconer

open MeasureTheory
open scoped ENNReal

variable {d : ℕ}

/-- The *distance set* of `E`: all distances realised between pairs of points of `E`. -/
def distanceSet (E : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => dist p.1 p.2) '' (E ×ˢ E)

/-! ## Challenges -/

/-- **Falconer's distance conjecture.** A compact set of Hausdorff dimension exceeding `d / 2`
has a distance set of positive Lebesgue measure. -/
theorem falconer (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d))) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞) / 2 < dimH E) : volume (distanceSet E) ≠ 0 := by
  sorry

/-- The stronger form, also conjectured: above the threshold the distance set even has nonempty
interior. -/
theorem falconer_interior (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d))) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞) / 2 < dimH E) : (interior (distanceSet E)).Nonempty := by
  sorry

/-- The planar case `d = 2`, the flagship: dimension greater than `1` should suffice. -/
theorem falconer_plane (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : IsCompact E)
    (hdim : 1 < dimH E) : volume (distanceSet E) ≠ 0 := by
  sorry

/-- The Guth–Iosevich–Ou–Wang theorem, the current planar record: dimension greater than `5/4`
suffices. Unlike the statements above this one is known. -/
theorem guth_iosevich_ou_wang (E : Set (EuclideanSpace ℝ (Fin 2))) (hE : IsCompact E)
    (hdim : 5 / 4 < dimH E) : volume (distanceSet E) ≠ 0 := by
  sorry

/-- The threshold is sharp: for every `d ≥ 2` there is a compact set of Hausdorff dimension exactly
`d / 2` whose distance set is Lebesgue-null. This is Falconer's construction, and it is the "even
wrong" guardrail — it rules out lowering the exponent. -/
theorem exists_sharp_example (hd : 2 ≤ d) :
    ∃ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E ∧ dimH E = (d : ℝ≥0∞) / 2 ∧
      volume (distanceSet E) = 0 := by
  sorry

/-- The pinned version (Peres–Schlag, Liu): the conclusion should hold for the distances from a
single point of `E`, for at least one such point. -/
theorem falconer_pinned (hd : 2 ≤ d) (E : Set (EuclideanSpace ℝ (Fin d))) (hE : IsCompact E)
    (hdim : (d : ℝ≥0∞) / 2 < dimH E) :
    ∃ x ∈ E, volume ((fun y => dist x y) '' E) ≠ 0 := by
  sorry

/-- Below dimension `1` the conclusion certainly fails, since the distance set is then a Lipschitz
image of a set of dimension less than `1`. This fixes the direction of the inequality. -/
theorem volume_distanceSet_eq_zero_of_dimH_lt_one
    (E : Set (EuclideanSpace ℝ (Fin d))) (hdim : dimH E < 1 / 2) :
    volume (distanceSet E) = 0 := by
  sorry

end Falconer
