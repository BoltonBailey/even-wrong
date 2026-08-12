/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib

/-!

# Von Neumann's fair coin procedure

This file contains some definitions and sorrys related to procedures for
simulating a fair coin with an unfair coin.

TODO: The file is a work in progress,
most of the statements are actually not the statements I am really interested in
due to degeneracy of different permutations of essentially the same procedure.

-/

@[expose] public section

namespace VonNeumannCoin

open scoped List

/-! ## Procedures -/

/-- A deterministic procedure: given the flips seen so far (`true` = heads), either return the fair
bit it has decided on, or `none`, meaning "flip again". -/
def Strategy : Type := List Bool → Option Bool

/--
A strategy is only valid, if when it returns a value on some word,
it returns that value on all extensions of that word.
-/
def Strategy.valid (s : Strategy) : Prop :=
  ∀ w b, s w = some b → ∀ v, w <+: v → s v = some b

/-! ## Probabilities and costs -/

/-- The probability that a coin of bias `p` (probability `p` of `true`) produces exactly the word
`w`, i.e. `p ^ (#heads) * (1 - p) ^ (#tails)`. -/
noncomputable def weight (p : ℝ) (w : List Bool) : ℝ :=
  p ^ w.count true * (1 - p) ^ w.count false

/-- Reordering a word does not change its probability: only the head and tail counts matter. -/
theorem weight_of_perm {p : ℝ} {v w : List Bool} (h : v ~ w) : weight p v = weight p w := by
  simp only [weight, h.count_eq]

/-- The probability that `s` has answered `b` after exactly `n` flips of a coin of bias `p`. For a
valid strategy this is nondecreasing in `n`, since answers are never retracted. -/
noncomputable def outputProbAt (s : Strategy) (p : ℝ) (b : Bool) (n : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, if s (List.ofFn x) = some b then weight p (List.ofFn x) else 0

/-- The probability that `s`, run against a coin of bias `p`, eventually answers `b`: the limit of
`outputProbAt` as the number of flips goes to infinity. -/
noncomputable def outputProb (s : Strategy) (p : ℝ) (b : Bool) : ℝ :=
  Filter.limUnder Filter.atTop (outputProbAt s p b)

/-- The probability that `s`, run against a coin of bias `p`, has answered within `n` flips. -/
noncomputable def haltWithinProb (s : Strategy) (p : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → Bool, if (s (List.ofFn x)).isSome then weight p (List.ofFn x) else 0

/-- The probability that `s`, run against a coin of bias `p`, answers at all. -/
noncomputable def haltProb (s : Strategy) (p : ℝ) : ℝ :=
  Filter.limUnder Filter.atTop (haltWithinProb s p)

/-- The probability that `s`, run against a coin of bias `p`, answers on flip `n` exactly: the
distribution of the number of flips used. -/
noncomputable def haltAtProb (s : Strategy) (p : ℝ) : ℕ → ℝ
  | 0 => haltWithinProb s p 0
  | n + 1 => haltWithinProb s p (n + 1) - haltWithinProb s p n

/-- The expected value of `f` applied to the number of flips that `s` uses against a coin of bias
`p`, where `f` is an arbitrary cost function. -/
noncomputable def expectedCost (s : Strategy) (p : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, f n * haltAtProb s p n

/-- The expected number of flips that `s` uses against a coin of bias `p`. -/
noncomputable def expectedFlips (s : Strategy) (p : ℝ) : ℝ :=
  expectedCost s p (fun n => (n : ℝ))

/-- A procedure is *fair* when, for **every** bias `p ∈ (0, 1)`, it halts almost surely and its
output is an unbiased bit. The bias is unknown, so fairness is required uniformly in `p`. -/
def Fair (s : Strategy) : Prop :=
  ∀ p ∈ Set.Ioo (0 : ℝ) 1, outputProb s p true = 1 / 2 ∧ outputProb s p false = 1 / 2

/-- The binary entropy of `p`, in bits. -/
noncomputable def binEnt (p : ℝ) : ℝ :=
  -p * Real.logb 2 p - (1 - p) * Real.logb 2 (1 - p)

/-! ## Von Neumann's procedure and its extensions -/

/-- Von Neumann's procedure: read the flips in pairs, halt on the first pair whose two flips
differ, and output the first flip of that pair. -/
def vonNeumann : List Bool → Option Bool
  | a :: b :: rest => if a == b then vonNeumann rest else some a
  | _ => none

/-- The literal "any multiple of 2" reading: read the flips in blocks of `2 * k`, halt on the first
block that is `k` copies of some `a` followed by `k` copies of `!a`, and output `a`. Fair for every
`k ≥ 1`, and equal to `vonNeumann` at `k = 1`. -/
def blockVonNeumann (k : ℕ) (w : List Bool) : Option Bool :=
  if h : 0 < k ∧ 2 * k ≤ w.length then
    if w.take (2 * k) = List.replicate k true ++ List.replicate k false then some true
    else if w.take (2 * k) = List.replicate k false ++ List.replicate k true then some false
    else blockVonNeumann k (w.drop (2 * k))
  else none
termination_by w.length
decreasing_by
  obtain ⟨hk, hw⟩ := h
  simp only [List.length_drop]
  omega

/-- The state of the extended procedure: `st[i]` is the value of the pending block of `2 ^ i`
flips, if one is currently held at level `i`. Levels hold at most one block each, so the state
after `n` flips has a block exactly at the set bits of `n`. -/
abbrev State : Type := List (Option Bool)

/-- One step of the extended procedure: either the new state, or the fair bit it halted with. -/
inductive Step where
  /-- The procedure is still running, in state `st`. -/
  | running (st : State) : Step
  /-- The procedure halted with the fair bit `b`. -/
  | halted (b : Bool) : Step
  deriving Repr

/-- Carry a block of value `b` into level `0` of the state, merging upwards like a binary counter.
Two blocks of the same size that agree merge into a block of twice the size; two that disagree are
the `HH…TT…` pattern, and the procedure halts with the value of the *earlier* block. -/
def carry (b : Bool) : State → Step
  | [] => Step.running [some b]
  | none :: st => Step.running (some b :: st)
  | some a :: st =>
    if a == b then
      match carry b st with
      | Step.running st' => Step.running (none :: st')
      | Step.halted c => Step.halted c
    else
      Step.halted a

/-- Feed a whole word to the extended procedure. -/
def run (w : List Bool) : Step :=
  w.foldl (fun step b =>
    match step with
    | Step.running st => carry b st
    | Step.halted c => Step.halted c) (Step.running [])

/-- The recursive (power-of-two) extension of von Neumann's procedure: a matched pair `HH` is one
flip of a derived coin, so run von Neumann's trick on the derived flips, and on *their* matched
pairs, and so on. Halts on `HT`, `TH`, `HHTT`, `TTHH`, `HHHHTTTT`, … -/
def extendedVonNeumann (w : List Bool) : Option Bool :=
  match run w with
  | Step.halted b => some b
  | Step.running _ => none

/-! ## Sanity checks -/

section Examples

/-- `vonNeumann` halts on `HT` with `H`. -/
example : vonNeumann [true, false] = some true := by decide

/-- `vonNeumann` does not halt on `HH`. -/
example : vonNeumann [true, true] = none := by decide

/-- `extendedVonNeumann` agrees with `vonNeumann` on the first pair. -/
example : extendedVonNeumann [false, true] = some false := by decide

/-- `extendedVonNeumann` halts on `HHTT`, outputting the first result. -/
example : extendedVonNeumann [true, true, false, false] = some true := by decide

/-- `extendedVonNeumann` does not halt on `HHHH`; it is holding one block of size `4`. -/
example : extendedVonNeumann [true, true, true, true] = none := by decide

/-- `extendedVonNeumann` halts on `HHHHTTTT`, where `vonNeumann` is still flipping. -/
example :
    extendedVonNeumann [true, true, true, true, false, false, false, false] = some true := by
  decide

end Examples

/-! ## Challenges: validity and fairness -/

/-- Von Neumann's procedure never changes its mind. -/
theorem vonNeumann_valid : Strategy.valid vonNeumann := by
  sorry

/-- The block procedures never change their minds. -/
theorem blockVonNeumann_valid (k : ℕ) : Strategy.valid (blockVonNeumann k) := by
  sorry

/-- The power-of-two extension never changes its mind. -/
theorem extendedVonNeumann_valid : Strategy.valid extendedVonNeumann := by
  sorry

/-- A sufficient condition for fairness, and the reason all of these procedures work: an
involution `σ` on words that permutes each word (hence preserves its probability, whatever `p` is)
while swapping the output bit, pairs up the `H`-halting words with the `T`-halting ones. -/
theorem fair_of_symmetry (s : Strategy) (σ : List Bool → List Bool) (hσ : Function.Involutive σ)
    (hperm : ∀ w, σ w ~ w) (hswap : ∀ w b, s w = some b → s (σ w) = some (!b))
    (hhalt : ∀ p ∈ Set.Ioo (0 : ℝ) 1, haltProb s p = 1) : Fair s := by
  sorry

/-- Von Neumann's procedure is fair. -/
theorem vonNeumann_fair : Fair vonNeumann := by
  sorry

/-- The power-of-two extension is fair. -/
theorem extendedVonNeumann_fair : Fair extendedVonNeumann := by
  sorry

/-- The "multiple of 2" procedures are fair as well, for every block size: `HH…TT…` and `TT…HH…`
are equally likely. So the ambiguity in the Wikipedia sentence is not about *correctness*. -/
theorem blockVonNeumann_fair (k : ℕ) (hk : 0 < k) : Fair (blockVonNeumann k) := by
  sorry

/-- At `k = 1`, the "multiple of 2" reading is exactly von Neumann's procedure. -/
theorem blockVonNeumann_one : blockVonNeumann 1 = vonNeumann := by
  sorry

/-! ## Challenges: expected number of flips -/

/-- Von Neumann's procedure uses `1 / (p * (1 - p))` flips on average: pairs succeed with
probability `2 * p * (1 - p)` and cost `2` flips each. -/
theorem expectedFlips_vonNeumann (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedFlips vonNeumann p = 1 / (p * (1 - p)) := by
  sorry

/-- The `k`-block procedure uses `k / (p * (1 - p)) ^ k` flips on average. -/
theorem expectedFlips_blockVonNeumann (k : ℕ) (hk : 0 < k) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedFlips (blockVonNeumann k) p = k / (p * (1 - p)) ^ k := by
  sorry

/-- Bigger fixed blocks are strictly worse, for every bias: the "any multiple of 2" reading buys
nothing, because `p * (1 - p) ≤ 1 / 4`. The recursive extension is the one that helps. -/
theorem expectedFlips_blockVonNeumann_lt (k : ℕ) (hk : 1 < k) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedFlips vonNeumann p < expectedFlips (blockVonNeumann k) p := by
  sorry

/-- The recursive extension strictly improves on von Neumann's procedure, for every bias: the
flips discarded by von Neumann on a matched pair are recycled. -/
theorem expectedFlips_extendedVonNeumann_lt (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedFlips extendedVonNeumann p < expectedFlips vonNeumann p := by
  sorry

/-- No fair procedure can decide in fewer than two flips: one flip carries no `p`-free fair bit. -/
theorem two_le_expectedFlips (s : Strategy) (hv : s.valid) (hs : Fair s) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) : 2 ≤ expectedFlips s p := by
  sorry

/-- The information-theoretic lower bound: extracting one fair bit costs at least `1 / binEnt p`
flips on average, since each flip supplies `binEnt p` bits of entropy. -/
theorem entropy_le_expectedFlips (s : Strategy) (hv : s.valid) (hs : Fair s) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) : 1 / binEnt p ≤ expectedFlips s p := by
  sorry

/-! ## Challenges: is the extension optimal?

The first question. Exactly one of the next two statements is true; a solution establishes one and
refutes the other. Note that optimality is demanded *uniformly in `p`*, which is what makes the
question non-vacuous: for a single known `p` one may tune the procedure to it. -/

/-- **The main challenge.** Among all fair procedures, the power-of-two extension minimises the
expected number of flips, simultaneously for every bias. -/
theorem extendedVonNeumann_optimal (s : Strategy) (hv : s.valid) (hs : Fair s) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedFlips extendedVonNeumann p ≤ expectedFlips s p := by
  sorry

/-- The negation of `extendedVonNeumann_optimal`: some fair procedure beats the extension at some
bias. -/
theorem exists_fair_expectedFlips_lt :
    ∃ s : Strategy, s.valid ∧ Fair s ∧ ∃ p ∈ Set.Ioo (0 : ℝ) 1,
      expectedFlips s p < expectedFlips extendedVonNeumann p := by
  sorry

/-- Weaker, and prior to both: is there a fair procedure that is optimal for *all* biases at once,
whether or not it is the one above?  A negative answer would say the trade-off between biases is
genuine and "the best procedure" is not well defined without fixing `p`. -/
theorem exists_uniformly_optimal :
    ∃ s : Strategy, s.valid ∧ Fair s ∧ ∀ t : Strategy, t.valid → Fair t →
      ∀ p ∈ Set.Ioo (0 : ℝ) 1, expectedFlips s p ≤ expectedFlips t p := by
  sorry

/-! ## Challenges: other functions of the number of flips

The second question. Expected flips is one cost among many; one might instead care about the
probability of finishing within a budget, or about `𝔼[N ^ 2]`, or about a discounted cost.
`extendedVonNeumann_haltWithinProb_le` is the strongest possible answer — stochastic dominance —
and it implies `extendedVonNeumann_minimizes_cost`. Again, exactly one of
`extendedVonNeumann_minimizes_cost` and `exists_fair_expectedCost_lt` is true. -/

/-- Stochastic dominance: for every budget `n` and every bias, no fair procedure is more likely
than the extension to have finished within `n` flips. -/
theorem extendedVonNeumann_haltWithinProb_le (s : Strategy) (hv : s.valid) (hs : Fair s) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    haltWithinProb s p n ≤ haltWithinProb extendedVonNeumann p n := by
  sorry

/-- Stochastic dominance implies optimality for every monotone cost function. -/
theorem expectedCost_le_of_haltWithinProb_le (s t : Strategy) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (h : ∀ n, haltWithinProb s p n ≤ haltWithinProb t p n) (f : ℕ → ℝ) (hf : Monotone f) :
    expectedCost t p f ≤ expectedCost s p f := by
  sorry

/-- The extension minimises `𝔼[f N]` for every monotone cost function `f`, at every bias. -/
theorem extendedVonNeumann_minimizes_cost (f : ℕ → ℝ) (hf : Monotone f) (s : Strategy)
    (hv : s.valid) (hs : Fair s) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    expectedCost extendedVonNeumann p f ≤ expectedCost s p f := by
  sorry

/-- The negation: the optimal procedure depends on which function of the flip count is being
minimised. -/
theorem exists_fair_expectedCost_lt :
    ∃ f : ℕ → ℝ, Monotone f ∧ ∃ s : Strategy, s.valid ∧ Fair s ∧ ∃ p ∈ Set.Ioo (0 : ℝ) 1,
      expectedCost s p f < expectedCost extendedVonNeumann p f := by
  sorry

/-! ## Challenges: how many procedures can be optimal at all?

A third question, about the shape of the whole trade-off: which procedures does *some* cost
function justify, and how many are there? Costs must be strictly monotone here, or the question
degenerates: under a constant cost every fair procedure ties (each halts almost surely, so
`𝔼[f N] = f 0`), and every fair procedure would be "potentially optimal".

Exactly one of `potentiallyOptimal_finite` and `potentiallyOptimal_infinite` is true, but beware
a second degeneracy: relabelling outputs along a symmetry as in `fair_of_symmetry` preserves both
fairness and the distribution of the number of flips, so a single optimal procedure carrying such
a symmetry already forces infinitude. `haltWithinProb_potentiallyOptimal_finite` is the version
that survives relabelling: procedures with equal `haltWithinProb` have equal `expectedCost` under
every cost function, so it asks whether only finitely many cost *behaviours* can be optimal. -/

/-- The cost function `f` makes `s` the best fair procedure: `s` is fair and minimises `𝔼[f N]`
among fair procedures, simultaneously for every bias. -/
def OptimalFor (f : ℕ → ℝ) (s : Strategy) : Prop :=
  s.valid ∧ Fair s ∧ ∀ t : Strategy, t.valid → Fair t →
    ∀ p ∈ Set.Ioo (0 : ℝ) 1, expectedCost s p f ≤ expectedCost t p f

/-- The procedures that some strictly monotone cost function makes optimal. -/
def potentiallyOptimal : Set Strategy :=
  {s | ∃ f : ℕ → ℝ, StrictMono f ∧ OptimalFor f s}

/-- The procedures that every strictly monotone cost function makes optimal.
`extendedVonNeumann_minimizes_cost` (with `extendedVonNeumann_valid` and
`extendedVonNeumann_fair`) would place `extendedVonNeumann` here. -/
def universallyOptimal : Set Strategy :=
  {s | ∀ f : ℕ → ℝ, StrictMono f → OptimalFor f s}

/-- Universally optimal procedures are potentially optimal: witness the cost `f n = n`. -/
theorem universallyOptimal_subset_potentiallyOptimal :
    universallyOptimal ⊆ potentiallyOptimal :=
  fun _ hs => ⟨_, Nat.strictMono_cast, hs _ Nat.strictMono_cast⟩

/-- Only finitely many procedures are potentially optimal. -/
theorem potentiallyOptimal_finite : potentiallyOptimal.Finite := by
  sorry

/-- The negation of `potentiallyOptimal_finite`: infinitely many procedures are potentially
optimal. -/
theorem potentiallyOptimal_infinite : potentiallyOptimal.Infinite := by
  sorry

/-- The relabelling-proof form of the question: among the potentially optimal procedures, are
there only finitely many halting profiles? -/
theorem haltWithinProb_potentiallyOptimal_finite :
    (haltWithinProb '' potentiallyOptimal).Finite := by
  sorry

end VonNeumannCoin
