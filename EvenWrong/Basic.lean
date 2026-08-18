/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

/-!
# EvenWrong.Basic

Root documentation module for the `EvenWrong` library.

`EvenWrong` is the **mostly-human** half of this repository. It collects
mathematical *statements* (challenges). Statements here are allowed to:

* carry `sorry`d proofs that nobody has completed yet, and
* be *outright false* — "even wrong" statements are permitted (see
  `EvenWrong.Demo.two_plus_two`). A false statement simply never receives a
  solution in `NotWrong`.

Each public theorem in an `EvenWrong.*` module is a *challenge* that the
`NotWrong` library may try to discharge in a
[comparator](https://github.com/leanprover/comparator)-friendly way. See the
repository `README.md` for the full workflow.

## Organization

Challenges are filed by subject: `EvenWrong.Analysis.*`, `EvenWrong.Combinatorics.*`,
`EvenWrong.Complexity.*`, `EvenWrong.Computability.*`, `EvenWrong.Games.*`,
`EvenWrong.GroupTheory.*`, `EvenWrong.NumberTheory.*`, `EvenWrong.Probability.*` and
`EvenWrong.SetTheory.*`. `Games` collects both multi-player strategic settings and the
equity of single-player games under optimal play. `Complexity` shares a machine model,
fixed once in `EvenWrong.Complexity.Basic`. Only this module and `EvenWrong.Demo` live at
the root.

Many of the challenges transcribe entries from the [open problems tier
list](https://github.com/evand/open-math-problems) that had no Lean statement anywhere —
neither in Mathlib nor in DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures). Each such module
names its entry number in its docstring. These are open problems, so their challenges are not
expected to be discharged; what they buy is a well-formed statement to argue about, and the
smaller lemmas alongside them (known special cases, sharpness examples, sanity checks on the
definitions) are the parts a solution can realistically reach.
-/

@[expose] public section
