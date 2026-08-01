/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

/-!
# NotWrong.Basic

Root documentation module for the `NotWrong` library.

`NotWrong` is the **mostly-AI** half of this repository. It contains *solutions*:
real, `sorry`-free proofs of statements posed in `EvenWrong`, written in a
[comparator](https://github.com/leanprover/comparator)-friendly format.

"Comparator-friendly" means: for each solved challenge, `NotWrong` declares a
theorem with **the exact same fully-qualified name and statement** as the
`EvenWrong` challenge, but with a genuine proof attached. `NotWrong` modules do
**not** import `EvenWrong`; each side is built independently and `comparator`
checks that the two declarations are identical up to their proof terms (see the
`comparator/` directory).

Solution modules mirror the topic path of the challenges they solve, so
`EvenWrong.Games.ProblemFourteen` is answered by
`NotWrong.Games.ProblemFourteen`.

Invariants for everything under `NotWrong/`:

* no `sorry` / `admit`, and the standard Mathlib CI checks pass;
* the set of `EvenWrong` challenges proven here never shrinks;
* changes that do not add a newly-proven challenge must improve the golf metric
  (see `scripts/golf_metric.sh` and the `README.md`).
-/

@[expose] public section
