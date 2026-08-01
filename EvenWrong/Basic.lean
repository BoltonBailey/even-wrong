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

Challenges are filed by subject: `EvenWrong.Combinatorics.*`, `EvenWrong.Computability.*`
and `EvenWrong.Games.*`. `Games` collects both multi-player strategic settings and the
equity of single-player games under optimal play. Only this module and `EvenWrong.Demo`
live at the root.
-/

@[expose] public section
