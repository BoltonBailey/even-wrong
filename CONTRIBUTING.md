# Contributing

This repository has two libraries with very different contribution rules. Read
the section for the one you are touching. The overall design is summarized in
the [README](README.md).

## Contributing to `EvenWrong` (statements / challenges)

`EvenWrong` is the human-curated collection of *statements* we would like to see
proven. It is intentionally permissive about correctness:

- Proofs may be `sorry`. In fact most new challenges will be pure `sorry`s.
- Statements may be **false** ("even wrong"). A false statement is harmless: it
  simply never receives a matching solution in `NotWrong`.
- You do not need to prove anything to add a challenge.

Guidelines:

1. Put each challenge in a module under `EvenWrong/` (e.g. `EvenWrong/MyTopic.lean`)
   and `import` it from [`EvenWrong.lean`](EvenWrong.lean).
2. Give every challenge a stable, descriptive, fully-qualified name. `NotWrong`
   and the `comparator/` configs refer to challenges **by name**, so renaming a
   challenge breaks its solution.
3. Prefer statements phrased with `Init`/`Mathlib` definitions. comparator
   matches a solution against a challenge by checking that the *statement* uses
   identical declarations, so a challenge built on bespoke local definitions can
   only be solved by a `NotWrong` file that reproduces those exact definitions.
4. When you add a challenge that you expect to be solvable, add a corresponding
   entry to a `comparator/*.json` config so solvers know what to target.

## Contributing to `NotWrong` (solutions)

`NotWrong` is the AI-maintained collection of *solutions*. Editing is meant to
be highly permissive (ultimately fully automated PR acceptance), gated only by
the objective checks below — enforced by
[`.github/workflows/notwrong-ci.yml`](.github/workflows/notwrong-ci.yml).

A PR to `NotWrong` is accepted if **all** of the following hold:

1. **Sorry-free & builds.** No `sorry`/`admit`; `lake build` succeeds and the
   standard Mathlib CI checks pass.
   - Local check: `python3 scripts/check_no_sorry.py`
2. **No regression in proven challenges.** It must not decrease the number of
   `EvenWrong` challenges that comparator accepts.
   - Local check: `COMPARATOR_BIN=... scripts/count_proven.sh`
3. **Progress or golf.** If the PR does *not* increase the number of proven
   challenges, it must *strictly decrease* the golf metric.
   - Local check: `python3 scripts/golf_metric.py`

### How to write a solution

To solve `EvenWrong.SomeTopic.foo`:

1. Create or edit a module under `NotWrong/` (mirroring the challenge's topic is
   conventional, e.g. `NotWrong/SomeTopic.lean`) and `import` it from
   [`NotWrong.lean`](NotWrong.lean).
2. **Do not** import `EvenWrong`. Re-declare the theorem under its exact
   fully-qualified name (`EvenWrong.SomeTopic.foo`) with the identical statement,
   and attach a real proof.
3. Ensure a `comparator/*.json` config pairs the challenge module with your
   solution module and lists the theorem name under `theorem_names`. Keep
   `permitted_axioms` to the intended set (default:
   `propext`, `Quot.sound`, `Classical.choice`).

See [`NotWrong/Demo.lean`](NotWrong/Demo.lean) and
[`comparator/Demo.json`](comparator/Demo.json) for a worked example.
