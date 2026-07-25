# Even Wrong

NOTE: This repo is a work-in-progress, I will have to do more work to understand the security concerns behind this approach to library development before I accept PRs.

---

This is a repository for Human-AI collaboration in Lean 4, somewhat inspired by projects like [merely-true](https://github.com/merely-true/merely-true) and [lean-pool](https://github.com/Vilin97/lean-pool), and roughly following some of the ideas in [this post](https://thequantummilkman.substack.com/p/thoughts-on-ai-formal-codebase-maintenance).

In this repository, we draw the line against allowing statements that are "not even wrong": All statements must be well-formed claims in Lean. This is less restrictive than the repositories mentioned above, in that "even wrong" statements are allowed, in the sense that we allow statements with a `sorry`d proof, without a programmatic check that these statements are, in fact, true. But it's also perhaps more restrictive than a project like TauCeti, where the idea is that the spec is informal.

## Structure

- [`EvenWrong/`](EvenWrong/) — a mostly-human library of mathematical statements and definitions
- [`NotWrong/`](NotWrong/) — a mostly-AI library of solutions.
- comparator/ -      comparator configs describing solutions
- scripts/  -        metric + check scripts used by CI

Updates to `NotWrong` essentially take the form of an optimization problem that AIs can be directed to solve, where the following priorities in decreasing order of importance

1. Make sure that any lean code in the folder passes standard CI / Linter checks.
1. Satisfy as many of the comparator checks as possible (i.e. prove as many theorems as possible)
1. Make sure that the code quality is as good as possible, according to a particular programmatic metric defined in the scripts folder.

