# Even Wrong

This is a repository for Human-AI collaboration in Lean 4, somewhat inspired by projects like [merely-true](https://github.com/merely-true/merely-true) and [lean-pool](https://github.com/Vilin97/lean-pool), and roughly following some of the ideas in [this post](https://thequantummilkman.substack.com/p/thoughts-on-ai-formal-codebase-maintenance).

Unlike the repositories mentioned above, in this repository, *even wrong* statements are allowed. However, we do not allow statements that are "not even wrong". All statements must be well-formed claims in Lean, with at least a `sorry`d proof.

## Structure

The repository is split into two Lean libraries, declared in [lakefile.toml](lakefile.toml):

- [`EvenWrong/`](EvenWrong/) — a **mostly-human** library of mathematical *statements* ("challenges"). Statements here are allowed to carry `sorry`d proofs.
- [`NotWrong/`](NotWrong/) — a **mostly-AI** library of *solutions*: real, `sorry`-free proofs of statements posed in `EvenWrong`, written in a [comparator](https://github.com/leanprover/comparator)-friendly format.

The link between the two is the [`comparator/`](comparator/) directory: each `*.json` there is a comparator configuration pairing a challenge module with its solution module and listing the theorem names that should match.

```
EvenWrong/        challenges  (sorry allowed; may be false)
NotWrong/         solutions   (sorry-free; comparator-friendly)
comparator/       *.json configs pairing challenges <-> solutions
scripts/          metric + check scripts used by CI
```

### Comparator-friendly format

For each solved challenge, `NotWrong` declares a theorem with **the exact same fully-qualified name and statement** as the `EvenWrong` challenge, but with a genuine proof attached. `NotWrong` modules do **not** import `EvenWrong`; the two sides are built independently, and [comparator](https://github.com/leanprover/comparator) checks that the declarations are identical up to their proof terms and that the solution uses only permitted axioms.

Concretely, the worked example in this repo is:

| | challenge | solution |
|---|---|---|
| module | [`EvenWrong/Demo.lean`](EvenWrong/Demo.lean) | [`NotWrong/Demo.lean`](NotWrong/Demo.lean) |
| `EvenWrong.Demo.nat_add_comm` | `:= by sorry` | `:= Nat.add_comm n m` |
| `EvenWrong.Demo.two_plus_two` | `2 + 2 = 5 := by sorry` | *(false — no solution)* |

paired by [`comparator/Demo.json`](comparator/Demo.json).

## Contribution policy

See [CONTRIBUTING.md](CONTRIBUTING.md) for details. In short:

`EvenWrong` is human-curated; add statements you would like to see proven (`sorry` and false statements welcome).

`NotWrong` allows highly permissive editing (intended to be fully automated acceptance of PRs) subject to the following constraints, enforced by [`.github/workflows/notwrong-ci.yml`](.github/workflows/notwrong-ci.yml):

- PRs to `NotWrong` must be sorry-free and pass the standard Mathlib CI checks.
- PRs to `NotWrong` must not decrease the number of statements from `EvenWrong` that are successfully proven within comparator.
- PRs to `NotWrong` that do not increase the number of proven statements from `EvenWrong` must successfully golf `NotWrong` according to the metric below.

### The golf metric

The golf metric is the total number of **non-whitespace characters** across every `*.lean` file under `NotWrong/`, **after stripping Lean comments**. Comments are stripped first so that golfing never creates pressure to delete documentation. Lower is better.

It is computed by [`scripts/golf_metric.py`](scripts/golf_metric.py):

```sh
python3 scripts/golf_metric.py        # prints a single integer
```

### Counting proven challenges

The authoritative count of proven challenges comes from running comparator over every config in `comparator/`:

```sh
COMPARATOR_BIN=/path/to/comparator scripts/count_proven.sh
```

comparator is not an ordinary library dependency — it needs [`landrun`](https://github.com/Zouuup/landrun) and [`lean4export`](https://github.com/leanprover/lean4export) (and, on current kernels, a `systemd-run` wrapper). See its [README](https://github.com/leanprover/comparator) and the header of [`scripts/count_proven.sh`](scripts/count_proven.sh). Because this needs a suitable Linux host, the comparator job in CI is provided as a documented, commented-out template; the build and the sorry-free / golf-metric guards run on the standard runner.

## Local development

```sh
lake exe cache get   # fetch the Mathlib build cache
lake build           # builds the EvenWrong and NotWrong libraries

python3 scripts/check_no_sorry.py    # NotWrong must be sorry-free
python3 scripts/golf_metric.py       # current golf metric
```

## GitHub configuration

To set up the GitHub repository:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

