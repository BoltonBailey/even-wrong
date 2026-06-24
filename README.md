# Even Wrong

This is a repository for Human-AI collaboration in Lean4, somewhat inspired by projects like [merely-true](https://github.com/merely-true/merely-true) and [lean-pool](https://github.com/Vilin97/lean-pool), and roughly following some of the ideas in [this post](https://thequantummilkman.substack.com/p/thoughts-on-ai-formal-codebase-maintenance).

Unlike the repositories mentioned above, in this repository it is even allowed to submit statements that are wrong (i.e. that have `sorry`d proofs that may not be possible to create because they reflect false statements). 

## TODO Structure

The repository is (should be) structured into two subdirectories

- `/EvenWrong`, a mostly-human constructed library allowing `sorry`d statements and proofs.
- `/NotWrong`, a mostly-AI constructed library that contains proofs of statements in the `/EvenWrong` folder, in a [comparator](https://github.com/leanprover/comparator)-friendly format.

We allow highly permissive editing of `/NotWrong` (i.e. fully automated acceptance of PRs) subject to the following constraints:

- PRs to `/NotWrong` must be sorry-free and pass the standard mathlib CI checks
- PRs to `/NotWrong` must not decrease the number of statements from `/EvenWrong` that are successfully proven within comparator.
- PRs to `/NotWrong` that do not increase the number of proven statements from `/EvenWrong` must successfully golf `/NotWrong` according to a specified metric.


## GitHub configuration (TODO)

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
