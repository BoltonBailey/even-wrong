#!/usr/bin/env bash
#
# count_proven.sh — count the EvenWrong challenges that NotWrong proves.
#
# For every config in comparator/*.json this runs `comparator`. If comparator
# accepts a config, all of that config's `theorem_names` count as proven. The
# script prints the running result per config and a final total to stdout, and
# exits non-zero if any config fails (so it can gate CI).
#
# comparator is not a normal library dependency: it needs `landrun`,
# `lean4export`, and (on current kernels) a `systemd-run` wrapper. See
# https://github.com/leanprover/comparator. Point this script at the binary and
# helpers with:
#
#   COMPARATOR_BIN       path to the comparator binary            (required)
#   COMPARATOR_RUN       command prefix used to invoke it
#                        (default: "lake env"; on Linux the comparator README
#                        recommends a `systemd-run ... -- bash -c` wrapper)
#   COMPARATOR_LANDRUN   forwarded to comparator (see its README)
#   COMPARATOR_LEAN4EXPORT  forwarded to comparator (see its README)
#
# Example:
#   COMPARATOR_BIN=/path/to/comparator scripts/count_proven.sh
#
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
CONFIG_DIR="$REPO_ROOT/comparator"
RUN_PREFIX="${COMPARATOR_RUN:-lake env}"

if [[ -z "${COMPARATOR_BIN:-}" ]]; then
  echo "error: set COMPARATOR_BIN to the path of the comparator binary" >&2
  echo "       (see https://github.com/leanprover/comparator)" >&2
  exit 2
fi

shopt -s nullglob
configs=("$CONFIG_DIR"/*.json)
if [[ ${#configs[@]} -eq 0 ]]; then
  echo "no comparator configs found in $CONFIG_DIR"
  echo "total proven: 0"
  exit 0
fi

count_theorems() { # $1 = config path -> number of theorem_names entries
  python3 -c 'import json,sys; print(len(json.load(open(sys.argv[1])).get("theorem_names", [])))' "$1"
}

total=0
failed=0
for cfg in "${configs[@]}"; do
  name="$(basename "$cfg")"
  if (cd "$REPO_ROOT" && $RUN_PREFIX "$COMPARATOR_BIN" "$cfg"); then
    n="$(count_theorems "$cfg")"
    total=$((total + n))
    echo "PASS  $name  (+$n)"
  else
    failed=$((failed + 1))
    echo "FAIL  $name"
  fi
done

echo "total proven: $total"
if [[ $failed -gt 0 ]]; then
  echo "$failed config(s) failed" >&2
  exit 1
fi
