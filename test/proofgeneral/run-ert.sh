#!/bin/sh
# Run the ProofGeneral tests in batch-mode Emacs.
#
# Usage: run-ert.sh NARYA-EXECUTABLE PROOFGENERAL-ELISP-DIR
#
# The tests are skipped, not failed, if ProofGeneral can't be found (see
# narya-pg-tests.el), or if NARYA_SKIP_PG_TESTS is set to a nonempty value.
# The Emacs output is shown only if a test fails; otherwise this prints
# nothing, except for a one-line notice if the tests were skipped.

set -u

if [ -n "${NARYA_SKIP_PG_TESTS:-}" ]; then
  exit 0
fi

here=$(cd "$(dirname "$0")" && pwd)
narya_dir=$(cd "$(dirname "$1")" && pwd) || exit 1
pg_dir=$(cd "$2" && pwd) || exit 1
log=$(mktemp "${TMPDIR:-/tmp}/narya-pg-tests.XXXXXX")
trap 'rm -f "$log"' EXIT

# ProofGeneral runs the program "narya", so we put the one being tested first
# on the PATH.
PATH="$narya_dir:$PATH" NARYA_PG_DIR="$pg_dir" \
  emacs --batch -l ert -l "$here/narya-pg-tests.el" \
  -f ert-run-tests-batch-and-exit >"$log" 2>&1
status=$?

if [ $status -ne 0 ]; then
  cat "$log"
  exit $status
fi

if grep -q "^Ran .* skipped" "$log"; then
  echo "ProofGeneral tests: $(grep '^Ran ' "$log" | sed 's/ (.*//') (is ProofGeneral installed?)"
fi
