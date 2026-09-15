#!/usr/bin/env bash
# Build the library and run the axiom audit.  Exits non-zero if anything regresses.
set -euo pipefail
cd "$(dirname "$0")"
echo "== lake build =="
lake build
echo
echo "== axiom audit (enumerates the environment; not a hand-written list) =="
lake env lean scripts/Audit.lean | tee /tmp/chowstanley_audit.txt
echo
grep -q "Classical.choice 0" /tmp/chowstanley_audit.txt \
  || { echo "FAIL: Classical.choice appears"; exit 1; }
grep -q "other/sorry 0" /tmp/chowstanley_audit.txt \
  || { echo "FAIL: sorryAx or an unexpected axiom appears"; exit 1; }
echo "OK"
