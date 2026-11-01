#!/usr/bin/env bash
# Build the Lean proof of R(12,12) >= 1658.
#
# The eight H01Branch modules each need 4-7 GB of memory in the Lean kernel, and
# R1658.Checks about 8 GB. `lake build` compiles independent modules in parallel and has
# no option to limit this, so the branch modules are built one at a time first.
set -euo pipefail
cd "$(dirname "$0")/.."

lake exe cache get
for i in 0 1 2 3 4 5 6 7; do
  echo "== RamseyIncrement.R1212.H01Branch$i"
  lake build "RamseyIncrement.R1212.H01Branch$i"
done
# The default target imports RamseyIncrement.R1658.Main, so it includes the final theorem.
lake build
lake env lean AxiomAudit1658.lean
