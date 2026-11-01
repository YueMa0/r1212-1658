# Building and auditing the Lean proof

All commands are run from lean/.

| File | Purpose |
|---|---|
| build_r1658.sh | fetch the Mathlib cache, build the eight H01Branch modules one at a time, build the default target, print the axioms |
| leanchecker_r1658.sh | leanchecker replay of all 25 modules, one per run, plus a control |
| sources.sha256 | SHA-256 of the Lean sources, entry points, helper scripts and build files in lean/ |
| nanoda/ | the check with nanoda, an independent kernel |
| logs/ | the records of our runs |

The default target, RamseyIncrement.lean, imports only RamseyIncrement.R1658.Main. So `lake build` compiles the 25 modules that the theorem needs: the 6 new modules in RamseyIncrement/R1658/ and 19 modules of r1212-1642 v1.0.0, unchanged (see UPSTREAM.md at the top of the repository).

## What Lean checks, and what it does not

- **Lean.** `RamseyIncrement.R1658.r1212_lower_bound : 1658 ≤ ramseyNumber 12 12`. The finite checks on the 81 core vertices (`noK12`, `checks_ok`, `rowR_cert`, and the lemmas that tie the lookup tables to their definitions) are evaluated by the Lean kernel with `decide +kernel`, so they are part of the proof. The proof uses `mathon_isRamseyFree` and `paley_cliqueFree` from r1212-1642 (M(797) is an (11,11)-colouring) and Tatarevic's definition of `ramseyNumber`.
- **Not Lean: that the colouring defined in Lean is graph/r1212_1657.graph.** gen/gen_data.py generates the tables in RamseyIncrement/R1658/Data.lean from the published file. tools/compare_export.py rebuilds all 1657 × 1657 colours from Data.lean, following the definitions in Graph.lean, and compares them with the file. Export.lean has Lean's interpreter evaluate rows of `G1657.Adj` directly. The theorem does not depend on these comparisons.

```bash
python3 gen/gen_data.py ../graph/r1212_1657.graph --out /tmp/Data.lean
cmp /tmp/Data.lean RamseyIncrement/R1658/Data.lean
python3 tools/compare_export.py ../graph/r1212_1657.graph
```

gen_data.py also runs the finite checks in Python, with the same algorithms, as a preliminary check; the proof does not use it. compare_export.py needs Python 3.12 or later. The quick-check workflow runs these three commands and checks sources.sha256; it does not run Lean.

## Memory

Each H01Branch module needs 4–7 GB in the Lean kernel, and R1658.Checks about 8 GB, during both compilation and replay. Lake compiles independent modules in parallel, and leanchecker replays the modules it is given in parallel, so the scripts take the large modules one at a time.

## Logs (lean/audit/logs/)

These are from runs on 1 November 2026 on a Windows computer, with Lean 4.32.1 and the Mathlib revision in lake-manifest.json. Our own driver compiled the modules one at a time by calling `lean` with the options of lakefile.lean, instead of `lake build`. leanchecker, lean4export and nanoda were called as in the scripts here.

| Log | Contents |
|---|---|
| build_and_replay.tsv | for each of the 25 modules, in build order: compile time and peak memory, SHA-256 of the .olean, and the leanchecker replay of that .olean (exit code, time, peak memory). All were compiled from source and all replays exit 0: 1687 s to compile, 1281 s to replay, at most 7.8 GB (Checks). The last line is a control: a missing module exits 1 |
| axioms.log | output of AxiomAudit1658.lean: the final theorem depends only on propext, Classical.choice and Quot.sound; `noK12` and `checks_ok` only on propext |
| compare_export.json | output of tools/compare_export.py: all 2,745,649 entries rebuilt from Data.lean equal the file, and so do the 85 rows that Lean's interpreter evaluated |

The 85 interpreter rows are 26 rows written by Export.lean (the 20 certificate vertices and the first 6 added vertices) and the first 59 rows of the file, written by an earlier version of Export.lean that went through all rows in file order. On the core rows the interpreter took about 65 s per row, and both runs were stopped before the end. The rebuild from Data.lean covers every entry.

The sources of these runs are the files in lean/; their SHA-256 are in sources.sha256.
