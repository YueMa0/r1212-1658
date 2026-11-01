# R(12,12) ≥ 1658

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23827702.svg)](https://doi.org/10.5281/zenodo.23827702)

This repository contains a red/blue colouring of the complete graph K₁₆₅₇ with no monochromatic K₁₂, so R(12,12) ≥ 1658.

To our knowledge this improves the best published lower bound, R(12,12) ≥ 1641 (M. Tatarevic, [arXiv:2608.06531](https://arxiv.org/abs/2608.06531), August 2026), and our earlier R(12,12) ≥ 1642 ([r1212-1642](https://github.com/YueMa0/r1212-1642), [doi:10.5281/zenodo.23770924](https://doi.org/10.5281/zenodo.23770924)). The literature search was last made on 1 November 2026. The result has not been peer reviewed.

## The result

- [graph/r1212_1657.graph](graph/r1212_1657.graph) has 1657 lines of 1657 characters. Character w of line v is 1 if the edge vw is red and 0 if it is blue.
- SHA-256: `a3eb1cd2c1f67eb14f2fe2e207c64292616df3fa0b0d95454db4d4e614411219`.
- It contains no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1658.
- The result is computer-verified, and proved in Lean 4 with Mathlib; see [How it was checked](#how-it-was-checked) and [The Lean proof](#the-lean-proof).

## The colouring in brief

- Vertices 0–1595 are the Mathon–Shearer (11,11)-colouring M(797), in the vertex order of r1212-1642.
- C, a red K₁₀, and I, a blue K₁₀, are the certificates of r1212-1642. V° denotes the other 1576 vertices of M(797).
- The 61 added vertices 1596–1656 each behave in one of three ways towards V°:
  - **copy** of a vertex g of C ∪ I: the added vertex has the colour of g to every vertex of V°;
  - **constant red**;
  - **constant blue**.
- 39 added vertices are copies, 11 are constant red and 11 constant blue. Every vertex of C ∪ I has at least one copy.
- The colours among the 81 vertices of C ∪ I and the added vertices are not given by a formula; they are the ones in the file.
- [graph/README.md](graph/README.md) lists the type of every added vertex. [graph/r1212_1657.json](graph/r1212_1657.json) has the same data in machine-readable form.

The first 45 added vertices have the same types as the 45 added vertices of the r1212-1642 colouring, which come from Tatarevic's increment and rule R*. The colours among the added vertices are different.

## How it was checked

| Check | What it establishes | Where | Cost |
|---|---|---|---|
| exhaustive clique search | no monochromatic K₁₂ in graph/r1212_1657.graph, without using any structure of the graph | verify/bruteforce_kclique.c; the output of our run is in verify/results/ | 15.4 CPU-hours: 1 h 55 min with 8 threads on an Apple M4 Mac mini |
| output check | the search output has each of the 3,314 tasks exactly once, with the right task sizes, and every result is "none" | verify/check_bruteforce_output.py | seconds |
| clone projection | the same, using only that M(797) is an (11,11)-colouring | verify/check_projection.py | seconds |
| Lean proof | R(12,12) ≥ 1658, from the fact that M(797) is an (11,11)-colouring (proved in Lean in r1212-1642) and finite checks that the Lean kernel evaluates | lean/ | about 30 minutes to compile, up to 8 GB of memory |

- **The exhaustive search** uses the program of r1212-1642, unchanged. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices come after v and have colour c to v. So for each vertex v and colour c, the program decides whether those later vertices contain a K₁₁ of colour c. Each pair (v, c) is one task.
- **Controls.** Before the main run, the same binary reproduced the published run of r1212-1642 task by task, including node counts: both tasks with v = 10, and all tasks with v ≥ 1000. The binary is byte-identical to the one of that run. It also found the K₁₂s planted into two modified copies of the colouring: one in the last 12 vertices, one inside the largest task. Both copies are in verify/controls/.
- **The clone projection** is the check of r1212-1642, patched only for the order of the graph and the names of the extra vertices. It reduces the question to the 81 vertices of C ∪ I and the added vertices; the argument is in its docstring. That M(797) is an (11,11)-colouring is due to Mathon (1987), and is checked by computer in r1212-1642. The exhaustive search does not need this fact.

## The Lean proof

[lean/](lean/) proves, in Lean 4.32.1 with Mathlib,

```lean
theorem RamseyIncrement.R1658.r1212_lower_bound : 1658 ≤ ramseyNumber 12 12
```

where `ramseyNumber` is Tatarevic's definition, as in r1212-1642.

- **The colouring.** lean/RamseyIncrement/R1658/Graph.lean defines it as M(797) and the 61 added vertices, using tables that lean/gen/gen_data.py generates from graph/r1212_1657.graph (in Data.lean).
- **The argument** is the clone projection. It uses one fact about M(797), that it is an (11,11)-colouring (proved in Lean in r1212-1642), and finite checks on the 81 core vertices, which the Lean kernel evaluates. It does not use the exhaustive search.
- **Axioms**: only propext, Classical.choice and Quot.sound. No `sorry`, no `native_decide`.
- **Independent kernels.** After all 25 modules were compiled from source, leanchecker replayed every module, and nanoda, a Lean kernel written separately in Rust, checked the theorem together with all 29,307 declarations it uses, Mathlib included. Both accepted the proof. nanoda rejected a copy with one bit of a table changed.
- **Not part of the proof**: that the colouring defined in Lean is the published file. lean/tools/compare_export.py rebuilds all of its colours from Data.lean, following the definitions in Graph.lean, and they equal the file; so do the 85 rows that Lean's interpreter evaluated.

19 of the 25 modules come unchanged from r1212-1642 v1.0.0, and 5 of those from Tatarevic's repository ([UPSTREAM.md](UPSTREAM.md)). The new modules are in lean/RamseyIncrement/R1658/. [lean/audit/README.md](lean/audit/README.md) explains how to build and audit the proof, and records our runs.

## How this work was done

The colouring was found on 30 October 2026 by Yue Ma together with Claude (Claude Opus 5.5, by Anthropic), working as an agent in Claude Code. The research started from exploratory work by GPT-6 Astra (OpenAI) in three directions for extending rule R* of r1212-1642; the search that found the colouring grew out of one of them. Yue Ma chose the research direction, approved each stage and decides how the result is published. Claude designed and ran the search on a Windows computer, and prepared the checks in verify/. Claude also wrote the Lean proof in lean/, and ran the builds and kernel checks recorded in lean/audit/ on that computer. The exhaustive search in verify/results/ was run on an Apple M4 Mac mini, following the instructions in verify/README.md.

## Checking it yourself

The quick check needs Python 3 with numpy and networkx, and takes seconds:

```bash
python3 verify/check_projection.py graph/r1212_1657.graph
```

The exhaustive search needs a C compiler. It takes about 2 hours with 8 threads on an Apple M4 (15.4 CPU-hours). Start with a new output file each time; verify/README.md explains why.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1657.graph 12 bruteforce.jsonl 8
python3 verify/check_bruteforce_output.py graph/r1212_1657.graph bruteforce.jsonl --t 12
```

The last command should print `RESULT: no monochromatic K12` and `CHECK: PASS`. It can also check the output of our run:

```bash
python3 verify/check_bruteforce_output.py graph/r1212_1657.graph verify/results/candidate_1657.jsonl --t 12
```

The Lean proof needs [elan](https://github.com/leanprover/elan), which installs the Lean version in lean/lean-toolchain, and about 8 GB of memory. The script first downloads the Mathlib cache. On our computer, compiling the 25 modules one at a time took 28 minutes.

```bash
bash lean/audit/build_r1658.sh
```

It ends by printing the axioms of the main theorems; lean/audit/logs/axioms.log has our output. lean/audit/README.md also describes the replay with leanchecker and the check with nanoda.

## Layout

| Path | Contents |
|---|---|
| graph/ | the colouring, its SHA-256, its vertex order and the type of every added vertex |
| verify/ | the exhaustive search program, its output checker, the clone-projection check, the two control colourings, and the outputs of our run |
| lean/ | the Lean proof, the scripts to build and audit it, and the records of our runs |
| UPSTREAM.md | the files in lean/ that come from r1212-1642 and Tatarevic's repository |

## Credits

- The (11,11)-colouring M(797) is due to Mathon (1987) and Shearer (1986).
- **Milos Tatarevic**: the two-parameter increment R(k+1, s+1) ≥ R(k,s) + 2k + 2s ([arXiv:2608.06531](https://arxiv.org/abs/2608.06531)). Together with rule R* of r1212-1642, it gives the types of the first 45 added vertices. His Lean development, through r1212-1642, provides the definition of `ramseyNumber` and the basic lemmas used here.
- The programs in verify/ come from r1212-1642, except check_bruteforce_output.py, which is new.
- 19 of the Lean modules come unchanged from r1212-1642, and 5 of those from Tatarevic's [ramsey-increment-theorem](https://github.com/milostatarevic/ramsey-increment-theorem); see UPSTREAM.md.
- **New in this repository**: the colouring, and the Lean proof in lean/RamseyIncrement/R1658/ with its tools.
- **Author**: Yue Ma. For the role of AI, see [How this work was done](#how-this-work-was-done).

## How to cite

Each release is archived on Zenodo. To cite all versions, use [doi:10.5281/zenodo.23827702](https://doi.org/10.5281/zenodo.23827702). Version 1.0.0, without the Lean proof, is [doi:10.5281/zenodo.23827703](https://doi.org/10.5281/zenodo.23827703). Citation metadata is in [CITATION.cff](CITATION.cff); GitHub shows it under "Cite this repository". Please cite Tatarevic's paper and r1212-1642 as well.

## License

MIT; see [LICENSE](LICENSE).
