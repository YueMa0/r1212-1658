# R(12,12) ≥ 1658

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23827702.svg)](https://doi.org/10.5281/zenodo.23827702)

This repository contains a red/blue colouring of the complete graph K₁₆₅₇ with no monochromatic K₁₂, so R(12,12) ≥ 1658.

To our knowledge this improves the best published lower bound, R(12,12) ≥ 1641 (M. Tatarevic, [arXiv:2608.06531](https://arxiv.org/abs/2608.06531), August 2026), and our earlier R(12,12) ≥ 1642 ([r1212-1642](https://github.com/YueMa0/r1212-1642), [doi:10.5281/zenodo.23770924](https://doi.org/10.5281/zenodo.23770924)). The literature search was made on 30 October 2026. The result has not been peer reviewed.

## The result

- [graph/r1212_1657.graph](graph/r1212_1657.graph) has 1657 lines of 1657 characters. Character w of line v is 1 if the edge vw is red and 0 if it is blue.
- SHA-256: `a3eb1cd2c1f67eb14f2fe2e207c64292616df3fa0b0d95454db4d4e614411219`.
- It contains no red K₁₂ and no blue K₁₂, so R(12,12) ≥ 1658.
- The result is computer-verified. There is no Lean proof of it. The Lean proof in r1212-1642 covers R(12,12) ≥ 1642 only.

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

- **The exhaustive search** uses the program of r1212-1642, unchanged. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices come after v and have colour c to v. So for each vertex v and colour c, the program decides whether those later vertices contain a K₁₁ of colour c. Each pair (v, c) is one task.
- **Controls.** Before the main run, the same binary reproduced the published run of r1212-1642 task by task, including node counts: both tasks with v = 10, and all tasks with v ≥ 1000. The binary is byte-identical to the one of that run. It also found the K₁₂s planted into two modified copies of the colouring: one in the last 12 vertices, one inside the largest task. Both copies are in verify/controls/.
- **The clone projection** is the check of r1212-1642, patched only for the order of the graph and the names of the extra vertices. It reduces the question to the 81 vertices of C ∪ I and the added vertices; the argument is in its docstring. That M(797) is an (11,11)-colouring is due to Mathon (1987), and is checked by computer in r1212-1642. The exhaustive search does not need this fact.

## How this work was done

The colouring was found on 30 October 2026 by Yue Ma together with Claude (Claude Opus 5.5, by Anthropic), working as an agent in Claude Code. The research started from exploratory work by GPT-6 Astra (OpenAI) in three directions for extending rule R* of r1212-1642; the search that found the colouring grew out of one of them. Yue Ma chose the research direction, approved each stage and decides how the result is published. Claude designed and ran the search on a Windows computer, and prepared the checks in verify/. The exhaustive search in verify/results/ was run on an Apple M4 Mac mini, following the instructions in verify/README.md.

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

## Layout

| Path | Contents |
|---|---|
| graph/ | the colouring, its SHA-256, its vertex order and the type of every added vertex |
| verify/ | the exhaustive search program, its output checker, the clone-projection check, the two control colourings, and the outputs of our run |

## Credits

- The (11,11)-colouring M(797) is due to Mathon (1987) and Shearer (1986).
- **Milos Tatarevic**: the two-parameter increment R(k+1, s+1) ≥ R(k,s) + 2k + 2s ([arXiv:2608.06531](https://arxiv.org/abs/2608.06531)). Together with rule R* of r1212-1642, it gives the types of the first 45 added vertices.
- The programs in verify/ come from r1212-1642, except check_bruteforce_output.py, which is new.
- **New in this repository**: the colouring.
- **Author**: Yue Ma. For the role of AI, see [How this work was done](#how-this-work-was-done).

## How to cite

Version 1.0.0 is archived on Zenodo: [doi:10.5281/zenodo.23827703](https://doi.org/10.5281/zenodo.23827703). To cite all versions, use [doi:10.5281/zenodo.23827702](https://doi.org/10.5281/zenodo.23827702). Citation metadata is in [CITATION.cff](CITATION.cff); GitHub shows it under "Cite this repository". Please cite Tatarevic's paper and r1212-1642 as well.

## License

MIT; see [LICENSE](LICENSE).
