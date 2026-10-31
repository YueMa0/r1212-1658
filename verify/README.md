# Computer checks of the colouring

These programs read graph/r1212_1657.graph.

## Exhaustive search

bruteforce_kclique.c uses no structure of the graph. Every monochromatic K₁₂ has a smallest vertex v, and its other 11 vertices are later vertices joined to v in its colour c. So for each v and c the program decides whether P(v,c) = {w > v : colour(v,w) = c} contains a K₁₁ of colour c. That is 3,314 tasks, each an exact bitset branch and bound. The largest task has |P(v,c)| = 834.

```bash
cc -O3 -pthread -o bruteforce_kclique verify/bruteforce_kclique.c
./bruteforce_kclique graph/r1212_1657.graph 12 bruteforce.jsonl 8
```

The last argument is the number of threads.

- The program is the one of r1212-1642, unchanged: SHA-256 541a83313b5e78e9246953ea0f597db63db01f8f18fa2b475b795109b1056e44.
- The verify/README.md of r1212-1642 lists its known robustness issues, D1–D5. The one that matters in practice: on restart, a task counts as finished if a line of the output file merely starts with its (v, c), so **always start with a new output file**, or remove a truncated last line first.
- check_bruteforce_output.py, below, covers the others: it checks task coverage, task sizes and witnesses.

## Output check

check_bruteforce_output.py needs only the Python standard library.

```bash
python3 verify/check_bruteforce_output.py graph/r1212_1657.graph bruteforce.jsonl --t 12
```

It checks that:

- the graph is symmetric with a zero diagonal;
- every line is one complete JSON object;
- every task (v, c) appears exactly once;
- each task size m equals |P(v,c)| computed from the graph;
- every result is "none", and every "found" (none are expected here) comes with a valid monochromatic K₁₂.

It prints `CHECK: PASS` or `CHECK: FAIL`.

## Clone projection

check_projection.py needs numpy and networkx, and takes seconds.

```bash
python3 verify/check_projection.py graph/r1212_1657.graph
```

It is the check of r1212-1642, patched only for the order of the graph (1657) and the names of the 16 extra added vertices. It reads the type of every added vertex from the file. It then checks a condition on the 81 vertices of C ∪ I and the added vertices which, together with the (11,11) property of M(797), rules out a monochromatic K₁₂. The argument is in its docstring. With an argument u:v it flips the edge uv first, as a negative control.

## Our run

verify/results/ has the outputs of our run, with SHA256SUMS; [results/README.md](results/README.md) lists them.

- The run was made on 30 October 2026 on an Apple M4 Mac mini, with 8 threads.
  - All 3,314 tasks are "none": 2.194 × 10¹¹ nodes, 15.38 CPU-hours, 1 h 55 min.
  - The largest task, (10, red) with |P| = 834, took 172 s.
- The binary is byte-identical to the one of the published run of r1212-1642.

The controls ran with the same binary before the main run, and all passed:

- the published run of r1212-1642, reproduced task by task including node counts: both tasks with v = 10, and all 1,282 tasks with v ≥ 1000;
- a red K₁₂ planted in the last 12 vertices of the colouring, found as task (1645, red);
- a red K₁₂ planted inside the largest task, (10, red), found.

## The control colourings

verify/controls/ has the two control colourings, gzipped, and controls.json, which describes them. Each is the colouring with 12 vertices made into a red K₁₂, so it differs from graph/r1212_1657.graph only on pairs inside those 12 vertices.

- control_tail_1657.graph.gz: the last 12 vertices, 1645–1656. Task (1645, red) must be "found".
- control_big_1657.graph.gz: 12 vertices, the smallest being 10, so the K₁₂ lies inside the largest task. Task (10, red) must be "found".

To check the outputs of our run against them (the checker reads .gz files directly):

```bash
python3 verify/check_bruteforce_output.py verify/controls/control_tail_1657.graph.gz verify/results/control_tail.jsonl --t 12 --spec verify/controls/controls.json --name control_tail
python3 verify/check_bruteforce_output.py verify/controls/control_big_1657.graph.gz verify/results/control_big.jsonl --t 12 --spec verify/controls/controls.json --name control_big
```

With --spec, the checker also checks the SHA-256 of the control colouring and that it differs from graph/r1212_1657.graph only inside the planted set. In our run, "base" was r4_strong_candidate_1657.graph, the name the colouring had there; in this copy of controls.json it is the path of graph/r1212_1657.graph. Nothing else in the file changed.

To run the controls yourself, unpack them first. The arguments after the number of threads are the node cap (0 means none) and the range of v, v_lo ≤ v < v_hi. The second control takes about 2 minutes.

```bash
gunzip -k verify/controls/control_tail_1657.graph.gz verify/controls/control_big_1657.graph.gz
./bruteforce_kclique verify/controls/control_tail_1657.graph 12 control_tail.jsonl 8 0 1645 1657
./bruteforce_kclique verify/controls/control_big_1657.graph 12 control_big.jsonl 8 0 10 11
```
