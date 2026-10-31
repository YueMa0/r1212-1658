# Outputs of our run

The exhaustive search of graph/r1212_1657.graph and its four controls, run on 30 October 2026 on an Apple M4 Mac mini with 8 threads. The files are exactly as the run wrote them, except for one line removed from setup.txt (see below). [SHA256SUMS](SHA256SUMS) lists their SHA-256; check with `sha256sum -c SHA256SUMS` in this folder.

| File | Contents |
|---|---|
| setup.txt | date, compiler, SHA-256 of the source and of the binary |
| candidate_1657.jsonl | one line per task: all 3,314 tasks "none", 2.194 × 10¹¹ nodes |
| candidate_1657.meta.txt | start and end time, SHA-256 of the graph and of the binary, command |
| candidate_1657.stderr.txt | the program's log |
| candidate_1657.check.txt | the output of check_bruteforce_output.py |
| control_published_v10.\*, control_published_v1000.\* | the published run of r1212-1642, reproduced task by task |
| control_tail.\*, control_big.\* | the two planted-K₁₂ controls |

- The run read the colouring under the name r4_strong_candidate_1657.graph. It is the same file as graph/r1212_1657.graph, with the same SHA-256 (in candidate_1657.meta.txt).
- We removed the second line of setup.txt, which gave the host name and the kernel version of the Mac. So its SHA-256 differs from the file the run wrote; SHA256SUMS lists the file as published here.
- setup.txt records the THREADS setting at setup time (4). Every run used 8 threads, as the command lines in the .meta.txt files and the .stderr.txt logs show.
- The binary (SHA-256 37720b55…, Apple clang 21.0.0) is byte-identical to the one of the published run of r1212-1642.
- The control graphs differ from the colouring only on pairs inside the planted vertex sets; their SHA-256 are in control_tail.meta.txt and control_big.meta.txt. The control graphs themselves are in [../controls/](../controls/).
- In control_big, the K₁₂ found is not the planted set. It contains three planted vertices, and exactly one of its 66 pairs, {356, 1036}, is blue in the colouring; planting made that pair red.
