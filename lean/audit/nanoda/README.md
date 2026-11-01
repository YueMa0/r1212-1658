# Independent kernel check with nanoda

[nanoda](https://github.com/ammkrn/nanoda_lib) is a type checker for Lean 4 written independently of Lean, in Rust. It checks the export of `RamseyIncrement.R1658.r1212_lower_bound` together with every declaration it uses, Mathlib included.

## Versions

The same as for r1212-1642:

- lean4export: tag v4.32.2 (commit 86e4a33), with its lean-toolchain changed to leanprover/lean4:v4.32.1, built with that toolchain.
- nanoda_lib: commit d0a02cc (version 0.4.30), built with `cargo build --release --locked`.

## Running it

```bash
LEAN4EXPORT=/path/to/lean4export NANODA=/path/to/nanoda_bin lean/audit/nanoda/run_nanoda.sh
```

The export is about 142 MB. The configuration (configs/full.json) turns on nanoda's Nat and String extensions and permits only the axioms propext, Classical.choice and Quot.sound; any other axiom is an error. It also prints the theorem and the definitions in its statement, so that the statement can be compared with the source.

## Results (1 November 2026, Windows, one thread)

| Check | Declarations | Result | Time | Peak memory |
|---|---:|---|---:|---:|
| **r1212_lower_bound, complete** | **29,307** | **no errors** | 722 s | 6.2 GB |
| control: `badRow_spec` as exported | 689 | no errors | 3 s | 0.7 GB |
| control: the same export with one bit of `badRLit` changed | — | **rejected**: `assertion failed: self.def_eq(u, v)`, exit code 101 | 0.5 s | — |

- logs/full.log is the output of the complete check. It prints the statement as `LE.le (OfNat.ofNat 1658) (RamseyIncrement.ramseyNumber (OfNat.ofNat 12) (OfNat.ofNat 12))`, and the definitions of ramseyNumber, ForcesRamsey, HasRamseyColoring, IsRamseyFree, SimpleGraph.CliqueFree, IsNClique and IsClique.
- The complete export contains the axioms propext, Classical.choice and Quot.sound and no others.
- `badRow_spec` (Checks.lean) states that the table of conflicts, the literal `badRLit` in Data.lean, agrees with its definition. In the control, bit 5 of that literal was flipped in the export (its `natVal` XOR 32), and nothing else was changed. The rejection shows that nanoda actually performs the kernel computations of the proof.
- SHA-256 of the exports: complete `4a2f10b8df5ec4b51a33f1f61d76c9b7020d9a179b8d37acaaffe9b47d1cb532` (141,608,298 bytes); control `ee17830606ef0cf57929575c51095cfa1b1f356afb0202aebe286e85c033fadb`; changed control `66eab977a6d61000083e0ebcf7d55a90527498940d59b012a5a088790d7eca98`.
- The configurations in configs/ differ from the ones we ran only in `export_file_path`, which pointed into our build directory.
