# rank-two-nonnegative-approximation

Standalone formal definition of Q036. `record.json` preserves the exact
board source, target, requested result and equation used for this definition.
`Challenge.lean` imports only Mathlib. `Solution.lean` is its identical starting
copy, with the open theorem deliberately unproved.

## Modelling choices

This question requests only an instance map F, so the theorem has no extra recovery requirement. Factors are arbitrary nonnegative real matrices of shapes m×2 and 2×n; asymmetric factors and irrational entries are allowed. Error is exactly the sum of squared entrywise residuals with a non-strict threshold. Dimensions may be zero. The finite encoding applies to the rational input, not to an unrequested factor output.

Finite indices are zero based. Numerical data use Q001's self-delimiting binary
encoding unless the source explicitly requires unary. The requested construction alone must be a deterministic polynomial-time TM2 computation with a polynomial output bound. Its correctness is satisfiability equivalence. No recovery algorithm or finitely encoded real-factor output is required. Legal-instance predicates are specifications,
not algorithms the proposed reduction must execute.

## Build and verification

Lean 4.35.0 and matching Mathlib are pinned by `lean-toolchain`, `lakefile.toml`
and `lake-manifest.json`. In this directory run:

```sh
lake exe cache get Mathlib.Computability.TuringMachine.Computable Mathlib.Analysis.Real.Sqrt
LEAN_NUM_THREADS=2 lake build
lake env lean Audit.lean
./scripts/verify-comparator.sh
```

The comparator script and repository-root Linux CI follow the pinned Q001
reference. They run the bundled `lake comparator` with the strict axiom policy,
then, for an unfilled solution, require full statement agreement and rejection
only for `sorryAx`. Green CI verifies an open template, not a completed proof.
The script needs Linux and bubblewrap; macOS compilation is not comparator
verification. `Tests.lean` checks finite boundary examples, not general semantic
equivalence. Human review of the problem statement remains necessary.

## Provenance and license

Infrastructure follows Q001 at `6e5d9d7aa425db5f01ee44f4c4e1710cf2993fda`.
The files in this formal project are licensed under Apache-2.0; see `LICENSE`.
This does not change licensing of other files in the research repository.

Local verification results are recorded in `evidence/statement/verification.json`.
The comparator prerequisite test passes on macOS; its real Linux verdict cases
are skipped, and the comparator script itself exits at the missing `bwrap` prerequisite.
