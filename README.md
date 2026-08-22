# Mathematical proofs and formalizations

[![Lean verification](https://github.com/mbaccaro-dev/mathematical-proofs/actions/workflows/lean.yml/badge.svg)](https://github.com/mbaccaro-dev/mathematical-proofs/actions/workflows/lean.yml)

The [`MathematicalProofs`](MathematicalProofs/) directory contains one
self-contained folder per paper. Each paper folder keeps the readable
manuscript together with the exact Lean project used to check its formal
claims.

## Palomar verification

Each of the seven `Lean` projects contains a Palomar v0.4
`formalization.yaml`, a trusted `Challenge.lean`, a separate `Solution.lean`,
and a `comparator.json` that requires NanoDa. Run
`bash scripts/verify-palomar.sh <path-to-Lean-project>` on Linux to replay the
exact pinned Comparator, Lean kernel, NanoDa, and Landrun checks. Registration,
when authorized, uses the [Palomar submission form](https://submit.palomar-registry.org/).
