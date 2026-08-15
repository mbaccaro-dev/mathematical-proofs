# Lean verification

This directory is a self-contained Lean 4 project for the mathematical claims
formalized alongside the paper.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

## Build

From this `Lean` directory, run:

```text
lake build
```

The paper-wide certificate is:

```text
BoundaryConstantObstruction/IncompleteGamma/PaperCertificate.lean
```

To check that entry point directly, run:

```text
lake env lean BoundaryConstantObstruction/IncompleteGamma/PaperCertificate.lean
```

The certificate prints the axioms used by the main paper declarations. The
formalization certifies the printed Lean statements; literature attribution,
novelty, exposition, and publication judgments are outside the Lean kernel.
