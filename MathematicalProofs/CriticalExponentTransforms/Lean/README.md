# Lean verification

This self-contained Lean 4 project proves the finite multilinear mixture law
for real-valued continuous signals on the positive half-line.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

## Build

From this `Lean` directory, run:

```text
lake build --wfail
```

The axiom-reporting certificate is:

```text
RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

Check it directly with:

```text
lake env lean RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

## Exact scope

Lean derives the exact finite perturbation expansion from multilinearity and
dilation covariance and proves the normalized dyadic-energy limit by dominated
convergence. Given the first nonzero grouped coefficient, it proves the leading
norm limit, positivity of the energy constant, and the strict
critical-exponent gap.

The paper's zero-channel and error-term branches, together with its phase-orbit,
positive-homogeneous, Mellin, saturation, and two-sided-germ results, are
separate manuscript arguments.
