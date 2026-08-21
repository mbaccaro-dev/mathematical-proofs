# Lean verification

This self-contained Lean 4 project proves the finite multilinear mixture law
and a nonlinear periodic phase-orbit energy law.

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

For normed-space-valued phase orbits, Lean derives the complete logarithmic
normal form from exact covariance and proves the periodic norm profile and
off-critical exponent gap. Given one positive dyadic-energy block, the selected
theorem rules out the zero orbit and proves that the next full-turn block is
positive with the exact geometric scaling factor.

The phase theorem's measure-theoretic block-selection step and the paper's
zero-channel, error-term, positive-homogeneous, Mellin, saturation, and
two-sided-germ results are separate manuscript arguments.
