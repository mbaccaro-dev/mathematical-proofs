# Lean verification

This is a self-contained Lean 4 project for the kernel-checked portion of the
accompanying paper.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

## Build

From this `Lean` directory, run:

```text
lake build
```

The axiom-reporting certificate is:

```text
RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
```

Check it directly with:

```text
lake env lean RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
```

## Exact scope

Lean checks:

- divergence of the exact weights `Lambda(n) / sqrt(n)`;
- equality of the positive-integer and prime-power-filtered prefixes;
- the abstract sharp local threshold from approximate fixed vectors;
- divergence of every scalar budget that pays the required local cost; and
- the finite-prefix and summable-weight controls.

The concrete `C_c^∞` normalized-dilation construction, the compact-support
autocorrelation tail, and the explicit-formula sign/normalization bridge are
proved in the manuscript but are not claimed as Lean-checked. Literature,
novelty, exposition, and publication judgments are also outside the kernel.
