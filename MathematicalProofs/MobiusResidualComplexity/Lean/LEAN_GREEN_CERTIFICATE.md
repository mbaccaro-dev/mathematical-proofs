# Lean Green certificate

Status: **PASS**

Date: 2026-08-18

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0

## Checks

From the `Lean` directory:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The pinned project completed its 3,010-job build successfully. The public
theorem certificate completed with exit code 0 and printed the axiom report
for all eight theorems. No report contains `sorryAx`; the listed dependencies
are the standard Mathlib axioms `propext`, `Classical.choice`, and
`Quot.sound`.

A static scan found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`,
`set_option`, or `decreasing_by` in the project source.

## Verified scope

Lean checks:

- cancellation of an opposite-sign unit pair;
- the absolute-value bound for a finite sum of unit-bounded terms;
- the finite matching bound after complete pairs cancel;
- equal positive and negative counts in a zero-sum unit cell;
- impossibility of the strict exponent sandwich;
- the square-root threshold identity;
- the endpoint-doubling inequality; and
- its lift from one endpoint to a doubled cutoff.

The prime number theorem, band-product asymptotic, logarithmic scale
conversion, gcd-residual matching model, exact rank-pair compression, and
global sparse-jump counting argument remain manuscript proofs. Literature,
novelty, exposition, and publication judgments are also outside the kernel.

## Exact artifact hashes

SHA-256:

```text
f10f62e5f474d7c302983021df5c19813f329ae46b66a4ef3e74da99b37f74a7  Manuscript/mobius_residual_complexity_baccaro_20260818.pdf
e0b7ba28d972aaf75163c74a3134f6d30f0136ab4c1b826b0cf46b07c5f1ce03  Manuscript/paper.tex
549f9ccab57d9a7ad304e975ad802f9424921e1387b4f88a599fd8db326b1026  Manuscript/references.bib
57a25208918a32866cab3f80a9c51b215c7ba9e2524b2391d6056338f3947d53  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
6c782c458ee005bdec7a224af975b24db2d33b1e9b2fd0b53c4f79cdb79d7898  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
0cc02375dd76e63f17eafd841d94ea39a736c292b53643e5d0f587a148dcc0ff  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/CombinatorialKernel.lean
```

The GitHub Actions workflow repeats the pinned build and public certificate
check on every push and pull request.
