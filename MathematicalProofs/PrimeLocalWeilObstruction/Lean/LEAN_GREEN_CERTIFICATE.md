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
lake build
lake env lean RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
```

The pinned project completed a clean build of 2,765 jobs. The public theorem
certificate completed with exit code 0. Its axiom report contains no
`sorryAx`; the listed dependencies are the standard Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`.

The project source also contains no `sorry`, `admit`, `unsafe`, or explicit
`axiom` declaration.

## Verified scope

Lean checks:

- divergence of the exact weights `Lambda(n) / sqrt(n)`;
- equality of positive-integer and prime-power-filtered prefixes;
- the abstract sharp local threshold from approximate fixed vectors;
- divergence of every scalar budget paying the required local cost; and
- the finite-prefix and summable-weight controls.

The concrete smooth compactly supported dilation argument, autocorrelation
tail, and explicit-formula sign and normalization bridge remain manuscript
proofs. The certificate does not present those analytic steps, literature
claims, novelty, or exposition as kernel-checked.

## Exact artifact hashes

SHA-256:

```text
b4e0bcf5353897dcf5e3f9f1713f66759010f59f7dcd5979107d071c63f9b234  Manuscript/prime_local_weil_obstruction_baccaro_20260818.pdf
40b3490b99af524cb5752a06f48abca981955a2357bc0d625fc149057798f66c  Manuscript/paper.tex
36895e484cac085b33492b0376a17aea7200454d186f321161c40571db8b86de  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
e347641d400eb5107f9470b142f3e480c7ae3187b1fae088371feeeda0d82e14  Lean/RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
```

The GitHub Actions workflow repeats the pinned build and public certificate
check on every push and pull request.
