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
lake env lean RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
```

The pinned project completed a clean build of 3,009 jobs. The public theorem
certificate completed with exit code 0. Its axiom report contains no
`sorryAx`; the listed dependencies are the standard Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`.

A static scan found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`,
`set_option`, or `decreasing_by` in the project source.

## Verified scope

Lean checks:

- the algebraic rewrite from a distinguished-chain correction to a negative tail;
- strict positivity of both signed weights under the printed relative bound;
- normalization of a pointwise residual bound to the tolerance `tau`;
- the two-sign output separation after scale normalization; and
- the final Lipschitz lower-bound quotient.

The prime number theorem, Chebyshev and partial-summation estimates, Selberg's
formula, residual moments, compact-transform asymptotics, and the generalized
von Mangoldt hierarchy remain manuscript proofs. Literature, novelty,
exposition, and publication judgments are also outside the kernel.

## Exact artifact hashes

SHA-256:

```text
b7666b592dd3a5922596bf35fc57ca228840f2e340e51a51f50cc517c3e26431  Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf
344a60845311253fcac8fd01933ba8af7e9f9dda2f0a04f9c4e55ef0df8d20e9  Manuscript/paper.tex
3a66df0c25310c878132a1f1e85c5f9017223e03498f9d7313435822fca8feb4  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
7779621fec8b7d546ee624276fc7b2932fa310b51e41c10620623ff3fe6b4375  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
5912536caeff092fbfa3468fdbc5e458d9214bcfb6fb06d8bf3639b4be51a9f9  Lean/RiemannHypothesisProofFactory/SelbergConditioning/FiniteKernel.lean
```

The GitHub Actions workflow repeats the pinned build and public certificate
check on every push and pull request.
