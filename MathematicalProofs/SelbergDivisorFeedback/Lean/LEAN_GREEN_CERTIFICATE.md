# Lean verification certificate

Status: **PASS**

Verification date: 2026-08-21

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0 at commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Checks

From the `Lean` directory:

```text
lake build --wfail
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
```

The pinned project build completed successfully (3,011 jobs). The direct
challenge, solution, and certificate checks completed with exit code 0. The
single `sorry` declaration is the intended hole in `Challenge.lean`.

The certificate prints three axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `set_option`, or `decreasing_by` declaration.

## Independent statement checks

The exact one-theorem Challenge/Solution surface passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Windows replay covered statement comparison and both kernels. The
repository workflow supplies the isolated Linux execution.

## Verified scope

Lean proves that correcting one coefficient on a finite set of primes gives
exact weighted centering, with coefficients extended by zero outside the set.
Under the stated nonzero-coefficient and uniform-bound hypotheses, it also
exhibits a prime with nonzero residual and proves the logarithmic residual
bound for every positive integer using the exact prime-factorization formula.

The prime-number asymptotics, near-linear output separation, Selberg remainder,
residual moments, and generalized von Mangoldt hierarchy remain manuscript
proofs.

## Exact artifact hashes

SHA-256:

```text
b7666b592dd3a5922596bf35fc57ca228840f2e340e51a51f50cc517c3e26431  Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf
344a60845311253fcac8fd01933ba8af7e9f9dda2f0a04f9c4e55ef0df8d20e9  Manuscript/paper.tex
3a66df0c25310c878132a1f1e85c5f9017223e03498f9d7313435822fca8feb4  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
f52f2f0aaaedf0520a08575bd766045baf8ef691ab52a05e6a37091a06fe10d9  Lean/lakefile.toml
384d13d949742b0ccb9dab94448e57e1d5fc1e8e13b57b5b480651a86fdeaa20  Lean/RiemannHypothesisProofFactory/SelbergConditioning.lean
5912536caeff092fbfa3468fdbc5e458d9214bcfb6fb06d8bf3639b4be51a9f9  Lean/RiemannHypothesisProofFactory/SelbergConditioning/FiniteKernel.lean
7cfce81c6a1bfa284a1aa9cef4b944daceb2dfe1b5a84c48e191855f587411a1  Lean/RiemannHypothesisProofFactory/SelbergConditioning/ConditioningWitness.lean
2f416bcccba710108a3ba5f9dfcc8b884900d67a7f4142e6f13265d016dff3c7  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PrimeFactorConstruction.lean
80f6f8b8221197113d039b00de9a193176836403172e00b9ed181cee4de49fc4  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
aa8b857807b3a515fd0bf84be0aa420bd848d788f83eed476b6fa42ac8ef049d  Lean/Challenge.lean
24032d2f60df3e12968b2482fe323250986f4f769620fa1853597c860d863a7c  Lean/Solution.lean
dcfb124ff62661184c62dbd6c08e160c220e05542ba9953ffc52408ca3372d42  Lean/comparator.json
ec8afff18403d26a03189a8ad1f391257af8478e22a496b563b22eccfdd726e2  Lean/formalization.yaml
```
