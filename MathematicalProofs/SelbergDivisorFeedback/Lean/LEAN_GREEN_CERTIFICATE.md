# Lean Green and Palomar preflight certificate

Status: **PASS**

Verification date: 2026-08-20

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0 at commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Lean checks

From the `Lean` directory:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
```

The build completed successfully (3,010 jobs). Direct checks of
`Challenge.lean`, `Solution.lean`, and the public certificate completed with
exit code 0. The only `sorry` is the intended challenge hole.

The certificate prints six axiom reports. None contains `sorryAx`; the
reported dependencies are the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding the challenge
found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`, `set_option`,
or `decreasing_by` declaration.

## Palomar preflight

The exact six-theorem Challenge/Solution surface passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean kernel, and NanoDa at
commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Comparator replay used its upstream-compatible non-isolating
development shim. The repository workflow pins real Landrun at commit
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; that isolation gate will run on
Ubuntu after a separately authorized push. The `formalization.yaml` file
passes the exact Palomar v0.4 schema and the repository's equivalent local
metadata checks. `enable_nanoda` is exactly `true`.

## Verified scope

Lean checks the distinguished-chain correction identity, positivity of both
signed perturbations, residual normalization, two-sign output separation, the
Lipschitz lower-bound quotient, and a single packaged finite two-sign
conditioning obstruction theorem.

The prime number theorem, Chebyshev and partial-summation estimates, Selberg's
formula, residual moments, compact-transform asymptotics, and generalized von
Mangoldt hierarchy remain manuscript proofs. Literature, novelty, exposition,
peer review, and publication judgments are outside the kernel.

## Exact artifact hashes

SHA-256:

```text
b7666b592dd3a5922596bf35fc57ca228840f2e340e51a51f50cc517c3e26431  Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf
344a60845311253fcac8fd01933ba8af7e9f9dda2f0a04f9c4e55ef0df8d20e9  Manuscript/paper.tex
3a66df0c25310c878132a1f1e85c5f9017223e03498f9d7313435822fca8feb4  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
5912536caeff092fbfa3468fdbc5e458d9214bcfb6fb06d8bf3639b4be51a9f9  Lean/RiemannHypothesisProofFactory/SelbergConditioning/FiniteKernel.lean
7cfce81c6a1bfa284a1aa9cef4b944daceb2dfe1b5a84c48e191855f587411a1  Lean/RiemannHypothesisProofFactory/SelbergConditioning/ConditioningWitness.lean
056aa0613d77495b6650f98c1dc5bf7eb64d2e6a6917c2d22e162154dd9c32dc  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
b3bc383bad015d138a96014321e43029a02bf4591469df33adf6c74e1e021f41  Lean/Challenge.lean
947fd3d5407fb0230295c408a5cf1d66aa4612743085fcedbfbb277651079ffa  Lean/Solution.lean
71c1bb8c7e929c3d0feca0313b226b604964845b05c66b52a4f238a3b5440503  Lean/comparator.json
68620c45479ec23e19737c747b1857b308828646ced11b01c174c463a353b474  Lean/formalization.yaml
```

No commit, push, registry upload, or submission is certified here.
