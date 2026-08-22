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

The pinned project build and the direct challenge, solution, and certificate
checks completed successfully. The single `sorry` is the intended theorem
hole in `Challenge.lean`; the solution and implementation contain none.

The certificate prints one axiom report containing only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `Lean.ofReduceBool`, `set_option`, or
`decreasing_by` use.

## Independent statement checks

The comparator configuration selects the exact one-theorem Challenge/Solution
surface. A local replay passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`. The local replay ran
without Linux Landrun isolation. The repository workflow is configured to run
the same pinned checks under Landrun isolation for its committed SHA.

## Verified scope

Lean constructs the two explicit plus/minus von Mangoldt perturbations from
the stated standard analytic inputs. For every sufficiently large observation
scale and every tolerance in `(0, 1]`, it proves positive prime-power cone
membership, divisor-feedback error at most that tolerance through twice the
scale, a quantitative near-linear separation of the two summatory errors, and
one uniform linear Selberg bound for both weights.

The weighted prime-number limit, negligible powers-of-two contribution,
coefficient and Chebyshev estimates, divisor identity, moment and harmonic
bounds, and classical Selberg estimate are explicit hypotheses rather than
formalized analytic proofs. The generalized von Mangoldt hierarchy remains
manuscript-level mathematics.

## Exact artifact hashes

SHA-256:

```text
b7666b592dd3a5922596bf35fc57ca228840f2e340e51a51f50cc517c3e26431  Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf
344a60845311253fcac8fd01933ba8af7e9f9dda2f0a04f9c4e55ef0df8d20e9  Manuscript/paper.tex
3a66df0c25310c878132a1f1e85c5f9017223e03498f9d7313435822fca8feb4  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
f52f2f0aaaedf0520a08575bd766045baf8ef691ab52a05e6a37091a06fe10d9  Lean/lakefile.toml
e59b33c3fc5d3657ede773a476c077593319b17b3fe0dca9eda8d52d21fd7f75  Lean/Challenge.lean
b89fe6e3520f10a1aaad5e9c6e318b0d168ee96bb0069c9ad839baacf4822feb  Lean/RiemannHypothesisProofFactory.lean
1e55d785d42fa311c7aa7e151be84155109995242464df9f57fcf45f948e67ea  Lean/RiemannHypothesisProofFactory/SelbergConditioning.lean
4f031ad3d80bced56c19439fc18595f78c3b270b7b1b59459ae5399a639f1cc6  Lean/RiemannHypothesisProofFactory/SelbergConditioning/ConditioningWitness.lean
5912536caeff092fbfa3468fdbc5e458d9214bcfb6fb06d8bf3639b4be51a9f9  Lean/RiemannHypothesisProofFactory/SelbergConditioning/FiniteKernel.lean
88c0f63037b47f86d612eef4668083a53fc0b7cf75e209165a7b7b32731ff940  Lean/RiemannHypothesisProofFactory/SelbergConditioning/InfinitePrimePowerConstruction.lean
c566013dfae56670ff48e929bccafeea1428a24afea3270e1a11fcafdf01192e  Lean/RiemannHypothesisProofFactory/SelbergConditioning/NearLinearConditioning.lean
ed77c6d1c11cb804e57442f3b1825cd4a4968a6524b64ab9e60dd2316cbf6ed3  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
2f416bcccba710108a3ba5f9dfcc8b884900d67a7f4142e6f13265d016dff3c7  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PrimeFactorConstruction.lean
9c0d25dbc8bee5be986d9080e6a10bb50e420a70f6bc4e261219c1d8fbf3563e  Lean/RiemannHypothesisProofFactory/SelbergConditioning/SelbergStability.lean
e6f2885b2318997c6950c971b4c020c37dfe1c9d2468ad86e74857c9d4651941  Lean/Solution.lean
8858ea536a43ccb69adde34b449903545a4c38ce2e7bab10744e13f38ed12bf5  Lean/comparator.json
b798233910cea8a460eebbb0483996e47e3036055052810c038c0cdfb22d1bfe  Lean/formalization.yaml
```
