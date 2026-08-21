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

The pinned project build completed successfully (3,012 jobs). The direct
challenge, solution, and certificate checks completed with exit code 0. The
three `sorry` declarations are the intended holes in `Challenge.lean`.

The certificate prints five axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `Lean.ofReduceBool`, `set_option`, or
`decreasing_by` declaration.

## Independent statement checks

The comparator configuration selects the exact three-theorem Challenge/Solution
surface. The repository workflow runs Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840` in an isolated Linux
execution. Its result is bound to the tested Git commit.

## Verified scope

Lean proves the finite prime-factor construction with exact weighted centering
and the logarithmic residual bound from prime factorization. Under an explicit
positive scale and the stated two-sign hypotheses, it proves nonzero output
separation and a strictly positive lower bound for every admissible Lipschitz
constant. It also proves the complete finite ordered-Selberg perturbation bound
from global nonnegativity, prefix, logarithmic-moment, and harmonic-mass
hypotheses.

The analytic lower bound for the constructed signed sum, prime-number
asymptotics, residual moments, and generalized von Mangoldt hierarchy remain
manuscript proofs.

## Exact artifact hashes

SHA-256:

```text
b7666b592dd3a5922596bf35fc57ca228840f2e340e51a51f50cc517c3e26431  Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf
344a60845311253fcac8fd01933ba8af7e9f9dda2f0a04f9c4e55ef0df8d20e9  Manuscript/paper.tex
3a66df0c25310c878132a1f1e85c5f9017223e03498f9d7313435822fca8feb4  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
f52f2f0aaaedf0520a08575bd766045baf8ef691ab52a05e6a37091a06fe10d9  Lean/lakefile.toml
50241e3bea29b745ce3dd982d7135c23b76a219c1e5acedef300ce80de26355a  Lean/RiemannHypothesisProofFactory/SelbergConditioning.lean
4f031ad3d80bced56c19439fc18595f78c3b270b7b1b59459ae5399a639f1cc6  Lean/RiemannHypothesisProofFactory/SelbergConditioning/ConditioningWitness.lean
2f416bcccba710108a3ba5f9dfcc8b884900d67a7f4142e6f13265d016dff3c7  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PrimeFactorConstruction.lean
9c0d25dbc8bee5be986d9080e6a10bb50e420a70f6bc4e261219c1d8fbf3563e  Lean/RiemannHypothesisProofFactory/SelbergConditioning/SelbergStability.lean
b7927a093175ad9dac6456f5975d02035e26b93d555a5e4f3bdca9c316d2fd99  Lean/RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
a33b979106f161f18f3560091c871174d9366d35745ee7345ef4956b96579605  Lean/Challenge.lean
a8d2d21d4f9e567534eb4d8de3b801310670ed314d8545062b739d882d8ac27e  Lean/Solution.lean
7f3b4e19a5178927adb1b996861e6c9405bb77114df34bc1f4b6300684528d69  Lean/comparator.json
28e449e44f238603622d8e44219a9ba624a3fe1d9e2122833ef8bf04bb6697ad  Lean/formalization.yaml
```
