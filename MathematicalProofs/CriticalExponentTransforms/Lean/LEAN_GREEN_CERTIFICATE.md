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
lake env lean RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

The pinned project completed its 3,010-job build successfully. The public
theorem certificate completed with exit code 0. Its axiom report contains no
`sorryAx`; the listed dependencies are the standard Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`.

A static scan found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`,
`set_option`, or `decreasing_by` in the project source.

## Verified scope

Lean checks:

- the multilinear orderwise and adjacent exponent-gap identities;
- strict decrease of successive multilinear exponents under the printed order;
- the shared homogeneous and phase exponent-gap identity;
- a scalar pure-power normal form from its scale equation;
- the saturation and two-sided-germ exponent arithmetic;
- strict interiority and exact inversion of saturation at positive scale; and
- the inverse Mellin-symbol lower bound from a bounded reciprocal symbol.

The Abel integral, vector-valued multilinear expansion and asymptotics,
phase-orbit normal form and periodic block analysis, operator-level pure-power
theorem, complex-measure Mellin theorem, saturation asymptotic and connector,
two-sided-germ comparison, and dyadic energy laws remain manuscript proofs.
Literature, novelty, exposition, and publication judgments are also outside
the kernel.

## Exact artifact hashes

SHA-256:

```text
c1a2d4ee7f6183c8385484af175ab484a94a5d28dec55c1e542f18b197ec8bff  Manuscript/critical_exponent_scale_transforms_baccaro_20260818.pdf
ed00fc9ed3b6c5a95be977bc121d53ae566c27e9508cbc2801c48ebfcd6768e3  Manuscript/paper.tex
69f79d7e2f5c02f1574708a920e8ac2e2d1005310a22b6c56a83a828ee9087e8  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
097429813827453a08672578c928d10829c17a8dfa3bf5367e6ddac269a4af8e  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
dfbcd8a1a12e7485761c01aad0a5e7c9b08e0c8b075bcfdf4f7b1205d1c8efe9  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/AlgebraicKernel.lean
```

The GitHub Actions workflow repeats the pinned build and public certificate
check on every push and pull request.
