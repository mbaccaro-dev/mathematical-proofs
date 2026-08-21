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
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The pinned project build completed successfully (3,013 jobs). The direct
challenge, solution, and certificate checks completed with exit code 0. The
single `sorry` declaration is the intended hole in `Challenge.lean`.

The certificate prints six axiom reports. Each contains only the standard
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

Lean proves that a finite zero-sum squarefree Möbius cell whose actual gcd
leaves a fixed residual budget admits an increasing-rank compression into
opposite-sign pairs. It preserves the two residual budgets, bounds pair gaps by
the cell diameter, and identifies exactly which pairs cross each real cutoff
and how many do so.

The asymptotic logarithmic lower bound, prime-number-theorem input, binomial
estimates, scale conversion, and global sparse-jump argument remain manuscript
proofs.

## Exact artifact hashes

SHA-256:

```text
f10f62e5f474d7c302983021df5c19813f329ae46b66a4ef3e74da99b37f74a7  Manuscript/mobius_residual_complexity_baccaro_20260818.pdf
e0b7ba28d972aaf75163c74a3134f6d30f0136ab4c1b826b0cf46b07c5f1ce03  Manuscript/paper.tex
549f9ccab57d9a7ad304e975ad802f9424921e1387b4f88a599fd8db326b1026  Manuscript/references.bib
57a25208918a32866cab3f80a9c51b215c7ba9e2524b2391d6056338f3947d53  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
5fc3e18ac5ca1890066e00c7456e75e89bd424c0b6cd75a61faa5ca13153ca2d  Lean/lakefile.toml
7e3fa48470efed54e382d0b680f1cac7add7b058d5f46a3d327b26e6e504401b  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity.lean
0cc02375dd76e63f17eafd841d94ea39a736c292b53643e5d0f587a148dcc0ff  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/CombinatorialKernel.lean
164214a01546aa76a57e4199a196f4d556c1485cfa717bbd69cf90a3d972f4c6  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/ExactCompression.lean
3f696d5cfb9b7b4c95362cf93af8e5cd8b3f7c63f9a3a91388e2887aab1d269d  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PairCompression.lean
37852840e69da2e1ebf75f9e26f9f644738547e8fcf65a6409fa291c4f8abe38  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
ffd1f5d5e574a4fd1fd1874ccdf5c43d8c05315dfe65d1f85235c4127bc304e7  Lean/Challenge.lean
c60a8a31c9098d04b7fb727e55a4e968971e3b30eaffd73d98b7f388f987d70a  Lean/Solution.lean
579d2ccb32d7a9957780ab0265f05f6a1bf0e9cea0fc87691973470a5655d2cd  Lean/comparator.json
8ce770396750b91a3c678fc8916c1f20679dac1ca3e7408f21949f92cf6f38d1  Lean/formalization.yaml
```
