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
lake env lean RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

The build completed successfully (3,011 jobs). Direct checks of
`Challenge.lean`, `Solution.lean`, and the public certificate completed with
exit code 0. The only `sorry` is the intended challenge hole.

The certificate prints 11 axiom reports. None contains `sorryAx`; the reported
dependencies are the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding the challenge
found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`, `set_option`,
or `decreasing_by` declaration.

## Palomar preflight

The exact 11-theorem Challenge/Solution surface passed Comparator at commit
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

Lean checks the operator-level pure-power normal form and exact critical gap,
the multilinear and homogeneous exponent identities, a scalar specialization,
saturation and two-sided-germ arithmetic, saturation interiority and inversion,
and the inverse Mellin-symbol lower bound.

The Abel integral, vector-valued asymptotics, phase-orbit analysis, pure-power
energy integral, complex-measure Mellin theorem, saturation connector,
two-sided-germ comparison, and dyadic energy laws remain manuscript proofs.
Literature, novelty, exposition, peer review, and publication judgments are
outside the kernel.

## Exact artifact hashes

SHA-256:

```text
c1a2d4ee7f6183c8385484af175ab484a94a5d28dec55c1e542f18b197ec8bff  Manuscript/critical_exponent_scale_transforms_baccaro_20260818.pdf
629457318ffbcf2d1db5bbf6f1a555e2179702ec480e41492e5dc1fe67d2511a  Manuscript/paper.tex
77fe2fec5a45a82ce0d7c7d1a27b7ac39f7d9d5a06bba7ee241d21b1922e690d  Manuscript/references.bib
d6d2691747f295ea7ba8e4e771934a177362166641f7b3538f4382141971d717  Lean/lake-manifest.json
b2b5068d5a4835675e651ce83b29c0ddb308d28b80076e7c007aef4630af0477  Lean/lean-toolchain
44e25459fec8bd42b6bf6c0c95cc2609f5e69daf5477c81b028516868115e295  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/AlgebraicKernel.lean
1c82f981fe18ecea0e485b515219a45ea0ea535975f23f67db4552007a00c0e9  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PurePowerGap.lean
33c5a999f0f444d172501d249d9ca1ea3ecb506b7f26352c1f492578bcb9b15c  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
43d1c1321880a5964ff24b8274060add03059ebc5b812d91ccf850f3a617cfc7  Lean/Challenge.lean
75a3f9b86230207bde956ef18e906409e17db94114a1764f208611213b25f236  Lean/Solution.lean
7d77c79ff152ecc26373df2ca6af05cd619ee9357f5c429ed895afa7c7fff960  Lean/comparator.json
317c943446aa7d700e090e3579b571f8fe9d11c074f90af8b9c49ce065e9828b  Lean/formalization.yaml
```

No commit, push, registry upload, or submission is certified here.
