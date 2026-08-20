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
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The build completed successfully (3,012 jobs). Direct checks of
`Challenge.lean`, `Solution.lean`, and the public certificate completed with
exit code 0. The only `sorry` is the intended challenge hole.

The certificate prints 12 axiom reports. None contains `sorryAx`; the reported
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

Lean checks opposite-sign pair cancellation, the finite matching bound,
zero-sum cell balance, the exact rank-pair crossing interval and cardinality,
the signed prefix-balance formula, inheritance of the residual prime-factor
budget under pairwise gcd, the terminal exponent contradiction, the
square-root threshold identity, and endpoint-doubling connectors.

The prime number theorem, band-product asymptotic, logarithmic scale
conversion, construction and ordering of the Möbius-sign lists, sign parity
after gcd removal, and global sparse-jump counting remain manuscript proofs.
Literature, novelty, exposition, peer review, and publication judgments are
outside the kernel.

## Exact artifact hashes

SHA-256:

```text
f10f62e5f474d7c302983021df5c19813f329ae46b66a4ef3e74da99b37f74a7  Manuscript/mobius_residual_complexity_baccaro_20260818.pdf
e0b7ba28d972aaf75163c74a3134f6d30f0136ab4c1b826b0cf46b07c5f1ce03  Manuscript/paper.tex
549f9ccab57d9a7ad304e975ad802f9424921e1387b4f88a599fd8db326b1026  Manuscript/references.bib
57a25208918a32866cab3f80a9c51b215c7ba9e2524b2391d6056338f3947d53  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
0cc02375dd76e63f17eafd841d94ea39a736c292b53643e5d0f587a148dcc0ff  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/CombinatorialKernel.lean
164214a01546aa76a57e4199a196f4d556c1485cfa717bbd69cf90a3d972f4c6  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/ExactCompression.lean
7b8fa74c7ea68d0ed40f1475748f47d0363cabdfc4dd6c4cf2e22046f1ae5c1e  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
b31912302ddfac23a29d8366cee7a38e5510cb8ae81a3443bcdd9015ac74af88  Lean/Challenge.lean
2f91058a496341a1b6a5ccc9d56a2f9f24c8e58ea8d5e1a945560980afb70dc0  Lean/Solution.lean
92d3afab87717ad2cf0f673799c1876250fb05cbabd325e67e483ba3124bea68  Lean/comparator.json
ac94f76ae00fa052d1b0150cce874eb9942a4e890ee02a897d61381b561202a5  Lean/formalization.yaml
```

No commit, push, registry upload, or submission is certified here.
