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
lake env lean RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
```

The build completed successfully (2,765 jobs). Direct checks of
`Challenge.lean`, `Solution.lean`, and the public certificate completed with
exit code 0. The only `sorry` is the intended challenge hole.

The certificate prints 13 axiom reports. None contains `sorryAx`; the reported
dependencies are the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding the challenge
found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`, `set_option`,
or `decreasing_by` declaration.

## Palomar preflight

The exact four-theorem Challenge/Solution surface passed Comparator at commit
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

Lean checks divergence of the exact weights `Lambda(n) / sqrt(n)`, equality of
the positive-integer and prime-power-filtered prefixes, the sharp abstract
local threshold, divergence of every scalar budget paying the required local
cost, and the finite-prefix and summable-weight controls.

The concrete smooth compactly supported dilation, autocorrelation tail, and
explicit-formula sign and normalization bridge remain manuscript proofs.
Literature, novelty, exposition, peer review, and publication judgments are
outside the kernel.

## Exact artifact hashes

SHA-256:

```text
b4e0bcf5353897dcf5e3f9f1713f66759010f59f7dcd5979107d071c63f9b234  Manuscript/prime_local_weil_obstruction_baccaro_20260818.pdf
40b3490b99af524cb5752a06f48abca981955a2357bc0d625fc149057798f66c  Manuscript/paper.tex
36895e484cac085b33492b0376a17aea7200454d186f321161c40571db8b86de  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
a56e34e5496f4ecf4ebf030d1fe872845d3db34b83e7e97cd74da47a1ae77a1a  Lean/RiemannHypothesisProofFactory/PrimeLocalWeil.lean
c9874a3c56cf4aed9529172cb1f96fa65576efe716da063c57faf264c356a512  Lean/RiemannHypothesisProofFactory/PrimeLocalWeil/BudgetObstruction.lean
e347641d400eb5107f9470b142f3e480c7ae3187b1fae088371feeeda0d82e14  Lean/RiemannHypothesisProofFactory/PrimeLocalWeil/PaperCertificate.lean
fb7a76f16d8bf33aca006162ef08f2c2c5e80d07e0cfb0e42ed623555e599cdb  Lean/Challenge.lean
2da9ac2c25626ec6f4d75cd760fe107c0d1868848893ea61915f6fd84b195393  Lean/Solution.lean
70b439bc7e0e86085b893f636675b412aa8fd985d6dd80dbd84a2bc85b8d49ba  Lean/comparator.json
42e1b6b5df16b3f2304ea5aa5db831b54c188f6e19eef57c10b5ded75eb1fc65  Lean/formalization.yaml
```

No commit, push, registry upload, or submission is certified here.
