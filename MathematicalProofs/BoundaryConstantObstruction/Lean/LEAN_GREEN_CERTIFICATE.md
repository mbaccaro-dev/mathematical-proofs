# Lean Green and Palomar preflight certificate

Status: **PASS**

Verification date: 2026-08-20

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0 at commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Lean checks

The pinned project build completed successfully (3,196 jobs). On Windows, the
full build used an exact-byte hard-linked verification copy with a shorter path
because one generated Mathlib path exceeds the legacy 260-character limit at
the repository's normal location. Direct checks of `Challenge.lean`,
`Solution.lean`, and
`BoundaryConstantObstruction/IncompleteGamma/PaperCertificate.lean` all
completed with exit code 0. The only `sorry` is the intended challenge hole.

The certificate prints 12 axiom reports. None contains `sorryAx`; the reported
dependencies are the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding the challenge
found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`, `set_option`,
or `decreasing_by` declaration.

## Palomar preflight

The submitted Comparator surface contains one research-level theorem:
`IncompleteGammaApproximant.theorem_A`. The exact Challenge/Solution pair
passed Comparator at commit `68a064109f01c08f47c8edc9f51d6a2bbffaa188`,
Lean4export at commit `15f6055e299ad5b89345e533cc2192f4cc00f659`,
the Lean kernel, and NanoDa at commit
`68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Comparator replay used its upstream-compatible non-isolating
development shim. The repository workflow pins real Landrun at commit
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; that isolation gate will run on
Ubuntu after a separately authorized push. The `formalization.yaml` file
passes the exact Palomar v0.4 schema and the repository's equivalent local
metadata checks. `enable_nanoda` is exactly `true`.

## Verified scope

Lean checks the paper's fully quantified main theorem: every finite
positive-shift incomplete-gamma approximant in the stated family has a
nonreal zero. The imported development also checks the finite definitions,
theta boundary identity, analytic and entire-function lemmas, growth estimate,
reflection-factorization contradiction, endpoint behavior, local zero motion,
and local-uniform convergence used by that theorem.

Literature attribution, novelty, exposition, peer review, and publication
judgments are outside the kernel.

## Exact artifact hashes

SHA-256:

```text
c3355319fc5db20927e31df5b3e792073d625cc9f8d1c093da32f25c458d72e4  Manuscript/boundary_constant_obstruction_baccaro_20260814.pdf
52bc123339394d11734aee828cb3a3295755778cc7ccf6b0272606ca5075d64d  Manuscript/paper.tex
a362616de608ac4a411900234a96b07e41d63336a3e1e30a8d546247baa7bc0a  Manuscript/references.bib
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
a5ae1b0f672acc80b9a419efa0673e05e36dc84732deea0ef8a20340ae6325ad  Lean/BoundaryConstantObstruction/IncompleteGamma/PaperTheorem.lean
e59c40f8cf72a15ca4c36776064c24d3383483e19e5831e7d5bc64b68352c081  Lean/BoundaryConstantObstruction/IncompleteGamma/PaperCertificate.lean
96a21b685a05035bc1ad89679e6538ff88ed768f617eae9aaed8f202f98e24c2  Lean/Challenge.lean
4cf0344a77956ead704e25944385e4faafde7befdffb8fc4b574e911878c40c5  Lean/Solution.lean
81e6b380be62d97bdc79d165c1bcfe5cd9f19a565493a3eab97100f272b5ca94  Lean/comparator.json
f2bae9e7bccaeb7825a20482bb40fb50f848445cda38d7b9d05bbedd5ef58740  Lean/formalization.yaml
```

No commit, push, registry upload, or submission is certified here.
