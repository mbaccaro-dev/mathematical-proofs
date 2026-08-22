# Lean verification certificate

Status: **PASS**

Verification date: 2026-08-22

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0 at commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Checks

The pinned project completed `lake build --wfail` successfully (3,136 jobs).
Direct checks of `Challenge.lean`, `Solution.lean`, and
`HaglundK1ZeroTrajectory/PaperCertificate.lean` completed with exit code 0.
The six `sorry` declarations are the intended holes in `Challenge.lean`.

The certificate reports only the standard Lean and Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding
`Challenge.lean` and generated dependencies found no `sorry`, `admit`,
`unsafe`, explicit `axiom`, or partial definition.

## Independent statement checks

The Comparator configuration selects one composite nonreal zero-trajectory
theorem together with its literal source and certificate definitions. The
exact Challenge/Solution pair passed
Comparator at commit `68a064109f01c08f47c8edc9f51d6a2bbffaa188`,
Lean4export at commit `15f6055e299ad5b89345e533cc2192f4cc00f659`,
the Lean default kernel, and NanoDa at commit
`68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Comparator replay used its upstream-compatible non-isolating
Windows development shim. The repository workflow pins Landrun at commit
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` and repeats the same checks in an
isolated Ubuntu job.

## Verified scope

Lean checks the literal first incomplete-gamma pencil and a single composite
consequence of the exact four-way first-quadrant certificate. Every certified
zero is simple and has a locally unique analytic branch with its exact negative imaginary
velocity. The pencil is real and strictly positive on the imaginary axis for
every nonnegative parameter. Every certified forward branch strictly descends
and obeys the explicit radius bound supplied by the outer-cone estimate.

The interval-arithmetic proof of the first-quadrant certificate, real-axis
positivity, Weierstrass preparation, Puiseux existence, and the full
arbitrary-multiplicity collision multiset theorem remain outside Lean. The
manuscript states and audits those parts separately.

## Exact artifact hashes

SHA-256:

```text
f85c12a07d606d5e8d870040e0ca6891d2011160cd943ed6f587c2616b037bdc  Manuscript/hc4_k1_zero_trajectory_theorem_baccaro_20260822.pdf
6313438135586f343a1a9f7bb96f0d5eafcee86aa3e03c58fe4dafc3907abf33  Manuscript/paper.tex
a0edf199c09bf206395836269c4997af866fd9874e8ebdfd34b446dbe1947360  Manuscript/references.bib
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
eec5369a6f0f28ba70102e666516a8c158829c77233887bd6a05476ce8c90b44  Lean/lakefile.toml
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
d23d4b681de6a7647ddb912c370014d39ca2261e920f5be455f654c85e87e603  Lean/HaglundK1ZeroTrajectory/AnalyticCertificate.lean
bb60991e2943b6ed81b4bac63902d3c93a06d228500d7972a80894a062931871  Lean/HaglundK1ZeroTrajectory/PaperCertificate.lean
47f50bc355512bbd484d195d26b35f973caca00814beaa5faca706a0c61afc4a  Lean/Challenge.lean
faf38d1538bdf1156818d70b43f7b07d3837a0c2dd6c9f52f183f676a69e7afc  Lean/Solution.lean
24f0a6c2b4b59b6e8a4cbffbdf7c5947de8ba1d1226e26a91573d3bd314dbc7f  Lean/comparator.json
f90f1a41eccb22cf3880c6471b02b644dc29deb5f99edf9cd61f72b5294747b7  Lean/formalization.yaml
```
