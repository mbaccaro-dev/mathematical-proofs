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
The five `sorry` declarations are the intended holes in `Challenge.lean`.

The certificate reports only the standard Lean and Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding
`Challenge.lean` and generated dependencies found no `sorry`, `admit`,
`unsafe`, explicit `axiom`, or partial definition.

## Independent statement checks

The Comparator configuration selects five statements together with their
literal source definitions. The exact Challenge/Solution pair passed
Comparator at commit `68a064109f01c08f47c8edc9f51d6a2bbffaa188`,
Lean4export at commit `15f6055e299ad5b89345e533cc2192f4cc00f659`,
the Lean default kernel, and NanoDa at commit
`68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Comparator replay used its upstream-compatible non-isolating
Windows development shim. The repository workflow pins Landrun at commit
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` and repeats the same checks in an
isolated Ubuntu job.

## Verified scope

Lean checks the literal first incomplete-gamma pencil, the exact implication
from the four-way first-quadrant certificate to simple zeros and strict
downward velocity, imaginary-axis exclusion for every nonnegative parameter,
the explicit forward branch bound supplied by the outer-cone estimate, the
one-sided collision-direction contradiction, and the local analytic zero
branch with its exact derivative.

The numerical interval atlas, real-axis positivity, Weierstrass preparation,
Puiseux existence, and the full arbitrary-multiplicity collision multiset
theorem remain outside Lean. The manuscript states and audits those parts
separately.

## Exact artifact hashes

SHA-256:

```text
f85c12a07d606d5e8d870040e0ca6891d2011160cd943ed6f587c2616b037bdc  Manuscript/hc4_k1_zero_trajectory_theorem_baccaro_20260822.pdf
6313438135586f343a1a9f7bb96f0d5eafcee86aa3e03c58fe4dafc3907abf33  Manuscript/paper.tex
a0edf199c09bf206395836269c4997af866fd9874e8ebdfd34b446dbe1947360  Manuscript/references.bib
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
eec5369a6f0f28ba70102e666516a8c158829c77233887bd6a05476ce8c90b44  Lean/lakefile.toml
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
7fef2cffffe3810c19aeeb8b01cc7b244355d51fe2af3ddde8cc2acaae049f4  Lean/HaglundK1ZeroTrajectory/AnalyticCertificate.lean
1f1d5cec300cb06b76614457f45d41b6784cb4407ef6550a5f7169db411ca9e8  Lean/HaglundK1ZeroTrajectory/PaperCertificate.lean
4f0988c26478ea53eea1a1a4b0066b5858131dea3ee47817fc4134eeddc14231  Lean/Challenge.lean
faf38d1538bdf1156818d70b43f7b07d3837a0c2dd6c9f52f183f676a69e7afc  Lean/Solution.lean
921e5c380087dbdb5af97b594c8c172048923b5dc7c4a25e82e4bea0b29af88b  Lean/comparator.json
c96940d4d8d73f1100022e65137d3b376fd572e57a9484c99360d7a9a001ce72  Lean/formalization.yaml
```
