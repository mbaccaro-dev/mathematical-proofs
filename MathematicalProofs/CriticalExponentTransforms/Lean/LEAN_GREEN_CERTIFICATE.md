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
lake env lean RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

The pinned project build completed successfully (3,254 jobs). The direct
challenge, solution, and certificate checks completed with exit code 0. The
six `sorry` declarations are the intended holes in `Challenge.lean`.

The certificate prints thirteen axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `Lean.ofReduceBool`, `set_option`, or
`decreasing_by` declaration.

## Independent statement checks

The comparator configuration selects the exact four-theorem Challenge/Solution
surface. The repository workflow runs Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840` in an isolated Linux
execution. Its result is bound to the tested Git commit.

## Verified scope

For real-valued continuous signals on the positive half-line, Lean derives the
exact finite perturbation expansion from multilinearity and dilation
covariance. It proves the normalized dyadic-energy limit by dominated
convergence. Under the exact first-visible-term hypotheses, it also proves the
leading norm limit, strict positivity of the energy constant, and the exact
critical-exponent gap. For nonlinear periodic phase orbits, Lean derives the
complete logarithmic normal form. Given one positive dyadic-energy block, it
proves the exact full-turn recurrence and positivity of the next block, so the
selected phase theorem cannot collapse to the zero orbit.

The measure-theoretic derivation of a positive phase block and the paper's
zero-channel, error-term, complex-measure Mellin, saturation, and two-sided-germ
branches remain manuscript proofs.

## Exact artifact hashes

SHA-256:

```text
c1a2d4ee7f6183c8385484af175ab484a94a5d28dec55c1e542f18b197ec8bff  Manuscript/critical_exponent_scale_transforms_baccaro_20260818.pdf
629457318ffbcf2d1db5bbf6f1a555e2179702ec480e41492e5dc1fe67d2511a  Manuscript/paper.tex
77fe2fec5a45a82ce0d7c7d1a27b7ac39f7d9d5a06bba7ee241d21b1922e690d  Manuscript/references.bib
d6d2691747f295ea7ba8e4e771934a177362166641f7b3538f4382141971d717  Lean/lake-manifest.json
b2b5068d5a4835675e651ce83b29c0ddb308d28b80076e7c007aef4630af0477  Lean/lean-toolchain
8e81aa1c1744577c7043bdb7b03057ef25106fe054cc0d945117d8bf3d6e526e  Lean/lakefile.toml
7dbb1306611c3db1a5ce5744c6982ede26796af1b273e5dd199d679ae6f417a6  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms.lean
44e25459fec8bd42b6bf6c0c95cc2609f5e69daf5477c81b028516868115e295  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/AlgebraicKernel.lean
1c82f981fe18ecea0e485b515219a45ea0ea535975f23f67db4552007a00c0e9  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PurePowerGap.lean
fde5e8f28fd84a9998f1e567fc111ceae8599af1e356def5f3ce340b526ff270  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/FiniteMixture.lean
b4be536f16e762d1b3d1ba2a9bca4a8b3eeb6da58054d1ea2eb71e80043996f1  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/MultilinearMixture.lean
4e6eb3911f85876778aae749b96f82aaa938a9cc2cb2d54f17581fefde527ff3  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/MixtureEnergy.lean
c2ba1cc1b368635550c264bd6f43c08b5d64023575a411174af6365bcccdffd1  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/MixtureGapLaw.lean
a3fb2616152a3a95af6ccac73ea60aa57ed0ef8e550f0d194eee13ea97cf76f3  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PhaseOrbit.lean
0a147d18f7504bc48c8f01c51f37d30a69ae17493c3f630529c2988ca6fc182b  Lean/RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
ae0c3f1aa9756c8e66671ae95c242a428a953cbd40a9e2b3e580753531634b6e  Lean/Challenge.lean
a098c5952adc626141bf47380cdae024b54226f4c0f8655628ffe884e51a4b25  Lean/Solution.lean
bf44421561687537cf91a44220e019b226bc1b4d2b19effd85fe64e5e144da06  Lean/comparator.json
027b0e4d35facf0768b6a7c52cb458473c177c8ca60fcbb42d8c16de3d58d7b6  Lean/formalization.yaml
```
