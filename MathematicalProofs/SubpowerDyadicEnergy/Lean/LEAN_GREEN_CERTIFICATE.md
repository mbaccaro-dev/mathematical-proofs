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
lake env lean RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
```

The pinned project build and the direct challenge, solution, and certificate
checks completed successfully. The three `sorry` declarations are the
intended theorem holes in `Challenge.lean`; the solution and implementation
contain none.

The certificate prints three axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `Lean.ofReduceBool`, `set_option`, or
`decreasing_by` use.

## Independent statement checks

The comparator configuration selects the exact three-theorem Challenge/Solution
surface. A local replay passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`. The local replay ran
without Linux Landrun isolation. The repository workflow is configured to run
the same pinned checks under Landrun isolation for its committed SHA.

## Verified scope

Lean proves the exact power-of-two balance connecting dyadic defect, block
variation, and completed cumulative Möbius-logarithm energy, including the
initial boundary term. Eventual defect nonnegativity on exactly those dyadic
blocks gives an explicit all-endpoint cubic energy bound with the earlier
scales retained. With the explicitly assumed weighted-squarefree remainder
estimate, Lean also proves the sharp `6 / pi^2` leading coefficient at powers
of two.

The eventual sign condition and weighted-squarefree remainder estimate are not
proved. The subpower-energy equivalences, Mellin and Fourier analysis,
reciprocal-zeta continuation, functional-equation step, zero simplicity, and
reciprocal-residue budget remain manuscript-level mathematics.

## Exact artifact hashes

SHA-256:

```text
1a1c7d260bbc8b793d201114feae24148097dcfd3484a8bb113d65416750854f  Manuscript/subpower_dyadic_mobius_mangoldt_equivalence_baccaro_20260820.pdf
83960fcc8d28b7f8d3b25406954e6278859527e3e5f9f546dbb7d21d537ca9ec  Manuscript/paper.tex
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
12106ce1df01821b8728a993623c02551d6598228ac25def62e374756ba2d9f7  Lean/lakefile.toml
bf3f8a9c4a5b97ef2583a3b23785e17a1d46417869bfc967765576a59f08373f  Lean/Challenge.lean
8c7e22441f4beb06a615efd6de2a2ce86e3b6eb0a9faeaea39ab6a212774b4a4  Lean/RiemannHypothesisProofFactory.lean
51defac4bd87b61362af91aa83f138470d347d221fc59b787fc7631e8b66827c  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy.lean
c56f1735e03f82d5a8cd0ca00a100a5f537cbc7ef3a6611f51bec3a4196fd92b  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/DiscreteKernel.lean
afba0761c012297b9a2a1540909cc355a13d2c5245fdf8c15017a42ae68c2c45  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/DyadicBalance.lean
69301972bac09b7e8a6c37e35b4c4358a04c1e23442b5d68a08ea8c89314bcc9  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/EventualDyadicBalance.lean
88e65b24952008900359a4e88e5e01c67664c878fb72aa069acf61b1b02aa594  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
2831352c49816d784763b623b768114744e62233b8487a23a0e3f12e8737f7a1  Lean/Solution.lean
656f9489ccd6b8a0caf04fc9c1a1dfd60d34fe61ef747537d143c962a4786ffe  Lean/comparator.json
f29d6da5630fe95f00e0f8d1ed694bb0561f66bd3d7488cee1128192979ed29b  Lean/formalization.yaml
```
