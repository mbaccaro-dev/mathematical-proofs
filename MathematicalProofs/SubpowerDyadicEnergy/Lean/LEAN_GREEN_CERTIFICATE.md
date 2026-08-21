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
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
```

The pinned project build completed successfully (3,010 jobs). The direct
challenge, solution, and public-certificate checks completed with exit code 0.
The four `sorry` declarations are the intended holes in `Challenge.lean`.

The public certificate prints four axiom reports. None contains `sorryAx`; all
four report only the standard Lean/Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`. A source scan excluding the challenge
found no `sorry`, `admit`, `unsafe`, explicit `axiom`, `partial`, `sorryAx`,
`set_option`, `decreasing_by`, or `Lean.ofReduceBool` use.

## Comparator and independent-kernel checks

The exact four-theorem Challenge/Solution surface passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean kernel, and NanoDa at
commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`.

The local Comparator replay used its non-isolating development launcher on
Windows. The repository workflow pins real Landrun at commit
`811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`; the isolated run is performed by
the Ubuntu workflow. `formalization.yaml` passes the Palomar v0.4 schema,
`enable_nanoda` is `true`, and the selected Lean project contains exactly one
Lake file, one toolchain file, and one committed manifest. `Challenge.lean` is
106 lines and 3,446 bytes, below Palomar's preferred review surface.

## Verified scope

Lean checks the exact dyadic prefix-square identity, including the strict
predecessor convention and both right endpoints. Under the paper's universal
two-endpoint defect condition, it checks the sharp one-step recursion, the
floor-halving recurrence, and an explicit cubic logarithmic bound for
normalized prefix energy.

The condition itself is not proved. The subpower-energy equivalences,
Mellin-Plancherel argument, reciprocal-zeta continuation, functional-equation
step, squarefree asymptotics, local pole-energy analysis, simplicity theorem,
reciprocal-residue budget, and the equivalence with the Riemann hypothesis
remain manuscript-level mathematics.

## Exact artifact hashes

SHA-256:

```text
1a1c7d260bbc8b793d201114feae24148097dcfd3484a8bb113d65416750854f  Manuscript/subpower_dyadic_mobius_mangoldt_equivalence_baccaro_20260820.pdf
83960fcc8d28b7f8d3b25406954e6278859527e3e5f9f546dbb7d21d537ca9ec  Manuscript/paper.tex
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
c56f1735e03f82d5a8cd0ca00a100a5f537cbc7ef3a6611f51bec3a4196fd92b  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/DiscreteKernel.lean
2bb3657692eed721b343e4beef6ed17ac1630c618fbf96206a415f5b8eb20f55  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
f8b7f09018710a583d9f701bdc2c51a1caf4f767363a8e8302cde129b66dce04  Lean/Challenge.lean
0d1ced1ca1a01297d2bb3157ee94e92ebd6c35b7c1e00feed60e442749cc8117  Lean/Solution.lean
a8be52adc2d61e04752e7fff147a5a95d3cf5b4d447d21ac8e95eeb4611bdb74  Lean/comparator.json
5c62ed9a110463317f6657eb5dee04f910f4592ea56fee321abbbdc415873749  Lean/formalization.yaml
```
