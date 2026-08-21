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

The pinned project build completed successfully (3,011 jobs). The direct
challenge, solution, and certificate checks completed with exit code 0. The
two `sorry` declarations are the intended holes in `Challenge.lean`.

The certificate prints two axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `set_option`, `decreasing_by`, or
`Lean.ofReduceBool` use.

## Independent statement checks

The comparator configuration selects the exact two-theorem Challenge/Solution
surface. The repository workflow runs Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840` in an isolated Linux
execution. Its result is bound to the tested Git commit.

## Verified scope

Lean proves the exact conservation law connecting the paper's dyadic defect,
block variation, boundary term, and positive cumulative prefix energy, with
the strict predecessor convention and both right endpoints. Assuming the
paper's universal two-endpoint condition, it derives an explicit cubic
logarithmic bound for cumulative energy at every integer endpoint.

The two-endpoint condition itself is not proved. The equivalence with the
Riemann hypothesis, Mellin and Fourier analysis, reciprocal-zeta continuation,
zero simplicity, and reciprocal-residue budget remain manuscript proofs.

## Exact artifact hashes

SHA-256:

```text
1a1c7d260bbc8b793d201114feae24148097dcfd3484a8bb113d65416750854f  Manuscript/subpower_dyadic_mobius_mangoldt_equivalence_baccaro_20260820.pdf
83960fcc8d28b7f8d3b25406954e6278859527e3e5f9f546dbb7d21d537ca9ec  Manuscript/paper.tex
bffbd18097880fd6a9fe24d7a1d37cc408e8e19e96d6e2ec65fb2ca32f5fa1ab  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
12106ce1df01821b8728a993623c02551d6598228ac25def62e374756ba2d9f7  Lean/lakefile.toml
2f28d20f06efacd4c41b901c6e670138492b740424fa20c5298b4b3a85954483  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy.lean
c56f1735e03f82d5a8cd0ca00a100a5f537cbc7ef3a6611f51bec3a4196fd92b  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/DiscreteKernel.lean
afba0761c012297b9a2a1540909cc355a13d2c5245fdf8c15017a42ae68c2c45  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/DyadicBalance.lean
e30615f9444f4d0bf0e8d155b13ab6afa4e445d41a98fc9a8e5faacd9ca7f918  Lean/RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
f376eadef39f23b957e9394fb723ddac205d4b854a2435e31f80a32653e3643b  Lean/Challenge.lean
09af9493458d577177123cdbf3cd07229f194333bd4db3452183314b527f153f  Lean/Solution.lean
09a33c4a0bbd824e1322fea4d8a382310865bf7f14471a1b650c4dcd0cd72e72  Lean/comparator.json
3b7dd2e35bd435fd750e5844efa93818839bbd668cb7da645ee842beb2b8c7e1  Lean/formalization.yaml
```
