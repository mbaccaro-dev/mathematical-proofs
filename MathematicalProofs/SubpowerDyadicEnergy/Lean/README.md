# Lean verification

This self-contained Lean 4 project proves the paper's central discrete
power-of-two energy consequences.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Build

From this `Lean` directory, run:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
```

The public statement and proof surfaces are `Challenge.lean` and
`Solution.lean`. Their exact comparison configuration is `comparator.json`.

## Exact scope

Lean checks:

- the literal Möbius-logarithm weights, prefix sums, and half-open dyadic blocks;
- the exact global power-of-two balance joining dyadic defect, block variation,
  and completed cumulative energy, including its initial boundary term;
- the sharp `6 / pi^2` leading energy coefficient under an explicitly stated
  weighted-squarefree remainder estimate; and
- the all-endpoint cubic cumulative-energy bound from eventual nonnegativity
  only on the power-of-two blocks, with earlier scales kept explicitly.

Lean does not check the paper's subpower-energy equivalences, Mellin or Fourier
analysis, holomorphic continuation of reciprocal zeta, functional-equation
argument, the weighted-squarefree remainder premise, local pole-energy
analysis, simplicity of zeros, reciprocal-residue budget, or any assertion of
the eventual sign condition. Those remain manuscript-level mathematics.
