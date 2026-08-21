# Lean verification

This self-contained Lean 4 project proves the paper's central discrete
cumulative-energy consequence.

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
- the exact conservation law joining dyadic defect, block variation, and
  completed cumulative energy, including both right endpoints;
- the logarithmic block estimate and floor-halving recurrence under the
  universal two-endpoint condition; and
- the resulting explicit cubic bound for the paper's positive cumulative
  prefix energy at every endpoint.

Lean does not check the paper's subpower-energy equivalences, Mellin or Fourier
analysis, holomorphic continuation of reciprocal zeta, functional-equation
argument, squarefree asymptotics, local pole-energy analysis, simplicity of
zeros, reciprocal-residue budget, or any assertion of the universal
two-endpoint condition. Those remain manuscript-level mathematics.
