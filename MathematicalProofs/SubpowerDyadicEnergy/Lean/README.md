# Lean verification

This self-contained Lean 4 project checks the discrete theorem core of the
accompanying paper.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`, commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Build

From this `Lean` directory, run:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/SubpowerDyadicEnergy/PaperCertificate.lean
```

The Palomar statement and proof surfaces are `Challenge.lean` and
`Solution.lean`. Their exact comparison configuration is `comparator.json`.

## Exact scope

Lean checks:

- the literal Möbius-logarithm weights, prefix sums, and half-open dyadic blocks;
- the exact identity `2D = 3V - H`, including the strict predecessor and endpoint completion terms;
- the sharp parity-uniform one-step prefix-energy recursion under the universal two-endpoint condition;
- the logarithmic block estimate and floor-halving recurrence; and
- the resulting explicit cubic bound for normalized prefix energy.

Lean does not check the paper's subpower-energy equivalences, Mellin or Fourier
analysis, holomorphic continuation of reciprocal zeta, functional-equation
argument, squarefree asymptotics, local pole-energy analysis, simplicity of
zeros, reciprocal-residue budget, or any assertion of the universal
two-endpoint condition. Those remain manuscript-level mathematics.
