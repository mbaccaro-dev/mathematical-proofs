# Lean verification

This self-contained Lean 4 project checks the formalized analytic core of the
accompanying paper.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

## Build

From this `Lean` directory, run:

```text
lake build --wfail
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean HaglundK1ZeroTrajectory/PaperCertificate.lean
```

For the full Palomar preflight, run from the repository root:

```text
bash scripts/verify-palomar.sh MathematicalProofs/HaglundK1ZeroTrajectory/Lean
```

## Exact scope

Lean checks:

- the literal incomplete-gamma integral representation of the first pencil;
- the exact implication from the four-way interval certificate to simple
  zeros and strictly descending imaginary velocity;
- strict positivity on the imaginary axis for every nonnegative parameter;
- an explicit uniform branch bound from the paper's outer-cone estimate;
- the scaled-limit contradiction that excludes upper-half-plane emergence to
  the right of a real collision; and
- the locally unique analytic zero branch and its exact derivative.

The large interval atlas is an external verified computation. Real-axis
positivity, Weierstrass preparation, Puiseux existence, and the full
arbitrary-multiplicity multiset argument are proved in the manuscript and are
not represented as Lean-checked.
