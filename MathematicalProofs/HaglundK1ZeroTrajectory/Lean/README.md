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

For the full independent verification, run from the repository root:

```text
bash scripts/verify-palomar.sh MathematicalProofs/HaglundK1ZeroTrajectory/Lean
```

## Exact scope

Comparator selects one composite theorem over the literal incomplete-gamma
pencil. Given the exact first-quadrant certificate, it proves that every
first-quadrant zero is simple and has a locally unique analytic branch with its exact
negative imaginary velocity. It also proves that the pencil is real and
strictly positive on the imaginary axis for every nonnegative parameter, and
that every certified forward branch strictly descends and stays inside an
explicit radius.

The interval-arithmetic proof of the first-quadrant certificate is external to
Lean. Real-axis positivity, Weierstrass preparation, Puiseux existence, and
the full arbitrary-multiplicity multiset argument are proved in the manuscript
and are not represented as Lean-checked.
