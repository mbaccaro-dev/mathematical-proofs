# Lean verification

This self-contained Lean 4 project checks the finite prime-factor construction,
the nondegenerate two-sign conditioning calculation, and the paper's finite
quantitative Selberg-feedback estimate.

## Pinned environment

- Lean: `v4.33.0`
- Mathlib: `v4.33.0`

## Build

From this `Lean` directory, run:

```text
lake build --wfail
```

The axiom-reporting certificate is:

```text
RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
```

Check it directly with:

```text
lake env lean RiemannHypothesisProofFactory/SelbergConditioning/PaperCertificate.lean
```

## Exact scope

Lean checks a nonzero coefficient family supported on a finite set containing
only primes. Correcting one distinguished prime makes the weighted
prime-power mean exactly zero. The corrected family is zero off that finite
set, remains nonzero at a prime, and the exact prime factorization formula for
`log n` bounds its divisor residual by `C log n` for every integer.

Under a positive normalization scale and a positive power-scale hypothesis,
Lean converts the manuscript's signed-sum lower bound into nonzero two-sign
output separation and a strictly positive Lipschitz lower bound. The
signed-sum estimate itself remains an explicit analytic input.

Lean also checks the full finite ordered Selberg perturbation. Global
nonnegativity and a linear prefix bound for the base weight control the linear
hyperbola term, while the perturbation's harmonic mass controls both the
linear and quadratic terms with the stated explicit constant.

Lean does not check the prime number theorem, Chebyshev or partial-summation
estimates, near-linear output separation, asymptotic Selberg remainder,
residual moments,
the compact transform asymptotics, or the generalized von Mangoldt hierarchy.
Those are proved in the manuscript.
