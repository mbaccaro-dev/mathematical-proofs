# Lean verification

This self-contained Lean 4 project checks the finite prime-factor construction
at the core of the accompanying paper's conditioning witness.

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

Lean does not check the prime number theorem, Chebyshev or partial-summation
estimates, near-linear output separation, Selberg's formula, residual moments,
the compact transform asymptotics, or the generalized von Mangoldt hierarchy.
Those are proved in the manuscript.
