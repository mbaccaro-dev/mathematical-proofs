# Lean verification

This self-contained Lean 4 project checks the finite algebraic kernel of the
accompanying paper.

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

Lean checks:

- the combined finite implication from two analytic witness estimates to
  normalized residual bounds, output separation, and the Lipschitz lower bound;
- the algebraic rewrite from a distinguished-chain correction to a negative tail;
- strict positivity of both signed weights under the printed relative bound;
- normalization of a pointwise residual bound to the tolerance `tau`;
- the two-sign output separation after scale normalization; and
- the final Lipschitz lower-bound quotient.

Lean does not check the prime number theorem, Chebyshev or partial-summation
estimates, Selberg's formula, residual first and second moments, the compact
transform asymptotics, or the generalized von Mangoldt hierarchy.  Those are
proved in the manuscript.  Literature, novelty, exposition, and publication
judgments are also outside the kernel.
