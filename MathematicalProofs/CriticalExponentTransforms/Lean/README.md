# Lean verification

This self-contained Lean 4 project checks the algebraic kernel of the
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
RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

Check it directly with:

```text
lake env lean RiemannHypothesisProofFactory/CriticalExponentTransforms/PaperCertificate.lean
```

## Exact scope

Lean checks:

- the multilinear orderwise and adjacent exponent-gap identities;
- strict decrease of successive multilinear exponents when `rho < sigma`;
- the shared homogeneous and phase exponent-gap identity;
- a scalar pure-power normal-form specialization from its scale equation;
- the saturation and two-sided-germ exponent arithmetic;
- strict interiority and exact inversion of saturation at positive scale; and
- the inverse Mellin-symbol lower bound from a bounded reciprocal symbol.

Lean does not check the Abel integral; the vector-valued multilinear expansion
and asymptotics; the phase-orbit normal form and periodic block analysis; the
operator-level pure-power theorem; the complex-measure Mellin theorem; the
saturation pure-power asymptotic and connector; the two-sided-germ comparison;
or any dyadic energy law. Those are proved in the manuscript. Literature,
novelty, exposition, and publication judgments are also outside the kernel.
