# Lean verification

This self-contained Lean 4 project checks the paper's explicit infinite
prime-power perturbation and its near-linear Selberg conditioning theorem.

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

Lean checks the distinguished prime-two correction, constant coefficients on
every prime-power chain, and the two actual von Mangoldt perturbations. From
the stated standard analytic inputs, it proves positive prime-power cone
membership, divisor-feedback tolerance at every index through twice the
observation scale, a quantitative near-linear summatory-output separation, and
one uniform linear Selberg bound for both weights.

The weighted prime-number limit, negligible powers-of-two chain, coefficient
and Chebyshev estimates, exact divisor identity, perturbation moment and
harmonic bounds, and classical Selberg estimate remain explicit inputs. The
generalized von Mangoldt hierarchy remains manuscript-level.
