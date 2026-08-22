# Lean certificate

This package proves the prime-band mechanism used in *Logarithmic
Residual-Complexity Barriers for Local Möbius Cancellation*.

The formal results prove an exact residual-or-unmatched dichotomy for a fixed
prime band. At each large scale, either the allowed edge length reaches the
retained-prime product or every member of the prime-product family is
individually unmatched. Chebyshev estimates and unique factorization give the
explicit binomial and factorial population bounds. The development also proves
the exact logarithmic conversion between product scale and rank and the
resulting budget separation.

The final sparse-binomial comparison with a general `O(X^beta)` unmatched set,
and therefore the paper's full limsup conclusion, remain manuscript proofs.
They are not included in the formal claim.

Build with:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The project is pinned to Lean 4.33.0 and its matching Mathlib revision. The
second command prints the axiom dependencies of the four selected results.
