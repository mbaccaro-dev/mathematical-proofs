# Lean certificate

This package proves the prime-band mechanism used in *Logarithmic
Residual-Complexity Barriers for Local Möbius Cancellation*.

The formal results show that a fixed band of primes eventually supplies the
required squarefree product family with exact binomial size. They then prove
that a single global matching subject to the stated residual and edge bounds
must leave the whole family unmatched. Finally, they establish the exact
logarithmic conversion between product scale and prime-product rank and the
resulting budget separation.

The final comparison between the binomial population and a general
`O(X^beta)` unmatched set remains a manuscript proof. It is not included in
the formal claim.

Build with:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The project is pinned to Lean 4.33.0 and its matching Mathlib revision. The
second command prints the axiom dependencies of the four selected results.
