# Lean certificate

This package checks the finite algebraic and combinatorial kernel used in
*Logarithmic Residual-Complexity Barriers for Local Möbius Cancellation*.
It verifies opposite-sign pair cancellation, the finite matching bound after
the pair decomposition, balance of a zero-sum unit cell, the exact number of
rank pairs that cross a sign cutoff, inheritance of a residual prime-factor
budget after replacing a common divisor by the pairwise gcd, the contradiction
in the strict exponent sandwich, the square-root constant identity, and the
endpoint-doubling step in the sparse-jump argument.

The package intentionally does not claim a full formalization of the paper.
In particular, it does not formalize the prime number theorem, the binomial
family asymptotic, the logarithmic scale conversion, construction and ordering
of the Möbius-sign lists, sign parity after gcd removal, or the global
sparse-jump counting argument. Those remain manuscript-level proofs.

Build with:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The project is pinned to Lean 4.33.0 and its matching Mathlib revision. The
second command prints the axiom dependencies of every public theorem in the
finite certificate.
