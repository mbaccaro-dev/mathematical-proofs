# Lean certificate

This package proves the finite pair-compression theorem used in
*Logarithmic Residual-Complexity Barriers for Local Möbius Cancellation*.
A nonempty zero-sum cell of positive squarefree integers is split by Möbius
sign and paired in increasing rank. The formal theorem constructs the common
core as the gcd of the cell and proves that the pairs have opposite signs,
preserve the residual prime-factor budget after passing to the pairwise gcd,
remain within the actual cell diameter, and cross each real cutoff exactly as
many times as the absolute signed mass below it. It also identifies the
crossing ranks with the pairs whose endpoints straddle the cutoff.

The package intentionally does not claim a full formalization of the paper.
In particular, it does not formalize the prime number theorem, the binomial
family asymptotic, the logarithmic scale conversion, or the global
sparse-jump counting argument. Those remain manuscript-level proofs.

Build with:

```text
lake build --wfail
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The project is pinned to Lean 4.33.0 and its matching Mathlib revision. The
second command prints the axiom dependencies of every public theorem in the
finite certificate.
