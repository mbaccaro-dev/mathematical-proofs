import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandObstruction

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

/-- A single partner map is a global matching when every used edge is
reciprocal and has distinct endpoints.  The same map is used at every cutoff. -/
def IsGlobalMatching (mate : ℕ → Option ℕ) : Prop :=
  ∀ ⦃a b : ℕ⦄, mate a = some b → mate b = some a ∧ a ≠ b

/-- The two residual cofactors have opposite numbers of distinct prime
factors.  For squarefree endpoints this is the opposite-Möbius-sign
condition after their common gcd has been removed. -/
def OppositeResidualParity (a b : ℕ) : Prop :=
  (omega (a / Nat.gcd a b)) % 2 ≠ (omega (b / Nat.gcd a b)) % 2

/-- Exact admissibility of one edge at its own maximum endpoint. -/
def ResidualEdgeAdmissible
    (R edgeBound : ℕ → ℕ) (a b : ℕ) : Prop :=
  let T := max a b
  0 < a ∧ 0 < b ∧ a ≠ b ∧
    Squarefree a ∧ Squarefree b ∧
    omega (a / Nat.gcd a b) ≤ R T ∧
    omega (b / Nat.gcd a b) ≤ R T ∧
    OppositeResidualParity a b ∧
    Nat.dist a b ≤ edgeBound T

/-- A global matching whose endpoint-scale residual and edge bounds are
controlled on a prime-band family leaves at least the entire binomial family
unmatched.  This connector retains both residual bounds, parity, endpoint
ownership, and the use of one global partner map, even though the arithmetic
contradiction already follows from the first residual bound. -/
theorem globalMatching_primeBand_unmatched_lower_bound
    (mate : ℕ → Option ℕ) (R edgeBound : ℕ → ℕ)
    (Q : Finset ℕ) (k y z scale budget edgeCeiling : ℕ)
    (hglobal : IsGlobalMatching mate)
    (hprime : ∀ p ∈ Q, Nat.Prime p)
    (hband : ∀ p ∈ Q, y ≤ p ∧ p ≤ z)
    (hy : 0 < y)
    (hbudget : R scale ≤ budget)
    (hedgeCeiling : edgeBound scale ≤ edgeCeiling)
    (hRmono : Monotone R)
    (hEmono : Monotone edgeBound)
    (hscale : ∀ a ∈ primeBandProducts Q k, ∀ b,
      mate a = some b → max a b ≤ scale)
    (hadmissible : ∀ a ∈ primeBandProducts Q k, ∀ b,
      mate a = some b → ResidualEdgeAdmissible R edgeBound a b)
    (hceiling : edgeCeiling < y ^ (k - budget)) :
    Nat.choose Q.card k ≤ (unmatchedSquarefreeThrough mate (z ^ k)).card := by
  apply primeBand_unmatched_lower_bound mate Q k y z budget edgeCeiling
    hprime hband hy hceiling
  intro a ha b hab
  have hadm := hadmissible a ha b hab
  have hT := hscale a ha b hab
  have hRT : R (max a b) ≤ budget :=
    (hRmono hT).trans hbudget
  have hET : edgeBound (max a b) ≤ edgeCeiling :=
    (hEmono hT).trans hedgeCeiling
  have hreciprocal := (hglobal hab).1
  exact ⟨hadm.2.1, hadm.2.2.1, hadm.2.2.2.2.2.1.trans hRT,
    hadm.2.2.2.2.2.2.2.2.trans hET⟩

end RiemannHypothesisProofFactory.MobiusResidualComplexity
