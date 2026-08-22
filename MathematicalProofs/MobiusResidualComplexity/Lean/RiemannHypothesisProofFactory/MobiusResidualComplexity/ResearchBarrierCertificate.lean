import RiemannHypothesisProofFactory.MobiusResidualComplexity.GlobalMatchingObstruction
import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandGrowth

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open Real

/-- A completely explicit finite-scale certificate for the manuscript's
residual-complexity mechanism.  Chebyshev supplies the wide prime band,
unique factorization supplies its exact binomial product population, and the
endpoint-scale gcd obstruction forces that whole population to be unmatched
by one global residual-admissible matching. -/
theorem chebyshev_globalMatching_population_barrier
    (mate : ℕ → Option ℕ) (R edgeBound : ℕ → ℕ)
    (A y k scale budget edgeCeiling : ℕ)
    (hglobal : IsGlobalMatching mate)
    (hA : 1 ≤ A) (hy : 1 < y)
    (hk : (k : ℝ) ≤
      (((A * y : ℕ) : ℝ) * log 2 - log (((A * y : ℕ) : ℝ) + 1)) /
          log ((A * y : ℕ) : ℝ) -
        (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ)))
    (hbudget : R scale ≤ budget)
    (hedgeCeiling : edgeBound scale ≤ edgeCeiling)
    (hRmono : Monotone R)
    (hEmono : Monotone edgeBound)
    (hscale : ∀ a ∈ primeBandProducts (widePrimeBand A y) k, ∀ b,
      mate a = some b → max a b ≤ scale)
    (hadmissible : ∀ a ∈ primeBandProducts (widePrimeBand A y) k, ∀ b,
      mate a = some b → ResidualEdgeAdmissible R edgeBound a b)
    (hseparation : edgeCeiling < y ^ (k - budget)) :
    k ≤ (widePrimeBand A y).card ∧
      Nat.choose (widePrimeBand A y).card k ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card ∧
      ((((widePrimeBand A y).card + 1 - k : ℕ) : ℝ) ^ k /
          (k.factorial : ℝ)) ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card := by
  have hcount := widePrimeBand_has_at_least A y k hA hy hk
  have hunmatched :
      Nat.choose (widePrimeBand A y).card k ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card := by
    apply globalMatching_primeBand_unmatched_lower_bound mate R edgeBound
      (widePrimeBand A y) k y (A * y) scale budget edgeCeiling hglobal
    · exact fun p hp ↦ prime_of_mem_widePrimeBand hp
    · exact fun p hp ↦ widePrimeBand_bounds hp
    · omega
    · exact hbudget
    · exact hedgeCeiling
    · exact hRmono
    · exact hEmono
    · exact hscale
    · exact hadmissible
    · exact hseparation
  refine ⟨hcount, hunmatched, ?_⟩
  exact (Nat.pow_le_choose k (widePrimeBand A y).card).trans
    (by exact_mod_cast hunmatched)

end RiemannHypothesisProofFactory.MobiusResidualComplexity
