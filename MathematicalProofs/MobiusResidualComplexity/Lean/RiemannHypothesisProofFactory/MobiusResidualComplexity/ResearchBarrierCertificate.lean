import RiemannHypothesisProofFactory.MobiusResidualComplexity.GlobalMatchingObstruction
import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandAsymptotics

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
    (∀ a ∈ primeBandProducts (widePrimeBand A y) k, mate a = none) ∧
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
  have hpointwise :
      ∀ a ∈ primeBandProducts (widePrimeBand A y) k, mate a = none := by
    apply globalMatching_primeBand_forced_unmatched mate R edgeBound
      (widePrimeBand A y) k y scale budget edgeCeiling hglobal
    · exact fun p hp ↦ prime_of_mem_widePrimeBand hp
    · exact fun p hp ↦ (widePrimeBand_bounds hp).1
    · omega
    · exact hbudget
    · exact hedgeCeiling
    · exact hRmono
    · exact hEmono
    · exact hscale
    · exact hadmissible
    · exact hseparation
  refine ⟨hpointwise, hcount, hunmatched, ?_⟩
  exact (Nat.pow_le_choose k (widePrimeBand A y).card).trans
    (by exact_mod_cast hunmatched)

/-- Exact finite residual-or-unmatched dichotomy.  For a global admissible
matching on the Chebyshev prime band, either the edge ceiling reaches the
retained-prime scale, or every band product is unmatched and the unmatched
population obeys the explicit binomial and factorial lower bounds. -/
theorem chebyshev_globalMatching_residual_or_unmatched_barrier
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
      mate a = some b → ResidualEdgeAdmissible R edgeBound a b) :
    y ^ (k - budget) ≤ edgeCeiling ∨
      ((∀ a ∈ primeBandProducts (widePrimeBand A y) k, mate a = none) ∧
        k ≤ (widePrimeBand A y).card ∧
        Nat.choose (widePrimeBand A y).card k ≤
          (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card ∧
        ((((widePrimeBand A y).card + 1 - k : ℕ) : ℝ) ^ k /
            (k.factorial : ℝ)) ≤
          (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card) := by
  by_cases hseparation : y ^ (k - budget) ≤ edgeCeiling
  · exact Or.inl hseparation
  · exact Or.inr (chebyshev_globalMatching_population_barrier
      mate R edgeBound A y k scale budget edgeCeiling hglobal hA hy hk
      hbudget hedgeCeiling hRmono hEmono hscale hadmissible
      (Nat.lt_of_not_ge hseparation))

/-- If the unmatched population is smaller than the prime-product family,
the retained-prime scale cannot exceed the allowed edge length. -/
theorem chebyshev_globalMatching_residual_budget_barrier
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
    (hfew : (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card <
      Nat.choose (widePrimeBand A y).card k) :
    y ^ (k - budget) ≤ edgeCeiling := by
  rcases chebyshev_globalMatching_residual_or_unmatched_barrier
      mate R edgeBound A y k scale budget edgeCeiling hglobal hA hy hk
      hbudget hedgeCeiling hRmono hEmono hscale hadmissible with hlarge | hmany
  · exact hlarge
  · exact False.elim ((not_lt_of_ge hmany.2.2.1) hfew)

/-- All-scale form of the finite dichotomy on the explicit fixed band
`(y, 8y]`.  At rank `floor(y^delta)`, every sufficiently large scale either
admits an edge ceiling at least as large as the retained-prime product, or the
entire prime-product family is unmatched with the stated binomial lower
bounds. -/
theorem eventually_octuple_globalMatching_residual_or_unmatched_barrier
    (mate : ℕ → Option ℕ) (R edgeBound budget edgeCeiling : ℕ → ℕ)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hglobal : IsGlobalMatching mate)
    (hRmono : Monotone R)
    (hEmono : Monotone edgeBound)
    (hbudget : ∀ᶠ y : ℕ in Filter.atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      R (2 * (8 * y) ^ k) ≤ budget y)
    (hedgeCeiling : ∀ᶠ y : ℕ in Filter.atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      edgeBound (2 * (8 * y) ^ k) ≤ edgeCeiling y)
    (hscale : ∀ᶠ y : ℕ in Filter.atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      ∀ a ∈ primeBandProducts (widePrimeBand 8 y) k, ∀ b,
        mate a = some b → max a b ≤ 2 * (8 * y) ^ k)
    (hadmissible : ∀ᶠ y : ℕ in Filter.atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      ∀ a ∈ primeBandProducts (widePrimeBand 8 y) k, ∀ b,
        mate a = some b → ResidualEdgeAdmissible R edgeBound a b) :
    ∀ᶠ y : ℕ in Filter.atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      y ^ (k - budget y) ≤ edgeCeiling y ∨
        ((∀ a ∈ primeBandProducts (widePrimeBand 8 y) k, mate a = none) ∧
          k ≤ (widePrimeBand 8 y).card ∧
          Nat.choose (widePrimeBand 8 y).card k ≤
            (unmatchedSquarefreeThrough mate ((8 * y) ^ k)).card ∧
          ((((widePrimeBand 8 y).card + 1 - k : ℕ) : ℝ) ^ k /
              (k.factorial : ℝ)) ≤
            (unmatchedSquarefreeThrough mate ((8 * y) ^ k)).card) := by
  filter_upwards [Filter.eventually_ge_atTop 2,
    eventually_octupleChebyshev_dominates_floor hdelta0 hdelta1,
    hbudget, hedgeCeiling, hscale, hadmissible]
      with y hy hprimeSupply hbudgetY hedgeY hscaleY hadmissibleY
  exact chebyshev_globalMatching_residual_or_unmatched_barrier
    mate R edgeBound 8 y ⌊(y : ℝ) ^ delta⌋₊
      (2 * (8 * y) ^ ⌊(y : ℝ) ^ delta⌋₊) (budget y) (edgeCeiling y)
      hglobal (by norm_num) (by omega) hprimeSupply hbudgetY hedgeY
      hRmono hEmono hscaleY hadmissibleY

end RiemannHypothesisProofFactory.MobiusResidualComplexity
