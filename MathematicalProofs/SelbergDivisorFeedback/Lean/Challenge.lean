import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RiemannHypothesisProofFactory.SelbergConditioning

noncomputable def primeFactorResidual (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * c p

noncomputable def centeredPrimeCoefficient
    (P : Finset ℕ) (q : ℕ) (raw : ℕ → ℝ) (p : ℕ) : ℝ :=
  if p ∉ P then 0
  else if p = q then
    -((q : ℝ) - 1) * ∑ r ∈ P.erase q, raw r / ((r : ℝ) - 1)
  else raw p

/-- A centered finite prime coefficient family gives an exact mean-zero
prime-power perturbation and a logarithmically controlled divisor residual. -/
theorem finite_prime_factor_conditioning_construction
    (P : Finset ℕ) (q : ℕ) (raw : ℕ → ℝ) (C : ℝ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hqP : q ∈ P)
    (hnonzero : ∃ p ∈ P.erase q, raw p ≠ 0)
    (hC : 0 ≤ C)
    (hcoeff : ∀ p ∈ P,
      |centeredPrimeCoefficient P q raw p| ≤ C * Real.log p) :
    (∑ p ∈ P,
        centeredPrimeCoefficient P q raw p / ((p : ℝ) - 1) = 0) ∧
      (∀ n : ℕ,
        |primeFactorResidual (centeredPrimeCoefficient P q raw) n| ≤
          C * Real.log n) ∧
      ∃ p ∈ P,
        centeredPrimeCoefficient P q raw p ≠ 0 ∧
        primeFactorResidual (centeredPrimeCoefficient P q raw) p =
          centeredPrimeCoefficient P q raw p := by
  sorry

end RiemannHypothesisProofFactory.SelbergConditioning
