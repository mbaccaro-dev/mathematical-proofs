import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

open Filter
open scoped ArithmeticFunction BigOperators Topology

namespace RiemannHypothesisProofFactory.SelbergConditioning

noncomputable def primeFactorResidual (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * c p

noncomputable def orderedHyperbolaSum
    (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / m), f m * g n

noncomputable def logarithmicMoment (e : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, e n * Real.log n

noncomputable def harmonicMass (e : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |e n| / (n : ℝ)

noncomputable def oddPrimeCoefficient (rho : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then
    (p : ℝ) ^ (rho - 1) * Real.log p
  else
    0

noncomputable def oddCorrectionTerm (rho : ℝ) (p : ℕ) : ℝ :=
  oddPrimeCoefficient rho p / ((p : ℝ) - 1)

noncomputable def twoCoefficient (rho : ℝ) : ℝ :=
  -∑' p : ℕ, oddCorrectionTerm rho p

noncomputable def infinitePrimeCoefficient (rho : ℝ) (p : ℕ) : ℝ :=
  if p = 2 then twoCoefficient rho else oddPrimeCoefficient rho p

noncomputable def infinitePrimePowerPerturbation (rho : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n then infinitePrimeCoefficient rho n.minFac else 0

noncomputable def oddPrimePowerPart (rho : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac ≠ 2 then oddPrimeCoefficient rho n.minFac else 0

def twoPrimePowerIndicator (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac = 2 then 1 else 0

noncomputable def arithmeticPrefix (a : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, a n

structure StandardPrimePowerInputs (rho : ℝ) : Prop where
  oneHalf_lt_rho : (1 / 2 : ℝ) < rho
  rho_lt_one : rho < 1
  correctionSummable : Summable (oddCorrectionTerm rho)
  oddPrimePowerAsymptotic :
    Tendsto
      (fun X : ℕ =>
        arithmeticPrefix (oddPrimePowerPart rho) X / (X : ℝ) ^ rho)
      atTop (nhds (1 / rho))
  twoPrimePowerNegligible :
    Tendsto
      (fun X : ℕ =>
        arithmeticPrefix twoPrimePowerIndicator X / (X : ℝ) ^ rho)
      atTop (nhds 0)

noncomputable def plusMangoldtWeight (rho eta : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n + eta * infinitePrimePowerPerturbation rho n

noncomputable def minusMangoldtWeight (rho eta : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - eta * infinitePrimePowerPerturbation rho n

def InPrimePowerCone (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
  (∀ n, ¬IsPrimePow n → a n = 0) ∧
  ∀ p k l : ℕ, p.Prime → k ≠ 0 → l ≠ 0 → a (p ^ k) = a (p ^ l)

noncomputable def selbergStatistic (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  logarithmicMoment a N + orderedHyperbolaSum a a N

noncomputable def divisorFeedbackResidual (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, a d - Real.log n

noncomputable def summatoryError (a : ℕ → ℝ) (X : ℕ) : ℝ :=
  arithmeticPrefix a X - (X : ℝ)

structure StandardConditioningInputs (rho : ℝ) : Type
    extends StandardPrimePowerInputs rho where
  coefficientBound : ℝ
  coefficientBound_pos : 0 < coefficientBound
  coefficient_bound : ∀ p : ℕ, p.Prime →
    |infinitePrimeCoefficient rho p| ≤ coefficientBound * Real.log p
  perturbation_divisor_identity : ∀ n : ℕ, n ≠ 0 →
    ∑ d ∈ n.divisors, infinitePrimePowerPerturbation rho d =
      primeFactorResidual (infinitePrimeCoefficient rho) n
  chebyshevConstant : ℝ
  chebyshevConstant_nonneg : 0 ≤ chebyshevConstant
  vonMangoldt_prefix : ∀ N y : ℕ, y ≤ N →
    ∑ n ∈ Finset.Icc 1 y, ArithmeticFunction.vonMangoldt n ≤
      chebyshevConstant * (y : ℝ)
  perturbationLogConstant : ℝ
  perturbationLogConstant_nonneg : 0 ≤ perturbationLogConstant
  perturbation_log_moment : ∀ N : ℕ,
    |logarithmicMoment (infinitePrimePowerPerturbation rho) N| ≤
      perturbationLogConstant * (N : ℝ)
  perturbationHarmonicConstant : ℝ
  perturbationHarmonicConstant_nonneg : 0 ≤ perturbationHarmonicConstant
  perturbation_harmonic : ∀ N : ℕ,
    harmonicMass (infinitePrimePowerPerturbation rho) N ≤
      perturbationHarmonicConstant
  baseSelbergConstant : ℝ
  base_selberg : ∀ N : ℕ,
    |selbergStatistic ArithmeticFunction.vonMangoldt N -
      2 * (N : ℝ) * Real.log N| ≤ baseSelbergConstant * (N : ℝ)

noncomputable def conditioningScale {rho : ℝ}
    (inputs : StandardConditioningInputs rho) (X : ℕ) (tau : ℝ) : ℝ :=
  tau / (inputs.coefficientBound * Real.log ((2 * X : ℕ) : ℝ))

noncomputable def conditioningScaleCap {rho : ℝ}
    (inputs : StandardConditioningInputs rho) : ℝ :=
  1 / (inputs.coefficientBound * Real.log 4)

noncomputable def conditioningSelbergConstant {rho : ℝ}
    (inputs : StandardConditioningInputs rho) : ℝ :=
  inputs.baseSelbergConstant +
    conditioningScaleCap inputs * inputs.perturbationLogConstant +
    2 * inputs.chebyshevConstant *
      (conditioningScaleCap inputs * inputs.perturbationHarmonicConstant) +
    (conditioningScaleCap inputs * inputs.perturbationHarmonicConstant) ^ 2

/-- For every sufficiently large observation scale and every tolerance at
most one, the two explicit von Mangoldt perturbations remain in the positive
prime-power cone, agree with divisor feedback to that tolerance through twice
the scale, have a quantitative summatory-output separation, and retain one
uniform linear Selberg bound. -/
theorem near_linear_conditioning_witness
    (rho : ℝ) (inputs : StandardConditioningInputs rho) :
    ∃ X0 : ℕ, 2 ≤ X0 ∧ ∀ X ≥ X0, ∀ tau : ℝ,
      0 < tau → tau ≤ 1 →
      InPrimePowerCone
          (plusMangoldtWeight rho (conditioningScale inputs X tau)) ∧
      InPrimePowerCone
          (minusMangoldtWeight rho (conditioningScale inputs X tau)) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ 2 * X →
        |divisorFeedbackResidual
            (plusMangoldtWeight rho (conditioningScale inputs X tau)) n| ≤ tau ∧
        |divisorFeedbackResidual
            (minusMangoldtWeight rho (conditioningScale inputs X tau)) n| ≤ tau) ∧
      tau * (X : ℝ) ^ rho /
          (rho * inputs.coefficientBound *
            Real.log ((2 * X : ℕ) : ℝ)) ≤
        |summatoryError
            (plusMangoldtWeight rho (conditioningScale inputs X tau)) X -
          summatoryError
            (minusMangoldtWeight rho (conditioningScale inputs X tau)) X| ∧
      ∀ N : ℕ,
        |selbergStatistic
              (plusMangoldtWeight rho (conditioningScale inputs X tau)) N -
            2 * (N : ℝ) * Real.log N| ≤
            conditioningSelbergConstant inputs * (N : ℝ) ∧
        |selbergStatistic
              (minusMangoldtWeight rho (conditioningScale inputs X tau)) N -
            2 * (N : ℝ) * Real.log N| ≤
            conditioningSelbergConstant inputs * (N : ℝ) := by
  sorry

end RiemannHypothesisProofFactory.SelbergConditioning
