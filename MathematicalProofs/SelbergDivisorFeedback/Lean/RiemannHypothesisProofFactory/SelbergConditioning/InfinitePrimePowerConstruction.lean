import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Infinite prime-power construction for Selberg divisor feedback

This module isolates the manuscript's fixed infinite perturbation.  The
analytic inputs are stated only for the unsigned odd-prime-power family and
the negligible powers-of-two chain.  The signed centered asymptotic is then a
conclusion, not a premise.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannHypothesisProofFactory.SelbergConditioning

/-- The positive coefficient placed on an odd prime chain. -/
noncomputable def oddPrimeCoefficient (rho : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ p ≠ 2 then
    (p : ℝ) ^ (rho - 1) * Real.log p
  else
    0

/-- The summand whose total is cancelled at the prime `2`. -/
noncomputable def oddCorrectionTerm (rho : ℝ) (p : ℕ) : ℝ :=
  oddPrimeCoefficient rho p / ((p : ℝ) - 1)

/-- The distinguished coefficient that centers the complete prime-power
family. -/
noncomputable def twoCoefficient (rho : ℝ) : ℝ :=
  -∑' p : ℕ, oddCorrectionTerm rho p

/-- The fixed coefficient on a prime chain.  It is zero away from primes. -/
noncomputable def infinitePrimeCoefficient (rho : ℝ) (p : ℕ) : ℝ :=
  if p = 2 then twoCoefficient rho else oddPrimeCoefficient rho p

/-- The complete centered series indexed by possible prime bases. -/
noncomputable def centeredPrimeSeriesTerm (rho : ℝ) (p : ℕ) : ℝ :=
  if p = 2 then twoCoefficient rho else oddCorrectionTerm rho p

/-- The manuscript's fixed perturbation, constant along each prime-power
chain and zero off prime powers. -/
noncomputable def infinitePrimePowerPerturbation (rho : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n then infinitePrimeCoefficient rho n.minFac else 0

/-- The unsigned odd-prime-power part of the perturbation. -/
noncomputable def oddPrimePowerPart (rho : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac ≠ 2 then oddPrimeCoefficient rho n.minFac else 0

/-- Indicator of the powers-of-two chain. -/
def twoPrimePowerIndicator (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac = 2 then 1 else 0

/-- A strict positive-index prefix sum. -/
noncomputable def arithmeticPrefix (a : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, a n

/-- The standard analytic inputs used by this module.  These inputs contain
no signed cancellation conclusion: the first is absolute convergence of the
odd correction series, the second is the weighted PNT consequence for the
unsigned odd-prime-power family, and the third records that the single
powers-of-two chain has zero `X^rho` density. -/
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

@[simp]
theorem oddPrimeCoefficient_two (rho : ℝ) :
    oddPrimeCoefficient rho 2 = 0 := by
  simp [oddPrimeCoefficient]

@[simp]
theorem oddCorrectionTerm_two (rho : ℝ) :
    oddCorrectionTerm rho 2 = 0 := by
  simp [oddCorrectionTerm]

@[simp]
theorem infinitePrimeCoefficient_two (rho : ℝ) :
    infinitePrimeCoefficient rho 2 = twoCoefficient rho := by
  simp [infinitePrimeCoefficient]

theorem infinitePrimeCoefficient_odd_prime
    (rho : ℝ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    infinitePrimeCoefficient rho p =
      (p : ℝ) ^ (rho - 1) * Real.log p := by
  simp [infinitePrimeCoefficient, oddPrimeCoefficient, hp, hp2]

theorem infinitePrimeCoefficient_nonprime
    (rho : ℝ) {p : ℕ} (hp : ¬p.Prime) (hp2 : p ≠ 2) :
    infinitePrimeCoefficient rho p = 0 := by
  simp [infinitePrimeCoefficient, oddPrimeCoefficient, hp, hp2]

/-- The auxiliary centered term is exactly the manuscript coefficient divided
by `p - 1`; at `p = 2` the denominator is one. -/
theorem centeredPrimeSeriesTerm_eq_coefficient_divisor
    (rho : ℝ) (p : ℕ) :
    centeredPrimeSeriesTerm rho p =
      infinitePrimeCoefficient rho p / ((p : ℝ) - 1) := by
  by_cases hp : p = 2
  · subst p
    norm_num [centeredPrimeSeriesTerm, infinitePrimeCoefficient]
  · simp [centeredPrimeSeriesTerm, infinitePrimeCoefficient,
      oddCorrectionTerm, hp]

/-- Absolute convergence of the odd correction series gives convergence of
the complete centered series after changing the single term at `2`. -/
theorem centeredPrimeSeriesTerm_summable
    (rho : ℝ) (h : Summable (oddCorrectionTerm rho)) :
    Summable (centeredPrimeSeriesTerm rho) := by
  have hsingle : Summable
      (fun p : ℕ => if p = 2 then twoCoefficient rho else 0) :=
    (hasSum_ite_eq 2 (twoCoefficient rho)).summable
  have hadd := h.add hsingle
  refine hadd.congr ?_
  intro p
  by_cases hp : p = 2
  · subst p
    simp [centeredPrimeSeriesTerm]
  · simp [centeredPrimeSeriesTerm, hp]

/-- The distinguished coefficient at `2` makes the full infinite coefficient
series exactly centered. -/
theorem centeredPrimeSeriesTerm_tsum_eq_zero
    (rho : ℝ) (h : Summable (oddCorrectionTerm rho)) :
    ∑' p : ℕ, centeredPrimeSeriesTerm rho p = 0 := by
  have hsingle : Summable
      (fun p : ℕ => if p = 2 then twoCoefficient rho else 0) :=
    (hasSum_ite_eq 2 (twoCoefficient rho)).summable
  calc
    ∑' p : ℕ, centeredPrimeSeriesTerm rho p =
        ∑' p : ℕ,
          (oddCorrectionTerm rho p +
            if p = 2 then twoCoefficient rho else 0) := by
      apply tsum_congr
      intro p
      by_cases hp : p = 2
      · subst p
        simp [centeredPrimeSeriesTerm]
      · simp [centeredPrimeSeriesTerm, hp]
    _ = (∑' p : ℕ, oddCorrectionTerm rho p) +
        ∑' p : ℕ, (if p = 2 then twoCoefficient rho else 0) :=
      h.tsum_add hsingle
    _ = 0 := by
      simp [twoCoefficient]

/-- Exact manuscript centering identity for the infinite prime coefficients. -/
theorem infinitePrimeCoefficient_centered
    (rho : ℝ) (h : Summable (oddCorrectionTerm rho)) :
    Summable
        (fun p : ℕ => infinitePrimeCoefficient rho p / ((p : ℝ) - 1)) ∧
      (∑' p : ℕ,
        infinitePrimeCoefficient rho p / ((p : ℝ) - 1)) = 0 := by
  have hcongr :
      (fun p : ℕ => infinitePrimeCoefficient rho p / ((p : ℝ) - 1)) =
        centeredPrimeSeriesTerm rho := by
    funext p
    exact (centeredPrimeSeriesTerm_eq_coefficient_divisor rho p).symm
  rw [hcongr]
  exact
    ⟨centeredPrimeSeriesTerm_summable rho h,
      centeredPrimeSeriesTerm_tsum_eq_zero rho h⟩

theorem centeredPrimeSeries
    (rho : ℝ) (inputs : StandardPrimePowerInputs rho) :
    Summable (centeredPrimeSeriesTerm rho) ∧
      (∑' p : ℕ, centeredPrimeSeriesTerm rho p = 0) :=
  ⟨centeredPrimeSeriesTerm_summable rho inputs.correctionSummable,
    centeredPrimeSeriesTerm_tsum_eq_zero rho inputs.correctionSummable⟩

@[simp]
theorem infinitePrimePowerPerturbation_prime_pow
    (rho : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    infinitePrimePowerPerturbation rho (p ^ k) =
      infinitePrimeCoefficient rho p := by
  simp [infinitePrimePowerPerturbation, isPrimePow_pow_iff hk,
    hp.isPrimePow, hp.pow_minFac hk]

theorem infinitePrimePowerPerturbation_eq_zero_of_not_prime_pow
    (rho : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    infinitePrimePowerPerturbation rho n = 0 := by
  simp [infinitePrimePowerPerturbation, hn]

/-- The perturbation is exactly constant on every positive-exponent prime
power chain. -/
theorem infinitePrimePowerPerturbation_chain_constant
    (rho : ℝ) {p k l : ℕ} (hp : p.Prime) (hk : k ≠ 0) (hl : l ≠ 0) :
    infinitePrimePowerPerturbation rho (p ^ k) =
      infinitePrimePowerPerturbation rho (p ^ l) := by
  rw [infinitePrimePowerPerturbation_prime_pow rho hp hk,
    infinitePrimePowerPerturbation_prime_pow rho hp hl]

/-- Pointwise decomposition into the unsigned odd-prime-power family and the
single centered powers-of-two chain. -/
theorem infinitePrimePowerPerturbation_decomposition
    (rho : ℝ) (n : ℕ) :
    infinitePrimePowerPerturbation rho n =
      oddPrimePowerPart rho n +
        twoCoefficient rho * twoPrimePowerIndicator n := by
  by_cases hn : IsPrimePow n
  · by_cases htwo : n.minFac = 2
    · simp [infinitePrimePowerPerturbation, oddPrimePowerPart,
        twoPrimePowerIndicator, hn, htwo, infinitePrimeCoefficient]
    · simp [infinitePrimePowerPerturbation, oddPrimePowerPart,
        twoPrimePowerIndicator, hn, htwo, infinitePrimeCoefficient]
  · simp [infinitePrimePowerPerturbation, oddPrimePowerPart,
      twoPrimePowerIndicator, hn]

/-- Exact finite-prefix decomposition used before taking the analytic limit. -/
theorem arithmeticPrefix_infinitePrimePowerPerturbation
    (rho : ℝ) (X : ℕ) :
    arithmeticPrefix (infinitePrimePowerPerturbation rho) X =
      arithmeticPrefix (oddPrimePowerPart rho) X +
        twoCoefficient rho * arithmeticPrefix twoPrimePowerIndicator X := by
  classical
  unfold arithmeticPrefix
  simp_rw [infinitePrimePowerPerturbation_decomposition]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]

/-- The signed centered prefix asymptotic follows from the unsigned weighted
PNT input and the negligible distinguished chain. -/
theorem infinitePrimePowerPerturbation_asymptotic
    (rho : ℝ) (inputs : StandardPrimePowerInputs rho) :
    Tendsto
      (fun X : ℕ =>
        arithmeticPrefix (infinitePrimePowerPerturbation rho) X /
          (X : ℝ) ^ rho)
      atTop (nhds (1 / rho)) := by
  have htwo : Tendsto
      (fun X : ℕ =>
        twoCoefficient rho *
          (arithmeticPrefix twoPrimePowerIndicator X / (X : ℝ) ^ rho))
      atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul inputs.twoPrimePowerNegligible)
  have hadd := inputs.oddPrimePowerAsymptotic.add htwo
  convert hadd using 1
  · funext X
    rw [arithmeticPrefix_infinitePrimePowerPerturbation]
    ring_nf
  · ring_nf

end RiemannHypothesisProofFactory.SelbergConditioning
