import RiemannHypothesisProofFactory.SelbergConditioning.InfinitePrimePowerConstruction
import RiemannHypothesisProofFactory.SelbergConditioning.PrimeFactorConstruction
import RiemannHypothesisProofFactory.SelbergConditioning.SelbergStability
import RiemannHypothesisProofFactory.SelbergConditioning.FiniteKernel
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sequence-level near-linear conditioning witness

This module connects the explicit infinite prime-power perturbation to the
actual von Mangoldt weight.  Analytic estimates not supplied by the pinned
Mathlib release remain explicit fields of `StandardConditioningInputs`.
-/

open Filter
open scoped ArithmeticFunction BigOperators Topology

namespace RiemannHypothesisProofFactory.SelbergConditioning

/-- The positive-sign perturbation of the von Mangoldt weight. -/
noncomputable def plusMangoldtWeight (rho eta : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n + eta * infinitePrimePowerPerturbation rho n

/-- The negative-sign perturbation of the von Mangoldt weight. -/
noncomputable def minusMangoldtWeight (rho eta : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n - eta * infinitePrimePowerPerturbation rho n

/-- The manuscript's positive prime-power cone. -/
def InPrimePowerCone (a : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ a n) ∧
  (∀ n, ¬IsPrimePow n → a n = 0) ∧
  ∀ p k l : ℕ, p.Prime → k ≠ 0 → l ≠ 0 → a (p ^ k) = a (p ^ l)

/-- The exact Selberg statistic with ordered hyperbola pairs. -/
noncomputable def selbergStatistic (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  logarithmicMoment a N + orderedHyperbolaSum a a N

/-- Divisor feedback measured against the exact von Mangoldt identity. -/
noncomputable def divisorFeedbackResidual (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, a d - Real.log n

/-- The summatory output centered at its main term. -/
noncomputable def summatoryError (a : ℕ → ℝ) (X : ℕ) : ℝ :=
  arithmeticPrefix a X - (X : ℝ)

/-- Standard analytic estimates used after the explicit construction.  No
signed-prefix lower bound, output separation, or conditioning conclusion is a
field of this structure. -/
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

/-- Scale used by the normalized pair at observation point `X`. -/
noncomputable def conditioningScale {rho : ℝ}
    (inputs : StandardConditioningInputs rho) (X : ℕ) (tau : ℝ) : ℝ :=
  tau / (inputs.coefficientBound * Real.log ((2 * X : ℕ) : ℝ))

/-- One scale cap valid for every `X ≥ 2` and `tau ≤ 1`. -/
noncomputable def conditioningScaleCap {rho : ℝ}
    (inputs : StandardConditioningInputs rho) : ℝ :=
  1 / (inputs.coefficientBound * Real.log 4)

/-- The common displayed Selberg constant for the normalized family. -/
noncomputable def conditioningSelbergConstant {rho : ℝ}
    (inputs : StandardConditioningInputs rho) : ℝ :=
  inputs.baseSelbergConstant +
    conditioningScaleCap inputs * inputs.perturbationLogConstant +
    2 * inputs.chebyshevConstant *
      (conditioningScaleCap inputs * inputs.perturbationHarmonicConstant) +
    (conditioningScaleCap inputs * inputs.perturbationHarmonicConstant) ^ 2

/-- The normalized scale is globally small enough for positivity and is
bounded by a constant independent of `X` and `tau`. -/
theorem conditioningScale_bounds
    {rho : ℝ} (inputs : StandardConditioningInputs rho)
    {X : ℕ} (hX : 2 ≤ X) {tau : ℝ} (htau : 0 ≤ tau)
    (htauOne : tau ≤ 1) :
    0 ≤ conditioningScale inputs X tau ∧
      |conditioningScale inputs X tau| ≤ conditioningScaleCap inputs ∧
      |conditioningScale inputs X tau| * inputs.coefficientBound < 1 := by
  have hlog4 : 1 < Real.log 4 := by
    rw [Real.log_four_eq]
    have htwo := Real.log_two_gt_d9
    norm_num at htwo ⊢
    linarith
  have hfour : (4 : ℝ) ≤ ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast (show 4 ≤ 2 * X by omega)
  have hlogle : Real.log 4 ≤ Real.log ((2 * X : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) hfour
  have hlogX : 0 < Real.log ((2 * X : ℕ) : ℝ) :=
    lt_of_lt_of_le (by linarith : 0 < Real.log 4) hlogle
  have hC := inputs.coefficientBound_pos
  have hden : 0 < inputs.coefficientBound *
      Real.log ((2 * X : ℕ) : ℝ) := mul_pos hC hlogX
  have hden4 : 0 < inputs.coefficientBound * Real.log 4 :=
    mul_pos hC (lt_trans (by norm_num) hlog4)
  have hdenle : inputs.coefficientBound * Real.log 4 ≤
      inputs.coefficientBound * Real.log ((2 * X : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle hC.le
  have heta0 : 0 ≤ conditioningScale inputs X tau :=
    div_nonneg htau hden.le
  have hetacap : |conditioningScale inputs X tau| ≤
      conditioningScaleCap inputs := by
    rw [abs_of_nonneg heta0]
    unfold conditioningScale conditioningScaleCap
    calc
      tau / (inputs.coefficientBound * Real.log ((2 * X : ℕ) : ℝ)) ≤
          1 / (inputs.coefficientBound * Real.log ((2 * X : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right htauOne hden.le
      _ ≤ 1 / (inputs.coefficientBound * Real.log 4) :=
        one_div_le_one_div_of_le hden4 hdenle
  refine ⟨heta0, hetacap, ?_⟩
  calc
    |conditioningScale inputs X tau| * inputs.coefficientBound ≤
        conditioningScaleCap inputs * inputs.coefficientBound :=
      mul_le_mul_of_nonneg_right hetacap hC.le
    _ = 1 / Real.log 4 := by
      unfold conditioningScaleCap
      field_simp
    _ < 1 := (div_lt_one (lt_trans (by norm_num) hlog4)).2 hlog4

/-- Convergence to the positive constant `1 / rho` forces the manuscript's
eventual positive lower bound. -/
theorem eventual_signed_prefix_lower_bound
    (rho : ℝ) (inputs : StandardPrimePowerInputs rho) :
    ∃ X0 : ℕ, ∀ X ≥ X0,
      (X : ℝ) ^ rho / (2 * rho) ≤
        |arithmeticPrefix (infinitePrimePowerPerturbation rho) X| := by
  have hrho : 0 < rho := lt_trans (by norm_num) inputs.oneHalf_lt_rho
  have hhalf : 1 / (2 * rho) < 1 / rho := by
    apply one_div_lt_one_div_of_lt hrho
    linarith
  have heventually : ∀ᶠ X : ℕ in atTop,
      1 / (2 * rho) <
        arithmeticPrefix (infinitePrimePowerPerturbation rho) X /
          (X : ℝ) ^ rho :=
    (tendsto_order.1
      (infinitePrimePowerPerturbation_asymptotic rho inputs)).1 _ hhalf
  rcases (eventually_atTop.1 heventually) with ⟨X0, hX0⟩
  refine ⟨max X0 1, ?_⟩
  intro X hX
  have hX0' : X0 ≤ X := (le_max_left X0 1).trans hX
  have hXone : 1 ≤ X := (le_max_right X0 1).trans hX
  have hpow : 0 < (X : ℝ) ^ rho :=
    Real.rpow_pos_of_pos (by exact_mod_cast (zero_lt_one.trans_le hXone)) rho
  have hratio := hX0 X hX0'
  have hlower : (X : ℝ) ^ rho / (2 * rho) <
      arithmeticPrefix (infinitePrimePowerPerturbation rho) X := by
    calc
      (X : ℝ) ^ rho / (2 * rho) =
          (1 / (2 * rho)) * (X : ℝ) ^ rho := by ring
      _ < (arithmeticPrefix (infinitePrimePowerPerturbation rho) X /
          (X : ℝ) ^ rho) * (X : ℝ) ^ rho :=
        mul_lt_mul_of_pos_right hratio hpow
      _ = arithmeticPrefix (infinitePrimePowerPerturbation rho) X := by
        field_simp
  exact hlower.le.trans (le_abs_self _)

theorem plusMangoldtWeight_prime_pow
    (rho eta : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    plusMangoldtWeight rho eta (p ^ k) =
      Real.log p + eta * infinitePrimeCoefficient rho p := by
  rw [plusMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    infinitePrimePowerPerturbation_prime_pow rho hp hk]

theorem minusMangoldtWeight_prime_pow
    (rho eta : ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    minusMangoldtWeight rho eta (p ^ k) =
      Real.log p - eta * infinitePrimeCoefficient rho p := by
  rw [minusMangoldtWeight, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp,
    infinitePrimePowerPerturbation_prime_pow rho hp hk]

theorem mangoldt_weights_off_prime_powers
    (rho eta : ℝ) {n : ℕ} (hn : ¬IsPrimePow n) :
    plusMangoldtWeight rho eta n = 0 ∧ minusMangoldtWeight rho eta n = 0 := by
  simp [plusMangoldtWeight, minusMangoldtWeight,
    ArithmeticFunction.vonMangoldt_apply, hn,
    infinitePrimePowerPerturbation_eq_zero_of_not_prime_pow rho hn]

/-- A pointwise coefficient bound and a small scale put both actual weights
in the positive prime-power cone. -/
theorem mangoldt_weights_mem_prime_power_cone
    (rho eta C : ℝ)
    (_hC : 0 < C)
    (hcoeff : ∀ p : ℕ, p.Prime →
      |infinitePrimeCoefficient rho p| ≤ C * Real.log p)
    (hsmall : |eta| * C < 1) :
    InPrimePowerCone (plusMangoldtWeight rho eta) ∧
      InPrimePowerCone (minusMangoldtWeight rho eta) := by
  have hpositive : ∀ n : ℕ, IsPrimePow n →
      0 < plusMangoldtWeight rho eta n ∧
        0 < minusMangoldtWeight rho eta n := by
    intro n hn
    have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
    have hlog : 0 < Real.log (n.minFac : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hp.one_lt)
    have hbound : |infinitePrimeCoefficient rho n.minFac| ≤
        C * Real.log n.minFac := hcoeff n.minFac hp
    have hpair := signed_perturbations_pos
      (Real.log n.minFac) (infinitePrimeCoefficient rho n.minFac)
      eta C hlog hbound hsmall
    simpa [plusMangoldtWeight, minusMangoldtWeight,
      ArithmeticFunction.vonMangoldt_apply, hn,
      infinitePrimePowerPerturbation] using hpair
  have hnonnegPlus : ∀ n, 0 ≤ plusMangoldtWeight rho eta n := by
    intro n
    by_cases hn : IsPrimePow n
    · exact (hpositive n hn).1.le
    · exact (mangoldt_weights_off_prime_powers rho eta hn).1.ge
  have hnonnegMinus : ∀ n, 0 ≤ minusMangoldtWeight rho eta n := by
    intro n
    by_cases hn : IsPrimePow n
    · exact (hpositive n hn).2.le
    · exact (mangoldt_weights_off_prime_powers rho eta hn).2.ge
  refine ⟨⟨hnonnegPlus, ?_, ?_⟩, ⟨hnonnegMinus, ?_, ?_⟩⟩
  · intro n hn
    exact (mangoldt_weights_off_prime_powers rho eta hn).1
  · intro p k l hp hk hl
    rw [plusMangoldtWeight_prime_pow rho eta hp hk,
      plusMangoldtWeight_prime_pow rho eta hp hl]
  · intro n hn
    exact (mangoldt_weights_off_prime_powers rho eta hn).2
  · intro p k l hp hk hl
    rw [minusMangoldtWeight_prime_pow rho eta hp hk,
      minusMangoldtWeight_prime_pow rho eta hp hl]

/-- The infinite coefficient bound gives the exact logarithmic divisor-feedback
bound used at every observation scale. -/
theorem infinitePrimeFactorResidual_abs_le_log
    (rho C : ℝ)
    (hcoeff : ∀ p : ℕ, p.Prime →
      |infinitePrimeCoefficient rho p| ≤ C * Real.log p) (n : ℕ) :
    |primeFactorResidual (infinitePrimeCoefficient rho) n| ≤
      C * Real.log n := by
  apply primeFactorResidual_abs_le_log
  intro p hp
  exact hcoeff p (Nat.prime_of_mem_primeFactors hp)

/-- Normalization by `C log(2X)` controls every divisor-feedback coordinate
through `2X` by the requested tolerance. -/
theorem normalized_divisor_feedback_le_tolerance
    (rho C tau : ℝ) (X n : ℕ)
    (hC : 0 < C) (htau : 0 ≤ tau) (hX : 1 ≤ X)
    (hnpos : 1 ≤ n) (hnX : n ≤ 2 * X)
    (hcoeff : ∀ p : ℕ, p.Prime →
      |infinitePrimeCoefficient rho p| ≤ C * Real.log p) :
    |(tau / (C * Real.log ((2 * X : ℕ) : ℝ))) *
        primeFactorResidual (infinitePrimeCoefficient rho) n| ≤ tau := by
  have htwoX : (1 : ℝ) < ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * X by omega)
  have hlog : 0 < Real.log ((2 * X : ℕ) : ℝ) := Real.log_pos htwoX
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hnpos)
  have hlogle : Real.log n ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    apply Real.log_le_log hnreal
    exact_mod_cast hnX
  have hresidual := infinitePrimeFactorResidual_abs_le_log rho C hcoeff n
  have hresidual' :
      |primeFactorResidual (infinitePrimeCoefficient rho) n| ≤
        C * Real.log ((2 * X : ℕ) : ℝ) := by
    exact hresidual.trans (mul_le_mul_of_nonneg_left hlogle hC.le)
  exact scaled_residual_le_tolerance _ tau C (Real.log ((2 * X : ℕ) : ℝ))
    htau hC hlog hresidual'

/-- The divisor residual of the actual plus weight is the scaled
prime-factor residual. -/
theorem plusMangoldtWeight_divisor_feedback
    (rho eta : ℝ) (inputs : StandardConditioningInputs rho)
    {n : ℕ} (hn : n ≠ 0) :
    divisorFeedbackResidual (plusMangoldtWeight rho eta) n =
      eta * primeFactorResidual (infinitePrimeCoefficient rho) n := by
  classical
  unfold divisorFeedbackResidual plusMangoldtWeight
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum,
    inputs.perturbation_divisor_identity n hn]
  ring

/-- The divisor residual of the actual minus weight is the negative scaled
prime-factor residual. -/
theorem minusMangoldtWeight_divisor_feedback
    (rho eta : ℝ) (inputs : StandardConditioningInputs rho)
    {n : ℕ} (hn : n ≠ 0) :
    divisorFeedbackResidual (minusMangoldtWeight rho eta) n =
      -eta * primeFactorResidual (infinitePrimeCoefficient rho) n := by
  classical
  unfold divisorFeedbackResidual minusMangoldtWeight
  simp_rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ArithmeticFunction.vonMangoldt_sum,
    inputs.perturbation_divisor_identity n hn]
  ring

/-- Exact summatory difference of the two actual perturbed weights. -/
theorem mangoldt_weight_prefix_difference
    (rho eta : ℝ) (X : ℕ) :
    arithmeticPrefix (plusMangoldtWeight rho eta) X -
        arithmeticPrefix (minusMangoldtWeight rho eta) X =
      2 * eta * arithmeticPrefix (infinitePrimePowerPerturbation rho) X := by
  classical
  unfold arithmeticPrefix plusMangoldtWeight minusMangoldtWeight
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  ring

/-- The eventual signed-prefix estimate gives the paper's normalized output
separation for the actual plus/minus weights. -/
theorem normalized_mangoldt_output_separation
    (rho C tau : ℝ) (X : ℕ)
    (hrho : 0 < rho) (hC : 0 < C) (htau : 0 ≤ tau)
    (hX : 1 ≤ X)
    (hlower : (X : ℝ) ^ rho / (2 * rho) ≤
      |arithmeticPrefix (infinitePrimePowerPerturbation rho) X|) :
    tau * (X : ℝ) ^ rho /
        (rho * C * Real.log ((2 * X : ℕ) : ℝ)) ≤
      |arithmeticPrefix
          (plusMangoldtWeight rho
            (tau / (C * Real.log ((2 * X : ℕ) : ℝ)))) X -
        arithmeticPrefix
          (minusMangoldtWeight rho
            (tau / (C * Real.log ((2 * X : ℕ) : ℝ)))) X| := by
  have htwoX : (1 : ℝ) < ((2 * X : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < 2 * X by omega)
  have hlog : 0 < Real.log ((2 * X : ℕ) : ℝ) := Real.log_pos htwoX
  have hsep := scaled_two_sign_separation rho tau C
    (Real.log ((2 * X : ℕ) : ℝ)) ((X : ℝ) ^ rho)
    (arithmeticPrefix (infinitePrimePowerPerturbation rho) X)
    hrho htau hC hlog hlower
  rw [mangoldt_weight_prefix_difference]
  calc
    _ ≤ |(tau / (C * Real.log ((2 * X : ℕ) : ℝ))) *
          arithmeticPrefix (infinitePrimePowerPerturbation rho) X -
        (-(tau / (C * Real.log ((2 * X : ℕ) : ℝ)))) *
          arithmeticPrefix (infinitePrimePowerPerturbation rho) X| := hsep
    _ = _ := by
      congr 1
      ring

/-- Scaling pulls out of the logarithmic perturbation moment. -/
theorem logarithmicMoment_scaled
    (e : ℕ → ℝ) (scale : ℝ) (N : ℕ) :
    logarithmicMoment (fun n => scale * e n) N =
      scale * logarithmicMoment e N := by
  classical
  unfold logarithmicMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- Scaling pulls out of the harmonic mass through its absolute value. -/
theorem harmonicMass_scaled
    (e : ℕ → ℝ) (scale : ℝ) (N : ℕ) :
    harmonicMass (fun n => scale * e n) N =
      |scale| * harmonicMass e N := by
  classical
  unfold harmonicMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [abs_mul]
  ring

theorem orderedHyperbolaSum_scale_left
    (f g : ℕ → ℝ) (scale : ℝ) (N : ℕ) :
    orderedHyperbolaSum (fun n => scale * f n) g N =
      scale * orderedHyperbolaSum f g N := by
  classical
  unfold orderedHyperbolaSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem orderedHyperbolaSum_scale_right
    (f g : ℕ → ℝ) (scale : ℝ) (N : ℕ) :
    orderedHyperbolaSum f (fun n => scale * g n) N =
      scale * orderedHyperbolaSum f g N := by
  classical
  unfold orderedHyperbolaSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The ordered hyperbola domain is invariant under swapping its two
coordinates. -/
theorem orderedHyperbolaSum_comm
    (f g : ℕ → ℝ) (N : ℕ) :
    orderedHyperbolaSum f g N = orderedHyperbolaSum g f N := by
  classical
  have hinner (a : ℕ) (ha : a ∈ Finset.Icc 1 N) (u v : ℕ → ℝ) :
      ∑ b ∈ Finset.Icc 1 (N / a), u a * v b =
        ∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then u a * v b else 0 := by
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have hset :
        (Finset.Icc 1 N).filter (fun b => a * b ≤ N) =
          Finset.Icc 1 (N / a) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨hb1, hbN⟩, hab⟩
        exact ⟨hb1, (Nat.le_div_iff_mul_le ha0).2 (by simpa [mul_comm] using hab)⟩
      · rintro ⟨hb1, hbdiv⟩
        have hbN : b ≤ N := hbdiv.trans (Nat.div_le_self N a)
        exact ⟨⟨hb1, hbN⟩,
          (by simpa [mul_comm] using (Nat.le_div_iff_mul_le ha0).1 hbdiv)⟩
    rw [← hset, Finset.sum_filter]
  unfold orderedHyperbolaSum
  calc
    (∑ a ∈ Finset.Icc 1 N,
        ∑ b ∈ Finset.Icc 1 (N / a), f a * g b) =
        ∑ a ∈ Finset.Icc 1 N,
          ∑ b ∈ Finset.Icc 1 N,
            if a * b ≤ N then f a * g b else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hinner a ha f g
    _ = ∑ b ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 N,
            if b * a ≤ N then g b * f a else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro a ha
      simp only [mul_comm]
    _ = ∑ b ∈ Finset.Icc 1 N,
          ∑ a ∈ Finset.Icc 1 (N / b), g b * f a := by
      apply Finset.sum_congr rfl
      intro b hb
      exact (hinner b hb g f).symm

/-- Ordered hyperbola sums are bilinear over pointwise addition. -/
theorem orderedHyperbolaSum_add
    (f g : ℕ → ℝ) (N : ℕ) :
    orderedHyperbolaSum (fun n => f n + g n) (fun n => f n + g n) N =
      orderedHyperbolaSum f f N + orderedHyperbolaSum f g N +
        orderedHyperbolaSum g f N + orderedHyperbolaSum g g N := by
  classical
  unfold orderedHyperbolaSum
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  ring

/-- Logarithmic moments are linear over pointwise addition. -/
theorem logarithmicMoment_add
    (f g : ℕ → ℝ) (N : ℕ) :
    logarithmicMoment (fun n => f n + g n) N =
      logarithmicMoment f N + logarithmicMoment g N := by
  classical
  unfold logarithmicMoment
  simp_rw [add_mul, Finset.sum_add_distrib]

/-- Exact expansion of the Selberg statistic around a base weight. -/
theorem selbergStatistic_add
    (base e : ℕ → ℝ) (N : ℕ)
    (hcross : orderedHyperbolaSum base e N =
      orderedHyperbolaSum e base N) :
    selbergStatistic (fun n => base n + e n) N =
      selbergStatistic base N + selbergPerturbation base e N := by
  classical
  unfold selbergStatistic selbergPerturbation
  rw [logarithmicMoment_add, orderedHyperbolaSum_add]
  rw [hcross]
  ring

/-- The actual scaled prime-power perturbation preserves the classical
Selberg `O(N)` remainder, with every constant displayed. -/
theorem scaled_mangoldt_selberg_stability
    (rho scale : ℝ) (inputs : StandardConditioningInputs rho) (N : ℕ) :
    |selbergStatistic
          (fun n => ArithmeticFunction.vonMangoldt n +
            scale * infinitePrimePowerPerturbation rho n) N -
        2 * (N : ℝ) * Real.log N| ≤
      (inputs.baseSelbergConstant +
        |scale| * inputs.perturbationLogConstant +
        2 * inputs.chebyshevConstant *
          (|scale| * inputs.perturbationHarmonicConstant) +
        (|scale| * inputs.perturbationHarmonicConstant) ^ 2) * (N : ℝ) := by
  let e : ℕ → ℝ := fun n =>
    scale * infinitePrimePowerPerturbation rho n
  have hlog : |logarithmicMoment e N| ≤
      (|scale| * inputs.perturbationLogConstant) * (N : ℝ) := by
    rw [show logarithmicMoment e N =
        scale * logarithmicMoment (infinitePrimePowerPerturbation rho) N by
      exact logarithmicMoment_scaled _ _ _]
    rw [abs_mul]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left (inputs.perturbation_log_moment N)
        (abs_nonneg scale))
  have hharmonic : harmonicMass e N ≤
      |scale| * inputs.perturbationHarmonicConstant := by
    rw [show harmonicMass e N =
        |scale| * harmonicMass (infinitePrimePowerPerturbation rho) N by
      exact harmonicMass_scaled _ _ _]
    exact mul_le_mul_of_nonneg_left (inputs.perturbation_harmonic N)
      (abs_nonneg scale)
  have hfeedback := finite_selberg_feedback_stability
    ArithmeticFunction.vonMangoldt e N
    (|scale| * inputs.perturbationLogConstant)
    inputs.chebyshevConstant
    (|scale| * inputs.perturbationHarmonicConstant)
    inputs.chebyshevConstant_nonneg
    (mul_nonneg (abs_nonneg scale)
      inputs.perturbationHarmonicConstant_nonneg)
    hlog (fun n => ArithmeticFunction.vonMangoldt_nonneg)
    (inputs.vonMangoldt_prefix N) hharmonic
  have hcross : orderedHyperbolaSum ArithmeticFunction.vonMangoldt e N =
      orderedHyperbolaSum e ArithmeticFunction.vonMangoldt N := by
    exact orderedHyperbolaSum_comm _ _ _
  rw [selbergStatistic_add ArithmeticFunction.vonMangoldt e N hcross]
  calc
    |selbergStatistic ArithmeticFunction.vonMangoldt N +
        selbergPerturbation ArithmeticFunction.vonMangoldt e N -
        2 * (N : ℝ) * Real.log N| ≤
      |selbergStatistic ArithmeticFunction.vonMangoldt N -
          2 * (N : ℝ) * Real.log N| +
        |selbergPerturbation ArithmeticFunction.vonMangoldt e N| := by
      rw [show selbergStatistic ArithmeticFunction.vonMangoldt N +
          selbergPerturbation ArithmeticFunction.vonMangoldt e N -
          2 * (N : ℝ) * Real.log N =
        (selbergStatistic ArithmeticFunction.vonMangoldt N -
          2 * (N : ℝ) * Real.log N) +
          selbergPerturbation ArithmeticFunction.vonMangoldt e N by ring]
      exact abs_add_le _ _
    _ ≤ inputs.baseSelbergConstant * (N : ℝ) +
        (|scale| * inputs.perturbationLogConstant +
          2 * inputs.chebyshevConstant *
            (|scale| * inputs.perturbationHarmonicConstant) +
          (|scale| * inputs.perturbationHarmonicConstant) ^ 2) * (N : ℝ) := by
      exact add_le_add (inputs.base_selberg N) hfeedback
    _ = _ := by ring

/-- A common scale cap turns the preceding exact estimate into one Selberg
constant independent of the chosen observation scale and tolerance. -/
theorem scaled_mangoldt_selberg_stability_uniform
    (rho scale scaleCap : ℝ) (inputs : StandardConditioningInputs rho)
    (hscale : |scale| ≤ scaleCap) (hcap : 0 ≤ scaleCap) (N : ℕ) :
    |selbergStatistic
          (fun n => ArithmeticFunction.vonMangoldt n +
            scale * infinitePrimePowerPerturbation rho n) N -
        2 * (N : ℝ) * Real.log N| ≤
      (inputs.baseSelbergConstant +
        scaleCap * inputs.perturbationLogConstant +
        2 * inputs.chebyshevConstant *
          (scaleCap * inputs.perturbationHarmonicConstant) +
        (scaleCap * inputs.perturbationHarmonicConstant) ^ 2) * (N : ℝ) := by
  have hs0 : 0 ≤ |scale| := abs_nonneg scale
  have hB := inputs.perturbationLogConstant_nonneg
  have hC := inputs.chebyshevConstant_nonneg
  have hD := inputs.perturbationHarmonicConstant_nonneg
  have hlinear :
      |scale| * inputs.perturbationLogConstant ≤
        scaleCap * inputs.perturbationLogConstant :=
    mul_le_mul_of_nonneg_right hscale hB
  have hmass :
      |scale| * inputs.perturbationHarmonicConstant ≤
        scaleCap * inputs.perturbationHarmonicConstant :=
    mul_le_mul_of_nonneg_right hscale hD
  have hcross :
      2 * inputs.chebyshevConstant *
          (|scale| * inputs.perturbationHarmonicConstant) ≤
        2 * inputs.chebyshevConstant *
          (scaleCap * inputs.perturbationHarmonicConstant) :=
    mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hC)
  have hsq :
      (|scale| * inputs.perturbationHarmonicConstant) ^ 2 ≤
        (scaleCap * inputs.perturbationHarmonicConstant) ^ 2 := by
    have := mul_le_mul hmass hmass
      (mul_nonneg hs0 hD) (mul_nonneg hcap hD)
    simpa [pow_two] using this
  have hcoeff :
      inputs.baseSelbergConstant +
          |scale| * inputs.perturbationLogConstant +
          2 * inputs.chebyshevConstant *
            (|scale| * inputs.perturbationHarmonicConstant) +
          (|scale| * inputs.perturbationHarmonicConstant) ^ 2 ≤
        inputs.baseSelbergConstant +
          scaleCap * inputs.perturbationLogConstant +
          2 * inputs.chebyshevConstant *
            (scaleCap * inputs.perturbationHarmonicConstant) +
          (scaleCap * inputs.perturbationHarmonicConstant) ^ 2 := by
    linarith
  exact (scaled_mangoldt_selberg_stability rho scale inputs N).trans
    (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N))

/-- The manuscript's near-linear conditioning witness, with the PNT and
classical Selberg estimates isolated in `StandardConditioningInputs` rather
than hidden in the conclusion.  The signed-prefix separation is derived from
the proved limit in `InfinitePrimePowerConstruction`. -/
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
  rcases eventual_signed_prefix_lower_bound rho inputs.toStandardPrimePowerInputs with
    ⟨X1, hX1⟩
  refine ⟨max X1 2, le_max_right _ _, ?_⟩
  intro X hX tau htau htauOne
  have hXX1 : X1 ≤ X := (le_max_left X1 2).trans hX
  have hXtwo : 2 ≤ X := (le_max_right X1 2).trans hX
  have hscaleBounds := conditioningScale_bounds inputs hXtwo htau.le htauOne
  rcases hscaleBounds with ⟨hscale0, hscaleCap, hsmall⟩
  have hcones := mangoldt_weights_mem_prime_power_cone
    rho (conditioningScale inputs X tau) inputs.coefficientBound
    inputs.coefficientBound_pos inputs.coefficient_bound hsmall
  refine ⟨hcones.1, hcones.2, ?_, ?_, ?_⟩
  · intro n hn1 hnX
    have hnormalized := normalized_divisor_feedback_le_tolerance
      rho inputs.coefficientBound tau X n inputs.coefficientBound_pos
      htau.le (le_trans (by norm_num) hXtwo) hn1 hnX inputs.coefficient_bound
    constructor
    · rw [plusMangoldtWeight_divisor_feedback rho
          (conditioningScale inputs X tau) inputs
          (Nat.ne_of_gt (zero_lt_one.trans_le hn1))]
      simpa [conditioningScale] using hnormalized
    · rw [minusMangoldtWeight_divisor_feedback rho
          (conditioningScale inputs X tau) inputs
          (Nat.ne_of_gt (zero_lt_one.trans_le hn1))]
      simpa [conditioningScale, abs_neg] using hnormalized
  · have hrho : 0 < rho :=
      lt_trans (by norm_num) inputs.oneHalf_lt_rho
    have hsep := normalized_mangoldt_output_separation
      rho inputs.coefficientBound tau X hrho inputs.coefficientBound_pos
      htau.le (le_trans (by norm_num) hXtwo) (hX1 X hXX1)
    have hsep' :
        tau * (X : ℝ) ^ rho /
            (rho * inputs.coefficientBound *
              Real.log ((2 * X : ℕ) : ℝ)) ≤
          |arithmeticPrefix
              (plusMangoldtWeight rho (conditioningScale inputs X tau)) X -
            arithmeticPrefix
              (minusMangoldtWeight rho (conditioningScale inputs X tau)) X| := by
      simpa [conditioningScale, Nat.mul_comm] using hsep
    exact hsep'.trans_eq (by
      unfold summatoryError
      congr 1
      ring)
  · have hlog4 : 0 < Real.log 4 := by
      exact Real.log_pos (by norm_num)
    have hcap0 : 0 ≤ conditioningScaleCap inputs := by
      unfold conditioningScaleCap
      exact div_nonneg zero_le_one
        (mul_pos inputs.coefficientBound_pos hlog4).le
    intro N
    constructor
    · change
        |selbergStatistic
              (fun n => ArithmeticFunction.vonMangoldt n +
                conditioningScale inputs X tau *
                  infinitePrimePowerPerturbation rho n) N -
            2 * (N : ℝ) * Real.log N| ≤
          conditioningSelbergConstant inputs * (N : ℝ)
      simpa only [conditioningSelbergConstant] using
        (scaled_mangoldt_selberg_stability_uniform rho
          (conditioningScale inputs X tau) (conditioningScaleCap inputs)
          inputs hscaleCap hcap0 N)
    · have hminusScale :
          |-(conditioningScale inputs X tau)| ≤ conditioningScaleCap inputs := by
        simpa using hscaleCap
      have hminusFun :
          minusMangoldtWeight rho (conditioningScale inputs X tau) =
            fun n => ArithmeticFunction.vonMangoldt n +
              (-(conditioningScale inputs X tau)) *
                infinitePrimePowerPerturbation rho n := by
        funext n
        unfold minusMangoldtWeight
        ring
      rw [hminusFun]
      simpa only [conditioningSelbergConstant] using
        (scaled_mangoldt_selberg_stability_uniform rho
          (-(conditioningScale inputs X tau)) (conditioningScaleCap inputs)
          inputs hminusScale hcap0 N)

end RiemannHypothesisProofFactory.SelbergConditioning
