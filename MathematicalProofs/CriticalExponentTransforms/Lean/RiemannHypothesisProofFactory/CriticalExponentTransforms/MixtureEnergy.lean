import RiemannHypothesisProofFactory.CriticalExponentTransforms.MultilinearMixture
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Filter Finset Fintype Real Topology MeasureTheory Set
open scoped BigOperators Interval

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

noncomputable def normalizedMixtureProfile
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (X u : ℝ) : V :=
  ∑ i : Fin d,
    (c ^ (i.1 + 1)) •
      (((X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
          mixtureExponent d (r0.1 + 1) sigma rho kappa)) *
        (u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)) • v i)

theorem normalizedMixtureProfile_tendsto
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (u : ℝ) (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0) :
    Tendsto
      (fun X : ℝ ↦ normalizedMixtureProfile d c sigma rho kappa v r0 X u)
      atTop
      (nhds ((u ^ mixtureExponent d (r0.1 + 1) sigma rho kappa) •
        ((c ^ (r0.1 + 1)) • v r0))) := by
  classical
  unfold normalizedMixtureProfile
  let a : Fin d → V := fun i =>
    if i = r0 then
      (u ^ mixtureExponent d (r0.1 + 1) sigma rho kappa) •
        ((c ^ (r0.1 + 1)) • v r0)
    else 0
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Tendsto
        (fun X : ℝ =>
          (c ^ (i.1 + 1)) •
            (((X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
                mixtureExponent d (r0.1 + 1) sigma rho kappa)) *
              (u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)) • v i))
        atTop (nhds (a i)) := by
    intro i _hi
    rcases lt_trichotomy i r0 with hir | hir | hir
    · simp [a, ne_of_lt hir, hvanish i hir]
    · subst i
      simp [a, smul_smul, mul_comm]
    · have hindex : 0 < ((i.1 : ℝ) - (r0.1 : ℝ)) := by
        apply sub_pos.mpr
        exact_mod_cast (show r0.1 < i.1 from hir)
      have hgap : 0 < ((i.1 : ℝ) - (r0.1 : ℝ)) * (sigma - rho) :=
        mul_pos hindex (sub_pos.mpr hsigmaRho)
      have hpow : Tendsto
          (fun X : ℝ => X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
              mixtureExponent d (r0.1 + 1) sigma rho kappa))
          atTop (nhds 0) := by
        convert tendsto_rpow_neg_atTop hgap using 1
        · funext X
          congr 1
          rw [mixtureExponent_sub_eq]
          push_cast
          ring
      have hcst : Tendsto
          (fun _ : ℝ => c ^ (i.1 + 1)) atTop (nhds (c ^ (i.1 + 1))) :=
        tendsto_const_nhds
      have hu : Tendsto
          (fun _ : ℝ => u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)
          atTop (nhds (u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)) :=
        tendsto_const_nhds
      have hinner := (hpow.mul hu).smul_const (v i)
      have hout := hcst.smul hinner
      simpa only [a, ne_of_gt hir, if_false, smul_zero, smul_smul,
        zero_mul, mul_zero, zero_smul] using hout
  have hsum := tendsto_finsetSum Finset.univ hterm
  simpa [a] using hsum

lemma rpow_abs_le_on_unit_dyadic {u a : ℝ} (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    |u ^ a| ≤ 2 ^ |a| := by
  have hu0 : 0 ≤ u := le_trans zero_le_one hu.1
  rw [abs_of_nonneg (Real.rpow_nonneg hu0 a)]
  by_cases ha : 0 ≤ a
  · calc
      u ^ a ≤ 2 ^ a := Real.rpow_le_rpow (le_trans zero_le_one hu.1) hu.2 ha
      _ = 2 ^ |a| := by rw [abs_of_nonneg ha]
  · have ha' : a ≤ 0 := le_of_not_ge ha
    calc
      u ^ a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu.1 ha'
      _ ≤ 2 ^ |a| := Real.one_le_rpow (by norm_num) (abs_nonneg a)

lemma mixtureExponent_diff_nonpos
    (d : ℕ) (sigma rho kappa : ℝ) (r0 i : Fin d)
    (hsigmaRho : rho < sigma) (hri : r0 ≤ i) :
    mixtureExponent d (i.1 + 1) sigma rho kappa -
        mixtureExponent d (r0.1 + 1) sigma rho kappa ≤ 0 := by
  rw [mixtureExponent_sub_eq]
  have hcast :
      (((r0.1 + 1 : ℕ) : ℝ) - ((i.1 + 1 : ℕ) : ℝ)) =
        (r0.1 : ℝ) - (i.1 : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hindex : (r0.1 : ℝ) - (i.1 : ℝ) ≤ 0 := by
    exact sub_nonpos.mpr (by exact_mod_cast hri)
  exact mul_nonpos_of_nonpos_of_nonneg hindex (sub_nonneg.mpr hsigmaRho.le)

noncomputable def mixtureProfileBound
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) : ℝ :=
  ∑ i : Fin d,
    |c ^ (i.1 + 1)| *
      (2 ^ |mixtureExponent d (i.1 + 1) sigma rho kappa| * ‖v i‖)

lemma normalizedMixtureProfile_norm_le
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0)
    {X u : ℝ} (hX : 1 ≤ X) (hu : u ∈ Set.Icc (1 : ℝ) 2) :
    ‖normalizedMixtureProfile d c sigma rho kappa v r0 X u‖ ≤
      mixtureProfileBound d c sigma rho kappa v := by
  classical
  unfold normalizedMixtureProfile mixtureProfileBound
  calc
    ‖∑ i : Fin d,
        (c ^ (i.1 + 1)) •
          (((X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
              mixtureExponent d (r0.1 + 1) sigma rho kappa)) *
            (u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)) • v i)‖ ≤
        ∑ i : Fin d,
          ‖(c ^ (i.1 + 1)) •
            (((X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
                mixtureExponent d (r0.1 + 1) sigma rho kappa)) *
              (u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)) • v i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin d,
        |c ^ (i.1 + 1)| *
          (2 ^ |mixtureExponent d (i.1 + 1) sigma rho kappa| * ‖v i‖) := by
      apply Finset.sum_le_sum
      intro i _hi
      by_cases hir : i < r0
      · rw [hvanish i hir]
        simp
      · have hri : r0 ≤ i := le_of_not_gt hir
        let beta := mixtureExponent d (i.1 + 1) sigma rho kappa -
          mixtureExponent d (r0.1 + 1) sigma rho kappa
        let alpha := mixtureExponent d (i.1 + 1) sigma rho kappa
        have hbeta : beta ≤ 0 :=
          mixtureExponent_diff_nonpos d sigma rho kappa r0 i hsigmaRho hri
        have hX0 : 0 ≤ X := le_trans zero_le_one hX
        have hXpow_nonneg : 0 ≤ X ^ beta := Real.rpow_nonneg hX0 beta
        have hXpow : |X ^ beta| ≤ 1 := by
          rw [abs_of_nonneg hXpow_nonneg]
          exact Real.rpow_le_one_of_one_le_of_nonpos hX hbeta
        have hupow := rpow_abs_le_on_unit_dyadic (a := alpha) hu
        have hproduct : |(X ^ beta) * (u ^ alpha)| ≤ 2 ^ |alpha| := by
          rw [abs_mul]
          calc
            |X ^ beta| * |u ^ alpha| ≤ 1 * |u ^ alpha| :=
              mul_le_mul_of_nonneg_right hXpow (abs_nonneg (u ^ alpha))
            _ ≤ 1 * (2 ^ |alpha|) :=
              mul_le_mul_of_nonneg_left hupow zero_le_one
            _ = 2 ^ |alpha| := one_mul _
        simp only [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hproduct (norm_nonneg (v i)))
          (abs_nonneg (c ^ (i.1 + 1)))

noncomputable def normalizedMixtureEnergyIntegrand
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (X u : ℝ) : ℝ :=
  ‖normalizedMixtureProfile d c sigma rho kappa v r0 X u‖ ^ 2 / u

noncomputable def normalizedMixtureDyadicEnergy
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (X : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..2,
    normalizedMixtureEnergyIntegrand d c sigma rho kappa v r0 X u

lemma normalizedMixtureProfile_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (X : ℝ) :
    ContinuousOn
      (normalizedMixtureProfile d c sigma rho kappa v r0 X)
      (Set.Ioc (1 : ℝ) 2) := by
  classical
  unfold normalizedMixtureProfile
  apply continuousOn_finsetSum
  intro i _hi
  have hpow : ContinuousOn
      (fun u : ℝ ↦ u ^ mixtureExponent d (i.1 + 1) sigma rho kappa)
      (Set.Ioc (1 : ℝ) 2) := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans zero_lt_one hu.1)
    exact ContinuousAt.continuousWithinAt
      (continuousAt_id.rpow_const (Or.inl hu0))
  exact continuousOn_const.smul
    ((continuousOn_const.mul hpow).smul continuousOn_const)

lemma normalizedMixtureEnergyIntegrand_continuousOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (X : ℝ) :
    ContinuousOn
      (normalizedMixtureEnergyIntegrand d c sigma rho kappa v r0 X)
      (Set.Ioc (1 : ℝ) 2) := by
  unfold normalizedMixtureEnergyIntegrand
  apply ContinuousOn.div
  · exact (normalizedMixtureProfile_continuousOn d c sigma rho kappa v r0 X).norm.pow 2
  · exact continuousOn_id
  · intro u hu
    exact ne_of_gt (lt_trans zero_lt_one hu.1)

lemma mixtureProfileBound_nonneg
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) :
    0 ≤ mixtureProfileBound d c sigma rho kappa v := by
  unfold mixtureProfileBound
  apply Finset.sum_nonneg
  intro i _hi
  positivity

theorem normalizedMixtureDyadicEnergy_tendsto
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0) :
    Tendsto
      (normalizedMixtureDyadicEnergy d c sigma rho kappa v r0)
      atTop
      (nhds (∫ u in (1 : ℝ)..2,
        ‖(u ^ mixtureExponent d (r0.1 + 1) sigma rho kappa) •
          ((c ^ (r0.1 + 1)) • v r0)‖ ^ 2 / u)) := by
  unfold normalizedMixtureDyadicEnergy
  let M := mixtureProfileBound d c sigma rho kappa v
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ ↦ M ^ 2)
  · filter_upwards with X
    simpa [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using
      (normalizedMixtureEnergyIntegrand_continuousOn d c sigma rho kappa v r0 X).aestronglyMeasurable
        measurableSet_Ioc
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    filter_upwards with u
    intro hu
    simp only [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hu
    have huIcc : u ∈ Set.Icc (1 : ℝ) 2 := ⟨hu.1.le, hu.2⟩
    have hp := normalizedMixtureProfile_norm_le d c sigma rho kappa v r0
      hsigmaRho hvanish hX huIcc
    have hM : 0 ≤ M := mixtureProfileBound_nonneg d c sigma rho kappa v
    have hsquare :
        ‖normalizedMixtureProfile d c sigma rho kappa v r0 X u‖ ^ 2 ≤ M ^ 2 := by
      nlinarith [norm_nonneg
        (normalizedMixtureProfile d c sigma rho kappa v r0 X u)]
    have hu0 : 0 < u := lt_trans zero_lt_one hu.1
    unfold normalizedMixtureEnergyIntegrand
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) hu0.le)]
    apply (div_le_iff₀ hu0).2
    calc
      ‖normalizedMixtureProfile d c sigma rho kappa v r0 X u‖ ^ 2 ≤ M ^ 2 :=
        hsquare
      _ ≤ M ^ 2 * u := by
        calc
          M ^ 2 = M ^ 2 * 1 := by ring
          _ ≤ M ^ 2 * u :=
            mul_le_mul_of_nonneg_left hu.1.le (sq_nonneg M)
  · exact intervalIntegrable_const
  · filter_upwards with u
    intro hu
    have hp := normalizedMixtureProfile_tendsto d c sigma rho kappa v r0 u hsigmaRho hvanish
    simpa only [normalizedMixtureEnergyIntegrand] using (hp.norm.pow 2).div_const u

noncomputable def mixtureDyadicEnergyLeadingConstant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) : ℝ :=
  ∫ u in (1 : ℝ)..2,
    ‖(u ^ mixtureExponent d (r0.1 + 1) sigma rho kappa) •
      ((c ^ (r0.1 + 1)) • v r0)‖ ^ 2 / u

lemma mixtureDyadicEnergyLeadingConstant_pos
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hc : c ≠ 0) (hvisible : v r0 ≠ 0) :
    0 < mixtureDyadicEnergyLeadingConstant d c sigma rho kappa v r0 := by
  let z : V := (c ^ (r0.1 + 1)) • v r0
  have hz : z ≠ 0 := smul_ne_zero (pow_ne_zero _ hc) hvisible
  unfold mixtureDyadicEnergyLeadingConstant
  apply intervalIntegral.integral_pos (by norm_num : (1 : ℝ) < 2)
  · intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hu.1)
    have hpow : ContinuousWithinAt
        (fun x : ℝ ↦ x ^ mixtureExponent d (r0.1 + 1) sigma rho kappa)
        (Set.Icc (1 : ℝ) 2) u :=
      ContinuousAt.continuousWithinAt
        (continuousAt_id.rpow_const (Or.inl hu0))
    exact (((hpow.smul continuousWithinAt_const).norm.pow 2).div
      continuousWithinAt_id hu0)
  · intro u hu
    exact div_nonneg (sq_nonneg _) (le_of_lt (lt_trans zero_lt_one hu.1))
  · refine ⟨1, by simp, ?_⟩
    simp only [one_rpow, one_smul, div_one]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)

end RiemannHypothesisProofFactory.CriticalExponentTransforms
