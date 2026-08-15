import BoundaryConstantObstruction.IncompleteGamma.ClassicalXi
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
Local-uniform convergence of the manuscript's exact finite
upper-incomplete-gamma approximants to the classical pole-removed Xi
completion.  The proof uses the positive Jacobi-theta tail as a single
integrable majorant on every complex compact set.
-/

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

lemma S_nonneg (N : ℕ) (u : ℝ) : 0 ≤ S N u := by
  unfold S
  exact Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

lemma S_le_thetaTailKernel (N : ℕ) (u : ℝ) :
    S N u ≤ thetaTailKernel u := by
  rw [← (hasSum_kernelTerm u).tsum_eq]
  exact (hasSum_kernelTerm u).summable.sum_le_tsum
    (Finset.range N) fun _ _ => (Real.exp_pos _).le

lemma tendsto_S_thetaTailKernel (u : ℝ) :
    Tendsto (fun N : ℕ => S N u) atTop (nhds (thetaTailKernel u)) := by
  simpa only [S] using (hasSum_kernelTerm u).tendsto_sum_nat

lemma S_continuous (N : ℕ) : Continuous (S N) := by
  unfold S kernelTerm
  fun_prop

/-- The positive weighted remainder after the first `N` theta summands. -/
def firstIntegralTailWeight (R : ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  (thetaTailKernel u - S N u) * Real.exp (R * u)

lemma firstIntegralTailWeight_nonneg (R : ℝ) (N : ℕ) (u : ℝ) :
    0 ≤ firstIntegralTailWeight R N u := by
  exact mul_nonneg (sub_nonneg.mpr (S_le_thetaTailKernel N u))
    (Real.exp_pos _).le

lemma firstIntegralTailWeight_le (R : ℝ) (N : ℕ) (u : ℝ) :
    firstIntegralTailWeight R N u ≤
      thetaTailKernel u * Real.exp (R * u) := by
  unfold firstIntegralTailWeight
  have hS := S_nonneg N u
  have hexp := (Real.exp_pos (R * u)).le
  nlinarith

lemma firstIntegralTailWeight_continuousOn (R : ℝ) (N : ℕ) :
    ContinuousOn (firstIntegralTailWeight R N) (Ioi 0) := by
  unfold firstIntegralTailWeight
  exact (continuousOn_thetaTailKernel.sub (S_continuous N).continuousOn).mul
    ((Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).continuousOn)

lemma integrableOn_firstIntegralTailWeight {R : ℝ} (hR : 0 ≤ R) (N : ℕ) :
    IntegrableOn (firstIntegralTailWeight R N) (Ioi 0) := by
  refine (integrableOn_thetaTailKernel_mul_exp hR).mono' ?_ ?_
  · exact (firstIntegralTailWeight_continuousOn R N).aestronglyMeasurable
      measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs,
      abs_of_nonneg (firstIntegralTailWeight_nonneg R N u)]
    exact firstIntegralTailWeight_le R N u

/-- A scalar error bound which is uniform for `‖z‖ ≤ R`. -/
def firstIntegralTailBound (R : ℝ) (N : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), firstIntegralTailWeight R N u

lemma firstIntegralTailWeight_tendsto_zero (R u : ℝ) :
    Tendsto (fun N : ℕ => firstIntegralTailWeight R N u)
      atTop (nhds 0) := by
  have hsub : Tendsto (fun N : ℕ => thetaTailKernel u - S N u)
      atTop (nhds (thetaTailKernel u - thetaTailKernel u)) :=
    tendsto_const_nhds.sub (tendsto_S_thetaTailKernel u)
  have hmul := hsub.mul
    (show Tendsto (fun _ : ℕ => Real.exp (R * u)) atTop
      (nhds (Real.exp (R * u))) from tendsto_const_nhds)
  simpa only [firstIntegralTailWeight, sub_self, zero_mul] using hmul

theorem firstIntegralTailBound_tendsto_zero {R : ℝ} (hR : 0 ≤ R) :
    Tendsto (fun N : ℕ => firstIntegralTailBound R N) atTop (nhds 0) := by
  let major : ℝ → ℝ := fun u =>
    thetaTailKernel u * Real.exp (R * u)
  have hmeas : ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable (firstIntegralTailWeight R N)
        (volume.restrict (Ioi 0)) := by
    exact Eventually.of_forall fun N =>
      (firstIntegralTailWeight_continuousOn R N).aestronglyMeasurable
        measurableSet_Ioi
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      ‖firstIntegralTailWeight R N u‖ ≤ major u := by
    refine Eventually.of_forall fun N => ?_
    filter_upwards with u
    rw [Real.norm_eq_abs,
      abs_of_nonneg (firstIntegralTailWeight_nonneg R N u)]
    exact firstIntegralTailWeight_le R N u
  have hmajor : Integrable major (volume.restrict (Ioi 0)) := by
    change IntegrableOn major (Ioi 0)
    simpa only [major] using integrableOn_thetaTailKernel_mul_exp hR
  have hlim : ∀ᵐ u ∂(volume.restrict (Ioi 0)),
      Tendsto (fun N : ℕ => firstIntegralTailWeight R N u)
        atTop (nhds (0 : ℝ)) := by
    exact ae_of_all _ fun u => firstIntegralTailWeight_tendsto_zero R u
  have h := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (F := fun N : ℕ => firstIntegralTailWeight R N)
    (f := fun _ : ℝ => (0 : ℝ))
    (μ := volume.restrict (Ioi (0 : ℝ))) major
    hmeas hbound hmajor hlim
  simpa only [firstIntegralTailBound, integral_zero] using h

lemma firstIntegralTailBound_nonneg (R : ℝ) (N : ℕ) :
    0 ≤ firstIntegralTailBound R N := by
  unfold firstIntegralTailBound
  exact integral_nonneg_of_ae
    (ae_of_all _ fun u => firstIntegralTailWeight_nonneg R N u)

lemma integrableOn_S_mul_cos (N : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => (S N u : ℂ) * Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hsum :
      (fun u : ℝ => (S N u : ℂ) * Complex.cos (z * (u : ℂ))) =
        fun u : ℝ => ∑ n ∈ Finset.range N,
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
    funext u
    simp [S, Finset.sum_mul]
  rw [hsum]
  exact integrable_finsetSum (Finset.range N) fun n _ =>
    integrableOn_kernelTerm_mul_cos n z

lemma infiniteFirstIntegral_sub_firstIntegral (N : ℕ) (z : ℂ) :
    infiniteFirstIntegral z - firstIntegral N z =
      ∫ u in Ioi (0 : ℝ),
        ((thetaTailKernel u - S N u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ)) := by
  rw [infiniteFirstIntegral, firstIntegral,
    ← integral_sub (integrableOn_thetaTailKernel_mul_cos z)
      (integrableOn_S_mul_cos N z)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  push_cast
  ring

lemma dist_infiniteFirstIntegral_firstIntegral_le
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (N : ℕ) :
    dist (infiniteFirstIntegral z) (firstIntegral N z) ≤
      firstIntegralTailBound R N := by
  rw [dist_eq_norm, infiniteFirstIntegral_sub_firstIntegral]
  change
    ‖∫ u in Ioi (0 : ℝ),
        ((thetaTailKernel u - S N u : ℝ) : ℂ) *
          Complex.cos (z * (u : ℂ))‖ ≤
      ∫ u in Ioi (0 : ℝ), firstIntegralTailWeight R N u
  apply norm_integral_le_of_norm_le (integrableOn_firstIntegralTailWeight hR N)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  have htail : 0 ≤ thetaTailKernel u - S N u :=
    sub_nonneg.mpr (S_le_thetaTailKernel N u)
  have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (R * u) := by
    refine (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact mul_le_mul_of_nonneg_right hz hu0
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg htail]
  unfold firstIntegralTailWeight
  exact mul_le_mul_of_nonneg_left hcos htail

theorem firstIntegral_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun N : ℕ => firstIntegral N) infiniteFirstIntegral atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR, hKR⟩ : ∃ R : ℝ, R > 0 ∧ ∀ z ∈ K, ‖z‖ ≤ R :=
    hK.isBounded.exists_pos_norm_le
  have htail : ∀ᶠ N : ℕ in atTop, firstIntegralTailBound R N < ε :=
    (firstIntegralTailBound_tendsto_zero hR.le).eventually
      (eventually_lt_nhds hε)
  filter_upwards [htail] with N hN
  intro z hz
  exact (dist_infiniteFirstIntegral_firstIntegral_le hR.le
    (hKR z hz) N).trans_lt hN

lemma norm_Xi_multiplier_le {R : ℝ} (hR : 0 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖2 * (z ^ 2 + 1 / 4)‖ ≤ 2 * (R ^ 2 + 1 / 4) := by
  rw [norm_mul, Complex.norm_ofNat]
  gcongr
  calc
    ‖z ^ 2 + 1 / 4‖ ≤ ‖z ^ 2‖ + ‖(1 / 4 : ℂ)‖ := norm_add_le _ _
    _ = ‖z‖ ^ 2 + 1 / 4 := by norm_num [norm_pow]
    _ ≤ R ^ 2 + 1 / 4 := by nlinarith [norm_nonneg z]

lemma dist_classicalXi_XiIncompleteGamma_le
    {R : ℝ} (hR : 0 ≤ R) {z : ℂ} (hz : ‖z‖ ≤ R) (N : ℕ) :
    dist (classicalXi z) (XiIncompleteGamma N z) ≤
      (2 * (R ^ 2 + 1 / 4)) * firstIntegralTailBound R N := by
  rw [classicalXi_eq_infiniteFirstIntegral,
    XiIncompleteGamma_eq_firstIntegral, dist_eq_norm]
  have heq :
      (1 / 2 - 2 * (z ^ 2 + 1 / 4) * infiniteFirstIntegral z) -
          (1 / 2 - 2 * (z ^ 2 + 1 / 4) * firstIntegral N z) =
        -(2 * (z ^ 2 + 1 / 4)) *
          (infiniteFirstIntegral z - firstIntegral N z) := by ring
  rw [heq, norm_mul, norm_neg]
  have hfactor := norm_Xi_multiplier_le hR hz
  have hintegral := dist_infiniteFirstIntegral_firstIntegral_le hR hz N
  rw [dist_eq_norm] at hintegral
  exact mul_le_mul hfactor hintegral (norm_nonneg _)
    (by positivity)

/-- Exact local-uniform convergence claimed in the frozen manuscript. -/
theorem XiIncompleteGamma_tendstoLocallyUniformly :
    TendstoLocallyUniformly
      (fun N : ℕ => XiIncompleteGamma N) classicalXi atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR, hKR⟩ : ∃ R : ℝ, R > 0 ∧ ∀ z ∈ K, ‖z‖ ≤ R :=
    hK.isBounded.exists_pos_norm_le
  let C : ℝ := 2 * (R ^ 2 + 1 / 4)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hscaled :
      Tendsto (fun N : ℕ => C * firstIntegralTailBound R N)
        atTop (nhds 0) := by
    have h :=
      (show Tendsto (fun _ : ℕ => C) atTop (nhds C) from
        tendsto_const_nhds).mul
      (firstIntegralTailBound_tendsto_zero hR.le)
    simpa only [mul_zero] using h
  have htail : ∀ᶠ N : ℕ in atTop,
      C * firstIntegralTailBound R N < ε :=
    hscaled.eventually (eventually_lt_nhds hε)
  filter_upwards [htail] with N hN
  intro z hz
  exact (dist_classicalXi_XiIncompleteGamma_le hR.le (hKR z hz) N).trans_lt
    (by simpa only [C] using hN)

end IncompleteGammaApproximant
