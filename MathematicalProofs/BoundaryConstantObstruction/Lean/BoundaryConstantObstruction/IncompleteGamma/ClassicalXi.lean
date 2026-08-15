import BoundaryConstantObstruction.IncompleteGamma.Frontend
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- The pole-removed completed Riemann zeta function in the manuscript's
normalization. -/
def classicalXiCompletion (s : ℂ) : ℂ :=
  (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

/-- Critical-line coordinates, extended to a complex spectral parameter. -/
def classicalZetaCoordinate (z : ℂ) : ℂ :=
  1 / 2 + Complex.I * z

/-- The classical entire `Xi` function in the paper's spectral coordinate. -/
def classicalXi (z : ℂ) : ℂ :=
  classicalXiCompletion (classicalZetaCoordinate z)

/-- Away from the two removable exceptional points, the entire completion is
the standard polynomial multiple of Mathlib's meromorphic completed zeta. -/
theorem classicalXiCompletion_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    classicalXiCompletion s =
      (s * (s - 1) / 2) * completedRiemannZeta s := by
  rw [classicalXiCompletion, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- On the right half-plane, Mathlib's completed zeta has exactly the
archimedean normalization printed in the manuscript. -/
theorem completedRiemannZeta_eq_GammaReal_mul_of_re_pos {s : ℂ}
    (hs : 0 < s.re) :
    completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hmul := (eq_div_iff hGamma).mp (riemannZeta_def_of_ne_zero hs0)
  simpa only [mul_comm] using hmul.symm

/-- Exact agreement with the manuscript's displayed `xi` formula on a
nonempty regular domain.  `classicalXiCompletion` is its pole-removed entire
continuation at the exceptional points. -/
theorem classicalXiCompletion_eq_printed_formula {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    classicalXiCompletion s =
      (1 / 2) * s * (s - 1) *
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) *
        riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  rw [classicalXiCompletion_eq_mul_completedRiemannZeta hs0 hs1,
    completedRiemannZeta_eq_GammaReal_mul_of_re_pos hs, Gammaℝ_def]
  ring

/-- The exact pinned theta/Mellin substrate behind `classicalXi`. -/
theorem classicalXi_eq_thetaMellin (z : ℂ) :
    classicalXi z =
      (1 + classicalZetaCoordinate z * (classicalZetaCoordinate z - 1) *
        (mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
          (classicalZetaCoordinate z / 2) / 2)) / 2 := by
  rfl

lemma thetaPair_f_modif_of_one_lt {x : ℝ} (hx : 1 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x =
      (HurwitzZeta.cosKernel 0 x - 1 : ℝ) := by
  rw [WeakFEPair.f_modif, Pi.add_apply,
    indicator_of_mem (mem_Ioi.mpr hx),
    indicator_of_notMem (notMem_Ioo_of_ge hx.le), add_zero]
  simp only [HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  push_cast
  rfl

lemma thetaPair_f_modif_reciprocal {x : ℝ} (hx : 1 < x) :
    (HurwitzZeta.hurwitzEvenFEPair 0).f_modif (1 / x) =
      ((x ^ (1 / 2 : ℝ) : ℝ) : ℂ) •
        (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hself : P.g_modif = P.f_modif := by
    have h := congrArg WeakFEPair.f_modif
      HurwitzZeta.hurwitzEvenFEPair_zero_symm
    simpa [P, WeakFEPair.symm, WeakFEPair.f_modif,
      WeakFEPair.g_modif] using h
  have h := P.hf_modif_FE x (zero_lt_one.trans hx)
  rw [hself] at h
  simpa [P, HurwitzZeta.hurwitzEvenFEPair] using h

private def thetaMellinIntegrand (q : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (q - 1) • (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x

lemma integrableOn_thetaMellinIntegrand (q : ℂ) :
    IntegrableOn (thetaMellinIntegrand q) (Ioi 0) := by
  have h := IsStrongFEPair.hasMellin
    (HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair q
  exact h.1

lemma mellin_thetaPair_eq_lower_add_upper (q : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif q =
      (∫ x in Ioc (0 : ℝ) 1, thetaMellinIntegrand q x) +
      ∫ x in Ioi (1 : ℝ), thetaMellinIntegrand q x := by
  rw [mellin]
  change (∫ x in Ioi (0 : ℝ), thetaMellinIntegrand q x) = _
  have hsets : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext x
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hx, _⟩ | hx) <;> linarith
    · intro hx
      by_cases h1 : x ≤ 1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
  rw [← hsets, setIntegral_union]
  · exact disjoint_left.2 (by
      intro x hx hy
      exact (not_lt_of_ge hx.2) hy)
  · exact measurableSet_Ioi
  · exact (integrableOn_thetaMellinIntegrand q).mono_set (by
      intro x hx
      exact hx.1)
  · exact (integrableOn_thetaMellinIntegrand q).mono_set (by
      intro x hx
      exact zero_lt_one.trans (mem_Ioi.mp hx))

lemma thetaMellin_reciprocal_integrand (q : ℂ) {x : ℝ} (hx : 1 < x) :
    ((|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) : ℝ) •
        thetaMellinIntegrand q (x ^ (-1 : ℝ)) =
      thetaMellinIntegrand (1 / 2 - q) x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [Real.rpow_neg_one, ← one_div]
  unfold thetaMellinIntegrand
  rw [thetaPair_f_modif_reciprocal hx]
  simp only [abs_neg, abs_one, one_mul, Complex.real_smul, smul_eq_mul]
  push_cast
  rw [Complex.ofReal_cpow hx0.le, Complex.ofReal_cpow hx0.le,
    Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.inv_cpow_ofReal_nonneg hx0.le]
  rw [← Complex.cpow_neg]
  push_cast
  calc
    _ = (((x : ℂ) ^ (-2 : ℂ) *
          (x : ℂ) ^ (-(q - 1))) *
          (x : ℂ) ^ (1 / 2 : ℂ)) *
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by ring
    _ = (x : ℂ) ^ (((-2 : ℂ) + (-(q - 1))) + (1 / 2 : ℂ)) *
          (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne'),
        Complex.cpow_add _ _ (ofReal_ne_zero.mpr hx0.ne')]
    _ = _ := by
      congr 1
      ring

lemma lower_thetaMellin_eq_reflected_upper (q : ℂ) :
    (∫ x in Ioc (0 : ℝ) 1, thetaMellinIntegrand q x) =
      ∫ x in Ioi (1 : ℝ), thetaMellinIntegrand (1 / 2 - q) x := by
  rw [integral_Ioc_eq_integral_Ioo]
  let g : ℝ → ℂ := (Ioo (0 : ℝ) 1).indicator (thetaMellinIntegrand q)
  have hsub := integral_comp_rpow_Ioi g (p := (-1 : ℝ)) (by norm_num)
  have hrhs :
      (∫ y in Ioi (0 : ℝ), g y) =
        ∫ y in Ioo (0 : ℝ) 1, thetaMellinIntegrand q y := by
    change (∫ y in Ioi (0 : ℝ),
      (Ioo (0 : ℝ) 1).indicator (thetaMellinIntegrand q) y) = _
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [inter_eq_right.mpr]
    intro y hy
    exact mem_Ioi.mpr (mem_Ioo.mp hy).1
  have hlhs :
      (∫ x in Ioi (0 : ℝ),
          (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ))) =
        ∫ x in Ioi (1 : ℝ), thetaMellinIntegrand (1 / 2 - q) x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ),
          (Ioi (1 : ℝ)).indicator
            (thetaMellinIntegrand (1 / 2 - q)) x := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx0mem
        have hx0 : 0 < x := mem_Ioi.mp hx0mem
        by_cases hx1 : 1 < x
        · rw [indicator_of_mem (mem_Ioi.mpr hx1)]
          have hrecip : x ^ (-1 : ℝ) ∈ Ioo (0 : ℝ) 1 := by
            rw [Real.rpow_neg_one]
            exact mem_Ioo.mpr ⟨inv_pos.mpr hx0, inv_lt_one_of_one_lt₀ hx1⟩
          change (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
            (Ioo (0 : ℝ) 1).indicator (thetaMellinIntegrand q)
              (x ^ (-1 : ℝ)) = _
          rw [indicator_of_mem hrecip]
          exact thetaMellin_reciprocal_integrand q hx1
        · rw [indicator_of_notMem (notMem_Ioi.mpr (le_of_not_gt hx1))]
          have hrecip : x ^ (-1 : ℝ) ∉ Ioo (0 : ℝ) 1 := by
            rw [Real.rpow_neg_one]
            exact notMem_Ioo_of_ge ((one_le_inv₀ hx0).2 (le_of_not_gt hx1))
          change (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) •
            (Ioo (0 : ℝ) 1).indicator (thetaMellinIntegrand q)
              (x ^ (-1 : ℝ)) = 0
          rw [indicator_of_notMem hrecip, smul_zero]
      _ = _ := by
        rw [setIntegral_indicator measurableSet_Ioi]
        rw [inter_eq_right.mpr]
        intro x hx
        exact mem_Ioi.mpr (zero_lt_one.trans (mem_Ioi.mp hx))
  exact hrhs.symm.trans (hsub.symm.trans hlhs)

/-- The upper-half Mellin integral after the logarithmic substitution. -/
private def thetaLogIntegrand (q : ℂ) (v : ℝ) : ℂ :=
  ((Real.exp v : ℝ) : ℂ) ^ q *
    (HurwitzZeta.cosKernel 0 (Real.exp v) - 1 : ℝ)

lemma exp_smul_thetaMellinIntegrand (q : ℂ) {v : ℝ} (hv : 0 < v) :
    Real.exp v • thetaMellinIntegrand q (Real.exp v) =
      thetaLogIntegrand q v := by
  have hexp1 : 1 < Real.exp v := by
    simpa [← Real.exp_zero] using (Real.exp_lt_exp.mpr hv)
  unfold thetaMellinIntegrand thetaLogIntegrand
  rw [thetaPair_f_modif_of_one_lt hexp1]
  simp only [Complex.real_smul, smul_eq_mul]
  push_cast
  calc
    Complex.exp (v : ℂ) *
          (Complex.exp (v : ℂ) ^ (q - 1) *
            ((HurwitzZeta.cosKernel 0 (Real.exp v) : ℝ) - 1)) =
        (Complex.exp (v : ℂ) * Complex.exp (v : ℂ) ^ (q - 1)) *
          ((HurwitzZeta.cosKernel 0 (Real.exp v) : ℝ) - 1) := by
            rw [mul_assoc]
    _ = (Complex.exp (v : ℂ) ^ (1 : ℂ) *
          Complex.exp (v : ℂ) ^ (q - 1)) *
          ((HurwitzZeta.cosKernel 0 (Real.exp v) : ℝ) - 1) := by
            rw [Complex.cpow_one]
    _ = Complex.exp (v : ℂ) ^ ((1 : ℂ) + (q - 1)) *
          ((HurwitzZeta.cosKernel 0 (Real.exp v) : ℝ) - 1) := by
            rw [Complex.cpow_add _ _ (Complex.exp_ne_zero _)]
    _ = Complex.exp (v : ℂ) ^ q *
          ((HurwitzZeta.cosKernel 0 (Real.exp v) : ℝ) - 1) := by
            ring_nf

lemma thetaMellin_upper_eq_log_integral (q : ℂ) :
    (∫ x in Ioi (1 : ℝ), thetaMellinIntegrand q x) =
      2 * ∫ u in Ioi (0 : ℝ), thetaLogIntegrand q (2 * u) := by
  have hexp := integral_comp_exp_Ioi (thetaMellinIntegrand q) 0
  have hexp' :
      (∫ v in Ioi (0 : ℝ), thetaLogIntegrand q v) =
        ∫ x in Ioi (1 : ℝ), thetaMellinIntegrand q x := by
    rw [← Real.exp_zero]
    rw [← hexp]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact (exp_smul_thetaMellinIntegrand q (mem_Ioi.mp hv)).symm
  have hscale := integral_comp_mul_left_Ioi'
    (thetaLogIntegrand q) 0 (b := (2 : ℝ)) (by norm_num)
  rw [mul_zero] at hscale
  rw [← hexp']
  simpa only [Complex.real_smul, Complex.ofReal_ofNat] using hscale.symm

lemma mellin_thetaPair_eq_two_log_integrals (q : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif q =
      2 * (∫ u in Ioi (0 : ℝ), thetaLogIntegrand (1 / 2 - q) (2 * u)) +
      2 * ∫ u in Ioi (0 : ℝ), thetaLogIntegrand q (2 * u) := by
  rw [mellin_thetaPair_eq_lower_add_upper,
    lower_thetaMellin_eq_reflected_upper,
    thetaMellin_upper_eq_log_integral,
    thetaMellin_upper_eq_log_integral]

lemma integrableOn_thetaLogIntegrand (q : ℂ) :
    IntegrableOn (thetaLogIntegrand q) (Ioi 0) := by
  have hupper : IntegrableOn (thetaMellinIntegrand q) (Ioi 1) :=
    (integrableOn_thetaMellinIntegrand q).mono_set (by
      intro x hx
      exact zero_lt_one.trans (mem_Ioi.mp hx))
  have hexp : IntegrableOn
      (fun v : ℝ => Real.exp v • thetaMellinIntegrand q (Real.exp v))
      (Ioi 0) := by
    exact (integrableOn_comp_exp_Ioi (thetaMellinIntegrand q) 0).2 (by
      simpa using hupper)
  apply hexp.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  exact exp_smul_thetaMellinIntegrand q (mem_Ioi.mp hv)

lemma integrableOn_thetaLogIntegrand_two (q : ℂ) :
    IntegrableOn (fun u : ℝ => thetaLogIntegrand q (2 * u)) (Ioi 0) := by
  exact (integrableOn_Ioi_comp_mul_left_iff (thetaLogIntegrand q) 0
    (by norm_num : (0 : ℝ) < 2)).2 (by
      simpa using integrableOn_thetaLogIntegrand q)

lemma ofReal_exp_cpow (v : ℝ) (q : ℂ) :
    (((Real.exp v : ℝ) : ℂ) ^ q) = Complex.exp ((v : ℂ) * q) := by
  rw [Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  rw [Complex.log_exp
    (by simpa using neg_lt_zero.mpr Real.pi_pos)
    (by simpa using Real.pi_pos.le)]

/-- The infinite positive theta tail in exactly the normalization approached by `S N`. -/
def thetaTailKernel (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    (HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) - 1) / 2

/-- The two critical-line Mellin halves combine to the cosine-transform kernel. -/
lemma thetaLogIntegrand_critical_pair (z : ℂ) (u : ℝ) :
    thetaLogIntegrand
          (1 / 2 - classicalZetaCoordinate z / 2) (2 * u) +
        thetaLogIntegrand (classicalZetaCoordinate z / 2) (2 * u) =
      4 * ((thetaTailKernel u : ℝ) : ℂ) *
        Complex.cos (z * (u : ℂ)) := by
  unfold thetaLogIntegrand thetaTailKernel classicalZetaCoordinate
  rw [ofReal_exp_cpow, ofReal_exp_cpow]
  push_cast
  rw [show (2 : ℂ) * (u : ℂ) *
        (1 / 2 - (1 / 2 + Complex.I * z) / 2) =
        (u / 2 : ℝ) - (z * (u : ℂ)) * Complex.I by
      push_cast
      ring,
    show (2 : ℂ) * (u : ℂ) * ((1 / 2 + Complex.I * z) / 2) =
        (u / 2 : ℝ) + (z * (u : ℂ)) * Complex.I by
      push_cast
      ring]
  rw [Complex.exp_sub, Complex.exp_add, div_eq_mul_inv,
    ← Complex.exp_neg]
  calc
    Complex.exp (u / 2 : ℝ) * Complex.exp (-(z * (u : ℂ) * Complex.I)) *
          ((HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) : ℝ) - 1) +
        Complex.exp (u / 2 : ℝ) * Complex.exp (z * (u : ℂ) * Complex.I) *
          ((HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) : ℝ) - 1) =
      Complex.exp (u / 2 : ℝ) *
        (Complex.exp (z * (u : ℂ) * Complex.I) +
          Complex.exp (-(z * (u : ℂ)) * Complex.I)) *
        ((HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) : ℝ) - 1) := by ring
    _ = Complex.exp (u / 2 : ℝ) *
        (2 * Complex.cos (z * (u : ℂ))) *
        ((HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) : ℝ) - 1) := by
      rw [Complex.two_cos]
    _ = 4 *
        (Complex.exp ((u : ℂ) / 2) *
          ((HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) : ℝ) - 1) / 2) *
        Complex.cos (z * (u : ℂ)) := by
      have hexp : Complex.exp (((u / 2 : ℝ) : ℂ)) =
          Complex.exp ((u : ℂ) / 2) := by
        congr 1
        norm_num [Complex.ofReal_div]
      rw [hexp]
      ring

lemma hasSum_kernelTerm (u : ℝ) :
    HasSum (fun n : ℕ => kernelTerm n u) (thetaTailKernel u) := by
  have h := HurwitzZeta.hasSum_nat_cosKernel₀ 0
    (Real.exp_pos (2 * u))
  have hscaled := h.mul_left (Real.exp (u / 2) / 2)
  have hterms : HasSum (fun n : ℕ => kernelTerm n u)
      ((Real.exp (u / 2) / 2) *
        (HurwitzZeta.cosKernel 0 (Real.exp (2 * u)) - 1)) := by
    refine hscaled.congr_fun fun n => ?_
    simp only [zero_mul, mul_zero, Real.cos_zero, one_mul, kernelTerm]
    rw [show
        Real.exp (u / 2 - Real.pi * (n + 1 : ℝ) ^ 2 * Real.exp (2 * u)) =
          Real.exp (u / 2) *
            Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2 * Real.exp (2 * u)) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring
  convert hterms using 1
  unfold thetaTailKernel
  ring

lemma thetaTailKernel_nonneg (u : ℝ) : 0 ≤ thetaTailKernel u := by
  rw [← (hasSum_kernelTerm u).tsum_eq]
  exact tsum_nonneg fun n => (Real.exp_pos _).le

lemma continuousOn_thetaTailKernel : ContinuousOn thetaTailKernel (Ioi 0) := by
  have hexp2 : ContinuousOn (fun u : ℝ => Real.exp (2 * u)) (Ioi 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
  have hmaps : MapsTo (fun u : ℝ => Real.exp (2 * u)) (Ioi 0) (Ioi 0) := by
    intro u hu
    exact mem_Ioi.mpr (Real.exp_pos _)
  have hcos : ContinuousOn
      (fun u : ℝ => HurwitzZeta.cosKernel 0 (Real.exp (2 * u)))
      (Ioi 0) :=
    (HurwitzZeta.continuousOn_cosKernel 0).comp hexp2 hmaps
  unfold thetaTailKernel
  exact (((Real.continuous_exp.comp
    (continuous_id.div_const 2)).continuousOn).mul
      (hcos.sub continuousOn_const)).div_const 2

lemma integrableOn_thetaTailKernel_mul_cos (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => (thetaTailKernel u : ℂ) *
        Complex.cos (z * (u : ℂ))) (Ioi 0) := by
  let q : ℂ := classicalZetaCoordinate z / 2
  have href := integrableOn_thetaLogIntegrand_two (1 / 2 - q)
  have hq := integrableOn_thetaLogIntegrand_two q
  have hsum := href.add hq
  have hquarter := hsum.const_mul (1 / 4 : ℂ)
  apply hquarter.congr
  filter_upwards with u
  change (1 / 4 : ℂ) *
      (thetaLogIntegrand (1 / 2 - q) (2 * u) +
        thetaLogIntegrand q (2 * u)) = _
  rw [show q = classicalZetaCoordinate z / 2 by rfl,
    thetaLogIntegrand_critical_pair]
  ring

lemma cos_imaginary_radius (R u : ℝ) :
    Complex.cos (((R : ℂ) * Complex.I) * (u : ℂ)) =
      (Real.cosh (R * u) : ℝ) := by
  rw [show ((R : ℂ) * Complex.I) * (u : ℂ) =
      ((R * u : ℝ) : ℂ) * Complex.I by
    push_cast
    ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh]

lemma integrableOn_thetaTailKernel_mul_cosh (R : ℝ) :
    IntegrableOn
      (fun u : ℝ => thetaTailKernel u * Real.cosh (R * u))
      (Ioi 0) := by
  have hc := integrableOn_thetaTailKernel_mul_cos ((R : ℂ) * Complex.I)
  have hc' : IntegrableOn
      (fun u : ℝ => (thetaTailKernel u : ℂ) *
        (Real.cosh (R * u) : ℝ)) (Ioi 0) := by
    apply hc.congr
    filter_upwards with u
    rw [cos_imaginary_radius]
  have hn := hc'.norm
  change Integrable
    (fun u : ℝ => thetaTailKernel u * Real.cosh (R * u))
      (volume.restrict (Ioi 0))
  simpa only [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (thetaTailKernel_nonneg _),
    abs_of_nonneg (Real.cosh_pos _).le] using hn

lemma integrableOn_thetaTailKernel_mul_exp {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn
      (fun u : ℝ => thetaTailKernel u * Real.exp (R * u))
      (Ioi 0) := by
  let major : ℝ → ℝ := fun u =>
    2 * (thetaTailKernel u * Real.cosh (R * u))
  have hmajor : IntegrableOn major (Ioi 0) :=
    (integrableOn_thetaTailKernel_mul_cosh R).const_mul 2
  refine hmajor.mono' ?_ ?_
  · exact ((continuousOn_thetaTailKernel.mul
      ((Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousOn)).aestronglyMeasurable
          measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have htheta := thetaTailKernel_nonneg u
    have hexp_le : Real.exp (R * u) ≤ 2 * Real.cosh (R * u) := by
      rw [Real.cosh_eq]
      nlinarith [Real.exp_pos (-(R * u))]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg htheta (Real.exp_pos _).le)]
    change thetaTailKernel u * Real.exp (R * u) ≤ major u
    dsimp only [major]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hexp_le htheta)

/-- The infinite first-integral kernel represented by the completed zeta Mellin transform. -/
def infiniteFirstIntegral (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ),
    (thetaTailKernel u : ℂ) * Complex.cos (z * (u : ℂ))

theorem thetaMellin_eq_infiniteFirstIntegral (z : ℂ) :
    mellin (HurwitzZeta.hurwitzEvenFEPair 0).f_modif
        (classicalZetaCoordinate z / 2) =
      8 * infiniteFirstIntegral z := by
  let q : ℂ := classicalZetaCoordinate z / 2
  have href := integrableOn_thetaLogIntegrand_two (1 / 2 - q)
  have hq := integrableOn_thetaLogIntegrand_two q
  rw [show classicalZetaCoordinate z / 2 = q by rfl,
    mellin_thetaPair_eq_two_log_integrals]
  rw [show
      2 * (∫ u in Ioi (0 : ℝ), thetaLogIntegrand (1 / 2 - q) (2 * u)) +
          2 * ∫ u in Ioi (0 : ℝ), thetaLogIntegrand q (2 * u) =
        2 * ((∫ u in Ioi (0 : ℝ), thetaLogIntegrand (1 / 2 - q) (2 * u)) +
          ∫ u in Ioi (0 : ℝ), thetaLogIntegrand q (2 * u)) by ring]
  rw [← integral_add href hq]
  have hpair :
      (∫ u in Ioi (0 : ℝ),
          thetaLogIntegrand (1 / 2 - q) (2 * u) +
            thetaLogIntegrand q (2 * u)) =
        ∫ u in Ioi (0 : ℝ),
          4 * (thetaTailKernel u : ℂ) *
            Complex.cos (z * (u : ℂ)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    rw [show q = classicalZetaCoordinate z / 2 by rfl]
    exact thetaLogIntegrand_critical_pair z u
  rw [hpair]
  have hfactor :
      (∫ u in Ioi (0 : ℝ),
          4 * (thetaTailKernel u : ℂ) * Complex.cos (z * (u : ℂ))) =
        4 * ∫ u in Ioi (0 : ℝ),
          (thetaTailKernel u : ℂ) * Complex.cos (z * (u : ℂ)) := by
    rw [show (fun u : ℝ =>
        4 * (thetaTailKernel u : ℂ) * Complex.cos (z * (u : ℂ))) =
      fun u : ℝ => 4 *
        ((thetaTailKernel u : ℂ) * Complex.cos (z * (u : ℂ))) by
      funext u
      ring]
    exact integral_const_mul 4 _
  rw [hfactor]
  simp only [infiniteFirstIntegral]
  ring

theorem classicalXi_eq_infiniteFirstIntegral (z : ℂ) :
    classicalXi z =
      1 / 2 - 2 * (z ^ 2 + 1 / 4) * infiniteFirstIntegral z := by
  rw [classicalXi_eq_thetaMellin,
    thetaMellin_eq_infiniteFirstIntegral]
  rw [show classicalZetaCoordinate z * (classicalZetaCoordinate z - 1) =
      -(z ^ 2 + 1 / 4) by
    unfold classicalZetaCoordinate
    ring_nf
    rw [Complex.I_sq]
    ring]
  ring

end IncompleteGammaApproximant
