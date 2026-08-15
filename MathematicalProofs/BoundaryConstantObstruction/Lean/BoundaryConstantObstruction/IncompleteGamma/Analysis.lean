import BoundaryConstantObstruction.IncompleteGamma.Kernel
import BoundaryConstantObstruction.EntireFunctionRigidity.NonrealZeroObstructionReflection
import Mathlib.Analysis.Calculus.ParametricIntegral

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate FourierTransform

noncomputable section

namespace IncompleteGammaApproximant

/-- A reusable integrability lemma for the super-exponential kernels occurring
in the finite cosine transform. -/
lemma integrableOn_exp_linear_sub_exp_two (A a : ℝ) (hA : 0 < A) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => Real.exp (A * u - a * Real.exp (2 * u))) (Ioi 0) := by
  let g : ℝ → ℝ := fun y => y ^ (A / 2 - 1) * Real.exp (-a * y)
  have hg0 : IntegrableOn g (Ioi 0) := by
    simpa [g] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := A / 2 - 1) (b := a) (by linarith) one_pos ha
  have hg1 : IntegrableOn g (Ioi (Real.exp 0)) := by
    exact hg0.mono_set (by simp only [Real.exp_zero]; exact Ioi_subset_Ioi (by norm_num))
  have hcomp :
      IntegrableOn (fun v : ℝ => Real.exp v * g (Real.exp v)) (Ioi 0) := by
    exact (integrableOn_comp_exp_Ioi g 0).2 hg1
  have hscaled :
      IntegrableOn (fun u : ℝ => Real.exp (2 * u) * g (Real.exp (2 * u))) (Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun v : ℝ => Real.exp v * g (Real.exp v)) 0 (by norm_num : (0 : ℝ) < 2)).2
      (by simpa using hcomp)
  convert hscaled using 1
  ext u
  simp only [g]
  rw [← Real.exp_mul]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- Every finite kernel summand has all exponential moments needed below. -/
lemma integrableOn_phiTerm_mul_exp (n : ℕ) (A : ℝ) (hA : -(5 / 2 : ℝ) < A) :
    IntegrableOn (fun u : ℝ => phiTerm n u * Real.exp (A * u)) (Ioi 0) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have h9 := integrableOn_exp_linear_sub_exp_two (A + 9 / 2) a (by linarith) ha
  have h5 := integrableOn_exp_linear_sub_exp_two (A + 5 / 2) a (by linarith) ha
  have h := (h9.const_mul (4 * a ^ 2)).sub (h5.const_mul (6 * a))
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  symm
  change
    Real.exp (u / 2 - a * Real.exp (2 * u)) *
        (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u)) *
        Real.exp (A * u) =
      4 * a ^ 2 * Real.exp ((A + 9 / 2) * u - a * Real.exp (2 * u)) -
        6 * a * Real.exp ((A + 5 / 2) * u - a * Real.exp (2 * u))
  have h9u :
      Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (4 * u) *
          Real.exp (A * u) =
        Real.exp ((A + 9 / 2) * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h5u :
      Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (2 * u) *
          Real.exp (A * u) =
        Real.exp ((A + 5 / 2) * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = 4 * a ^ 2 *
          (Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (4 * u) *
            Real.exp (A * u)) -
        6 * a *
          (Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (2 * u) *
            Real.exp (A * u)) := by ring
    _ = _ := by rw [h9u, h5u]

/-- The finite kernel itself has every exponential moment above the harmless
lower threshold used by the derivative and Fourier arguments. -/
lemma integrableOn_Phi_mul_exp (N : ℕ) (A : ℝ) (hA : -(5 / 2 : ℝ) < A) :
    IntegrableOn (fun u : ℝ => Phi N u * Real.exp (A * u)) (Ioi 0) := by
  rw [show (fun u : ℝ => Phi N u * Real.exp (A * u)) =
      ∑ n ∈ Finset.range N, fun u => phiTerm n u * Real.exp (A * u) by
    funext u
    simp [Phi, Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.range N) fun n _ => integrableOn_phiTerm_mul_exp n A hA

lemma integrableOn_Phi (N : ℕ) : IntegrableOn (Phi N) (Ioi 0) := by
  simpa using integrableOn_Phi_mul_exp N 0 (by norm_num)

/-- Zero extension used only to invoke the real-line Riemann--Lebesgue theorem. -/
def phiExtension (N : ℕ) (u : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun v : ℝ => (Phi N v : ℂ)) u

lemma integrable_phiExtension (N : ℕ) : Integrable (phiExtension N) := by
  have h : IntegrableOn (fun u : ℝ => (Phi N u : ℂ)) (Ioi 0) :=
    (integrableOn_Phi N).ofReal
  exact h.integrable_indicator measurableSet_Ioi

/-- Fourier normalization used by Mathlib. -/
def fourierKernel (N : ℕ) (w : ℝ) : ℂ :=
  ∫ u : ℝ, 𝐞 (-(u * w)) • phiExtension N u

lemma fourierKernel_tendsto_cocompact (N : ℕ) :
    Tendsto (fourierKernel N) (cocompact ℝ) (nhds 0) := by
  exact Real.tendsto_integral_exp_smul_cocompact (phiExtension N)

lemma H_real_eq_fourierKernel_add (N : ℕ) (x : ℝ) :
    H N (x : ℂ) =
      fourierKernel N (x / (2 * Real.pi)) +
        fourierKernel N (-(x / (2 * Real.pi))) := by
  have hpos := (Real.fourierIntegral_convergent_iff (x / (2 * Real.pi))).2
    (integrable_phiExtension N)
  have hneg := (Real.fourierIntegral_convergent_iff (-(x / (2 * Real.pi)))).2
    (integrable_phiExtension N)
  have hpos' : Integrable
      (fun u : ℝ => 𝐞 (-(u * (x / (2 * Real.pi)))) • phiExtension N u) := by
    simpa only [Real.inner_apply, mul_comm] using hpos
  have hneg' : Integrable
      (fun u : ℝ => 𝐞 (-(u * (-(x / (2 * Real.pi))))) • phiExtension N u) := by
    simpa only [Real.inner_apply, mul_comm] using hneg
  rw [H, fourierKernel, fourierKernel, ← integral_add hpos' hneg']
  rw [← integral_indicator measurableSet_Ioi]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioi (0 : ℝ)
  · simp only [phiExtension, Set.indicator_of_mem hu, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul]
    rw [show (2 : ℂ) * ((Phi N u : ℂ) * Complex.cos ((x : ℂ) * (u : ℂ))) =
        (Phi N u : ℂ) * (2 * Complex.cos ((x : ℂ) * (u : ℂ))) by ring]
    rw [Complex.two_cos]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hp_arg :
        ((2 * Real.pi * (-(u * (x / (2 * Real.pi))) : ℝ) : ℝ) : ℂ) * I =
          -((x : ℂ) * (u : ℂ)) * I := by
      push_cast
      field_simp
    have hn_arg :
        ((2 * Real.pi * (-(u * (-(x / (2 * Real.pi)))) : ℝ) : ℝ) : ℂ) * I =
          ((x : ℂ) * (u : ℂ)) * I := by
      push_cast
      field_simp
    rw [hp_arg, hn_arg]
    ring
  · simp [phiExtension, hu]

lemma H_tendsto_atTop (N : ℕ) :
    Tendsto (fun x : ℝ => H N (x : ℂ)) atTop (nhds 0) := by
  have hRL := fourierKernel_tendsto_cocompact N
  have htop : Tendsto (fourierKernel N) atTop (nhds 0) :=
    hRL.mono_left atTop_le_cocompact
  have hbot : Tendsto (fourierKernel N) atBot (nhds 0) :=
    hRL.mono_left atBot_le_cocompact
  have hpi : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hp : Tendsto (fun x : ℝ => fourierKernel N (x / (2 * Real.pi))) atTop (nhds 0) :=
    htop.comp (tendsto_id.atTop_div_const hpi)
  have hn : Tendsto (fun x : ℝ => fourierKernel N (-(x / (2 * Real.pi)))) atTop (nhds 0) := by
    apply hbot.comp
    simpa only [neg_div] using
      (tendsto_div_const_atBot_of_pos hpi).2 tendsto_neg_atTop_atBot
  convert hp.add hn using 1
  · funext x
    exact H_real_eq_fourierKernel_add N x
  · simp

lemma H_tendsto_atBot (N : ℕ) :
    Tendsto (fun x : ℝ => H N (x : ℂ)) atBot (nhds 0) := by
  have hRL := fourierKernel_tendsto_cocompact N
  have htop : Tendsto (fourierKernel N) atTop (nhds 0) :=
    hRL.mono_left atTop_le_cocompact
  have hbot : Tendsto (fourierKernel N) atBot (nhds 0) :=
    hRL.mono_left atBot_le_cocompact
  have hpi : 0 < 2 * Real.pi := mul_pos two_pos Real.pi_pos
  have hp : Tendsto (fun x : ℝ => fourierKernel N (x / (2 * Real.pi))) atBot (nhds 0) :=
    hbot.comp ((tendsto_div_const_atBot_of_pos hpi).2 tendsto_id)
  have hn : Tendsto (fun x : ℝ => fourierKernel N (-(x / (2 * Real.pi)))) atBot (nhds 0) := by
    apply htop.comp
    simpa only [neg_div] using
      tendsto_neg_atBot_atTop.atTop_div_const hpi
  convert hp.add hn using 1
  · funext x
    exact H_real_eq_fourierKernel_add N x
  · simp

lemma F_tendsto_atTop (N : ℕ) (t : ℝ) :
    Tendsto (fun x : ℝ => F N t (x : ℂ)) atTop
      (nhds (t * boundaryConstant N : ℂ)) := by
  simpa [F] using (H_tendsto_atTop N).add_const (t * boundaryConstant N : ℂ)

lemma F_tendsto_atBot (N : ℕ) (t : ℝ) :
    Tendsto (fun x : ℝ => F N t (x : ℂ)) atBot
      (nhds (t * boundaryConstant N : ℂ)) := by
  simpa [F] using (H_tendsto_atBot N).add_const (t * boundaryConstant N : ℂ)

lemma H_even (N : ℕ) (z : ℂ) : H N (-z) = H N z := by
  simp only [H, neg_mul, Complex.cos_neg]

lemma F_even (N : ℕ) (t : ℝ) (z : ℂ) : F N t (-z) = F N t z := by
  rw [F, F, H_even]

/-- The finite cosine-transform term is of real type. -/
lemma H_conj (N : ℕ) (z : ℂ) :
    H N (conj z) = conj (H N z) := by
  unfold H
  simp only [map_mul, map_ofNat]
  congr 1
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change (Phi N u : ℂ) * Complex.cos (conj z * (u : ℂ)) =
    conj ((Phi N u : ℂ) * Complex.cos (z * (u : ℂ)))
  rw [map_mul, conj_ofReal, ← Complex.cos_conj]
  congr 2
  rw [map_mul, conj_ofReal]

/-- Every member of the shifted finite family is of real type. -/
lemma F_conj (N : ℕ) (t : ℝ) (z : ℂ) :
    F N t (conj z) = conj (F N t z) := by
  simp only [F, H_conj, map_add, conj_ofReal]

/-- The exact conjugation-and-sign zero orbit asserted in the manuscript.
The statement deliberately makes no claim that all four orbit points are
distinct. -/
theorem F_zero_symmetry_orbit {N : ℕ} {t : ℝ} {z : ℂ}
    (hz : F N t z = 0) :
    F N t (-z) = 0 ∧ F N t (conj z) = 0 ∧
      F N t (-conj z) = 0 := by
  constructor
  · simpa only [F_even] using hz
  constructor
  · rw [F_conj, hz, map_zero]
  · rw [F_even, F_conj, hz, map_zero]

lemma norm_cos_le_exp_norm (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
  have h := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  rw [← Complex.two_cos] at h
  have hp : ‖Complex.exp (z * I)‖ ≤ Real.exp ‖z‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, norm_I, mul_one]
  have hn : ‖Complex.exp (-z * I)‖ ≤ Real.exp ‖z‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, norm_neg, norm_I, mul_one]
  rw [norm_mul, Complex.norm_ofNat] at h
  nlinarith [norm_nonneg (Complex.cos z), hp, hn]

lemma norm_sin_le_exp_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp ‖z‖ := by
  have h := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  have heq : ‖(2 : ℂ) * Complex.sin z‖ =
      ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ := by
    rw [Complex.two_sin, norm_mul, norm_I, mul_one]
  have hp : ‖Complex.exp (z * I)‖ ≤ Real.exp ‖z‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, norm_I, mul_one]
  have hn : ‖Complex.exp (-z * I)‖ ≤ Real.exp ‖z‖ := by
    refine (Complex.norm_exp_le_exp_norm _).trans ?_
    rw [norm_mul, norm_neg, norm_I, mul_one]
  rw [← heq, norm_mul, Complex.norm_ofNat] at h
  nlinarith [norm_nonneg (Complex.sin z), hp, hn]

lemma phiTerm_continuous (n : ℕ) : Continuous (phiTerm n) := by
  unfold phiTerm
  fun_prop

lemma Phi_continuous (N : ℕ) : Continuous (Phi N) := by
  unfold Phi
  exact continuous_finset_sum _ fun n _ => phiTerm_continuous n

lemma integrableOn_Phi_mul_cos (N : ℕ) (z : ℂ) :
    IntegrableOn (fun u : ℝ => (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))) (Ioi 0) := by
  have hmajor : Integrable
      (fun u : ℝ => |Phi N u| * Real.exp (‖z‖ * u)) (volume.restrict (Ioi 0)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrableOn_Phi_mul_exp N ‖z‖ (by linarith [norm_nonneg z])).norm
  refine hmajor.mono'
    ((Complex.continuous_ofReal.comp (Phi_continuous N)).mul (by fun_prop) |>.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [norm_mul, norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_cos_le_exp_norm _).trans ?_
  apply Real.exp_le_exp.mpr
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]

lemma H_differentiable (N : ℕ) : Differentiable ℂ (H N) := by
  intro z
  let G : ℂ → ℝ → ℂ := fun w u => (Phi N u : ℂ) * Complex.cos (w * (u : ℂ))
  let G' : ℂ → ℝ → ℂ := fun w u =>
    (Phi N u : ℂ) * (-Complex.sin (w * (u : ℂ)) * (u : ℂ))
  let bound : ℝ → ℝ := fun u => |Phi N u| * Real.exp ((‖z‖ + 2) * u)
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa [bound, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrableOn_Phi_mul_exp N (‖z‖ + 2) (by linarith [norm_nonneg z])).norm
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (s := Metric.ball z 1) (F := G) (F' := G') (bound := bound)
    (Metric.ball_mem_nhds z zero_lt_one)
    (by
      filter_upwards with w
      exact ((Complex.continuous_ofReal.comp (Phi_continuous N)).mul
        (by fun_prop)).aestronglyMeasurable)
    (by
      change Integrable
        (fun u : ℝ => (Phi N u : ℂ) * Complex.cos (z * (u : ℂ)))
        (volume.restrict (Ioi 0))
      exact integrableOn_Phi_mul_cos N z)
    (by
      exact ((Complex.continuous_ofReal.comp (Phi_continuous N)).mul
        (by fun_prop)).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
      have hu0 : 0 < u := hu
      simp only [G', norm_mul, norm_real, Real.norm_eq_abs, neg_mul, norm_neg,
        abs_of_pos hu0]
      have hw' : ‖w‖ ≤ ‖z‖ + 1 := by
        have hd : ‖w - z‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
        calc
          ‖w‖ = ‖(w - z) + z‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ ≤ ‖z‖ + 1 := by linarith
      have hsin : ‖Complex.sin (w * (u : ℂ))‖ ≤
          Real.exp ((‖z‖ + 1) * u) := by
        refine (norm_sin_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]
        exact mul_le_mul_of_nonneg_right hw' hu.le
      have huexp : u ≤ Real.exp u := (Real.add_one_le_exp u).trans' (by linarith)
      rw [show bound u = |Phi N u| *
          (Real.exp ((‖z‖ + 1) * u) * Real.exp u) by
        simp only [bound, ← Real.exp_add]
        congr 2
        ring]
      gcongr)
    (by simpa [bound] using hbound)
    (by
      filter_upwards with u w hw
      dsimp only [G, G']
      simpa only [Function.comp_apply, id_eq, one_mul, mul_assoc] using
        ((Complex.hasDerivAt_cos (w * (u : ℂ))).comp w
          ((hasDerivAt_id w).mul_const (u : ℂ))).const_mul (Phi N u : ℂ))
  change DifferentiableAt ℂ
    (fun w => 2 * ∫ u in Ioi (0 : ℝ),
      (Phi N u : ℂ) * Complex.cos (w * (u : ℂ))) z
  exact (hmain.2.const_mul 2).differentiableAt

lemma F_differentiable (N : ℕ) (t : ℝ) : Differentiable ℂ (F N t) := by
  unfold F
  exact (H_differentiable N).add
    (differentiable_const (c := ((t * boundaryConstant N : ℝ) : ℂ)))

end IncompleteGammaApproximant
