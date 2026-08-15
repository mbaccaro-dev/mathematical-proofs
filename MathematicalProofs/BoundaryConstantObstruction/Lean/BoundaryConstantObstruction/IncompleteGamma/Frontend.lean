import BoundaryConstantObstruction.IncompleteGamma.ThetaIdentity
import BoundaryConstantObstruction.IncompleteGamma.Nonconstant
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
The exact upper-incomplete-gamma frontend printed in the manuscript, together
with its change of variables to the finite cosine-transform kernel.
-/

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- The upper incomplete gamma integral on a positive real lower endpoint.
For `t > 0`, the integrand is `t ^ (a - 1) * exp (-t)`, written through the
real logarithm to make its branch unambiguous. -/
def upperIncompleteGamma (a : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Ioi x,
    Complex.exp ((a - 1) * (Real.log t : ℂ) - (t : ℂ))

/-- `A⁻ᵃ Γ(a,A)`, with the positive-real power written on its real-log branch. -/
def scaledUpperIncompleteGamma (a : ℂ) (A : ℝ) : ℂ :=
  Complex.exp (-a * (Real.log A : ℂ)) * upperIncompleteGamma a A

def arithmeticScale (n : ℕ) : ℝ := Real.pi * (n + 1 : ℝ) ^ 2

def gammaKernel (a : ℂ) (A : ℝ) (u : ℝ) : ℂ :=
  Complex.exp (2 * a * (u : ℂ) - (A * Real.exp (2 * u) : ℝ))

def kernelDerivTerm (n : ℕ) (u : ℝ) : ℝ :=
  (1 / 2 - 2 * arithmeticScale n * Real.exp (2 * u)) * kernelTerm n u

def ibpPrimitive (n : ℕ) (z : ℂ) (u : ℝ) : ℂ :=
  (kernelDerivTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) +
    z * (kernelTerm n u : ℂ) * Complex.sin (z * (u : ℂ))

lemma arithmeticScale_pos (n : ℕ) : 0 < arithmeticScale n := by
  unfold arithmeticScale
  positivity

lemma integrableOn_gammaKernel (a : ℂ) {A : ℝ} (hA : 0 < A) :
    IntegrableOn (gammaKernel a A) (Ioi 0) := by
  let B : ℝ := |(2 * a).re| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hmajor := integrableOn_exp_linear_sub_exp_two B A hB hA
  refine hmajor.mono' ?_ ?_
  · exact (by unfold gammaKernel; fun_prop : Continuous (gammaKernel a A)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [gammaKernel, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (2 * a * (u : ℂ) - (A * Real.exp (2 * u) : ℝ)).re =
        (2 * a).re * u - A * Real.exp (2 * u) := by
      norm_num [mul_re]
      ring_nf
      left
      rw [show (u : ℂ) * 2 = ((u * 2 : ℝ) : ℂ) by norm_cast]
      exact Complex.exp_ofReal_re _
    rw [hre]
    have hcoef : (2 * a).re ≤ B := by
      dsimp [B]
      linarith [le_abs_self (2 * a).re]
    simp only [Set.mem_Ioi] at hu
    nlinarith

lemma kernelTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (kernelTerm n) (kernelDerivTerm n u) u := by
  let A : ℝ := arithmeticScale n
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v))
      (2 * Real.exp (2 * u)) u := by
    simpa only [id_eq, one_mul, mul_one, mul_comm] using
      (((hasDerivAt_id u).mul_const (2 : ℝ)).exp)
  have hin : HasDerivAt
      (fun v : ℝ => v / 2 - A * Real.exp (2 * v))
      (1 / 2 - 2 * A * Real.exp (2 * u)) u := by
    have h := ((hasDerivAt_id u).div_const 2).sub (h2.const_mul A)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun v : ℝ => v / 2 - A * Real.exp (2 * v))
      (Filter.Eventually.of_forall fun v => by simp only [Pi.sub_apply, id_eq])
    exact h'.congr_deriv (by ring)
  have h := hin.exp
  have h' := h.congr_of_eventuallyEq (f₁ := kernelTerm n)
    (Filter.Eventually.of_forall fun v => by
      simp only [kernelTerm, arithmeticScale, A])
  exact h'.congr_deriv (by
    unfold kernelDerivTerm kernelTerm
    dsimp [A, arithmeticScale]
    ring)

lemma kernelDerivTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (kernelDerivTerm n)
      (phiTerm n u + (1 / 4) * kernelTerm n u) u := by
  let A : ℝ := arithmeticScale n
  have hAexp : HasDerivAt (fun v : ℝ => A * Real.exp (2 * v))
      (2 * A * Real.exp (2 * u)) u := by
    have h2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v))
        (2 * Real.exp (2 * u)) u := by
      simpa only [id_eq, one_mul, mul_one, mul_comm] using
        (((hasDerivAt_id u).mul_const (2 : ℝ)).exp)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h2.const_mul A
  have hcoeff : HasDerivAt
      (fun v : ℝ => 1 / 2 - 2 * A * Real.exp (2 * v))
      (-4 * A * Real.exp (2 * u)) u := by
    have h := (hasDerivAt_const (x := u) (c := (1 / 2 : ℝ))).sub
      (hAexp.const_mul 2)
    have h' := h.congr_of_eventuallyEq
      (f₁ := fun v : ℝ => 1 / 2 - 2 * A * Real.exp (2 * v))
      (Filter.Eventually.of_forall fun v => by
        simp only [Pi.sub_apply]
        ring)
    exact h'.congr_deriv (by ring)
  have hk : HasDerivAt (kernelTerm n) (kernelDerivTerm n u) u :=
    kernelTerm_hasDerivAt n u
  have hprod := hcoeff.mul hk
  have hexp4 : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
    rw [show 4 * u = 2 * u + 2 * u by ring, Real.exp_add, pow_two]
  have hprod' : HasDerivAt (kernelDerivTerm n)
      (-4 * A * Real.exp (2 * u) * kernelTerm n u +
        (1 / 2 - 2 * A * Real.exp (2 * u)) * kernelDerivTerm n u) u := by
    exact hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => by
      simp only [kernelDerivTerm, A, Pi.mul_apply])
  apply hprod'.congr_deriv
  unfold phiTerm kernelDerivTerm kernelTerm
  dsimp [A, arithmeticScale]
  rw [hexp4]
  ring

lemma cos_mul_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.cos (z * (v : ℂ)))
      (-z * Complex.sin (z * (u : ℂ))) u := by
  have hinner : HasDerivAt (fun y : ℂ => z * y) z (u : ℂ) :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id (u : ℂ)).const_mul z
  have h := (Complex.hasDerivAt_cos (z * (u : ℂ))).comp (u : ℂ) hinner
  have hr := h.comp_ofReal
  have hr' : HasDerivAt (fun v : ℝ => Complex.cos (z * (v : ℂ)))
      (-Complex.sin (z * (u : ℂ)) * z) u := by
    simpa only [Function.comp_apply, id_eq] using hr
  exact hr'.congr_deriv (by ring)

lemma sin_mul_hasDerivAt (z : ℂ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.sin (z * (v : ℂ)))
      (z * Complex.cos (z * (u : ℂ))) u := by
  have hinner : HasDerivAt (fun y : ℂ => z * y) z (u : ℂ) :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id (u : ℂ)).const_mul z
  have h := (Complex.hasDerivAt_sin (z * (u : ℂ))).comp (u : ℂ) hinner
  have hr := h.comp_ofReal
  have hr' : HasDerivAt (fun v : ℝ => Complex.sin (z * (v : ℂ)))
      (Complex.cos (z * (u : ℂ)) * z) u := by
    simpa only [Function.comp_apply, id_eq] using hr
  exact hr'.congr_deriv (by ring)

lemma ibpPrimitive_hasDerivAt (n : ℕ) (z : ℂ) (u : ℝ) :
    HasDerivAt (ibpPrimitive n z)
      ((((phiTerm n u : ℝ) : ℂ) + (z ^ 2 + 1 / 4) * (kernelTerm n u : ℂ)) *
        Complex.cos (z * (u : ℂ))) u := by
  have hk := (kernelTerm_hasDerivAt n u).ofReal_comp
  have hkd := (kernelDerivTerm_hasDerivAt n u).ofReal_comp
  have hc := cos_mul_hasDerivAt z u
  have hs := sin_mul_hasDerivAt z u
  have h := (hkd.mul hc).add ((hk.const_mul z).mul hs)
  unfold ibpPrimitive
  apply h.congr_deriv
  push_cast
  ring

/-- Superexponential decay with an arbitrary linear coefficient.  The earlier
special-purpose boundary lemma only needed small coefficients; the complex
integration-by-parts boundary requires this uniform form. -/
lemma tendsto_exp_linear_sub_exp_two_atTop_general (k a : ℝ) (ha : 0 < a) :
    Tendsto (fun u : ℝ => Real.exp (k * u - a * Real.exp (2 * u)))
      atTop (nhds 0) := by
  let c : ℝ := |k| / (2 * a)
  let a' : ℝ := a * Real.exp (2 * c)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have ha' : 0 < a' := by
    dsimp [a']
    positivity
  have hexp : 1 + 2 * c ≤ Real.exp (2 * c) := by
    simpa [add_comm] using Real.add_one_le_exp (2 * c)
  have hc_eq : 2 * a * c = |k| := by
    dsimp [c]
    field_simp
  have hkabs : k ≤ |k| := le_abs_self k
  have hk' : k < 2 * a' := by
    dsimp [a']
    have hmul := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * a)
    nlinarith
  have hbase := tendsto_exp_linear_sub_exp_two_atTop k a' ha' hk'
  have hshift : Tendsto (fun u : ℝ => u - c) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-c) tendsto_id)
  have hcomp := hbase.comp hshift
  have hscaled := hcomp.const_mul (Real.exp (k * c))
  have hscaled0 : Tendsto
      (fun u : ℝ => Real.exp (k * c) *
        Real.exp (k * (u - c) - a' * Real.exp (2 * (u - c))))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hscaled
  apply hscaled0.congr'
  filter_upwards [] with u
  have hinner : a' * Real.exp (2 * (u - c)) = a * Real.exp (2 * u) := by
    dsimp [a']
    calc
      a * Real.exp (2 * c) * Real.exp (2 * (u - c)) =
          a * (Real.exp (2 * c) * Real.exp (2 * (u - c))) := by ring
      _ = a * Real.exp (2 * c + 2 * (u - c)) := by rw [Real.exp_add]
      _ = a * Real.exp (2 * u) := by congr 2 <;> ring
  rw [hinner, ← Real.exp_add]
  congr 1
  ring

lemma tendsto_exp_mul_kernelTerm_mul_of_norm_le
    (n : ℕ) (z : ℂ) (m : ℝ) (g : ℂ → ℂ)
    (hg : ∀ w : ℂ, ‖g w‖ ≤ Real.exp ‖w‖) :
    Tendsto
      (fun u : ℝ =>
        (Real.exp (m * u) : ℂ) * (kernelTerm n u : ℂ) * g (z * (u : ℂ)))
      atTop (nhds 0) := by
  let A : ℝ := arithmeticScale n
  have hmajor := tendsto_exp_linear_sub_exp_two_atTop_general
    (m + 1 / 2 + ‖z‖) A (arithmeticScale_pos n)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun u => norm_nonneg _)
    ?_ hmajor
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
  rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, kernelTerm, abs_of_pos (Real.exp_pos _),
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (m * u) * kernelTerm n u * ‖g (z * (u : ℂ))‖ ≤
        Real.exp (m * u) * kernelTerm n u * Real.exp ‖z * (u : ℂ)‖ := by
      exact mul_le_mul_of_nonneg_left (hg _) (by
        unfold kernelTerm
        positivity)
    _ = Real.exp ((m + 1 / 2 + ‖z‖) * u - A * Real.exp (2 * u)) := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
      unfold kernelTerm
      calc
        Real.exp (m * u) *
              Real.exp (u / 2 - Real.pi * (n + 1 : ℝ) ^ 2 * Real.exp (2 * u)) *
            Real.exp (‖z‖ * u) =
            Real.exp (m * u +
              (u / 2 - Real.pi * (n + 1 : ℝ) ^ 2 * Real.exp (2 * u)) +
              ‖z‖ * u) := by rw [Real.exp_add, Real.exp_add]
        _ = Real.exp ((m + 1 / 2 + ‖z‖) * u - A * Real.exp (2 * u)) := by
          congr 1
          dsimp [A, arithmeticScale]
          ring

lemma ibpPrimitive_tendsto_atTop (n : ℕ) (z : ℂ) :
    Tendsto (ibpPrimitive n z) atTop (nhds 0) := by
  have hc0 := tendsto_exp_mul_kernelTerm_mul_of_norm_le n z 0 Complex.cos
    norm_cos_le_exp_norm
  have hc2 := tendsto_exp_mul_kernelTerm_mul_of_norm_le n z 2 Complex.cos
    norm_cos_le_exp_norm
  have hs0 := tendsto_exp_mul_kernelTerm_mul_of_norm_le n z 0 Complex.sin
    norm_sin_le_exp_norm
  have hsum :=
    ((hc0.const_mul (1 / 2 : ℂ)).sub
      (hc2.const_mul (2 * arithmeticScale n : ℂ))).add (hs0.const_mul z)
  have hsum0 : Tendsto
      (fun u : ℝ =>
        (1 / 2 : ℂ) * ((Real.exp (0 * u) : ℂ) * (kernelTerm n u : ℂ) *
          Complex.cos (z * (u : ℂ))) -
        (2 * arithmeticScale n : ℂ) * ((Real.exp (2 * u) : ℂ) *
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) +
        z * ((Real.exp (0 * u) : ℂ) * (kernelTerm n u : ℂ) *
          Complex.sin (z * (u : ℂ)))) atTop (nhds 0) := by
    simpa only [mul_zero, sub_zero, add_zero] using hsum
  apply hsum0.congr'
  filter_upwards [] with u
  unfold ibpPrimitive kernelDerivTerm
  norm_num
  push_cast
  ring

@[simp] lemma ibpPrimitive_zero (n : ℕ) (z : ℂ) :
    ibpPrimitive n z 0 = -((boundaryTerm (n + 1) / 2 : ℝ) : ℂ) := by
  simp [ibpPrimitive, kernelDerivTerm, kernelTerm, boundaryTerm, arithmeticScale]
  push_cast
  ring

lemma integrableOn_phiTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hmajor : Integrable
      (fun u : ℝ => |phiTerm n u| * Real.exp (‖z‖ * u))
      (volume.restrict (Ioi 0)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
      (integrableOn_phiTerm_mul_exp n ‖z‖
        (by linarith [norm_nonneg z])).norm
  refine hmajor.mono'
    ((Complex.continuous_ofReal.comp (phiTerm_continuous n)).mul
      (by fun_prop) |>.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  simp only [norm_mul, norm_real, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_cos_le_exp_norm _).trans ?_
  apply Real.exp_le_exp.mpr
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]

lemma integral_comp_add_right_Ioi (g : ℝ → ℂ) (a : ℝ) :
    (∫ x in Ioi 0, g (x + a)) = ∫ y in Ioi a, g y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← integral_add_right_eq_self ((Ioi a).indicator g) a]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ioi 0
  · have hxa : x + a ∈ Ioi a := by simpa using add_lt_add_right hx a
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hxa]
  · have hxa : x + a ∉ Ioi a := by
      simpa [not_lt] using add_le_add_right (le_of_not_gt hx) a
    simp [hx, hxa]

lemma integral_comp_affine_Ioi (g : ℝ → ℂ) (a : ℝ) :
    2 * (∫ u in Ioi 0, g (2 * u + a)) = ∫ y in Ioi a, g y := by
  rw [integral_comp_mul_left_Ioi (fun x => g (x + a)) 0 (by norm_num : (0 : ℝ) < 2)]
  norm_num
  ring_nf
  exact integral_comp_add_right_Ioi g a

lemma upperIncompleteGamma_log_coordinate (a : ℂ) {A : ℝ} (hA : 0 < A) :
    upperIncompleteGamma a A =
      ∫ y in Ioi (Real.log A),
        Complex.exp (a * (y : ℂ) - (Real.exp y : ℂ)) := by
  rw [upperIncompleteGamma]
  rw [← integral_comp_log_Ioi
    (fun y : ℝ => Complex.exp (a * (y : ℂ) - (Real.exp y : ℂ))) hA]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxpos : 0 < x := lt_trans hA hx
  dsimp only
  change Complex.exp ((a - 1) * (Real.log x : ℂ) - (x : ℂ)) =
    x⁻¹ • Complex.exp
      (a * (Real.log x : ℂ) - (Real.exp (Real.log x) : ℂ))
  rw [show Real.exp (Real.log x) = x by exact Real.exp_log hxpos]
  rw [Complex.real_smul]
  rw [show ((x⁻¹ : ℝ) : ℂ) = Complex.exp (-(Real.log x : ℂ)) by
    rw [show -(Real.log x : ℂ) = ((-Real.log x : ℝ) : ℂ) by norm_cast]
    rw [← ofReal_exp]
    norm_cast
    rw [Real.exp_neg, Real.exp_log hxpos]]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem scaled_upperIncompleteGamma_eq_integral (a : ℂ) {A : ℝ} (hA : 0 < A) :
    Complex.exp (-a * (Real.log A : ℂ)) * upperIncompleteGamma a A =
      2 * ∫ u in Ioi (0 : ℝ),
        Complex.exp (2 * a * (u : ℂ) -
          (A * Real.exp (2 * u : ℝ) : ℝ)) := by
  rw [upperIncompleteGamma_log_coordinate a hA]
  have haff := integral_comp_affine_Ioi
    (fun y : ℝ => Complex.exp (a * (y : ℂ) - (Real.exp y : ℂ))) (Real.log A)
  rw [← haff]
  rw [show Complex.exp (-a * (Real.log A : ℂ)) *
      (2 * ∫ u in Ioi (0 : ℝ),
        Complex.exp (a * ((2 * u + Real.log A : ℝ) : ℂ) -
          (Real.exp (2 * u + Real.log A) : ℂ))) =
      2 * (Complex.exp (-a * (Real.log A : ℂ)) *
        ∫ u in Ioi (0 : ℝ),
          Complex.exp (a * ((2 * u + Real.log A : ℝ) : ℂ) -
            (Real.exp (2 * u + Real.log A) : ℂ))) by ring]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [show Real.exp (2 * u + Real.log A) = A * Real.exp (2 * u) by
    rw [Real.exp_add, Real.exp_log hA]
    ring]
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem scaledUpperIncompleteGamma_eq_gammaKernel (a : ℂ) {A : ℝ} (hA : 0 < A) :
    scaledUpperIncompleteGamma a A =
      2 * ∫ u in Ioi (0 : ℝ), gammaKernel a A u := by
  simpa [scaledUpperIncompleteGamma, gammaKernel] using
    scaled_upperIncompleteGamma_eq_integral a hA

/-- The manuscript's finite symmetrized incomplete-gamma approximant. -/
def xiPartial (N : ℕ) (s : ℂ) : ℂ :=
  1 / 2 + s * (s - 1) / 2 *
    ∑ n ∈ Finset.range N,
      (scaledUpperIncompleteGamma (s / 2) (arithmeticScale n) +
        scaledUpperIncompleteGamma ((1 - s) / 2) (arithmeticScale n))

/-- The critical-line normalization of the printed incomplete-gamma sum. -/
def XiIncompleteGamma (N : ℕ) (z : ℂ) : ℂ :=
  xiPartial N (1 / 2 + Complex.I * z)

/-- The finite cosine integral before the two integrations by parts. -/
def firstIntegral (N : ℕ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ),
    (S N u : ℂ) * Complex.cos (z * (u : ℂ))

lemma gammaKernel_critical_pair (n : ℕ) (z : ℂ) (u : ℝ) :
    gammaKernel ((1 / 2 + Complex.I * z) / 2) (arithmeticScale n) u +
        gammaKernel ((1 - (1 / 2 + Complex.I * z)) / 2) (arithmeticScale n) u =
      2 * ((kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) := by
  have hplus :
      gammaKernel ((1 / 2 + Complex.I * z) / 2) (arithmeticScale n) u =
        (kernelTerm n u : ℂ) *
          Complex.exp ((z * (u : ℂ)) * Complex.I) := by
    unfold gammaKernel kernelTerm arithmeticScale
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hminus :
      gammaKernel ((1 - (1 / 2 + Complex.I * z)) / 2) (arithmeticScale n) u =
        (kernelTerm n u : ℂ) *
          Complex.exp (-(z * (u : ℂ)) * Complex.I) := by
    unfold gammaKernel kernelTerm arithmeticScale
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hplus, hminus]
  rw [← mul_add, ← Complex.two_cos]
  ring

lemma integrableOn_kernelTerm_mul_cos (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ => (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  let s : ℂ := 1 / 2 + Complex.I * z
  have hplus := integrableOn_gammaKernel (s / 2) (arithmeticScale_pos n)
  have hminus := integrableOn_gammaKernel ((1 - s) / 2) (arithmeticScale_pos n)
  have htwo : IntegrableOn
      (fun u : ℝ => 2 * ((kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))))
      (Ioi 0) := by
    apply hplus.add hminus |>.congr
    filter_upwards [] with u
    change gammaKernel (s / 2) (arithmeticScale n) u +
      gammaKernel ((1 - s) / 2) (arithmeticScale n) u = _
    simpa only [s] using gammaKernel_critical_pair n z u
  have hhalf := htwo.const_mul (1 / 2 : ℂ)
  apply hhalf.congr
  filter_upwards [] with u
  ring

theorem scaledUpperIncompleteGamma_critical_pair (n : ℕ) (z : ℂ) :
    scaledUpperIncompleteGamma ((1 / 2 + Complex.I * z) / 2) (arithmeticScale n) +
        scaledUpperIncompleteGamma
          ((1 - (1 / 2 + Complex.I * z)) / 2) (arithmeticScale n) =
      4 * ∫ u in Ioi (0 : ℝ),
        (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  rw [scaledUpperIncompleteGamma_eq_gammaKernel _ (arithmeticScale_pos n),
    scaledUpperIncompleteGamma_eq_gammaKernel _ (arithmeticScale_pos n)]
  let gplus : ℝ → ℂ := fun u =>
    gammaKernel ((1 / 2 + Complex.I * z) / 2) (arithmeticScale n) u
  let gminus : ℝ → ℂ := fun u =>
    gammaKernel ((1 - (1 / 2 + Complex.I * z)) / 2) (arithmeticScale n) u
  have hplus : IntegrableOn gplus (Ioi 0) :=
    integrableOn_gammaKernel _ (arithmeticScale_pos n)
  have hminus : IntegrableOn gminus (Ioi 0) :=
    integrableOn_gammaKernel _ (arithmeticScale_pos n)
  rw [show 2 * (∫ u in Ioi (0 : ℝ), gplus u) +
      2 * (∫ u in Ioi (0 : ℝ), gminus u) =
      2 * ((∫ u in Ioi (0 : ℝ), gplus u) +
        ∫ u in Ioi (0 : ℝ), gminus u) by ring]
  rw [← integral_add hplus hminus]
  have hpair :
      (∫ u in Ioi (0 : ℝ), gplus u + gminus u) =
        ∫ u in Ioi (0 : ℝ),
          2 * ((kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    simpa only [gplus, gminus] using gammaKernel_critical_pair n z u
  rw [hpair, integral_const_mul]
  ring

lemma firstIntegral_eq_sum (N : ℕ) (z : ℂ) :
    firstIntegral N z =
      ∑ n ∈ Finset.range N,
        ∫ u in Ioi (0 : ℝ),
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  rw [firstIntegral]
  have hintegrand :
      (fun u : ℝ => (S N u : ℂ) * Complex.cos (z * (u : ℂ))) =
        fun u : ℝ => ∑ n ∈ Finset.range N,
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
    funext u
    simp [S, Finset.sum_mul]
  rw [hintegrand]
  exact integral_finsetSum (Finset.range N)
    (fun n _ => integrableOn_kernelTerm_mul_cos n z)

theorem sum_scaledUpperIncompleteGamma_critical_pair (N : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.range N,
      (scaledUpperIncompleteGamma ((1 / 2 + Complex.I * z) / 2) (arithmeticScale n) +
        scaledUpperIncompleteGamma
          ((1 - (1 / 2 + Complex.I * z)) / 2) (arithmeticScale n))) =
      4 * firstIntegral N z := by
  calc
    _ = ∑ n ∈ Finset.range N,
        4 * (∫ u in Ioi (0 : ℝ),
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact scaledUpperIncompleteGamma_critical_pair n z
    _ = 4 * ∑ n ∈ Finset.range N,
        ∫ u in Ioi (0 : ℝ),
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
            rw [Finset.mul_sum]
    _ = 4 * firstIntegral N z := by rw [firstIntegral_eq_sum]

/-- The exact incomplete-gamma-to-cosine identity printed before the
integration-by-parts refactor. -/
theorem XiIncompleteGamma_eq_firstIntegral (N : ℕ) (z : ℂ) :
    XiIncompleteGamma N z =
      1 / 2 - 2 * (z ^ 2 + 1 / 4) * firstIntegral N z := by
  unfold XiIncompleteGamma xiPartial
  rw [sum_scaledUpperIncompleteGamma_critical_pair]
  rw [show (1 / 2 + Complex.I * z) * (1 / 2 + Complex.I * z - 1) =
      -(z ^ 2 + 1 / 4) by
    ring_nf
    rw [Complex.I_sq]
    ring]
  ring

lemma integrableOn_ibpDerivative (n : ℕ) (z : ℂ) :
    IntegrableOn
      (fun u : ℝ =>
        (((phiTerm n u : ℝ) : ℂ) +
          (z ^ 2 + 1 / 4) * (kernelTerm n u : ℂ)) *
            Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hp := integrableOn_phiTerm_mul_cos n z
  have hk := (integrableOn_kernelTerm_mul_cos n z).const_mul (z ^ 2 + 1 / 4)
  apply (hp.add hk).congr
  filter_upwards [] with u
  simp only [Pi.add_apply]
  ring

/-- One summand of the manuscript's two integrations by parts, with the
boundary contribution retained exactly. -/
theorem integral_phiTerm_mul_cos_add_kernel (n : ℕ) (z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) +
      (z ^ 2 + 1 / 4) *
        (∫ u in Ioi (0 : ℝ),
          (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
      (boundaryTerm (n + 1) / 2 : ℝ) := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (f := ibpPrimitive n z)
    (f' := fun u : ℝ =>
      (((phiTerm n u : ℝ) : ℂ) +
        (z ^ 2 + 1 / 4) * (kernelTerm n u : ℂ)) *
          Complex.cos (z * (u : ℂ))) (m := (0 : ℂ))
    (fun u _ => ibpPrimitive_hasDerivAt n z u)
    (integrableOn_ibpDerivative n z)
    (ibpPrimitive_tendsto_atTop n z)
  rw [ibpPrimitive_zero] at h
  let p : ℝ → ℂ := fun u =>
    (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))
  let q : ℝ → ℂ := fun u =>
    (z ^ 2 + 1 / 4) *
      ((kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)))
  have hp : Integrable p (volume.restrict (Ioi 0)) :=
    integrableOn_phiTerm_mul_cos n z
  have hq : Integrable q (volume.restrict (Ioi 0)) :=
    (integrableOn_kernelTerm_mul_cos n z).const_mul (z ^ 2 + 1 / 4)
  have hdecomp :
      (fun u : ℝ =>
        (((phiTerm n u : ℝ) : ℂ) +
          (z ^ 2 + 1 / 4) * (kernelTerm n u : ℂ)) *
            Complex.cos (z * (u : ℂ))) = p + q := by
    funext u
    simp only [p, q, Pi.add_apply]
    ring
  rw [hdecomp] at h
  change (∫ u in Ioi (0 : ℝ), p u + q u) =
    0 - -((boundaryTerm (n + 1) / 2 : ℝ) : ℂ) at h
  rw [integral_add hp hq] at h
  dsimp only [q] at h
  rw [integral_const_mul] at h
  convert h using 1 <;> norm_num <;> ring

lemma integral_Phi_mul_cos_eq_sum (N : ℕ) (z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
      (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))) =
      ∑ n ∈ Finset.range N,
        ∫ u in Ioi (0 : ℝ),
          (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  have hintegrand :
      (fun u : ℝ => (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))) =
        fun u : ℝ => ∑ n ∈ Finset.range N,
          (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
    funext u
    simp [Phi, Finset.sum_mul]
  rw [hintegrand]
  exact integral_finsetSum (Finset.range N)
    (fun n _ => integrableOn_phiTerm_mul_cos n z)

/-- The exact finite-sum result of the manuscript's two integrations by parts. -/
theorem H_eq_partial_sub_firstIntegral (N : ℕ) (z : ℂ) :
    H N z =
      (∑ n ∈ Finset.range N, (boundaryTerm (n + 1) : ℂ)) -
        2 * (z ^ 2 + 1 / 4) * firstIntegral N z := by
  rw [H, integral_Phi_mul_cos_eq_sum, firstIntegral_eq_sum]
  calc
    2 * ∑ n ∈ Finset.range N,
          ∫ u in Ioi (0 : ℝ),
            (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) =
        ∑ n ∈ Finset.range N,
          2 * (∫ u in Ioi (0 : ℝ),
            (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) := by
      rw [Finset.mul_sum]
    _ = ∑ n ∈ Finset.range N,
        ((boundaryTerm (n + 1) : ℂ) -
          2 * (z ^ 2 + 1 / 4) *
            (∫ u in Ioi (0 : ℝ),
              (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)))) := by
      apply Finset.sum_congr rfl
      intro n hn
      have h := integral_phiTerm_mul_cos_add_kernel n z
      norm_num [Complex.ofReal_div] at h
      linear_combination 2 * h
    _ = (∑ n ∈ Finset.range N, (boundaryTerm (n + 1) : ℂ)) -
        2 * (z ^ 2 + 1 / 4) *
          ∑ n ∈ Finset.range N,
            ∫ u in Ioi (0 : ℝ),
              (kernelTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- The printed upper-incomplete-gamma formula and the compressed
cosine-transform definition are extensionally the same approximant. -/
theorem XiIncompleteGamma_eq_Xi (N : ℕ) (z : ℂ) :
    XiIncompleteGamma N z = Xi N z := by
  rw [XiIncompleteGamma_eq_firstIntegral, Xi, F,
    H_eq_partial_sub_firstIntegral, boundaryConstant_eq_partial]
  push_cast
  ring

end IncompleteGammaApproximant
