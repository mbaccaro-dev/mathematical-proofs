import BoundaryConstantObstruction.IncompleteGamma.Kernel
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-! The exact Jacobi-theta identity behind the manuscript's positive boundary constant. -/

open Complex Filter Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

def thetaTerm (n : ℤ) (a : ℝ) : ℝ :=
  Real.exp (-Real.pi * a * (n : ℝ) ^ 2)

def theta (a : ℝ) : ℝ := ∑' n : ℤ, thetaTerm n a

def thetaDerivTerm (n : ℤ) (a : ℝ) : ℝ :=
  -Real.pi * (n : ℝ) ^ 2 * Real.exp (-Real.pi * a * (n : ℝ) ^ 2)

def thetaDerivMajorant (n : ℤ) : ℝ :=
  Real.pi * ((n : ℝ) ^ 2 *
    Real.exp (-Real.pi * ((1 / 2 : ℝ) * (n : ℝ) ^ 2)))

lemma summable_thetaDerivMajorant : Summable thetaDerivMajorant := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) (T := (1 / 2 : ℝ))
    (by norm_num) 2
  have h' := h.mul_left Real.pi
  refine h'.congr ?_
  intro n
  simp only [thetaDerivMajorant, mul_zero, zero_mul, sub_zero, Int.cast_abs, sq_abs]

lemma thetaTerm_hasDerivAt (n : ℤ) (a : ℝ) :
    HasDerivAt (thetaTerm n) (thetaDerivTerm n a) a := by
  have h := (((hasDerivAt_id a).const_mul (-Real.pi * (n : ℝ) ^ 2)).exp)
  convert h using 1
  · funext x
    simp only [thetaTerm, id_eq]
    congr 1
    ring
  · simp only [thetaDerivTerm, id_eq, mul_one]
    have he : Real.exp (-Real.pi * (n : ℝ) ^ 2 * a) =
        Real.exp (-Real.pi * a * (n : ℝ) ^ 2) := by
      congr 1
      ring
    rw [he]
    ring

lemma thetaDerivTerm_norm_le {n : ℤ} {a : ℝ}
    (ha : a ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2 : ℝ)) :
    ‖thetaDerivTerm n a‖ ≤ thetaDerivMajorant n := by
  unfold thetaDerivTerm thetaDerivMajorant
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hcoeff : |-Real.pi * (n : ℝ) ^ 2| = Real.pi * (n : ℝ) ^ 2 := by
    have hn : -Real.pi * (n : ℝ) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)
    rw [abs_of_nonpos hn]
    ring
  rw [hcoeff]
  rw [show Real.pi * ((n : ℝ) ^ 2 *
      Real.exp (-Real.pi * ((1 / 2 : ℝ) * (n : ℝ) ^ 2))) =
      Real.pi * (n : ℝ) ^ 2 *
        Real.exp (-Real.pi * ((1 / 2 : ℝ) * (n : ℝ) ^ 2)) by ring]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg Real.pi_pos.le (sq_nonneg _))
  apply Real.exp_le_exp.mpr
  have ha' : (1 / 2 : ℝ) ≤ a := ha.1.le
  have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right ha' hn
  have hneg := mul_le_mul_of_nonpos_left hmul (neg_nonpos.mpr Real.pi_pos.le)
  simpa only [mul_assoc] using hneg

lemma summable_theta_one : Summable (fun n : ℤ => thetaTerm n 1) := by
  have h := summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ) (T := (1 : ℝ))
    (by norm_num) 0
  simpa [thetaTerm] using h

lemma theta_hasDerivAt_one :
    HasDerivAt theta (∑' n : ℤ, thetaDerivTerm n 1) 1 := by
  unfold theta
  apply hasDerivAt_tsum_of_isPreconnected summable_thetaDerivMajorant isOpen_Ioo
      ordConnected_Ioo.isPreconnected
      (fun n a _ => thetaTerm_hasDerivAt n a)
      (fun n a ha => thetaDerivTerm_norm_le ha)
      (show (1 : ℝ) ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) by norm_num)
      summable_theta_one
      (show (1 : ℝ) ∈ Ioo (1 / 2 : ℝ) (3 / 2 : ℝ) by norm_num)

lemma theta_functional (a : ℝ) (ha : 0 < a) :
    theta a = 1 / a ^ (1 / 2 : ℝ) * theta (1 / a) := by
  simpa [theta, thetaTerm, div_eq_mul_inv, mul_assoc] using
    Real.tsum_exp_neg_mul_int_sq ha

lemma theta_derivative_self_dual :
    4 * (∑' n : ℤ, thetaDerivTerm n 1) = -theta 1 := by
  let D : ℝ := ∑' n : ℤ, thetaDerivTerm n 1
  have htheta : HasDerivAt theta D 1 := theta_hasDerivAt_one
  have hpow : HasDerivAt (fun a : ℝ => a ^ (1 / 2 : ℝ)) (1 / 2 : ℝ) 1 := by
    convert Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := (1 / 2 : ℝ))
      (Or.inl one_ne_zero) using 1 <;> norm_num
  have hpref : HasDerivAt (fun a : ℝ => 1 / a ^ (1 / 2 : ℝ)) (-1 / 2 : ℝ) 1 := by
    have h := (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).div hpow (by norm_num)
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) / fun a : ℝ => a ^ (1 / 2 : ℝ))
      (-1 / 2 : ℝ) 1
    exact h.congr_deriv (by norm_num)
  have hinv : HasDerivAt (fun a : ℝ => 1 / a) (-1 : ℝ) 1 := by
    have h := (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).div
      (hasDerivAt_id (x := (1 : ℝ))) one_ne_zero
    change HasDerivAt ((fun _ : ℝ => (1 : ℝ)) / id) (-1 : ℝ) 1
    exact h.congr_deriv (by norm_num)
  have hcomp : HasDerivAt (fun a : ℝ => theta (1 / a)) (-D) 1 := by
    have htheta' : HasDerivAt theta D (1 / (1 : ℝ)) := by simpa using htheta
    have h := htheta'.comp 1 hinv
    change HasDerivAt (theta ∘ fun a : ℝ => 1 / a) (-D) 1
    exact h.congr_deriv (by ring)
  have hrhs : HasDerivAt
      (fun a : ℝ => 1 / a ^ (1 / 2 : ℝ) * theta (1 / a))
      ((-1 / 2 : ℝ) * theta 1 - D) 1 := by
    have h := hpref.mul hcomp
    change HasDerivAt
      ((fun a : ℝ => 1 / a ^ (1 / 2 : ℝ)) * fun a : ℝ => theta (1 / a))
      ((-1 / 2 : ℝ) * theta 1 - D) 1
    exact h.congr_deriv (by norm_num; ring)
  have hevent : theta =ᶠ[nhds (1 : ℝ)]
      (fun a : ℝ => 1 / a ^ (1 / 2 : ℝ) * theta (1 / a)) := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with a ha
    exact theta_functional a ha
  have heq : D = (-1 / 2 : ℝ) * theta 1 - D :=
    (htheta.congr_of_eventuallyEq hevent.symm).unique hrhs
  dsimp only [D] at heq ⊢
  linarith

lemma thetaTerm_even_one : Function.Even (fun n : ℤ => thetaTerm n 1) := by
  intro n
  simp [thetaTerm]

lemma thetaDerivTerm_even_one : Function.Even (fun n : ℤ => thetaDerivTerm n 1) := by
  intro n
  simp [thetaDerivTerm]

lemma summable_thetaDeriv_one : Summable (fun n : ℤ => thetaDerivTerm n 1) := by
  exact summable_thetaDerivMajorant.of_norm_bounded
    (fun n => thetaDerivTerm_norm_le (n := n) (a := (1 : ℝ)) (by norm_num))

lemma theta_one_decomposition :
    theta 1 = 1 + 2 * (∑' n : ℕ, thetaTerm (n + 1 : ℤ) 1) := by
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat thetaTerm_even_one summable_theta_one
  have hp : (∑' n : ℕ+, thetaTerm (n : ℤ) 1) =
      ∑' n : ℕ, thetaTerm (n + 1 : ℤ) 1 := by
    simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => thetaTerm (n : ℤ) 1))
  rw [hp] at h
  rw [theta]
  simpa [thetaTerm, two_smul ℝ] using h

lemma thetaDeriv_one_decomposition :
    (∑' n : ℤ, thetaDerivTerm n 1) =
      2 * (∑' n : ℕ, thetaDerivTerm (n + 1 : ℤ) 1) := by
  have h := tsum_int_eq_zero_add_two_mul_tsum_pnat
    thetaDerivTerm_even_one summable_thetaDeriv_one
  have hp : (∑' n : ℕ+, thetaDerivTerm (n : ℤ) 1) =
      ∑' n : ℕ, thetaDerivTerm (n + 1 : ℤ) 1 := by
    simpa using (tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => thetaDerivTerm (n : ℤ) 1))
  rw [hp] at h
  simpa [thetaDerivTerm, two_smul ℝ] using h

lemma summable_positiveGaussian : Summable (fun n : ℕ =>
    Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)) := by
  have h := (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ)
    (T := (1 : ℝ)) (by norm_num) 0).comp_injective
      (Int.ofNat_injective.comp Nat.succ_injective)
  refine h.congr ?_
  intro n
  simp [Function.comp_apply]

lemma summable_positiveGaussianMoment : Summable (fun n : ℕ =>
    (n + 1 : ℝ) ^ 2 * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)) := by
  have h := (summable_pow_mul_jacobiTheta₂_term_bound (0 : ℝ)
    (T := (1 : ℝ)) (by norm_num) 2).comp_injective
      (Int.ofNat_injective.comp Nat.succ_injective)
  refine h.congr ?_
  intro n
  simp [Function.comp_apply]

theorem tsum_boundaryTerm_succ :
    (∑' n : ℕ, boundaryTerm (n + 1)) = 1 / 2 := by
  let A : ℝ := ∑' n : ℕ, Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)
  let B : ℝ := ∑' n : ℕ,
    (n + 1 : ℝ) ^ 2 * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)
  have hthetaPos : (∑' n : ℕ, thetaTerm (n + 1 : ℤ) 1) = A := by
    apply tsum_congr
    intro n
    simp [thetaTerm, A]
  have hderivPos : (∑' n : ℕ, thetaDerivTerm (n + 1 : ℤ) 1) =
      -Real.pi * B := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [thetaDerivTerm, B]
    push_cast
    rw [show Real.exp (-Real.pi * 1 * (n + 1 : ℝ) ^ 2) =
        Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2) by
      congr 1
      ring]
    ring
  have h := theta_derivative_self_dual
  rw [thetaDeriv_one_decomposition, theta_one_decomposition, hthetaPos, hderivPos] at h
  have hBA : 4 * Real.pi * B - A = 1 / 2 := by linarith
  calc
    (∑' n : ℕ, boundaryTerm (n + 1)) =
        ∑' n : ℕ, (4 * Real.pi *
            ((n + 1 : ℝ) ^ 2 * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)) -
          Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)) := by
            apply tsum_congr
            intro n
            simp only [boundaryTerm]
            push_cast
            ring
    _ = (∑' n : ℕ, 4 * Real.pi *
            ((n + 1 : ℝ) ^ 2 * Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2))) -
          (∑' n : ℕ, Real.exp (-Real.pi * (n + 1 : ℝ) ^ 2)) := by
            exact (summable_positiveGaussianMoment.mul_left (4 * Real.pi)).tsum_sub
              summable_positiveGaussian
    _ = 4 * Real.pi * B - A := by rw [tsum_mul_left]
    _ = 1 / 2 := hBA

lemma summable_boundaryTerm_succ :
    Summable (fun n : ℕ => boundaryTerm (n + 1)) := by
  exact summable_boundaryTerm.comp_injective Nat.succ_injective

/-- The tail normalization used in Lean is exactly the finite-partial-sum
formula printed in the manuscript. -/
theorem boundaryConstant_eq_partial (N : ℕ) :
    boundaryConstant N =
      1 / 2 - ∑ n ∈ Finset.range N, boundaryTerm (n + 1) := by
  have hsplit := summable_boundaryTerm_succ.sum_add_tsum_nat_add N
  rw [tsum_boundaryTerm_succ] at hsplit
  have htail :
      (∑' n : ℕ, boundaryTerm (n + N + 1)) = boundaryConstant N := by
    rw [boundaryConstant]
    apply tsum_congr
    intro n
    congr 1
    omega
  rw [htail] at hsplit
  linarith

theorem boundaryConstant_lt_half {N : ℕ} (hN : 1 ≤ N) :
    boundaryConstant N < 1 / 2 := by
  rw [boundaryConstant_eq_partial]
  have hsum : 0 < ∑ n ∈ Finset.range N, boundaryTerm (n + 1) := by
    apply Finset.sum_pos
    · intro n hn
      exact boundaryTerm_pos (by omega)
    · exact ⟨0, Finset.mem_range.mpr (by omega)⟩
  linarith

theorem boundaryConstant_mem_Ioo {N : ℕ} (hN : 1 ≤ N) :
    boundaryConstant N ∈ Set.Ioo 0 (1 / 2 : ℝ) :=
  ⟨boundaryConstant_pos hN, boundaryConstant_lt_half hN⟩

end IncompleteGammaApproximant
