import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Topology.Algebra.Polynomial

open Asymptotics Filter Polynomial Topology

namespace EntireFunctionRigidity

/-- If every real rescaling of a complex exponential is one, its exponent is
zero. -/
theorem exponent_eq_zero_of_all_real_shifts (a : ℂ)
    (h : ∀ r : ℝ, Complex.exp (a * (r : ℂ)) = 1) : a = 0 := by
  let r : ℝ := 1 / (‖a‖ + 1)
  have hden : 0 < ‖a‖ + 1 := by positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hnorm : ‖a * (r : ℂ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    dsimp [r]
    calc
      ‖a‖ * (1 / (‖a‖ + 1)) = ‖a‖ / (‖a‖ + 1) := by ring
      _ < 1 := (div_lt_one hden).2 (by linarith [norm_nonneg a])
  have him_abs : |(a * (r : ℂ)).im| < Real.pi :=
    lt_of_le_of_lt (Complex.abs_im_le_norm _) (hnorm.trans (by linarith [Real.pi_gt_three]))
  have him_lower : -Real.pi < (a * (r : ℂ)).im := (abs_lt.1 him_abs).1
  have him_upper : (a * (r : ℂ)).im ≤ Real.pi := (abs_lt.1 him_abs).2.le
  have hz : a * (r : ℂ) = 0 :=
    Complex.exp_inj_of_neg_pi_lt_of_le_pi
      him_lower him_upper (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)
      (by simpa using h r)
  exact (mul_eq_zero.mp hz).resolve_right (Complex.ofReal_ne_zero.mpr hr.ne')

/-- Translating the argument of a nonzero complex polynomial does not change
its leading asymptotic, so the translated/original ratio tends to one on the
positive real axis. -/
theorem polynomial_shift_ratio_tendsto_one (P : ℂ[X]) (hP : P ≠ 0) (h : ℝ) :
    Tendsto (fun x : ℝ ↦ P.eval ((x + h : ℝ) : ℂ) / P.eval (x : ℂ))
      atTop (nhds 1) := by
  let Q : ℂ[X] := P.comp (X + C (h : ℂ))
  have hQdeg : Q.natDegree = P.natDegree := by
    simp [Q, natDegree_comp]
  have hQlead : Q.leadingCoeff = P.leadingCoeff := by
    dsimp [Q]
    rw [leadingCoeff_comp (by simp)]
    simp
  have hQequiv : Q.eval ~[Bornology.cobounded ℂ] P.eval := by
    have hQmono := Polynomial.isEquivalent_cobounded_leading_monomial (P := Q)
    have hPmono := Polynomial.isEquivalent_cobounded_leading_monomial (P := P)
    rw [hQdeg, hQlead] at hQmono
    exact hQmono.trans hPmono.symm
  have hQequivReal :
      (fun x : ℝ ↦ Q.eval (x : ℂ)) ~[atTop] (fun x : ℝ ↦ P.eval (x : ℂ)) :=
    hQequiv.comp_tendsto (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  have hcastCofinite :
      Tendsto (fun x : ℝ ↦ (x : ℂ)) atTop (cofinite : Filter ℂ) :=
    (RCLike.tendsto_ofReal_atTop_cobounded ℂ).mono_right (Bornology.le_cofinite ℂ)
  have hdenComplex : ∀ᶠ z : ℂ in cofinite, P.eval z ≠ 0 := by
    simpa [IsRoot] using eventually_cofinite_not_isRoot hP
  have hdenReal : ∀ᶠ x : ℝ in atTop, P.eval (x : ℂ) ≠ 0 :=
    hcastCofinite.eventually hdenComplex
  rw [isEquivalent_iff_tendsto_one hdenReal] at hQequivReal
  rw [show
    ((fun x : ℝ ↦ Q.eval (x : ℂ)) / (fun x : ℝ ↦ P.eval (x : ℂ))) =
      (fun x : ℝ ↦ Q.eval (x : ℂ) / P.eval (x : ℂ)) by rfl] at hQequivReal
  simpa [Q, eval_comp] using hQequivReal

/-- A complex polynomial with a finite limit along the positive real axis is
constant. -/
theorem polynomial_degree_le_zero_of_finite_real_limit (P : ℂ[X]) (c : ℂ)
    (hP : Tendsto (fun x : ℝ ↦ P.eval (x : ℂ)) atTop (nhds c)) : P.degree ≤ 0 := by
  by_contra hdeg
  have hdeg' : 0 < P.degree := lt_of_not_ge hdeg
  have hnorm_inf : Tendsto (fun x : ℝ ↦ ‖P.eval (x : ℂ)‖) atTop atTop := by
    apply P.tendsto_norm_atTop hdeg'
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (tendsto_abs_atTop_atTop : Tendsto (abs : ℝ → ℝ) atTop atTop)
  have hnorm_fin : Tendsto (fun x : ℝ ↦ ‖P.eval (x : ℂ)‖) atTop (nhds ‖c‖) := hP.norm
  have hlt : ∀ᶠ x : ℝ in atTop, ‖P.eval (x : ℂ)‖ < ‖c‖ + 1 :=
    (tendsto_order.1 hnorm_fin).2 _ (by linarith)
  have hge : ∀ᶠ x : ℝ in atTop, ‖c‖ + 1 ≤ ‖P.eval (x : ℂ)‖ :=
    (tendsto_atTop.1 hnorm_inf) (‖c‖ + 1)
  obtain ⟨x, hxlt, hxge⟩ := (hlt.and hge).exists
  exact (not_lt_of_ge hxge) hxlt

/-- A Hadamard exponential-polynomial representation with a finite nonzero
positive-tail limit represents a constant function.  This is the compressed
proof's asymptotic-translation rigidity step. -/
theorem factorized_finite_nonzero_limit_is_constant
    (F : ℂ → ℂ) (L a b : ℂ) (P : ℂ[X])
    (hL : L ≠ 0) (hP : P ≠ 0)
    (hlim : Tendsto (fun x : ℝ ↦ F (x : ℂ)) atTop (nhds L))
    (hfactor : ∀ z : ℂ, F z = Complex.exp (a * z + b) * P.eval z) :
    ∀ z w : ℂ, F z = F w := by
  have hexpShift : ∀ r : ℝ, Complex.exp (a * (r : ℂ)) = 1 := by
    intro r
    have hlimShift : Tendsto (fun x : ℝ ↦ F ((x + r : ℝ) : ℂ)) atTop (nhds L) :=
      hlim.comp (tendsto_atTop_add_const_right atTop r tendsto_id)
    have hratioBoundary :
        Tendsto (fun x : ℝ ↦ F ((x + r : ℝ) : ℂ) / F (x : ℂ)) atTop (nhds 1) :=
      (tendsto_div_nhds_one_iff_eq₀ hlimShift hlim hL).2 rfl
    have hratioIdentity :
        (fun x : ℝ ↦ F ((x + r : ℝ) : ℂ) / F (x : ℂ)) =
          (fun x : ℝ ↦ Complex.exp (a * (r : ℂ)) *
            (P.eval ((x + r : ℝ) : ℂ) / P.eval (x : ℂ))) := by
      funext x
      rw [hfactor, hfactor]
      have hexp :
          Complex.exp (a * ((x + r : ℝ) : ℂ) + b) =
            Complex.exp (a * (r : ℂ)) * Complex.exp (a * (x : ℂ) + b) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [hexp]
      field_simp [Complex.exp_ne_zero]
    have hratioFactorized :
        Tendsto (fun x : ℝ ↦ F ((x + r : ℝ) : ℂ) / F (x : ℂ)) atTop
          (nhds (Complex.exp (a * (r : ℂ)))) := by
      rw [hratioIdentity]
      simpa using
        (tendsto_const_nhds.mul (polynomial_shift_ratio_tendsto_one P hP r))
    exact tendsto_nhds_unique hratioFactorized hratioBoundary
  have ha : a = 0 := exponent_eq_zero_of_all_real_shifts a hexpShift
  have hpolyLimit :
      Tendsto (fun x : ℝ ↦ P.eval (x : ℂ)) atTop
        (nhds (Complex.exp (-b) * L)) := by
    have hconst :
        Tendsto (fun _ : ℝ ↦ Complex.exp (-b)) atTop (nhds (Complex.exp (-b))) :=
      tendsto_const_nhds
    have hscaled := hconst.mul hlim
    have hscaled' :
        Tendsto (fun x : ℝ ↦ Complex.exp (-b) * F (x : ℂ)) atTop
          (nhds (Complex.exp (-b) * L)) := by
      simpa using hscaled
    apply hscaled'.congr'
    filter_upwards [] with x
    rw [hfactor, ha]
    rw [← mul_assoc, ← Complex.exp_add]
    simp
  have hdegree : P.degree ≤ 0 :=
    polynomial_degree_le_zero_of_finite_real_limit P (Complex.exp (-b) * L) hpolyLimit
  have hPconst : P = C (P.coeff 0) := degree_le_zero_iff.mp hdegree
  intro z w
  rw [hfactor, hfactor, ha, hPconst]
  simp

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.exponent_eq_zero_of_all_real_shifts
#print axioms EntireFunctionRigidity.polynomial_shift_ratio_tendsto_one
#print axioms EntireFunctionRigidity.polynomial_degree_le_zero_of_finite_real_limit
#print axioms EntireFunctionRigidity.factorized_finite_nonzero_limit_is_constant
