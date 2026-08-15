import BoundaryConstantObstruction.EntireFunctionRigidity.AsymptoticTranslationRigidity

open Filter Polynomial Topology

namespace EntireFunctionRigidity

/-- A differentiable complex-valued function whose square is constant is
constant. -/
theorem constant_of_differentiable_mul_self_constant
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) (c : ℂ)
    (hsquare : ∀ z : ℂ, F z * F z = c) :
    ∀ z w : ℂ, F z = F w := by
  by_cases hc : c = 0
  · intro z w
    have hz : F z = 0 := eq_zero_of_mul_self_eq_zero ((hsquare z).trans hc)
    have hw : F w = 0 := eq_zero_of_mul_self_eq_zero ((hsquare w).trans hc)
    rw [hz, hw]
  · have hderiv : ∀ z : ℂ, deriv F z = 0 := by
      intro z
      have hFz : F z ≠ 0 := by
        intro hz
        apply hc
        rw [← hsquare z, hz, zero_mul]
      have hsqfun : (fun u : ℂ ↦ F u * F u) = fun _ ↦ c := by
        funext u
        exact hsquare u
      have hzero : deriv (fun u : ℂ ↦ F u * F u) z = 0 := by
        rw [hsqfun]
        simp
      rw [deriv_fun_mul (hF z) (hF z)] at hzero
      have hmul : ((2 : ℂ) * F z) * deriv F z = 0 := by
        calc
          ((2 : ℂ) * F z) * deriv F z =
              deriv F z * F z + F z * deriv F z := by ring
          _ = 0 := hzero
      exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero (by norm_num) hFz)
    exact is_const_of_deriv_eq_zero hF hderiv

/-- Reflection-product rigidity.  In an exponential-polynomial Hadamard
form, multiplying the values at `z` and `-z` cancels the exponential's linear
term.  Two finite real-tail limits make the resulting polynomial constant;
evenness then makes `F²` constant, hence `F` itself constant. -/
theorem factorized_two_sided_limit_even_is_constant
    (F : ℂ → ℂ) (Lpos Lneg a b : ℂ) (P : ℂ[X])
    (hF : Differentiable ℂ F)
    (hlimTop : Tendsto (fun x : ℝ ↦ F (x : ℂ)) atTop (nhds Lpos))
    (hlimBot : Tendsto (fun x : ℝ ↦ F (x : ℂ)) atBot (nhds Lneg))
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hfactor : ∀ z : ℂ, F z = Complex.exp (a * z + b) * P.eval z) :
    ∀ z w : ℂ, F z = F w := by
  let Q : ℂ[X] := C (Complex.exp (2 * b)) * P * P.comp (-X)
  have hproduct : ∀ z : ℂ, Q.eval z = F z * F (-z) := by
    intro z
    rw [hfactor, hfactor]
    simp only [Q, eval_mul, eval_C, eval_comp, eval_neg, eval_X]
    have hexp :
        Complex.exp (a * z + b) * Complex.exp (a * (-z) + b) =
          Complex.exp (2 * b) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  have hlimNeg :
      Tendsto (fun x : ℝ ↦ F ((-x : ℝ) : ℂ)) atTop (nhds Lneg) := by
    convert hlimBot.comp tendsto_neg_atTop_atBot using 1
    funext x
    simp [Function.comp_def]
  have hmul :
      Tendsto (fun x : ℝ ↦ F (x : ℂ) * F ((-x : ℝ) : ℂ)) atTop
        (nhds (Lpos * Lneg)) :=
    hlimTop.mul hlimNeg
  have hQlim :
      Tendsto (fun x : ℝ ↦ Q.eval (x : ℂ)) atTop (nhds (Lpos * Lneg)) := by
    apply hmul.congr'
    filter_upwards [] with x
    simpa using (hproduct (x : ℂ)).symm
  have hdegree : Q.degree ≤ 0 :=
    polynomial_degree_le_zero_of_finite_real_limit Q (Lpos * Lneg) hQlim
  have hQconst : Q = C (Q.coeff 0) := degree_le_zero_iff.mp hdegree
  have hsquare : ∀ z : ℂ, F z * F z = Q.coeff 0 := by
    intro z
    calc
      F z * F z = F z * F (-z) := by rw [heven z]
      _ = Q.eval z := (hproduct z).symm
      _ = Q.coeff 0 := by rw [hQconst]; simp
  exact constant_of_differentiable_mul_self_constant F hF (Q.coeff 0) hsquare

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.constant_of_differentiable_mul_self_constant
#print axioms EntireFunctionRigidity.factorized_two_sided_limit_even_is_constant
