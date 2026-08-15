import BoundaryConstantObstruction.EntireFunctionRigidity.EntireLog
import BoundaryConstantObstruction.EntireFunctionRigidity.SubquadraticAffine

open Filter Metric Set Topology

namespace EntireFunctionRigidity

/-- A zero-free entire function with a subquadratic logarithmic norm bound is
the exponential of an affine function.  This is the exact Hadamard consequence
needed after the finitely many zeros have been removed. -/
theorem exponential_affine_of_zero_free_subquadratic_growth
    (g : ℂ → ℂ) (B : ℝ → ℝ)
    (hg : Differentiable ℂ g) (hgne : ∀ z : ℂ, g z ≠ 0)
    (hBpos : ∀ R : ℝ, 0 < R → 0 < B R)
    (hNorm : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖g z‖ ≤ Real.exp (B R))
    (hsub : ∀ d e : ℝ, 0 ≤ d → 0 ≤ e →
      Tendsto (fun R : ℝ ↦ (2 * B (2 * R + d) + e) / R ^ 2)
        atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z : ℂ, g z = Complex.exp (a * z + b) := by
  obtain ⟨ℓ, hℓ, hExp⟩ := exists_differentiable_log_of_ne_zero g hg hgne
  have hRe : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R → (ℓ z).re ≤ B R := by
    intro R hR z hz
    have h := hNorm R hR z hz
    rw [← hExp z, Complex.norm_exp] at h
    exact Real.exp_le_exp.mp h
  obtain ⟨a, b, hab⟩ := affine_of_re_le_subquadratic ℓ B hℓ hBpos hRe hsub
  refine ⟨a, b, fun z ↦ ?_⟩
  rw [← hExp z, hab z]

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.exponential_affine_of_zero_free_subquadratic_growth
