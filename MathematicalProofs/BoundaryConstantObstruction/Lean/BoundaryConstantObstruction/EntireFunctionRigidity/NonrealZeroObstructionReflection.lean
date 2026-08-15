import BoundaryConstantObstruction.EntireFunctionRigidity.BoundaryFiniteZeros
import BoundaryConstantObstruction.EntireFunctionRigidity.FiniteZeroHadamard
import BoundaryConstantObstruction.EntireFunctionRigidity.ReflectionProductRigidity

open Filter Set Topology

namespace EntireFunctionRigidity

/-- Kernel-checked abstract form of the reflection-product successor proof.
Compared with the translation route, this uses the manuscript's evenness and
both already-required boundary limits to cancel the Hadamard exponential in
one step. -/
theorem exists_nonreal_zero_of_entire_growth_boundary_and_evenness
    (F : ℂ → ℂ) (B : ℝ → ℝ) (Lpos Lneg : ℂ)
    (hF : Differentiable ℂ F)
    (hlimTop : Tendsto (fun x : ℝ ↦ F x) atTop (nhds Lpos))
    (hlimBot : Tendsto (fun x : ℝ ↦ F x) atBot (nhds Lneg))
    (hLpos : Lpos ≠ 0) (hLneg : Lneg ≠ 0)
    (heven : ∀ z : ℂ, F (-z) = F z)
    (hnonconstant : ∃ z w : ℂ, F z ≠ F w)
    (hBpos : ∀ R : ℝ, 0 < R → 0 < B R)
    (hNormF : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖F z‖ ≤ Real.exp (B R))
    (hsub : ∀ d e : ℝ, 0 ≤ d → 0 ≤ e →
      Tendsto (fun R : ℝ ↦ (2 * B (2 * R + d) + e) / R ^ 2)
        atTop (nhds 0)) :
    ∃ z : ℂ, F z = 0 ∧ z.im ≠ 0 := by
  by_contra hno
  have hallReal : ∀ z : ℂ, F z = 0 → z.im = 0 := by
    intro z hz
    by_contra him
    exact hno ⟨z, hz, him⟩
  have hzeros : {z : ℂ | F z = 0}.Finite :=
    finite_zero_set_of_real_zeros_and_two_sided_nonzero_limits
      hF hlimTop hlimBot hLpos hLneg hallReal
  have hnonzero : ∃ z : ℂ, F z ≠ 0 := by
    have htop : ∀ᶠ x : ℝ in atTop, F x ≠ 0 := hlimTop.eventually_ne hLpos
    obtain ⟨x, hx⟩ := htop.exists
    exact ⟨x, hx⟩
  have hnotop : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_entire_of_exists_ne_zero hF hnonzero
  have hFanalytic : AnalyticOnNhd ℂ F univ :=
    hF.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨a, b, P, -, hfactor⟩ :=
    exists_exponential_polynomial_factorization_of_finite_zero_set
      F B hFanalytic hnotop hzeros hBpos hNormF hsub
  have hconstant : ∀ z w : ℂ, F z = F w :=
    factorized_two_sided_limit_even_is_constant
      F Lpos Lneg a b P hF hlimTop hlimBot heven hfactor
  obtain ⟨z, w, hzw⟩ := hnonconstant
  exact hzw (hconstant z w)

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.exists_nonreal_zero_of_entire_growth_boundary_and_evenness
