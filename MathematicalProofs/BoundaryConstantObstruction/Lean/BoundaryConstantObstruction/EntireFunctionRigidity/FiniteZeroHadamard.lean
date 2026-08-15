import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.Algebra.Polynomial
import BoundaryConstantObstruction.EntireFunctionRigidity.FiniteZeroFactorization
import BoundaryConstantObstruction.EntireFunctionRigidity.ZeroFreeGrowth

open Filter Metric Set Topology

namespace EntireFunctionRigidity

/-- A monic complex polynomial has norm at least one outside some centered
ball.  The constant case is exactly the polynomial one. -/
theorem monic_polynomial_norm_eventually_ge_one
    (P : Polynomial ℂ) (hP : P.Monic) :
    ∃ R₀ : ℝ, 0 ≤ R₀ ∧ ∀ z : ℂ, R₀ ≤ ‖z‖ → 1 ≤ ‖P.eval z‖ := by
  rcases le_or_gt P.degree 0 with hdeg | hdeg
  · have hPone : P = 1 := hP.degree_le_zero_iff_eq_one.mp hdeg
    exact ⟨0, le_rfl, by simp [hPone]⟩
  · have hlim : Tendsto (fun z : ℂ ↦ ‖P.eval z‖) (Bornology.cobounded ℂ) atTop :=
      P.tendsto_norm_atTop hdeg tendsto_norm_cobounded_atTop
    have hev : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, 1 ≤ ‖P.eval z‖ :=
      hlim.eventually_ge_atTop 1
    rcases (Filter.hasBasis_cobounded_norm (E := ℂ)).mem_iff.mp hev with
      ⟨R₀, -, hR₀⟩
    refine ⟨max R₀ 0, le_max_right _ _, fun z hz ↦ hR₀ ?_⟩
    exact (le_max_left R₀ 0).trans hz

/-- A centered growth bound for `F = P * g`, with `P` monic and `g` entire,
transfers to `g` after a fixed radial shift.  The maximum-modulus principle
fills the interior after the polynomial lower bound controls the boundary. -/
theorem norm_bound_zero_free_factor_of_monic_polynomial
    (F g : ℂ → ℂ) (P : Polynomial ℂ) (B : ℝ → ℝ)
    (hg : Differentiable ℂ g)
    (hP : P.Monic)
    (hfactor : ∀ z : ℂ, F z = P.eval z * g z)
    (hNormF : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖F z‖ ≤ Real.exp (B R)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖g z‖ ≤ Real.exp (B (R + K)) := by
  obtain ⟨R₀, hR₀, hPoutside⟩ := monic_polynomial_norm_eventually_ge_one P hP
  let K : ℝ := R₀ + 1
  have hK : 0 ≤ K := by dsimp [K]; linarith
  refine ⟨K, hK, ?_⟩
  intro R hR z hz
  let S : ℝ := R + K
  have hS : 0 < S := by dsimp [S]; linarith
  have hboundary : ∀ w ∈ sphere (0 : ℂ) S,
      ‖g w‖ ≤ Real.exp (B S) := by
    intro w hw
    have hwnorm : ‖w‖ = S := by simpa [mem_sphere_iff_norm] using hw
    have hPw : 1 ≤ ‖P.eval w‖ := by
      apply hPoutside
      rw [hwnorm]
      dsimp [S, K]
      linarith
    have hFw : ‖F w‖ ≤ Real.exp (B S) :=
      hNormF S hS w (by rw [hwnorm])
    rw [hfactor, norm_mul] at hFw
    nlinarith [norm_nonneg (g w)]
  apply Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball (hg.differentiableOn.diffContOnCl_ball (subset_univ _))
  · intro w hw
    exact hboundary w (frontier_ball_subset_sphere hw)
  · apply subset_closure
    rw [mem_ball_zero_iff]
    exact hz.trans_lt (by dsimp [S]; linarith)

/-- Bespoke finite-zero Hadamard consequence at exactly the manuscript's
growth ceiling.  It avoids introducing an abstract entire-function order API:
the supplied centered bound is consumed directly. -/
theorem exists_exponential_polynomial_factorization_of_finite_zero_set
    (F : ℂ → ℂ) (B : ℝ → ℝ)
    (hF : AnalyticOnNhd ℂ F univ)
    (hnotop : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (hzeros : {z : ℂ | F z = 0}.Finite)
    (hBpos : ∀ R : ℝ, 0 < R → 0 < B R)
    (hNormF : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖F z‖ ≤ Real.exp (B R))
    (hsub : ∀ d e : ℝ, 0 ≤ d → 0 ≤ e →
      Tendsto (fun R : ℝ ↦ (2 * B (2 * R + d) + e) / R ^ 2)
        atTop (nhds 0)) :
    ∃ a b : ℂ, ∃ P : Polynomial ℂ, P ≠ 0 ∧
      ∀ z : ℂ, F z = Complex.exp (a * z + b) * P.eval z := by
  obtain ⟨P, g, hPmonic, hPne, hg, hgne, hfactor⟩ :=
    exists_polynomial_zero_free_factorization_of_finite_zero_set
      F hF hnotop hzeros
  have hgd : Differentiable ℂ g :=
    Complex.analyticOnNhd_univ_iff_differentiable.mp hg
  obtain ⟨K, hK, hNormg⟩ :=
    norm_bound_zero_free_factor_of_monic_polynomial
      F g P B hgd hPmonic hfactor hNormF
  let Bg : ℝ → ℝ := fun R ↦ B (R + K)
  have hBgpos : ∀ R : ℝ, 0 < R → 0 < Bg R := by
    intro R hR
    apply hBpos
    linarith
  have hBgsub : ∀ d e : ℝ, 0 ≤ d → 0 ≤ e →
      Tendsto (fun R : ℝ ↦ (2 * Bg (2 * R + d) + e) / R ^ 2)
        atTop (nhds 0) := by
    intro d e hd he
    simpa only [Bg, add_assoc] using hsub (d + K) e (add_nonneg hd hK) he
  obtain ⟨a, b, hab⟩ :=
    exponential_affine_of_zero_free_subquadratic_growth
      g Bg hgd hgne hBgpos hNormg hBgsub
  refine ⟨a, b, P, hPne, fun z ↦ ?_⟩
  rw [hfactor, hab]
  exact mul_comm _ _

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.monic_polynomial_norm_eventually_ge_one
#print axioms EntireFunctionRigidity.norm_bound_zero_free_factor_of_monic_polynomial
#print axioms EntireFunctionRigidity.exists_exponential_polynomial_factorization_of_finite_zero_set
