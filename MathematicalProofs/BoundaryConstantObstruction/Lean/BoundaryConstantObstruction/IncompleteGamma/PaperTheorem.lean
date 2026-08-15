import BoundaryConstantObstruction.IncompleteGamma.Growth
import BoundaryConstantObstruction.IncompleteGamma.Frontend

open Complex Filter Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- Exact Lean form of the standalone paper's main nonreal-zero theorem. -/
theorem exists_nonreal_zero_F {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ z : ℂ, F N t z = 0 ∧ z.im ≠ 0 := by
  have hlimit_pos : 0 < t * boundaryConstant N :=
    mul_pos ht0 (boundaryConstant_pos hN)
  have hlimit_ne : (t * boundaryConstant N : ℂ) ≠ 0 := by
    norm_cast
    exact hlimit_pos.ne'
  have hnonconstant : ∃ z w : ℂ, F N t z ≠ F N t w := by
    by_contra h
    push_neg at h
    exact F_nonconstant hN t ⟨F N t 0, fun z => h z 0⟩
  exact EntireFunctionRigidity.exists_nonreal_zero_of_entire_growth_boundary_and_evenness
    (F N t) (growthBound N t)
    (t * boundaryConstant N : ℂ) (t * boundaryConstant N : ℂ)
    (F_differentiable N t)
    (F_tendsto_atTop N t)
    (F_tendsto_atBot N t)
    hlimit_ne hlimit_ne
    (F_even N t)
    hnonconstant
    (fun R hR => growthBound_pos N t hR)
    (fun R hR z hz => norm_F_le_growthBound N t hR.le z hz)
    (fun d e hd he => growthBound_subquadratic N t d e hd he)

/-- Endpoint corollary `t = 1`, where the paper's `Xi_N` is `F_{N,1}`. -/
theorem exists_nonreal_zero_Xi {N : ℕ} (hN : 1 ≤ N) :
    ∃ z : ℂ, Xi N z = 0 ∧ z.im ≠ 0 := by
  simpa only [Xi_eq_F_one] using
    (exists_nonreal_zero_F hN (t := (1 : ℝ)) (by norm_num) (by norm_num))

/-- The paper endpoint stated using its original upper-incomplete-gamma formula. -/
theorem exists_nonreal_zero_XiIncompleteGamma {N : ℕ} (hN : 1 ≤ N) :
    ∃ z : ℂ, XiIncompleteGamma N z = 0 ∧ z.im ≠ 0 := by
  simpa only [XiIncompleteGamma_eq_Xi] using exists_nonreal_zero_Xi hN

/-- Fully quantified manuscript theorem, preserving both endpoint bounds. -/
theorem theorem_A :
    ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ z : ℂ, F N t z = 0 ∧ z.im ≠ 0 := by
  intro N hN t ht0 ht1
  exact exists_nonreal_zero_F hN ht0 ht1

end IncompleteGammaApproximant

#print axioms IncompleteGammaApproximant.theorem_A
#print axioms IncompleteGammaApproximant.exists_nonreal_zero_XiIncompleteGamma
