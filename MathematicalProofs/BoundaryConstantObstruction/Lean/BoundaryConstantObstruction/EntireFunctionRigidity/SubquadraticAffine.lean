import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Filter Metric Set Topology

namespace EntireFunctionRigidity

/-- A Borel--Caratheodory/Cauchy bridge tailored to the manuscript's
`O(r * log r)` estimate.  The function `B` bounds the real part of an entire
function on centered balls.  The second hypothesis records exactly the
subquadratic limit needed after translating the center.

This formulation deliberately avoids a separate classical "order of an
entire function" API: it consumes the manuscript's quantitative bound
directly. -/
theorem affine_of_re_le_subquadratic
    (f : ℂ → ℂ) (B : ℝ → ℝ)
    (hf : Differentiable ℂ f)
    (hBpos : ∀ R : ℝ, 0 < R → 0 < B R)
    (hRe : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖z‖ ≤ R → (f z).re ≤ B R)
    (hsub : ∀ d e : ℝ, 0 ≤ d → 0 ≤ e →
      Tendsto
        (fun R : ℝ ↦
          (2 * B (2 * R + d) + e) / R ^ 2)
        atTop (nhds 0)) :
    ∃ a b : ℂ, ∀ z : ℂ, f z = a * z + b := by
  have hsecond : ∀ c : ℂ, iteratedDeriv 2 f c = 0 := by
    intro c
    let g : ℂ → ℂ := fun z ↦ f (z + c)
    have hg : Differentiable ℂ g := hf.comp (differentiable_id.add_const c)
    have hbound : ∀ R : ℝ, 0 < R →
        ‖iteratedDeriv 2 g 0‖ ≤
          2 * (2 * B (2 * R + ‖c‖) + 3 * ‖f c‖) / R ^ 2 := by
      intro R hR
      have houter : 0 < 2 * R := by positivity
      have hM : 0 < B (2 * R + ‖c‖) := by
        apply hBpos
        positivity
      have hgMaps : MapsTo g (ball 0 (2 * R)) {z | z.re ≤ B (2 * R + ‖c‖)} := by
        intro z hz
        apply hRe (2 * R + ‖c‖) (by positivity) (z + c)
        calc
          ‖z + c‖ ≤ ‖z‖ + ‖c‖ := norm_add_le _ _
          _ ≤ 2 * R + ‖c‖ := by
            have hz' : ‖z‖ < 2 * R := by simpa [mem_ball_zero_iff] using hz
            linarith
      have hsphere : ∀ z ∈ sphere (0 : ℂ) R,
          ‖g z‖ ≤ 2 * B (2 * R + ‖c‖) + 3 * ‖f c‖ := by
        intro z hz
        have hznorm : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
        have hzball : z ∈ ball (0 : ℂ) (2 * R) := by
          rw [mem_ball_zero_iff, hznorm]
          linarith
        have hbc := Complex.borelCaratheodory hM hg.differentiableOn hgMaps
          houter hzball
        have hgzero : g 0 = f c := by simp [g]
        rw [hznorm, hgzero] at hbc
        convert hbc using 1 <;> field_simp <;> ring
      have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
        (f := g) 2 hR hg.diffContOnCl hsphere
      norm_num at hcauchy ⊢
      exact hcauchy
    have hle : ∀ᶠ R : ℝ in atTop,
        ‖iteratedDeriv 2 g 0‖ ≤
          2 * (2 * B (2 * R + ‖c‖) + 3 * ‖f c‖) / R ^ 2 := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
      exact hbound R hR
    have hlim : Tendsto
        (fun R : ℝ ↦
          2 * (2 * B (2 * R + ‖c‖) + 3 * ‖f c‖) / R ^ 2)
        atTop (nhds 0) := by
      simpa only [mul_div_assoc, mul_zero] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℝ ↦ (2 : ℝ)) atTop (nhds 2)).mul
            (hsub ‖c‖ (3 * ‖f c‖) (norm_nonneg c) (by positivity)))
    have hnormzero : ‖iteratedDeriv 2 g 0‖ = 0 := by
      apply le_antisymm
      · exact ge_of_tendsto hlim hle
      · exact norm_nonneg _
    have hgsecond : iteratedDeriv 2 g 0 = 0 := norm_eq_zero.mp hnormzero
    simpa [g, iteratedDeriv_comp_add_const] using hgsecond
  have hderiv2 : ∀ z : ℂ, deriv (deriv f) z = 0 := by
    intro z
    simpa [iteratedDeriv_succ] using hsecond z
  have hderivConst : ∀ z w : ℂ, deriv f z = deriv f w :=
    is_const_of_deriv_eq_zero hf.deriv hderiv2
  let a : ℂ := deriv f 0
  let q : ℂ → ℂ := fun z ↦ f z - a * z
  have hq : Differentiable ℂ q :=
    hf.sub ((differentiable_const a).mul differentiable_id)
  have hqderiv : ∀ z : ℂ, deriv q z = 0 := by
    intro z
    rw [show deriv q z = deriv f z - a by
      dsimp [q]
      have hlin : HasDerivAt (fun w : ℂ ↦ a * w) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      exact (hf.differentiableAt.hasDerivAt.sub hlin).deriv]
    exact sub_eq_zero.mpr (hderivConst z 0)
  have hqconst : ∀ z w : ℂ, q z = q w := is_const_of_deriv_eq_zero hq hqderiv
  refine ⟨a, q 0, fun z ↦ ?_⟩
  have := hqconst z 0
  dsimp [q] at this ⊢
  linear_combination this

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.affine_of_re_le_subquadratic
