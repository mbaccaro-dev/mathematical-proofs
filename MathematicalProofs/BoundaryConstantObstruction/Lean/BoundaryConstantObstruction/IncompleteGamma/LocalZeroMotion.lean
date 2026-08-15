import BoundaryConstantObstruction.IncompleteGamma.Analysis
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Local motion of a simple zero

This module certifies the local-zero-motion remark in the paper.  It treats the
real shift parameter as the restriction of a complex parameter.  A simple zero
is inverted through the holomorphic map `z ↦ -H N z / boundaryConstant N`,
which gives both the local branch and its exact derivative.
-/

open Filter
open scoped Topology

namespace IncompleteGammaApproximant

/-- The complex shift parameter for which `z` is a zero of the shifted function. -/
noncomputable def zeroParameter (N : ℕ) (z : ℂ) : ℂ :=
  -H N z / (boundaryConstant N : ℂ)

/-- A simple zero of the shifted family has a locally unique holomorphic branch.
The two inverse identities are the local uniqueness certificate, and the strict
derivative is the printed motion formula. -/
theorem exists_local_zero_motion {N : ℕ} (hN : 1 ≤ N) {τ₀ z₀ : ℂ}
    (hzero : H N z₀ + τ₀ * (boundaryConstant N : ℂ) = 0)
    (hsimple : deriv (H N) z₀ ≠ 0) :
    ∃ z : ℂ → ℂ,
      z τ₀ = z₀ ∧
      (∀ᶠ τ in 𝓝 τ₀, H N (z τ) + τ * (boundaryConstant N : ℂ) = 0) ∧
      HasStrictDerivAt z (-(boundaryConstant N : ℂ) / deriv (H N) z₀) τ₀ ∧
      (∀ᶠ w in 𝓝 z₀, z (zeroParameter N w) = w) := by
  have hcR : boundaryConstant N ≠ 0 := ne_of_gt (boundaryConstant_pos hN)
  have hc : (boundaryConstant N : ℂ) ≠ 0 := by
    exact_mod_cast hcR
  have hcont : ContDiffAt ℂ 1 (H N) z₀ :=
    ((H_differentiable N).analyticAt z₀).contDiffAt
  have hstrictH : HasStrictDerivAt (H N) (deriv (H N) z₀) z₀ :=
    hcont.hasStrictDerivAt one_ne_zero
  have hstrictP :
      HasStrictDerivAt (fun z => zeroParameter N z)
        (-deriv (H N) z₀ / (boundaryConstant N : ℂ)) z₀ := by
    change HasStrictDerivAt (fun z => -H N z / (boundaryConstant N : ℂ))
      (-deriv (H N) z₀ / (boundaryConstant N : ℂ)) z₀
    exact hstrictH.neg.div_const (boundaryConstant N : ℂ)
  have hpne : -deriv (H N) z₀ / (boundaryConstant N : ℂ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hsimple) hc
  have hcenter : zeroParameter N z₀ = τ₀ := by
    apply (div_eq_iff hc).2
    linear_combination -hzero
  let z : ℂ → ℂ := hstrictP.localInverse (zeroParameter N)
    (-deriv (H N) z₀ / (boundaryConstant N : ℂ)) z₀ hpne
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · rw [← hcenter]
    exact (hstrictP.eventually_left_inverse hpne).self_of_nhds
  · have hr := hstrictP.eventually_right_inverse hpne
    rw [hcenter] at hr
    filter_upwards [hr] with τ hτ
    change zeroParameter N (z τ) = τ at hτ
    rw [zeroParameter] at hτ
    have hm : -H N (z τ) = τ * (boundaryConstant N : ℂ) :=
      (div_eq_iff hc).mp hτ
    linear_combination -hm
  · have hd := hstrictP.to_localInverse hpne
    rw [hcenter] at hd
    simpa [z, div_eq_mul_inv] using hd
  · exact hstrictP.eventually_left_inverse hpne

end IncompleteGammaApproximant
