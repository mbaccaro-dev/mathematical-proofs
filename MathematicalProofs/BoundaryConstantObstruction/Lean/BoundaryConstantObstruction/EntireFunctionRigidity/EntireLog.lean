import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Filter Set Topology

namespace EntireFunctionRigidity

/-- A zero-free entire function has an entire logarithm.  This is proved from
the primitive of its logarithmic derivative, so no branch-cut assumption is
introduced. -/
theorem exists_differentiable_log_of_ne_zero
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (hgne : ∀ z : ℂ, g z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, Differentiable ℂ ℓ ∧ ∀ z : ℂ, Complex.exp (ℓ z) = g z := by
  let q : ℂ → ℂ := fun z ↦ deriv g z / g z
  have hq : Differentiable ℂ q := by
    dsimp [q]
    exact hg.deriv.div hg hgne
  obtain ⟨p, hp⟩ := hq.isExactOn_univ
  have hp' : ∀ z : ℂ, HasDerivAt p (q z) z := fun z ↦ hp z (mem_univ z)
  have hpdiff : Differentiable ℂ p := fun z ↦ (hp' z).differentiableAt
  let k : ℂ → ℂ := fun z ↦ g z * Complex.exp (-p z)
  have hkdiff : Differentiable ℂ k := by
    dsimp [k]
    fun_prop
  have hkderiv : ∀ z : ℂ, deriv k z = 0 := by
    intro z
    have hneg : HasDerivAt (fun w : ℂ ↦ -p w) (-q z) z := (hp' z).neg
    have hexp : HasDerivAt (fun w : ℂ ↦ Complex.exp (-p w))
        (Complex.exp (-p z) * (-q z)) z :=
      (Complex.hasDerivAt_exp (-p z)).comp z hneg
    have hmul := hg.differentiableAt.hasDerivAt.mul hexp
    have hkformula : deriv k z =
        deriv g z * Complex.exp (-p z) +
          g z * (Complex.exp (-p z) * (-q z)) := by
      exact hmul.deriv
    rw [hkformula]
    dsimp [q]
    field_simp [hgne z, Complex.exp_ne_zero]
    ring
  have hkconst : ∀ z w : ℂ, k z = k w :=
    is_const_of_deriv_eq_zero hkdiff hkderiv
  let c : ℂ := k 0
  have hcne : c ≠ 0 := by
    dsimp [c, k]
    exact mul_ne_zero (hgne 0) (Complex.exp_ne_zero _)
  let ℓ : ℂ → ℂ := fun z ↦ p z + Complex.log c
  have hℓdiff : Differentiable ℂ ℓ := hpdiff.add_const _
  refine ⟨ℓ, hℓdiff, fun z ↦ ?_⟩
  have hkz : g z * Complex.exp (-p z) = c := by
    simpa [k, c] using hkconst z 0
  calc
    Complex.exp (ℓ z) = Complex.exp (p z) * Complex.exp (Complex.log c) := by
      simp [ℓ, Complex.exp_add]
    _ = Complex.exp (p z) * c := by rw [Complex.exp_log hcne]
    _ = g z := by
      apply (mul_left_cancel₀ (Complex.exp_ne_zero (-p z)))
      rw [← mul_assoc, ← Complex.exp_add]
      simpa [mul_comm] using hkz.symm

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.exists_differentiable_log_of_ne_zero
