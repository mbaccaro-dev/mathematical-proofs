import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Polynomial.Basic

open Filter Function Set Topology

namespace EntireFunctionRigidity

/-- Extract all zeros of a nonzero entire function when its zero set is
finite.  The returned factorized rational function is in fact entire because
the divisor is nonnegative.  Unlike `MeromorphicOn.extract_zeros_poles`, the
factorization here is pointwise on all of `ℂ`, not merely codiscrete. -/
theorem exists_zero_free_factorization_of_finite_zero_set
    (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F univ)
    (hnotop : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (hzeros : {z : ℂ | F z = 0}.Finite) :
    ∃ D : ℂ → ℤ, ∃ g : ℂ → ℂ,
      D.support.Finite ∧
      (∀ z : ℂ, 0 ≤ D z) ∧
      AnalyticOnNhd ℂ g univ ∧
      (∀ z : ℂ, g z ≠ 0) ∧
      ∀ z : ℂ, F z = (∏ᶠ u, (z - u) ^ D u) * g z := by
  let D := MeromorphicOn.divisor F univ
  change (F ⁻¹' ({0} : Set ℂ)).Finite at hzeros
  have hDfinite : D.support.Finite := by
    have hzeroSupport : F ⁻¹' ({0} : Set ℂ) = D.support := by
      simpa [D] using hF.meromorphicNFOn.zero_set_eq_divisor_support
        (fun u : (univ : Set ℂ) ↦ hnotop u)
    rw [← hzeroSupport]
    exact hzeros
  have hDnonneg : ∀ z : ℂ, 0 ≤ D z := by
    exact fun z ↦ MeromorphicOn.AnalyticOnNhd.divisor_nonneg hF z
  obtain ⟨g, hg, hgne, hEq⟩ :=
    hF.meromorphicOn.extract_zeros_poles
      (fun u : (univ : Set ℂ) ↦ hnotop u) hDfinite
  have hphi : AnalyticOnNhd ℂ (∏ᶠ u, (· - u) ^ D u) univ := by
    intro z _
    exact Function.FactorizedRational.analyticAt (hDnonneg z)
  have hrhs : AnalyticOnNhd ℂ ((∏ᶠ u, (· - u) ^ D u) • g) univ :=
    hphi.smul hg
  have hEq0 : F =ᶠ[𝓝[≠] (0 : ℂ)] ((∏ᶠ u, (· - u) ^ D u) • g) :=
    by
      change {x | F x = ((∏ᶠ u, (· - u) ^ D u) • g) x} ∈ 𝓝[≠] (0 : ℂ)
      simpa [D] using
        (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hEq) 0 (mem_univ 0)
  have hPointwise : F = ((∏ᶠ u, (· - u) ^ D u) • g) :=
    hF.eq_of_frequently_eq hrhs hEq0.frequently
  refine ⟨D, g, hDfinite, hDnonneg, hg, ?_, ?_⟩
  · intro z
    simpa using hgne ⟨z, mem_univ z⟩
  · intro z
    have hz := congrFun hPointwise z
    simpa [Function.FactorizedRational.finprod_eq_fun hDfinite] using hz

/-- Package the finite nonnegative divisor extracted above as an ordinary
polynomial.  This is the exact finite-zero factor needed by the manuscript's
Hadamard step; no infinite product or choice of root enumeration remains. -/
theorem exists_polynomial_zero_free_factorization_of_finite_zero_set
    (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F univ)
    (hnotop : ∀ z : ℂ, meromorphicOrderAt F z ≠ ⊤)
    (hzeros : {z : ℂ | F z = 0}.Finite) :
    ∃ P : Polynomial ℂ, ∃ g : ℂ → ℂ,
      P.Monic ∧
      P ≠ 0 ∧
      AnalyticOnNhd ℂ g univ ∧
      (∀ z : ℂ, g z ≠ 0) ∧
      ∀ z : ℂ, F z = P.eval z * g z := by
  obtain ⟨D, g, hDfinite, hDnonneg, hg, hgne, hfactor⟩ :=
    exists_zero_free_factorization_of_finite_zero_set F hF hnotop hzeros
  let P : Polynomial ℂ :=
    ∏ u ∈ hDfinite.toFinset,
      (Polynomial.X - Polynomial.C u) ^ (D u).toNat
  have hPmonic : P.Monic := by
    dsimp [P]
    exact Polynomial.monic_prod_of_monic _ _ fun u _ ↦
      (Polynomial.monic_X_sub_C u).pow _
  refine ⟨P, g, hPmonic, hPmonic.ne_zero, hg, hgne, ?_⟩
  intro z
  rw [hfactor]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset
    (s := hDfinite.toFinset)]
  · simp only [P, Polynomial.eval_prod, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    apply Finset.prod_congr rfl
    intro u hu
    rw [← zpow_natCast, Int.toNat_of_nonneg (hDnonneg u)]
  · intro u hu
    exact hDfinite.mem_toFinset.mpr (by
      rw [Function.mem_support]
      by_contra hDu
      simp [hDu] at hu)

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.exists_zero_free_factorization_of_finite_zero_set
#print axioms EntireFunctionRigidity.exists_polynomial_zero_free_factorization_of_finite_zero_set
