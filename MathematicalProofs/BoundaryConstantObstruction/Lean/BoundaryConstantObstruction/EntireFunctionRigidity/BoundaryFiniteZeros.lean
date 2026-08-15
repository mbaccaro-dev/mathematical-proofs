import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.RCLike

open Filter Function Set Topology

namespace EntireFunctionRigidity

/-- A nonzero entire function has finite meromorphic order at every point.
This is the local-order side condition needed by the finite-zero divisor
factorization. -/
theorem meromorphicOrderAt_ne_top_of_entire_of_exists_ne_zero
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (hF0 : ∃ z, F z ≠ 0) :
    ∀ z, meromorphicOrderAt F z ≠ ⊤ := by
  have hmer : Meromorphic F :=
    meromorphicOn_univ.mp
      (hF.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn
  rw [← hmer.exists_meromorphicOrderAt_ne_top_iff_forall]
  obtain ⟨z, hz⟩ := hF0
  exact ⟨z, (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmer z)).2
    (((hF z).continuousAt.eventually_ne hz).filter_mono nhdsWithin_le_nhds)⟩

/-- If every zero of a nonzero entire function lies in a fixed compact set,
then its zero set is finite. -/
theorem finite_zero_set_of_compact_bound
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {z₀ : ℂ} (hz₀ : F z₀ ≠ 0)
    {K : Set ℂ} (hK : IsCompact K)
    (hbound : {z | F z = 0} ⊆ K) :
    {z | F z = 0}.Finite := by
  have hco : {z | F z ≠ 0} ∈ codiscrete ℂ := by
    simpa only [preimage, mem_singleton_iff, mem_compl_iff] using
      AnalyticOnNhd.preimage_zero_mem_codiscrete
        (hF.differentiableOn.analyticOnNhd isOpen_univ) hz₀
  have hcoK : {z | F z ≠ 0} ∈ codiscreteWithin K :=
    Filter.codiscreteWithin_mono (Set.subset_univ K) hco
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcoK).subset fun z hz ↦
    ⟨hbound hz, by simpa using hz⟩

/-- If an entire function has nonzero limits on both real tails, then under
the supposition that all its zeros are real, its full complex zero set is
finite.  This packages exactly the compact-zero step in the manuscript. -/
theorem finite_zero_set_of_real_zeros_and_two_sided_nonzero_limits
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {Lpos Lneg : ℂ}
    (hlimTop : Tendsto (fun x : ℝ ↦ F x) atTop (nhds Lpos))
    (hlimBot : Tendsto (fun x : ℝ ↦ F x) atBot (nhds Lneg))
    (hLpos : Lpos ≠ 0) (hLneg : Lneg ≠ 0)
    (hreal : ∀ z : ℂ, F z = 0 → z.im = 0) :
    {z : ℂ | F z = 0}.Finite := by
  have htop : ∀ᶠ x : ℝ in atTop, F x ≠ 0 := hlimTop.eventually_ne hLpos
  have hbot : ∀ᶠ x : ℝ in atBot, F x ≠ 0 := hlimBot.eventually_ne hLneg
  obtain ⟨A, hA⟩ := eventually_atTop.mp htop
  obtain ⟨B, hB⟩ := eventually_atBot.mp hbot
  have hnonzero : ∃ z : ℂ, F z ≠ 0 := by
    obtain ⟨x, hx⟩ := htop.exists
    exact ⟨x, hx⟩
  obtain ⟨z₀, hz₀⟩ := hnonzero
  let R : ℝ := max |A| |B|
  let K : Set ℂ := ((↑) : ℝ → ℂ) '' Set.Icc (-R) R
  apply finite_zero_set_of_compact_bound hF hz₀
    (isCompact_Icc.image Complex.continuous_ofReal : IsCompact K)
  intro z hz
  have him : z.im = 0 := hreal z hz
  have hzreal : (z.re : ℂ) = z := by
    apply Complex.ext
    · simp
    · simpa [him]
  have hFreal : F (z.re : ℂ) = 0 := by simpa [hzreal] using hz
  have hzA : z.re < A := by
    apply lt_of_not_ge
    intro hAz
    exact (hA z.re hAz) hFreal
  have hBz : B < z.re := by
    apply lt_of_not_ge
    intro hzB
    exact (hB z.re hzB) hFreal
  refine ⟨z.re, ⟨?_, ?_⟩, hzreal⟩
  · calc
      -R ≤ -|B| := neg_le_neg (le_max_right |A| |B|)
      _ ≤ B := neg_abs_le B
      _ ≤ z.re := le_of_lt hBz
  · calc
      z.re ≤ A := le_of_lt hzA
      _ ≤ |A| := le_abs_self A
      _ ≤ R := le_max_left |A| |B|

end EntireFunctionRigidity

#print axioms EntireFunctionRigidity.meromorphicOrderAt_ne_top_of_entire_of_exists_ne_zero
#print axioms EntireFunctionRigidity.finite_zero_set_of_compact_bound
#print axioms EntireFunctionRigidity.finite_zero_set_of_real_zeros_and_two_sided_nonzero_limits
