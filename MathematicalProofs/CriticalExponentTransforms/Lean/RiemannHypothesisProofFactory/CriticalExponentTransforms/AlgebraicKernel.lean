import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Algebraic kernel for the critical-exponent transform paper

This module checks exact exponent-gap identities, the scalar pure-power
normal form, saturation inversion, and the inverse-symbol lower bound used in
the manuscript. It does not formalize the Abel integral; the vector-valued
multilinear expansion and its asymptotics; the phase-orbit normal form and
periodic block-energy lemma; the operator-level pure-power derivation; the
complex-measure Mellin theorem; the saturation pure-power formula and connector
inequality; the two-sided-germ comparison; or dyadic energy asymptotics.
-/

open Real

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

/-- The orderwise multilinear exponent gap printed in the manuscript. -/
theorem multilinear_gap_identity
    (d r sigma rho kappa : ℝ) :
    ((d - r) * sigma + r * rho - kappa) -
        ((d - r) * sigma + r / 2 - kappa) =
      r * (rho - 1 / 2) := by
  ring

/-- Adjacent multilinear mixture exponents strictly decrease when the
baseline exponent is larger than the perturbation exponent. -/
theorem multilinear_successive_exponent_lt
    (d r sigma rho kappa : ℝ)
    (hsigmaRho : rho < sigma) :
    (d - (r + 1)) * sigma + (r + 1) * rho - kappa <
      (d - r) * sigma + r * rho - kappa := by
  nlinarith

/-- Adjacent multilinear orders are separated by the baseline--perturbation
gap. -/
theorem multilinear_adjacent_gap_identity
    (d r sigma rho kappa : ℝ) :
    ((d - r) * sigma + r * rho - kappa) -
        ((d - (r + 1)) * sigma + (r + 1) * rho - kappa) =
      sigma - rho := by
  ring

/-- The common positive-homogeneous and phase-orbit exponent gap. -/
theorem homogeneous_gap_identity
    (q beta kappa : ℝ) :
    (q * beta - kappa) - (q / 2 - kappa) =
      q * (beta - 1 / 2) := by
  ring

/-- The scalar-valued pure-power normal form follows from the specialized
homogeneity/covariance identity by division by the nonzero dilation weight. -/
theorem scalar_pure_power_normal_form
    (g v x q rho kappa : ℝ)
    (hx : 0 < x)
    (hscale : x ^ (q * rho) * v = x ^ kappa * g) :
    g = x ^ (q * rho - kappa) * v := by
  have hkappa : x ^ kappa ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx kappa)
  calc
    g = (x ^ (q * rho) * v) / x ^ kappa := by
      apply (eq_div_iff hkappa).2
      simpa [mul_comm] using hscale.symm
    _ = (x ^ (q * rho) / x ^ kappa) * v := by ring
    _ = x ^ (q * rho - kappa) * v := by
      rw [Real.rpow_sub hx (q * rho) kappa]

/-- The normalized saturation exponent has the same relative gap. -/
theorem saturation_gap_identity (rho : ℝ) :
    (rho - 1) - (-1 / 2) = rho - 1 / 2 := by
  ring

/-- The two-sided power-germ exponent gap. -/
theorem germ_gap_identity (q rho : ℝ) :
    q * (rho - 1) - (-q / 2) = q * (rho - 1 / 2) := by
  ring

/-- The paper's canonical bounded saturation. -/
noncomputable def saturation (E x : ℝ) : ℝ := E / (x + |E|)

/-- Positive spatial scale keeps the saturation strictly inside the unit
interval. -/
theorem abs_saturation_lt_one
    (E x : ℝ) (hx : 0 < x) :
    |saturation E x| < 1 := by
  have hden : 0 < x + |E| := by positivity
  rw [saturation, abs_div, abs_of_pos hden]
  exact (div_lt_one hden).2 (by linarith [abs_nonneg E])

/-- The saturation is exactly invertible at every positive spatial scale. -/
theorem saturation_inverse
    (E x : ℝ) (hx : 0 < x) :
    x * saturation E x / (1 - |saturation E x|) = E := by
  have hden : 0 < x + |E| := by positivity
  have hratio : |E| / (x + |E|) < 1 :=
    (div_lt_one hden).2 (by linarith [abs_nonneg E])
  rw [saturation, abs_div, abs_of_pos hden]
  have hnonzero : 1 - |E| / (x + |E|) ≠ 0 := by linarith
  field_simp [ne_of_gt hx]
  ring

/-- A bounded inverse symbol supplies the lower modulus bound used in the
Mellin observability theorem. -/
theorem inverse_symbol_lower_bound
    (Mnu Meta : ℂ) (Aeta : ℝ)
    (hAeta : 0 < Aeta)
    (hproduct : Meta * Mnu = 1)
    (hupper : ‖Meta‖ ≤ Aeta) :
    1 / Aeta ≤ ‖Mnu‖ := by
  have hone : 1 = ‖Meta‖ * ‖Mnu‖ := by
    rw [← norm_mul, hproduct, norm_one]
  apply (div_le_iff₀ hAeta).2
  calc
    1 = ‖Meta‖ * ‖Mnu‖ := hone
    _ ≤ Aeta * ‖Mnu‖ :=
      mul_le_mul_of_nonneg_right hupper (norm_nonneg Mnu)
    _ = ‖Mnu‖ * Aeta := by ring

#print axioms multilinear_gap_identity
#print axioms multilinear_successive_exponent_lt
#print axioms multilinear_adjacent_gap_identity
#print axioms homogeneous_gap_identity
#print axioms scalar_pure_power_normal_form
#print axioms saturation_gap_identity
#print axioms germ_gap_identity
#print axioms abs_saturation_lt_one
#print axioms saturation_inverse
#print axioms inverse_symbol_lower_bound

end RiemannHypothesisProofFactory.CriticalExponentTransforms
