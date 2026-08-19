import Mathlib.Tactic

/-!
# Finite conditioning kernel for the Selberg divisor-feedback paper

This module checks the exact algebra used after the manuscript's analytic
number-theory estimates have been established: direct centering, signed
positivity, scale normalization, two-sign output separation, and the final
Lipschitz quotient.  It does not formalize the prime number theorem, Selberg's
formula, the residual moment estimates, or the compact and hierarchy
asymptotics.
-/

open Real

namespace RiemannHypothesisProofFactory.SelbergConditioning

/-- Splitting a convergent coefficient sum at one distinguished chain makes
the correcting coefficient the negative of the remaining tail. -/
theorem distinguished_correction_eq_neg_tail
    (distinguished total tail : ℝ)
    (htotal : total = distinguished + tail) :
    distinguished - total = -tail := by
  rw [htotal]
  ring

/-- A relative coefficient bound and a small signed scale preserve strict
positivity for both signs.  This is the finite algebra behind positivity of
the plus and minus perturbations on every prime-power chain. -/
theorem signed_perturbations_pos
    (base perturbation scale coefficientBound : ℝ)
    (hbase : 0 < base)
    (hbound : |perturbation| ≤ coefficientBound * base)
    (hsmall : |scale| * coefficientBound < 1) :
    0 < base + scale * perturbation ∧
      0 < base - scale * perturbation := by
  have hcoefficientBound : 0 ≤ coefficientBound := by
    by_contra hnegative
    have : coefficientBound * base < 0 :=
      mul_neg_of_neg_of_pos (lt_of_not_ge hnegative) hbase
    exact (not_lt_of_ge (abs_nonneg perturbation)) (hbound.trans_lt this)
  have hscaled : |scale * perturbation| < base := by
    rw [abs_mul]
    calc
      |scale| * |perturbation| ≤
          |scale| * (coefficientBound * base) :=
        mul_le_mul_of_nonneg_left hbound (abs_nonneg scale)
      _ = (|scale| * coefficientBound) * base := by ring
      _ < 1 * base :=
        mul_lt_mul_of_pos_right hsmall hbase
      _ = base := one_mul base
  constructor
  · have hlower := neg_abs_le (scale * perturbation)
    linarith
  · have hupper := le_abs_self (scale * perturbation)
    linarith

/-- Normalizing a residual by `tau / (C * ell)` converts the pointwise
`C * ell` bound into the exact tolerance `tau`. -/
theorem scaled_residual_le_tolerance
    (residual tau coefficientBound ell : ℝ)
    (htau : 0 ≤ tau)
    (hcoefficientBound : 0 < coefficientBound)
    (hell : 0 < ell)
    (hresidual : |residual| ≤ coefficientBound * ell) :
    |(tau / (coefficientBound * ell)) * residual| ≤ tau := by
  have hden : 0 < coefficientBound * ell :=
    mul_pos hcoefficientBound hell
  have hscale : 0 ≤ tau / (coefficientBound * ell) :=
    div_nonneg htau hden.le
  rw [abs_mul, abs_of_nonneg hscale]
  calc
    tau / (coefficientBound * ell) * |residual| ≤
        tau / (coefficientBound * ell) * (coefficientBound * ell) :=
      mul_le_mul_of_nonneg_left hresidual hscale
    _ = tau := by field_simp

/-- A lower bound for the fixed perturbation sum becomes the exact two-sign
output separation printed in the conditioning theorem after scale
normalization. -/
theorem scaled_two_sign_separation
    (rho tau coefficientBound ell xPow signedSum : ℝ)
    (hrho : 0 < rho)
    (htau : 0 ≤ tau)
    (hcoefficientBound : 0 < coefficientBound)
    (hell : 0 < ell)
    (hsignedSum : xPow / (2 * rho) ≤ |signedSum|) :
    tau * xPow / (rho * coefficientBound * ell) ≤
      |(tau / (coefficientBound * ell)) * signedSum -
        (-(tau / (coefficientBound * ell)) * signedSum)| := by
  have hden : 0 < coefficientBound * ell :=
    mul_pos hcoefficientBound hell
  have hscale : 0 ≤ tau / (coefficientBound * ell) :=
    div_nonneg htau hden.le
  have htwoScale : 0 ≤ 2 * (tau / (coefficientBound * ell)) :=
    mul_nonneg (by norm_num) hscale
  calc
    tau * xPow / (rho * coefficientBound * ell) =
        (2 * (tau / (coefficientBound * ell))) * (xPow / (2 * rho)) := by
      field_simp
    _ ≤ (2 * (tau / (coefficientBound * ell))) * |signedSum| :=
      mul_le_mul_of_nonneg_left hsignedSum htwoScale
    _ = |(tau / (coefficientBound * ell)) * signedSum -
        (-(tau / (coefficientBound * ell)) * signedSum)| := by
      rw [show (tau / (coefficientBound * ell)) * signedSum -
          (-(tau / (coefficientBound * ell)) * signedSum) =
          (2 * (tau / (coefficientBound * ell))) * signedSum by ring,
        abs_mul, abs_of_nonneg htwoScale]

/-- If an exact recovery map is Lipschitz on the constructed pair, the input
diameter and output separation force the paper's lower bound on its Lipschitz
constant. -/
theorem lipschitz_constant_lower_bound
    (rho tau coefficientBound ell xPow outputPlus outputMinus
      inputDistance lipschitzConstant : ℝ)
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (hcoefficientBound : 0 < coefficientBound)
    (hell : 0 < ell)
    (hinputDistance : inputDistance ≤ 2 * tau)
    (hlipschitzNonneg : 0 ≤ lipschitzConstant)
    (houtput : tau * xPow / (rho * coefficientBound * ell) ≤
      |outputPlus - outputMinus|)
    (hlipschitz : |outputPlus - outputMinus| ≤
      lipschitzConstant * inputDistance) :
    xPow / (2 * rho * coefficientBound * ell) ≤ lipschitzConstant := by
  have hchain : tau * xPow / (rho * coefficientBound * ell) ≤
      lipschitzConstant * (2 * tau) := by
    calc
      tau * xPow / (rho * coefficientBound * ell) ≤
          |outputPlus - outputMinus| := houtput
      _ ≤ lipschitzConstant * inputDistance := hlipschitz
      _ ≤ lipschitzConstant * (2 * tau) :=
        mul_le_mul_of_nonneg_left hinputDistance hlipschitzNonneg
  have htwoTau : 0 < 2 * tau := mul_pos (by norm_num) htau
  calc
    xPow / (2 * rho * coefficientBound * ell) =
        (tau * xPow / (rho * coefficientBound * ell)) / (2 * tau) := by
      field_simp
    _ ≤ lipschitzConstant := (div_le_iff₀ htwoTau).2 hchain

#print axioms distinguished_correction_eq_neg_tail
#print axioms signed_perturbations_pos
#print axioms scaled_residual_le_tolerance
#print axioms scaled_two_sign_separation
#print axioms lipschitz_constant_lower_bound

end RiemannHypothesisProofFactory.SelbergConditioning
