import RiemannHypothesisProofFactory.SelbergConditioning.FiniteKernel

/-!
# Finite two-sign conditioning witness

This module packages the paper's finite conditioning argument as one theorem.
The analytic construction supplies its residual and signed-sum hypotheses;
Lean checks the exact normalization, separation, and Lipschitz conclusion.
-/

namespace RiemannHypothesisProofFactory.SelbergConditioning

theorem finite_two_sign_conditioning_obstruction
    (rho tau coefficientBound ell xPow signedSum
      residualPlus residualMinus inputDistance lipschitzConstant : ℝ)
    (hrho : 0 < rho)
    (htau : 0 < tau)
    (hcoefficientBound : 0 < coefficientBound)
    (hell : 0 < ell)
    (hresidualPlus : |residualPlus| ≤ coefficientBound * ell)
    (hresidualMinus : |residualMinus| ≤ coefficientBound * ell)
    (hsignedSum : xPow / (2 * rho) ≤ |signedSum|)
    (hinputDistance : inputDistance ≤ 2 * tau)
    (hlipschitzNonneg : 0 ≤ lipschitzConstant)
    (hlipschitz :
      |(tau / (coefficientBound * ell)) * signedSum -
          (-(tau / (coefficientBound * ell)) * signedSum)| ≤
        lipschitzConstant * inputDistance) :
    |(tau / (coefficientBound * ell)) * residualPlus| ≤ tau ∧
      |(tau / (coefficientBound * ell)) * residualMinus| ≤ tau ∧
      tau * xPow / (rho * coefficientBound * ell) ≤
        |(tau / (coefficientBound * ell)) * signedSum -
          (-(tau / (coefficientBound * ell)) * signedSum)| ∧
      xPow / (2 * rho * coefficientBound * ell) ≤ lipschitzConstant := by
  have hplus := scaled_residual_le_tolerance residualPlus tau
    coefficientBound ell htau.le hcoefficientBound hell hresidualPlus
  have hminus := scaled_residual_le_tolerance residualMinus tau
    coefficientBound ell htau.le hcoefficientBound hell hresidualMinus
  have hseparation := scaled_two_sign_separation rho tau coefficientBound ell
    xPow signedSum hrho htau.le hcoefficientBound hell hsignedSum
  have hlower := lipschitz_constant_lower_bound rho tau coefficientBound ell
    xPow ((tau / (coefficientBound * ell)) * signedSum)
    (-(tau / (coefficientBound * ell)) * signedSum) inputDistance
    lipschitzConstant hrho htau hcoefficientBound hell hinputDistance
    hlipschitzNonneg hseparation hlipschitz
  exact ⟨hplus, hminus, hseparation, hlower⟩

end RiemannHypothesisProofFactory.SelbergConditioning
