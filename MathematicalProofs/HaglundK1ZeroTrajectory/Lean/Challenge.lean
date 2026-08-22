import Mathlib

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate

noncomputable section

namespace IncompleteGammaApproximant

def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  let a := Real.pi * (n + 1 : ℝ) ^ 2
  Real.exp (u / 2 - a * Real.exp (2 * u)) *
    (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u))

def Phi (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, phiTerm n u

def H (N : ℕ) (z : ℂ) : ℂ :=
  2 * ∫ u in Ioi (0 : ℝ),
    (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))

end IncompleteGammaApproximant

namespace HaglundK1ZeroTrajectory

open IncompleteGammaApproximant

def phiOne (z : ℂ) : ℂ := H 1 z

def phiTwo (z : ℂ) : ℂ := H 2 z - H 1 z

def pencil (z τ : ℂ) : ℂ := phiOne z + τ * phiTwo z

def realPencil (z : ℂ) (t : ℝ) : ℂ := pencil z (t : ℂ)

def delta (z : ℂ) (t : ℝ) : ℝ :=
  ((-phiTwo z) * conj (deriv (fun w => realPencil w t) z)).im

def parameterMap (z : ℂ) : ℂ := -phiOne z / phiTwo z

def phaseHeight (z : ℂ) : ℝ := -(phiOne z * conj (phiTwo z)).im

def zeroVelocity (z : ℂ) (t : ℝ) : ℂ :=
  -phiTwo z / deriv (fun w => realPencil w t) z

def levelNumerator (z : ℂ) : ℝ :=
  -(phiOne z * conj (phiTwo z)).re

def levelExcess (z : ℂ) : ℝ :=
  -((phiOne z + phiTwo z) * conj (phiTwo z)).re

def rawPhaseSlope (z : ℂ) : ℝ :=
  (deriv phiOne z * conj (phiTwo z) +
      phiOne z * conj (deriv phiTwo z)).im

def AtlasLeafConclusion (z : ℂ) : Prop :=
  phaseHeight z ≠ 0 ∨
  levelNumerator z < 0 ∨
  0 < levelExcess z ∨
  rawPhaseSlope z < 0

def AtlasCovers (S : Set ℂ) : Prop :=
  ∀ z ∈ S, phiTwo z ≠ 0 ∧ AtlasLeafConclusion z

def openFirstQuadrant : Set ℂ :=
  {z | 0 < z.re ∧ 0 < z.im}

def FirstQuadrantCertificate : Prop := AtlasCovers openFirstQuadrant

def InOuterCone (z : ℂ) : Prop :=
  256 ≤ ‖z‖ → (3 / 2 : ℝ) * Real.log ‖z‖ < z.im

theorem firstQuadrantCertificate_zero_simple_descending
    (hcert : FirstQuadrantCertificate) {z : ℂ}
    (hzre : 0 < z.re) (hzim : 0 < z.im) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hzero : realPencil z t = 0) :
    deriv (fun w => realPencil w t) z ≠ 0 ∧
      (zeroVelocity z t).im < 0 := by
  sorry

theorem realPencil_imaginaryAxis_ne_zero (y : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    realPencil (Complex.I * (y : ℂ)) t ≠ 0 := by
  sorry

theorem branch_uniformly_bounded
    (z : ℝ → ℂ) (I : Set ℝ) (H : ℝ)
    (him : ∀ t ∈ I, (z t).im ≤ H)
    (hcone : ∀ t ∈ I, InOuterCone (z t)) :
    ∀ t ∈ I, ‖z t‖ < max 256 (Real.exp (2 * H / 3)) := by
  sorry

theorem no_right_upper_emergence_of_scaled_limits
    {height velocity heightScale velocityScale : ℝ → ℝ}
    {heightCoeff velocityCoeff : ℝ}
    (hhc : 0 < heightCoeff) (hvc : 0 < velocityCoeff)
    (hhs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < heightScale s)
    (hvs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < velocityScale s)
    (hhlim : Tendsto (fun s => height s / heightScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 heightCoeff))
    (hvlim : Tendsto (fun s => velocity s / velocityScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 velocityCoeff))
    (hdescent : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      0 < height s → velocity s < 0) : False := by
  sorry

theorem exists_local_descending_zero_motion
    {z₀ : ℂ} {t₀ : ℝ}
    (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1)
    (hQ : phiTwo z₀ ≠ 0)
    (hleaf : AtlasLeafConclusion z₀)
    (hzero : realPencil z₀ t₀ = 0) :
    ∃ z : ℂ → ℂ,
      z (t₀ : ℂ) = z₀ ∧
      (∀ᶠ τ in 𝓝 (t₀ : ℂ), pencil (z τ) τ = 0) ∧
      HasStrictDerivAt z (zeroVelocity z₀ t₀) (t₀ : ℂ) ∧
      (∀ᶠ w in 𝓝 z₀, z (parameterMap w) = w) ∧
      (zeroVelocity z₀ t₀).im < 0 := by
  sorry

end HaglundK1ZeroTrajectory
