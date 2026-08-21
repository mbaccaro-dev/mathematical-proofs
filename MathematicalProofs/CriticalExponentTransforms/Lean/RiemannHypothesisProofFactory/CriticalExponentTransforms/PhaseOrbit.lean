import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

/-- A phase profile is the value at logarithmic radius zero of a phase-indexed
output orbit. -/
def phaseProfile {V : Type*} (g : ℝ → ℝ → V) (theta : ℝ) : V :=
  g theta 0

/-- Energy in one dyadic block after the radial variable is changed to its
logarithm. -/
noncomputable def logDyadicEnergy {V : Type*} [NormedAddCommGroup V]
    (g : ℝ → ℝ → V) (theta y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.log 2, ‖g theta (y + u)‖ ^ 2

/-- The phase-dependent block profile left after the radial power has been
factored out. -/
noncomputable def phaseBlockEnergy {V : Type*} [NormedAddCommGroup V]
    (A : ℝ → V) (alpha gamma delta : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.log 2,
    Real.exp (2 * alpha * u) * ‖A (delta + gamma * u)‖ ^ 2

/-- The covariance identity for a homogeneous phase orbit forces its complete
logarithmic normal form, periodic profile, norm law, and strict off-critical
radial gap. -/
theorem phase_orbit_normal_form
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ℝ → ℝ → V) (U : ℝ → V ≃ₗᵢ[ℝ] V)
    (q beta gamma kappa : ℝ)
    (hperiodic : ∀ theta t, g (theta + 2 * Real.pi) t = g theta t)
    (hcov : ∀ theta t,
      (Real.exp (q * beta * t)) • g (theta + gamma * t) 0 =
        (Real.exp (kappa * t)) • U t (g theta t))
    (hq : 0 < q) (hbeta : (1 : ℝ) / 2 < beta) :
    (∀ theta t,
      g theta t =
        (Real.exp ((q * beta - kappa) * t)) •
          (U t).symm (phaseProfile g (theta + gamma * t))) ∧
    (∀ theta,
      phaseProfile g (theta + 2 * Real.pi) = phaseProfile g theta) ∧
    (∀ theta t,
      ‖g theta t‖ =
        Real.exp ((q * beta - kappa) * t) *
          ‖phaseProfile g (theta + gamma * t)‖) ∧
    0 < (q * beta - kappa) - (q / 2 - kappa) := by
  have hnormal : ∀ theta t,
      g theta t =
        (Real.exp ((q * beta - kappa) * t)) •
          (U t).symm (phaseProfile g (theta + gamma * t)) := by
    intro theta t
    have h := congrArg (fun v : V ↦ (U t).symm v) (hcov theta t)
    simp only [map_smul, LinearIsometryEquiv.symm_apply_apply] at h
    rw [show g (theta + gamma * t) 0 =
        phaseProfile g (theta + gamma * t) by rfl] at h
    calc
      g theta t = (Real.exp (kappa * t))⁻¹ •
          ((Real.exp (kappa * t)) • g theta t) := by
        simp [Real.exp_ne_zero]
      _ = (Real.exp (kappa * t))⁻¹ •
          ((Real.exp (q * beta * t)) •
            (U t).symm (phaseProfile g (theta + gamma * t))) := by
        rw [← h]
      _ = ((Real.exp (kappa * t))⁻¹ * Real.exp (q * beta * t)) •
          (U t).symm (phaseProfile g (theta + gamma * t)) := by
        rw [smul_smul]
      _ = (Real.exp ((q * beta - kappa) * t)) •
          (U t).symm (phaseProfile g (theta + gamma * t)) := by
        congr 1
        rw [show (q * beta - kappa) * t =
            q * beta * t - kappa * t by ring, Real.exp_sub]
        field_simp
  refine ⟨hnormal, ?_, ?_, ?_⟩
  · intro theta
    exact hperiodic theta 0
  · intro theta t
    rw [hnormal theta t, norm_smul]
    simp
  · nlinarith

#print axioms phase_orbit_normal_form

/-- The normal form reduces every logarithmic dyadic block to an explicit
radial power times a periodic phase profile. -/
theorem log_dyadic_energy_reduction
    {V : Type*} [NormedAddCommGroup V]
    (g : ℝ → ℝ → V) (A : ℝ → V)
    (alpha gamma theta y : ℝ)
    (hnorm : ∀ theta t,
      ‖g theta t‖ = Real.exp (alpha * t) * ‖A (theta + gamma * t)‖) :
    logDyadicEnergy g theta y =
      Real.exp (2 * alpha * y) *
        phaseBlockEnergy A alpha gamma (theta + gamma * y) := by
  unfold logDyadicEnergy phaseBlockEnergy
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [hnorm]
  have hphase : theta + gamma * (y + u) =
      theta + gamma * y + gamma * u := by ring
  rw [hphase]
  rw [show alpha * (y + u) = alpha * y + alpha * u by ring,
    Real.exp_add]
  have hey : Real.exp (alpha * y) ^ 2 = Real.exp (2 * alpha * y) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have heu : Real.exp (alpha * u) ^ 2 = Real.exp (2 * alpha * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  ring_nf
  rw [hey, heu]
  ring

/-- A full turn of the phase leaves the reduced block profile unchanged. -/
theorem phase_block_energy_periodic
    {V : Type*} [NormedAddCommGroup V]
    (A : ℝ → V) (alpha gamma delta : ℝ)
    (hperiodic : ∀ theta, A (theta + 2 * Real.pi) = A theta) :
    phaseBlockEnergy A alpha gamma (delta + 2 * Real.pi) =
      phaseBlockEnergy A alpha gamma delta := by
  unfold phaseBlockEnergy
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  have hphase : delta + 2 * Real.pi + gamma * u =
      (delta + gamma * u) + 2 * Real.pi := by ring
  rw [hphase, hperiodic]

/-- If a logarithmic shift advances the phase by one full turn, consecutive
dyadic-block energies satisfy an exact geometric recurrence. -/
theorem phase_orbit_energy_recurrence
    {V : Type*} [NormedAddCommGroup V]
    (g : ℝ → ℝ → V) (A : ℝ → V)
    (alpha gamma theta y T : ℝ)
    (hnorm : ∀ theta t,
      ‖g theta t‖ = Real.exp (alpha * t) * ‖A (theta + gamma * t)‖)
    (hperiodic : ∀ theta, A (theta + 2 * Real.pi) = A theta)
    (hturn : gamma * T = 2 * Real.pi) :
    logDyadicEnergy g theta (y + T) =
      Real.exp (2 * alpha * T) * logDyadicEnergy g theta y := by
  rw [log_dyadic_energy_reduction (g := g) (A := A) alpha gamma theta (y + T) hnorm,
    log_dyadic_energy_reduction (g := g) (A := A) alpha gamma theta y hnorm]
  have hphase : theta + gamma * (y + T) =
      (theta + gamma * y) + 2 * Real.pi := by
    rw [mul_add, hturn]
    ring
  rw [hphase, phase_block_energy_periodic A alpha gamma
    (theta + gamma * y) hperiodic]
  rw [show 2 * alpha * (y + T) = 2 * alpha * T + 2 * alpha * y by ring,
    Real.exp_add]
  ring

/-- Exact covariance and one visible block give the phase-orbit normal form,
the off-critical exponent gap, and a nonzero geometric dyadic-energy law after
every prescribed full phase turn. -/
theorem phase_orbit_full_turn_energy_law
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (g : ℝ → ℝ → V) (U : ℝ → V ≃ₗᵢ[ℝ] V)
    (q beta gamma kappa T : ℝ)
    (hperiodic : ∀ theta t, g (theta + 2 * Real.pi) t = g theta t)
    (hcov : ∀ theta t,
      (Real.exp (q * beta * t)) • g (theta + gamma * t) 0 =
        (Real.exp (kappa * t)) • U t (g theta t))
    (hq : 0 < q) (hbeta : (1 : ℝ) / 2 < beta)
    (hturn : gamma * T = 2 * Real.pi)
    (hvisible : ∃ theta y, 0 < logDyadicEnergy g theta y) :
    ((∀ theta t,
      g theta t =
        (Real.exp ((q * beta - kappa) * t)) •
          (U t).symm (phaseProfile g (theta + gamma * t))) ∧
    (∀ theta,
      phaseProfile g (theta + 2 * Real.pi) = phaseProfile g theta) ∧
    (∀ theta t,
      ‖g theta t‖ =
        Real.exp ((q * beta - kappa) * t) *
          ‖phaseProfile g (theta + gamma * t)‖) ∧
    0 < (q * beta - kappa) - (q / 2 - kappa)) ∧
    (∀ theta y,
      logDyadicEnergy g theta (y + T) =
        Real.exp (2 * (q * beta - kappa) * T) *
          logDyadicEnergy g theta y) ∧
    ∃ theta y,
      0 < logDyadicEnergy g theta y ∧
      0 < logDyadicEnergy g theta (y + T) := by
  have hnormal := phase_orbit_normal_form g U q beta gamma kappa
    hperiodic hcov hq hbeta
  have hrec : ∀ theta y,
      logDyadicEnergy g theta (y + T) =
        Real.exp (2 * (q * beta - kappa) * T) *
          logDyadicEnergy g theta y := by
    intro theta y
    exact phase_orbit_energy_recurrence g (phaseProfile g)
      (q * beta - kappa) gamma theta y T hnormal.2.2.1 hnormal.2.1 hturn
  rcases hvisible with ⟨theta, y, hy⟩
  refine ⟨hnormal, hrec, theta, y, hy, ?_⟩
  rw [hrec theta y]
  exact mul_pos (Real.exp_pos _) hy

#print axioms log_dyadic_energy_reduction
#print axioms phase_orbit_energy_recurrence
#print axioms phase_orbit_full_turn_energy_law

end RiemannHypothesisProofFactory.CriticalExponentTransforms
