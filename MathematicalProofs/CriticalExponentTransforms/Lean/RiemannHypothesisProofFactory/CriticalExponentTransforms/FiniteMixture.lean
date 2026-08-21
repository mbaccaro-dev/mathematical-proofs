import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Leading term of a finite critical-exponent mixture

This module formalizes the analytic selection step in the paper's finite
multilinear mixture theorem.  When the baseline exponent is larger than the
perturbation exponent, successive mixture orders have strictly decreasing
radial exponents.  After normalization by the first nonzero order, every later
order tends to zero.
-/

open Filter Real
open scoped Topology

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

/-- The radial exponent of the order `r` term in a degree-`d` mixture. -/
def mixtureExponent (d r : ℕ) (sigma rho kappa : ℝ) : ℝ :=
  ((d : ℝ) - (r : ℝ)) * sigma + (r : ℝ) * rho - kappa

/-- A finite power mixture, indexed so that `i` represents order `i + 1`. -/
noncomputable def finitePowerMixture
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (x : ℝ) : V :=
  ∑ i : Fin d,
    (c ^ (i.1 + 1)) • ((x ^ mixtureExponent d (i.1 + 1) sigma rho kappa) • v i)

/-- The same mixture after dividing each order by the radial power of a
distinguished order.  This form avoids division at `x = 0` and is exactly the
normalization used in the leading-order argument as `x → +∞`. -/
noncomputable def normalizedFinitePowerMixture
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V)
    (r0 : Fin d) (x : ℝ) : V :=
  ∑ i : Fin d,
    (c ^ (i.1 + 1)) •
      ((x ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
        mixtureExponent d (r0.1 + 1) sigma rho kappa)) • v i)

lemma mixtureExponent_sub_eq
    (d r s : ℕ) (sigma rho kappa : ℝ) :
    mixtureExponent d r sigma rho kappa -
        mixtureExponent d s sigma rho kappa =
      ((s : ℝ) - (r : ℝ)) * (sigma - rho) := by
  simp only [mixtureExponent]
  ring

/-- The first nonzero order of a finite power mixture is the exact normalized
limit.  This is the non-algebraic leading-term selection step used in the
paper's multilinear mixture gap law. -/
theorem normalized_finitePowerMixture_tendsto_first_nonzero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0) :
    Tendsto
      (normalizedFinitePowerMixture d c sigma rho kappa v r0)
      atTop
      (𝓝 ((c ^ (r0.1 + 1)) • v r0)) := by
  classical
  unfold normalizedFinitePowerMixture
  let a : Fin d → V := fun i =>
    if i = r0 then (c ^ (r0.1 + 1)) • v r0 else 0
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Tendsto
        (fun x : ℝ =>
          (c ^ (i.1 + 1)) •
            ((x ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
              mixtureExponent d (r0.1 + 1) sigma rho kappa)) • v i))
        atTop (𝓝 (a i)) := by
    intro i _hi
    rcases lt_trichotomy i r0 with hir | hir | hir
    · simp [a, ne_of_lt hir, hvanish i hir]
    · subst i
      simp [a]
    · have hindex : 0 < ((i.1 : ℝ) - (r0.1 : ℝ)) := by
        apply sub_pos.mpr
        exact_mod_cast (show r0.1 < i.1 from hir)
      have hgap : 0 < ((i.1 : ℝ) - (r0.1 : ℝ)) * (sigma - rho) :=
        mul_pos hindex (sub_pos.mpr hsigmaRho)
      have hpow : Tendsto
          (fun x : ℝ =>
            x ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
              mixtureExponent d (r0.1 + 1) sigma rho kappa))
          atTop (𝓝 0) := by
        convert tendsto_rpow_neg_atTop hgap using 1
        · funext x
          congr 1
          rw [mixtureExponent_sub_eq]
          push_cast
          ring
      have hconstant : Tendsto
          (fun _ : ℝ => c ^ (i.1 + 1)) atTop (nhds (c ^ (i.1 + 1))) :=
        tendsto_const_nhds
      simpa [a, ne_of_gt hir] using
        hconstant.smul (hpow.smul_const (v i))
  have hsum := tendsto_finsetSum Finset.univ hterm
  simpa [a] using hsum

/-- With a nonzero first visible coefficient and nonzero mixture amplitude,
the normalized norm converges to a strictly positive limit. -/
theorem normalized_finitePowerMixture_norm_tendsto_pos
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hc : c ≠ 0)
    (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0)
    (hvisible : v r0 ≠ 0) :
    Tendsto
      (fun x => ‖normalizedFinitePowerMixture d c sigma rho kappa v r0 x‖)
      atTop
      (𝓝 (‖(c ^ (r0.1 + 1)) • v r0‖)) ∧
      0 < ‖(c ^ (r0.1 + 1)) • v r0‖ := by
  constructor
  · exact (normalized_finitePowerMixture_tendsto_first_nonzero
      d c sigma rho kappa v r0 hsigmaRho hvanish).norm
  · exact norm_pos_iff.mpr (smul_ne_zero (pow_ne_zero _ hc) hvisible)

/-- Every visible order lies above its order-matched critical exponent by the
exact positive gap printed in the paper. -/
theorem finite_mixture_visible_order_gap
    (r : ℕ) (rho : ℝ) (hr : 0 < r) (hrho : 1 / 2 < rho) :
    0 < (r : ℝ) * (rho - 1 / 2) := by
  exact mul_pos (by exact_mod_cast hr) (sub_pos.mpr hrho)

#print axioms normalized_finitePowerMixture_tendsto_first_nonzero
#print axioms normalized_finitePowerMixture_norm_tendsto_pos
#print axioms finite_mixture_visible_order_gap

end RiemannHypothesisProofFactory.CriticalExponentTransforms
