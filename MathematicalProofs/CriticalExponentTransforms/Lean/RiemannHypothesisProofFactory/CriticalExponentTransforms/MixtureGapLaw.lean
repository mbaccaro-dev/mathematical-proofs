import RiemannHypothesisProofFactory.CriticalExponentTransforms.MixtureEnergy

open Filter Finset Fintype Real Topology
open scoped BigOperators

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

/-- The exact finite binary expansion obtained directly from multilinearity
and dilation covariance. -/
theorem paper_multilinear_operator_expansion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      operatorDifference d B sigma rho c x =
        ∑ s ∈ ((Finset.univ : Finset (Finset (Fin d))).erase ∅),
          (c ^ s.card) •
            ((x.1 ^ subsetExponent d s sigma rho kappa) •
              subsetCoefficient d B sigma rho s) := by
  exact multilinear_operator_expansion d B sigma rho c kappa hcov

/-- The full normalized dyadic-energy limit for a finite mixture whose lower
orders vanish. -/
theorem paper_normalized_mixture_dyadic_energy_limit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ) (c sigma rho kappa : ℝ) (v : Fin d → V) (r0 : Fin d)
    (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 → v i = 0) :
    Tendsto
      (normalizedMixtureDyadicEnergy d c sigma rho kappa v r0)
      atTop
      (nhds (∫ u in (1 : ℝ)..2,
        ‖(u ^ mixtureExponent d (r0.1 + 1) sigma rho kappa) •
          ((c ^ (r0.1 + 1)) • v r0)‖ ^ 2 / u)) := by
  exact normalizedMixtureDyadicEnergy_tendsto d c sigma rho kappa v r0
    hsigmaRho hvanish

/-- After scaling by the first visible power of the dyadic base point, the
operator difference is exactly the finite profile used in the energy limit. -/
theorem scale_normalized_operator_profile_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ) (r0 : Fin d)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x)
    (X u : ℝ) (hX : 0 < X) (hu : 0 < u) :
    (X ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa)) •
        operatorDifference d B sigma rho c
          ⟨X * u, mul_pos hX hu⟩ =
      normalizedMixtureProfile d c sigma rho kappa
        (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 X u := by
  classical
  rw [operatorDifference_eq_finitePowerMixture d B sigma rho c kappa hcov]
  unfold finitePowerMixture normalizedMixtureProfile
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  rw [Real.mul_rpow hX.le hu.le]
  calc
    X ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa) *
          c ^ (i.1 + 1) *
            (X ^ mixtureExponent d (i.1 + 1) sigma rho kappa *
              u ^ mixtureExponent d (i.1 + 1) sigma rho kappa) =
        c ^ (i.1 + 1) *
          ((X ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa) *
              X ^ mixtureExponent d (i.1 + 1) sigma rho kappa) *
            u ^ mixtureExponent d (i.1 + 1) sigma rho kappa) := by ring
    _ = c ^ (i.1 + 1) *
          (X ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
              mixtureExponent d (r0.1 + 1) sigma rho kappa) *
            u ^ mixtureExponent d (i.1 + 1) sigma rho kappa) := by
          rw [← Real.rpow_add hX]
          ring_nf

/-- The paper's first-visible multilinear law.  Dilation covariance and
multilinearity give the exact finite expansion; the least nonzero grouped
coefficient then controls both the leading norm and the full dyadic energy.
The last conclusion is the strict critical-exponent gap. -/
theorem multilinear_mixture_gap_law
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ) (r0 : Fin d)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x)
    (hc : c ≠ 0) (hrho : (1 : ℝ) / 2 < rho) (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 →
      orderCoefficient d B sigma rho i.succ = 0)
    (hvisible : orderCoefficient d B sigma rho r0.succ ≠ 0) :
    (∀ (X u : ℝ) (hX : 0 < X) (hu : 0 < u),
      (X ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa)) •
          operatorDifference d B sigma rho c
            ⟨X * u, mul_pos hX hu⟩ =
        normalizedMixtureProfile d c sigma rho kappa
          (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 X u) ∧
    Tendsto
      (fun x : PosReal ↦
        ‖normalizedOperatorDifference d B sigma rho c kappa r0 x‖)
      atTop
      (nhds (‖(c ^ (r0.1 + 1)) •
        orderCoefficient d B sigma rho r0.succ‖)) ∧
    0 < ‖(c ^ (r0.1 + 1)) •
      orderCoefficient d B sigma rho r0.succ‖ ∧
    Tendsto
      (fun X : PosReal ↦
        normalizedMixtureDyadicEnergy d c sigma rho kappa
          (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 X.1)
      atTop
      (nhds (mixtureDyadicEnergyLeadingConstant d c sigma rho kappa
        (fun i ↦ orderCoefficient d B sigma rho i.succ) r0)) ∧
    0 < mixtureDyadicEnergyLeadingConstant d c sigma rho kappa
      (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 ∧
    0 < ((r0.1 + 1 : ℕ) : ℝ) * (rho - 1 / 2) := by
  have hnorm := multilinear_operator_norm_limit d B sigma rho c kappa r0
    hcov hc hsigmaRho hvanish hvisible
  have henergy := normalizedMixtureDyadicEnergy_tendsto d c sigma rho kappa
    (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 hsigmaRho hvanish
  have henergyPos := mixtureDyadicEnergyLeadingConstant_pos
    d c sigma rho kappa
    (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 hc hvisible
  refine ⟨?_, hnorm.1, hnorm.2, ?_, henergyPos, ?_⟩
  · intro X u hX hu
    exact scale_normalized_operator_profile_eq d B sigma rho c kappa r0
      hcov X u hX hu
  · exact henergy.comp tendsto_posReal_coe_atTop
  · exact mul_pos (by positivity) (sub_pos.mpr hrho)

end RiemannHypothesisProofFactory.CriticalExponentTransforms
