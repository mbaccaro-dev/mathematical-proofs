import RiemannHypothesisProofFactory.SubpowerDyadicEnergy.DyadicBalance

namespace RiemannHypothesisProofFactory.SubpowerDyadicEnergy

noncomputable section

open scoped BigOperators

/-- The manuscript's eventual-sign hypothesis: only the power-of-two blocks
`(2^j, 2^(j+1)]` are assumed to have nonnegative defect. -/
def eventualDyadicDefectFrom (j0 : ℕ) : Prop :=
  ∀ j : ℕ, j0 ≤ j → 0 ≤ paperD (2 ^ j) 0

/-- The completed energies at the finitely many powers of two preceding the
eventual-sign range. -/
def eventualDyadicBaseEnergy (j0 : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 j0, completedCumulativeEnergy (2 ^ j)

/-- The explicit cubic-logarithmic coefficient attached to the manuscript's
power-of-two eventual-sign hypothesis. -/
def eventualDyadicCubicConstant (j0 : ℕ) : ℝ :=
  eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3 +
    3 / Real.log (2 : ℝ)

/-- The manuscript's cumulative defect on the adjacent power-of-two blocks
from exponent `1` through exponent `J - 1`. -/
def dyadicDefectSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 J, paperD (2 ^ j) 0

/-- The corresponding cumulative diagonal variation.  Its blocks partition
the exact half-open range `2 < n ≤ 2^J`. -/
def dyadicVariationSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico 1 J, variation (2 ^ j) 0

/-- An explicit form of the standard weighted-squarefree remainder estimate,
restricted to the power-of-two endpoints used by the manuscript. -/
def weightedSquarefreeRemainderBound (C : ℝ) : Prop :=
  ∀ J : ℕ, 2 ≤ J →
    |dyadicVariationSum J -
        (2 / Real.pi ^ 2) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 3| ≤
      C * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2

theorem completedCumulativeEnergy_nonnegative (N : ℕ) :
    0 ≤ completedCumulativeEnergy N := by
  exact add_nonneg (cumulativeEnergy_nonnegative N) (boundaryEnergy_nonnegative N)

theorem cumulativeEnergy_mono {N M : ℕ} (hNM : N ≤ M) :
    cumulativeEnergy N ≤ cumulativeEnergy M := by
  unfold cumulativeEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hnM hnN
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))

theorem eventualDyadicBaseEnergy_nonnegative (j0 : ℕ) :
    0 ≤ eventualDyadicBaseEnergy j0 := by
  unfold eventualDyadicBaseEnergy
  apply Finset.sum_nonneg
  intro j hj
  exact completedCumulativeEnergy_nonnegative (2 ^ j)

/-- Summing the exact local conservation law gives the manuscript's global
power-of-two balance, with the initial completed boundary term retained. -/
theorem dyadic_global_energy_balance (J : ℕ) (hJ : 1 ≤ J) :
    2 * dyadicDefectSum J + completedCumulativeEnergy (2 ^ J) =
      3 * dyadicVariationSum J + completedCumulativeEnergy 2 := by
  induction J with
  | zero => omega
  | succ J ih =>
      by_cases hJ0 : J = 0
      · subst J
        simp [dyadicDefectSum, dyadicVariationSum]
      · have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.mpr hJ0
        have hih := ih hJ1
        have hpow : 2 ≤ 2 ^ J := by
          have hpow' : 2 ^ (1 : ℕ) ≤ 2 ^ J :=
            Nat.pow_le_pow_right (by norm_num) hJ1
          simpa using hpow'
        have hlocal := dyadic_energy_conservation (2 ^ J) 0 hpow
        have hendpoint : rightEndpoint (2 ^ J) 0 = 2 ^ (J + 1) := by
          simp [rightEndpoint, pow_succ, Nat.mul_comm]
        unfold dyadicDefectSum dyadicVariationSum at hih ⊢
        rw [Finset.sum_Ico_succ_top hJ1, Finset.sum_Ico_succ_top hJ1]
        rw [hendpoint] at hlocal
        linarith

private theorem eventualDyadicDefectFrom_implies_defect_sum_lower
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (J : ℕ) (hj0J : j0 ≤ J) :
    dyadicDefectSum j0 ≤ dyadicDefectSum J := by
  have htail :
      0 ≤ ∑ j ∈ Finset.Ico j0 J, paperD (2 ^ j) 0 := by
    apply Finset.sum_nonneg
    intro j hj
    exact hEventual j (Finset.mem_Ico.mp hj).1
  unfold dyadicDefectSum
  rw [← Finset.sum_Ico_consecutive _ hj0 hj0J]
  linarith

/-- With the standard weighted-squarefree remainder supplied explicitly, the
eventual-sign hypothesis yields the manuscript's sharp `6 / pi^2` leading
coefficient for completed energy at powers of two.  The lower-order constant
contains the exact finite prefix of possibly negative defects. -/
theorem eventualDyadicDefectFrom_implies_sharp_power_energy_bound
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (C : ℝ) (hSquarefree : weightedSquarefreeRemainderBound C)
    (J : ℕ) (hJ2 : 2 ≤ J) (hj0J : j0 ≤ J) :
    completedCumulativeEnergy (2 ^ J) ≤
      (6 / Real.pi ^ 2) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 +
        3 * C * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 +
        completedCumulativeEnergy 2 - 2 * dyadicDefectSum j0 := by
  have hbalance := dyadic_global_energy_balance J (by omega)
  have hdefect :=
    eventualDyadicDefectFrom_implies_defect_sum_lower
      j0 hj0 hEventual J hj0J
  have hremainder := hSquarefree J hJ2
  have hvariation :
      dyadicVariationSum J ≤
        (2 / Real.pi ^ 2) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 +
          C * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := by
    have hupper := (abs_le.mp hremainder).2
    linarith
  calc
    completedCumulativeEnergy (2 ^ J) ≤
        3 * dyadicVariationSum J + completedCumulativeEnergy 2 -
          2 * dyadicDefectSum j0 := by
      linarith
    _ ≤ 3 * ((2 / Real.pi ^ 2) *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 +
          C * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2) +
          completedCumulativeEnergy 2 - 2 * dyadicDefectSum j0 := by
      nlinarith
    _ = (6 / Real.pi ^ 2) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 +
          3 * C * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 +
          completedCumulativeEnergy 2 - 2 * dyadicDefectSum j0 := by
      ring

/-- One exact power-of-two block inherits the energy drift from its assumed
defect sign.  No odd endpoint or non-power-of-two left endpoint is assumed. -/
theorem eventualDyadicDefectFrom_implies_power_step
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (j : ℕ) (hj : j0 ≤ j) :
    completedCumulativeEnergy (2 ^ (j + 1)) ≤
      completedCumulativeEnergy (2 ^ j) +
        3 * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 := by
  have hj1 : 1 ≤ j := hj0.trans hj
  have hpow : 2 ≤ 2 ^ j := by
    have hpow' : 2 ^ (1 : ℕ) ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj1
    simpa using hpow'
  have hconservation := dyadic_energy_conservation (2 ^ j) 0 hpow
  have hD : 0 ≤ paperD (2 ^ j) 0 := hEventual j hj
  have hvariation := variation_le_log_sq (2 ^ j) 0 hpow (Or.inl rfl)
  have hendpoint : rightEndpoint (2 ^ j) 0 = 2 ^ (j + 1) := by
    simp [rightEndpoint, pow_succ, Nat.mul_comm]
  rw [hendpoint] at hconservation hvariation
  linarith

private theorem completedPowerEnergy_le_eventualDyadicBase
    (j0 J : ℕ) (hJ1 : 1 ≤ J) (hJj0 : J ≤ j0) :
    completedCumulativeEnergy (2 ^ J) ≤ eventualDyadicBaseEnergy j0 := by
  have hmem : J ∈ Finset.Icc 1 j0 := Finset.mem_Icc.mpr ⟨hJ1, hJj0⟩
  unfold eventualDyadicBaseEnergy
  exact Finset.single_le_sum
    (fun j hj => completedCumulativeEnergy_nonnegative (2 ^ j)) hmem

private theorem eventualDyadicDefectFrom_implies_power_majorant
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0) :
    ∀ J : ℕ, 1 ≤ J →
      completedCumulativeEnergy (2 ^ J) ≤
        eventualDyadicBaseEnergy j0 +
          3 * (J : ℝ) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := by
  intro J
  induction J using Nat.strong_induction_on with
  | h J ih =>
      intro hJ1
      by_cases hactive : j0 < J
      · let j := J - 1
        have hjJ : j + 1 = J := by
          dsimp [j]
          omega
        have hjlt : j < J := by
          dsimp [j]
          omega
        have hj0j : j0 ≤ j := by
          dsimp [j]
          omega
        have hj1 : 1 ≤ j := hj0.trans hj0j
        have hrec :=
          eventualDyadicDefectFrom_implies_power_step
            j0 hj0 hEventual j hj0j
        have hih := ih j hjlt hj1
        have hpowle : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hlogle :
            Real.log ((2 ^ j : ℕ) : ℝ) ≤
              Real.log ((2 ^ J : ℕ) : ℝ) := by
          exact Real.log_le_log (by positivity) (by exact_mod_cast hpowle)
        have hlogj0 : 0 ≤ Real.log ((2 ^ j : ℕ) : ℝ) :=
          Real.log_nonneg (by
            have hjpow1 : 1 ≤ 2 ^ j := Nat.one_le_pow j 2 (by norm_num)
            exact_mod_cast hjpow1)
        have hlogJ0 : 0 ≤ Real.log ((2 ^ J : ℕ) : ℝ) :=
          Real.log_nonneg (by
            have hJpow1 : 1 ≤ 2 ^ J := Nat.one_le_pow J 2 (by norm_num)
            exact_mod_cast hJpow1)
        have hsq :
            Real.log ((2 ^ j : ℕ) : ℝ) ^ 2 ≤
              Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := by
          nlinarith
        have hscaled :
            3 * (j : ℝ) * Real.log ((2 ^ j : ℕ) : ℝ) ^ 2 ≤
              3 * (j : ℝ) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
        rw [hjJ] at hrec
        have hjJR : (J : ℝ) = (j : ℝ) + 1 := by exact_mod_cast hjJ.symm
        rw [hjJR]
        nlinarith
      · have hJj0 : J ≤ j0 := Nat.le_of_not_gt hactive
        have hbase := completedPowerEnergy_le_eventualDyadicBase j0 J hJ1 hJj0
        have htail :
            0 ≤ 3 * (J : ℝ) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := by
          positivity
        exact hbase.trans (le_add_of_nonneg_right htail)

/-- The exact manuscript hypothesis gives a completed-energy `O(log^3)` bound
at every power of two.  The coefficient includes all scales before `j0` as an
explicit finite sum. -/
theorem eventualDyadicDefectFrom_implies_power_energy_cubic_bound
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (J : ℕ) (hJ : 1 ≤ J) :
    completedCumulativeEnergy (2 ^ J) ≤
      eventualDyadicCubicConstant j0 *
        Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
  have hmajor :=
    eventualDyadicDefectFrom_implies_power_majorant j0 hj0 hEventual J hJ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogpow :
      Real.log ((2 ^ J : ℕ) : ℝ) = (J : ℝ) * Real.log (2 : ℝ) := by
    have hcast : ((2 ^ J : ℕ) : ℝ) = (2 : ℝ) ^ J := by
      exact_mod_cast rfl
    rw [hcast]
    exact Real.log_pow 2 J
  have hlogle :
      Real.log (2 : ℝ) ≤ Real.log ((2 ^ J : ℕ) : ℝ) := by
    rw [hlogpow]
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    nlinarith
  have hcubes :
      Real.log (2 : ℝ) ^ 3 ≤ Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hlog2.le hlogle 3
  have hbasefactor :
      0 ≤ eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3 := by
    exact div_nonneg (eventualDyadicBaseEnergy_nonnegative j0) (by positivity)
  have hbaseeq :
      eventualDyadicBaseEnergy j0 =
        (eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3) *
          Real.log (2 : ℝ) ^ 3 := by
    field_simp [ne_of_gt hlog2]
  have hbase :
      eventualDyadicBaseEnergy j0 ≤
        (eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3) *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
    calc
      eventualDyadicBaseEnergy j0 =
          (eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3) *
            Real.log (2 : ℝ) ^ 3 := hbaseeq
      _ ≤ (eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3) *
            Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hcubes hbasefactor
  have htail :
      3 * (J : ℝ) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 =
        (3 / Real.log (2 : ℝ)) *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
    rw [hlogpow]
    field_simp [ne_of_gt hlog2]
  calc
    completedCumulativeEnergy (2 ^ J) ≤
        eventualDyadicBaseEnergy j0 +
          3 * (J : ℝ) * Real.log ((2 ^ J : ℕ) : ℝ) ^ 2 := hmajor
    _ ≤ (eventualDyadicBaseEnergy j0 / Real.log (2 : ℝ) ^ 3) *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 +
        (3 / Real.log (2 : ℝ)) *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
      rw [htail]
      exact add_le_add hbase le_rfl
    _ = eventualDyadicCubicConstant j0 *
          Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 := by
      unfold eventualDyadicCubicConstant
      ring

/-- Monotonicity of the positive cumulative energy lifts the power-of-two
bound to every `N`, evaluated at the first strict dyadic upper endpoint. -/
theorem eventualDyadicDefectFrom_implies_cumulative_energy_bound
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (N : ℕ) (_hN : 2 ≤ N) :
    cumulativeEnergy N ≤
      eventualDyadicCubicConstant j0 *
        Real.log ((2 ^ (binaryDepth N + 1) : ℕ) : ℝ) ^ 3 := by
  let J := binaryDepth N + 1
  have hJ : 1 ≤ J := by
    dsimp [J]
    omega
  have hNpow : N ≤ 2 ^ J := by
    dsimp [J, binaryDepth]
    exact (Nat.lt_pow_succ_log_self (by norm_num) N).le
  have hmono := cumulativeEnergy_mono hNpow
  have hboundary := boundaryEnergy_nonnegative (2 ^ J)
  have hcompleted : cumulativeEnergy (2 ^ J) ≤ completedCumulativeEnergy (2 ^ J) := by
    unfold completedCumulativeEnergy
    linarith
  have hpower :=
    eventualDyadicDefectFrom_implies_power_energy_cubic_bound
      j0 hj0 hEventual J hJ
  exact hmono.trans (hcompleted.trans hpower)

/-- The monotone lift can be written directly as an `O(log^3 N)` estimate:
the strict dyadic upper endpoint is smaller than `2 * N`. -/
theorem eventualDyadicDefectFrom_implies_cumulative_energy_cubic_bound
    (j0 : ℕ) (hj0 : 1 ≤ j0) (hEventual : eventualDyadicDefectFrom j0)
    (N : ℕ) (hN : 2 ≤ N) :
    cumulativeEnergy N ≤
      eventualDyadicCubicConstant j0 *
        (Real.log (N : ℝ) + Real.log (2 : ℝ)) ^ 3 := by
  let J := binaryDepth N + 1
  have hupper :=
    eventualDyadicDefectFrom_implies_cumulative_energy_bound
      j0 hj0 hEventual N hN
  have hpowfloor : 2 ^ binaryDepth N ≤ N := by
    simpa [binaryDepth] using
      Nat.pow_log_le_self 2 (Nat.ne_of_gt (by omega : 0 < N))
  have hpowdouble : 2 ^ J ≤ 2 * N := by
    dsimp [J]
    rw [pow_succ]
    nlinarith
  have hlogupper :
      Real.log ((2 ^ J : ℕ) : ℝ) ≤ Real.log ((2 * N : ℕ) : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpowdouble)
  have hlogdouble :
      Real.log ((2 * N : ℕ) : ℝ) =
        Real.log (N : ℝ) + Real.log (2 : ℝ) := by
    have hcast : ((2 * N : ℕ) : ℝ) = (2 : ℝ) * (N : ℝ) := by norm_num
    rw [hcast, Real.log_mul (by norm_num) (by positivity)]
    ring
  have hlogupper0 : 0 ≤ Real.log ((2 ^ J : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_pow J 2 (by norm_num))
  have hlogbound :
      Real.log ((2 ^ J : ℕ) : ℝ) ≤
        Real.log (N : ℝ) + Real.log (2 : ℝ) := by
    rw [← hlogdouble]
    exact hlogupper
  have hcubes :
      Real.log ((2 ^ J : ℕ) : ℝ) ^ 3 ≤
        (Real.log (N : ℝ) + Real.log (2 : ℝ)) ^ 3 := by
    exact pow_le_pow_left₀ hlogupper0 hlogbound 3
  have hconstant : 0 ≤ eventualDyadicCubicConstant j0 := by
    unfold eventualDyadicCubicConstant
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    exact add_nonneg
      (div_nonneg (eventualDyadicBaseEnergy_nonnegative j0) (by positivity))
      (div_nonneg (by norm_num) hlog2.le)
  exact hupper.trans (mul_le_mul_of_nonneg_left hcubes hconstant)

end

end RiemannHypothesisProofFactory.SubpowerDyadicEnergy
