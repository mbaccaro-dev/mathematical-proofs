import RiemannHypothesisProofFactory.SubpowerDyadicEnergy.DiscreteKernel

namespace RiemannHypothesisProofFactory.SubpowerDyadicEnergy

noncomputable section

open scoped BigOperators

/-- The paper's positive cumulative prefix energy. -/
def cumulativeEnergy (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 N,
    weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ))

/-- The boundary term that completes a dyadic block exactly. -/
def boundaryEnergy (N : ℕ) : ℝ :=
  weightPrefix N ^ 2 / (N + 1 : ℝ)

/-- Cumulative energy together with its right boundary term. -/
def completedCumulativeEnergy (N : ℕ) : ℝ :=
  cumulativeEnergy N + boundaryEnergy N

private theorem cumulativeEnergy_split (L R : ℕ) (hL : 2 ≤ L) (hLR : L ≤ R) :
    cumulativeEnergy R = cumulativeEnergy L +
      ∑ n ∈ Finset.Ioc L R,
        weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ)) := by
  have hset : Finset.Icc 2 R = Finset.Icc 2 L ∪ Finset.Ioc L R := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 2 L) (Finset.Ioc L R) := by
    rw [Finset.disjoint_left]
    intro n hnL hnR
    simp only [Finset.mem_Icc] at hnL
    simp only [Finset.mem_Ioc] at hnR
    omega
  unfold cumulativeEnergy
  rw [hset, Finset.sum_union hdisj]

private theorem sum_Ioc_eq_sum_Ioo_add_right
    (f : ℕ → ℝ) (L R : ℕ) (hLR : L < R) :
    (∑ n ∈ Finset.Ioc L R, f n) =
      (∑ n ∈ Finset.Ioo L R, f n) + f R := by
  have hset : Finset.Ioc L R = insert R (Finset.Ioo L R) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, Finset.sum_insert]
  · ring
  · simp

private theorem terminalEnergy_add_boundary (R : ℕ) (hR : 1 ≤ R) :
    weightPrefix R ^ 2 / ((R : ℝ) * (R + 1 : ℝ)) + boundaryEnergy R =
      blockEnergy R := by
  unfold boundaryEnergy blockEnergy
  have hR0 : (R : ℝ) ≠ 0 := by positivity
  have hR10 : ((R + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hR0, hR10]
  ring

/-- The printed boundary term is the exact change in completed cumulative energy. -/
theorem paperH_eq_completedCumulativeEnergy_difference
    (L eps : ℕ) (hL : 2 ≤ L) :
    paperH L eps =
      completedCumulativeEnergy (rightEndpoint L eps) -
        completedCumulativeEnergy L := by
  let R := rightEndpoint L eps
  have hLR : L < R := by
    dsimp [R, rightEndpoint]
    omega
  have hsplit := cumulativeEnergy_split L R hL hLR.le
  have hsum := sum_Ioc_eq_sum_Ioo_add_right
    (fun n => weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ))) L R hLR
  have hterminal := terminalEnergy_add_boundary R (by omega)
  unfold paperH completedCumulativeEnergy
  change
    blockEnergy R - boundaryEnergy L +
        (∑ n ∈ Finset.Ioo L R,
          weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ))) =
      cumulativeEnergy R + boundaryEnergy R -
        (cumulativeEnergy L + boundaryEnergy L)
  rw [hsplit, hsum]
  linarith

/-- One dyadic block obeys an exact conservation law between defect,
variation, and completed positive energy. -/
theorem dyadic_energy_conservation (L eps : ℕ) (hL : 2 ≤ L) :
    2 * paperD L eps +
        completedCumulativeEnergy (rightEndpoint L eps) =
      3 * variation L eps + completedCumulativeEnergy L := by
  rw [prefix_square_identity L eps hL,
    paperH_eq_completedCumulativeEnergy_difference L eps hL]
  ring

theorem cumulativeEnergy_nonnegative (N : ℕ) :
    0 ≤ cumulativeEnergy N := by
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))

theorem boundaryEnergy_nonnegative (N : ℕ) :
    0 ≤ boundaryEnergy N := by
  unfold boundaryEnergy
  positivity

/-- P1 controls the completed cumulative energy in one binary step. -/
theorem paperP1_implies_completed_energy_drift
    (hP1 : paperP1) (L eps : ℕ) (hL : 2 ≤ L)
    (heps : eps = 0 ∨ eps = 1) :
    completedCumulativeEnergy (rightEndpoint L eps) ≤
      completedCumulativeEnergy L +
        3 * Real.log (rightEndpoint L eps : ℝ) ^ 2 := by
  have hconservation := dyadic_energy_conservation L eps hL
  have hD : 0 ≤ paperD L eps := hP1 L hL eps heps
  have hvariation := variation_le_log_sq L eps hL heps
  linarith

theorem paperP1_implies_completed_binary_recurrence
    (hP1 : paperP1) (N : ℕ) (hN : 4 ≤ N) :
    completedCumulativeEnergy N ≤
      completedCumulativeEnergy (N / 2) + 3 * Real.log (N : ℝ) ^ 2 := by
  have hL : 2 ≤ N / 2 := by omega
  have heps : N % 2 = 0 ∨ N % 2 = 1 := Nat.mod_two_eq_zero_or_one N
  have hendpoint : rightEndpoint (N / 2) (N % 2) = N := by
    simpa [rightEndpoint] using Nat.div_add_mod N 2
  simpa [hendpoint] using
    paperP1_implies_completed_energy_drift hP1 (N / 2) (N % 2) hL heps

/-- The finite base value for the completed cumulative-energy recurrence. -/
def completedBaseEnergy : ℝ :=
  max (completedCumulativeEnergy 2) (completedCumulativeEnergy 3)

/-- An explicit cubic majorant for the paper's cumulative energy. -/
def cumulativeCubicConstant : ℝ :=
  completedBaseEnergy / Real.log (2 : ℝ) ^ 3 + 3 / Real.log (2 : ℝ)

theorem completedBaseEnergy_nonnegative :
    0 ≤ completedBaseEnergy := by
  apply le_max_of_le_left
  exact add_nonneg (cumulativeEnergy_nonnegative 2) (boundaryEnergy_nonnegative 2)

private theorem paperP1_implies_completed_majorant
    (hP1 : paperP1) :
    ∀ N : ℕ, 2 ≤ N →
      completedCumulativeEnergy N ≤
        completedBaseEnergy +
          3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      by_cases h4 : 4 ≤ N
      · have hhalf_lt : N / 2 < N := Nat.div_lt_self (by omega) (by omega)
        have hhalf_ge : 2 ≤ N / 2 := by omega
        have hrec := paperP1_implies_completed_binary_recurrence hP1 N h4
        have hih := ih (N / 2) hhalf_lt hhalf_ge
        have hlogle := log_half_le_log N h4
        have hloghalf0 : 0 ≤ Real.log ((N / 2 : ℕ) : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ N / 2 by omega))
        have hlogN0 : 0 ≤ Real.log (N : ℝ) :=
          Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
        have hsq :
            Real.log ((N / 2 : ℕ) : ℝ) ^ 2 ≤ Real.log (N : ℝ) ^ 2 := by
          nlinarith
        have hdepth := binaryDepth_halving N h4
        have hdepthR :
            (binaryDepth N : ℝ) = (binaryDepth (N / 2) : ℝ) + 1 := by
          exact_mod_cast hdepth.symm
        have hscaled :
            3 * (binaryDepth (N / 2) : ℝ) *
                Real.log ((N / 2 : ℕ) : ℝ) ^ 2 ≤
              3 * (binaryDepth (N / 2) : ℝ) * Real.log (N : ℝ) ^ 2 := by
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
        rw [hdepthR]
        nlinarith
      · have hcases : N = 2 ∨ N = 3 := by omega
        rcases hcases with rfl | rfl
        · have hb : completedCumulativeEnergy 2 ≤ completedBaseEnergy :=
            le_max_left _ _
          have htail :
              0 ≤ 3 * (binaryDepth 2 : ℝ) * Real.log (2 : ℝ) ^ 2 := by
            positivity
          exact hb.trans (le_add_of_nonneg_right htail)
        · have hb : completedCumulativeEnergy 3 ≤ completedBaseEnergy :=
            le_max_right _ _
          have htail :
              0 ≤ 3 * (binaryDepth 3 : ℝ) * Real.log (3 : ℝ) ^ 2 := by
            positivity
          exact hb.trans (le_add_of_nonneg_right htail)

/-- Under the exact P1 hypothesis, the paper's cumulative positive energy is
bounded by an explicit cubic logarithm at every endpoint. -/
theorem paperP1_implies_cumulative_energy_cubic_bound
    (hP1 : paperP1) (N : ℕ) (hN : 2 ≤ N) :
    cumulativeEnergy N ≤
      cumulativeCubicConstant * Real.log (N : ℝ) ^ 3 := by
  have hmajor := paperP1_implies_completed_majorant hP1 N hN
  have hboundary := boundaryEnergy_nonnegative N
  have hcumulative :
      cumulativeEnergy N ≤
        completedBaseEnergy +
          3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 := by
    unfold completedCumulativeEnergy at hmajor
    linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogle : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hdepth := binaryDepth_mul_log_two_le_log N (by omega)
  have hcubes : Real.log (2 : ℝ) ^ 3 ≤ Real.log (N : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hlog2.le hlogle 3
  have hbasefactor : 0 ≤ completedBaseEnergy / Real.log (2 : ℝ) ^ 3 := by
    exact div_nonneg completedBaseEnergy_nonnegative (by positivity)
  have hbaseeq :
      completedBaseEnergy =
        (completedBaseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (2 : ℝ) ^ 3 := by
    field_simp [ne_of_gt hlog2]
  have hbase :
      completedBaseEnergy ≤
        (completedBaseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (N : ℝ) ^ 3 := by
    calc
      completedBaseEnergy =
          (completedBaseEnergy / Real.log (2 : ℝ) ^ 3) *
            Real.log (2 : ℝ) ^ 3 := hbaseeq
      _ ≤ (completedBaseEnergy / Real.log (2 : ℝ) ^ 3) *
            Real.log (N : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hcubes hbasefactor
  have hscale : 0 ≤ (3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 2 := by
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hdepth hscale
  have htail :
      3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 ≤
        (3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 3 := by
    calc
      3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 =
          ((3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 2) *
            ((binaryDepth N : ℝ) * Real.log (2 : ℝ)) := by
              field_simp [ne_of_gt hlog2]
      _ ≤ ((3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 2) *
            Real.log (N : ℝ) := hscaled
      _ = (3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 3 := by ring
  calc
    cumulativeEnergy N ≤
        completedBaseEnergy +
          3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 := hcumulative
    _ ≤ (completedBaseEnergy / Real.log (2 : ℝ) ^ 3) *
          Real.log (N : ℝ) ^ 3 +
        (3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 3 :=
      add_le_add hbase htail
    _ = cumulativeCubicConstant * Real.log (N : ℝ) ^ 3 := by
      unfold cumulativeCubicConstant
      ring

end

end RiemannHypothesisProofFactory.SubpowerDyadicEnergy
