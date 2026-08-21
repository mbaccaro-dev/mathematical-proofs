import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace RiemannHypothesisProofFactory.SubpowerDyadicEnergy

noncomputable section

open scoped BigOperators

/-- The real-valued Möbius coefficient. -/
def moebiusReal (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℤ)

/-- The paper's coefficient `b_n = -μ(n) log n`. -/
def weight (n : ℕ) : ℝ :=
  -moebiusReal n * Real.log (n : ℝ)

/-- The prefix `B_N`, with `B_0 = 0`. -/
def weightPrefix (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, weight n

/-- The two dyadic right endpoints `2L` and `2L+1`. -/
def rightEndpoint (L eps : ℕ) : ℕ := 2 * L + eps

/-- The diagonal variation on the half-open block `L < n ≤ 2L+eps`. -/
def variation (L eps : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
    weight n ^ 2 / (n : ℝ)

/-- The growing correlation energy, using the strict predecessor `B_(n-1)`. -/
def growingEnergy (L eps : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
    weight n * weightPrefix (n - 1) / (n : ℝ)

/-- The paper's exact dyadic-defect quantity. -/
def paperD (L eps : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
    (weight n ^ 2 - weight n * weightPrefix (n - 1)) / (n : ℝ)

/-- Normalized prefix energy. -/
def blockEnergy (N : ℕ) : ℝ :=
  weightPrefix N ^ 2 / (N : ℝ)

/-- The nonnegative completion term in the block-energy telescope. -/
def blockDefect (L eps : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
    weightPrefix (n - 1) ^ 2 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ))

/-- The boundary expression printed in the paper. -/
def paperH (L eps : ℕ) : ℝ :=
  let R := rightEndpoint L eps
  weightPrefix R ^ 2 / (R : ℝ) - weightPrefix L ^ 2 / (L + 1 : ℝ) +
    ∑ n ∈ Finset.Ioo L R,
      weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ))

/-- The exact universal two-endpoint condition retained as a hypothesis. -/
def paperP1 : Prop :=
  ∀ L : ℕ, 2 ≤ L →
    ∀ eps : ℕ, (eps = 0 ∨ eps = 1) →
      0 ≤ paperD L eps

/-- The exact finite anchor for the terminal binary branches. -/
def baseEnergy : ℝ :=
  max (blockEnergy 2) (blockEnergy 3)

/-- The natural binary depth used by floor-halving. -/
def binaryDepth (N : ℕ) : ℕ :=
  Nat.log 2 N

/-- The coefficient-three majorant obtained by iterating the recurrence. -/
def recurrenceMajorant (N : ℕ) : ℝ :=
  baseEnergy + 3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2

/-- An explicit constant converting the recurrence majorant to a cubic logarithm. -/
def cubicConstant : ℝ :=
  baseEnergy / Real.log (2 : ℝ) ^ 3 + 3 / Real.log (2 : ℝ)

theorem paperD_eq_variation_sub_growingEnergy (L eps : ℕ) :
    paperD L eps = variation L eps - growingEnergy L eps := by
  unfold paperD variation growingEnergy
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem weightPrefix_succ (n : ℕ) :
    weightPrefix (n + 1) = weightPrefix n + weight (n + 1) := by
  simp [weightPrefix, Finset.sum_Icc_succ_top]

theorem weightPrefix_update (n : ℕ) (hn : 1 ≤ n) :
    weightPrefix n = weightPrefix (n - 1) + weight n := by
  have htop : n - 1 + 1 = n := by omega
  simpa [htop] using weightPrefix_succ (n - 1)

theorem blockEnergy_step (n : ℕ) (hn : 2 ≤ n) :
    blockEnergy n - blockEnergy (n - 1) =
      2 * (weight n * weightPrefix (n - 1) / (n : ℝ)) +
        weight n ^ 2 / (n : ℝ) -
          weightPrefix (n - 1) ^ 2 /
            ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
  rw [blockEnergy, blockEnergy, weightPrefix_update n (by omega)]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnmNat : 1 ≤ n - 1 := by omega
  have hnm0 : ((n - 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hnmNat)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    rw [← hcast]
    exact hnm0
  rw [hcast]
  field_simp [hn0, hn1]
  ring

theorem blockDefect_nonnegative (L eps : ℕ) :
    0 ≤ blockDefect L eps := by
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))

theorem sum_blockEnergy_steps (L R : ℕ) (hLR : L ≤ R) :
    (∑ n ∈ Finset.Ioc L R,
        (blockEnergy n - blockEnergy (n - 1))) =
      blockEnergy R - blockEnergy L := by
  induction R with
  | zero =>
      have hL : L = 0 := by omega
      simp [hL]
  | succ R ih =>
      by_cases h : L ≤ R
      · rw [Finset.sum_Ioc_succ_top h, ih h]
        have hpred : R + 1 - 1 = R := by omega
        rw [hpred]
        ring
      · have hEq : L = R + 1 := by omega
        simp [hEq]

theorem blockEnergy_identity (L eps : ℕ) (hL : 2 ≤ L) :
    blockEnergy (rightEndpoint L eps) - blockEnergy L =
      2 * growingEnergy L eps + variation L eps - blockDefect L eps := by
  have hLR : L ≤ rightEndpoint L eps := by
    simp [rightEndpoint]
    omega
  rw [← sum_blockEnergy_steps L (rightEndpoint L eps) hLR]
  calc
    (∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
        (blockEnergy n - blockEnergy (n - 1))) =
        ∑ n ∈ Finset.Ioc L (rightEndpoint L eps),
          (2 * (weight n * weightPrefix (n - 1) / (n : ℝ)) +
            weight n ^ 2 / (n : ℝ) -
              weightPrefix (n - 1) ^ 2 /
                ((n : ℝ) * ((n - 1 : ℕ) : ℝ))) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnL : L < n := (Finset.mem_Ioc.mp hn).1
      exact blockEnergy_step n (by omega)
    _ = 2 * growingEnergy L eps + variation L eps - blockDefect L eps := by
      change
        (∑ n ∈ Finset.Ioc L (2 * L + eps),
            (2 * (weight n * weightPrefix (n - 1) / (n : ℝ)) +
              weight n ^ 2 / (n : ℝ) -
                weightPrefix (n - 1) ^ 2 /
                  ((n : ℝ) * ((n - 1 : ℕ) : ℝ)))) =
          2 * (∑ n ∈ Finset.Ioc L (2 * L + eps),
            weight n * weightPrefix (n - 1) / (n : ℝ)) +
          (∑ n ∈ Finset.Ioc L (2 * L + eps),
            weight n ^ 2 / (n : ℝ)) -
          blockDefect L eps
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp [blockDefect, rightEndpoint, Finset.mul_sum]

private def genericDefect (L R : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ioc L R,
    weightPrefix (n - 1) ^ 2 / ((n : ℝ) * ((n - 1 : ℕ) : ℝ))

private theorem genericDefect_shift (L R : ℕ) (hL : 1 ≤ L) :
    genericDefect L R =
      ∑ n ∈ Finset.Ico L R,
        weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ)) := by
  unfold genericDefect
  refine Finset.sum_bij'
      (fun n _ => n - 1)
      (fun n _ => n + 1) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  · intro n hn
    have hn' := Finset.mem_Ico.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    omega
  · intro n hn
    omega
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hsub : n - 1 + 1 = n := by omega
    have hcast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hsub.symm
    rw [hcast]
    ring

private theorem sum_Ico_eq_first_add_Ioo
    (f : ℕ → ℝ) (L R : ℕ) (hLR : L < R) :
    (∑ n ∈ Finset.Ico L R, f n) = f L + ∑ n ∈ Finset.Ioo L R, f n := by
  have hset : Finset.Ico L R = insert L (Finset.Ioo L R) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hset, Finset.sum_insert]
  simp

theorem paperH_eq_energy_difference_add_defect
    (L eps : ℕ) (hL : 2 ≤ L) :
    paperH L eps =
      blockEnergy (rightEndpoint L eps) - blockEnergy L + blockDefect L eps := by
  let R := rightEndpoint L eps
  have hLR : L < R := by
    dsimp [R, rightEndpoint]
    omega
  have hshift := genericDefect_shift L R (by omega)
  have hsplit := sum_Ico_eq_first_add_Ioo
    (fun n => weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ))) L R hLR
  have hdefect : blockDefect L eps = genericDefect L R := by
    rfl
  rw [paperH, show rightEndpoint L eps = R by rfl, hdefect, hshift, hsplit]
  unfold blockEnergy
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have hL10 : ((L + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hL0, hL10]
  ring

/-- Exact manuscript identity `2D = 3V - H`. -/
theorem prefix_square_identity (L eps : ℕ) (hL : 2 ≤ L) :
    2 * paperD L eps = 3 * variation L eps - paperH L eps := by
  rw [paperD_eq_variation_sub_growingEnergy,
    paperH_eq_energy_difference_add_defect L eps hL]
  have hid := blockEnergy_identity L eps hL
  linarith

/-- P1 gives the paper's sharper parity-uniform one-step recursion. -/
theorem paperP1_implies_sharp_recursion
    (hP1 : paperP1) (N : ℕ) (hN : 4 ≤ N) :
    blockEnergy N ≤
      weightPrefix (N / 2) ^ 2 / ((N / 2 + 1 : ℕ) : ℝ) +
        3 * variation (N / 2) (N % 2) := by
  let L := N / 2
  let eps := N % 2
  have hL : 2 ≤ L := by
    dsimp [L]
    omega
  have heps : eps = 0 ∨ eps = 1 := by
    dsimp [eps]
    exact Nat.mod_two_eq_zero_or_one N
  have hendpoint : rightEndpoint L eps = N := by
    dsimp [L, eps, rightEndpoint]
    simpa [Nat.add_comm] using Nat.mod_add_div N 2
  have hD : 0 ≤ paperD L eps := hP1 L hL eps heps
  have hid := prefix_square_identity L eps hL
  have hsum :
      0 ≤ ∑ n ∈ Finset.Ioo L (rightEndpoint L eps),
        weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ)) := by
    apply Finset.sum_nonneg
    intro n hn
    exact div_nonneg (sq_nonneg _) (mul_nonneg (by positivity) (by positivity))
  have hH : paperH L eps ≤ 3 * variation L eps := by
    linarith
  have hHexpr :
      paperH L eps =
        blockEnergy N - weightPrefix L ^ 2 / ((L + 1 : ℕ) : ℝ) +
          ∑ n ∈ Finset.Ioo L N,
            weightPrefix n ^ 2 / ((n : ℝ) * (n + 1 : ℝ)) := by
    simp [paperH, blockEnergy, hendpoint]
  rw [hHexpr] at hH
  rw [hendpoint] at hsum
  linarith

theorem weight_sq_le_log_sq (n R : ℕ) (hn : 1 ≤ n) (hnR : n ≤ R) :
    weight n ^ 2 ≤ Real.log (R : ℝ) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le hnpos (by exact_mod_cast hnR)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlogle : Real.log (n : ℝ) ≤ Real.log (R : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hnpos hRpos (by exact_mod_cast hnR)
  have hmuabs : |moebiusReal n| ≤ (1 : ℝ) := by
    rw [moebiusReal, ← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hmubounds : -(1 : ℝ) ≤ moebiusReal n ∧ moebiusReal n ≤ 1 :=
    abs_le.mp hmuabs
  have hmu2 : moebiusReal n ^ 2 ≤ (1 : ℝ) := by nlinarith
  have hlog2 : Real.log (n : ℝ) ^ 2 ≤ Real.log (R : ℝ) ^ 2 := by nlinarith
  unfold weight
  calc
    (-moebiusReal n * Real.log (n : ℝ)) ^ 2 =
        moebiusReal n ^ 2 * Real.log (n : ℝ) ^ 2 := by ring
    _ ≤ 1 * Real.log (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hmu2 (sq_nonneg _)
    _ ≤ 1 * Real.log (R : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hlog2 zero_le_one
    _ = Real.log (R : ℝ) ^ 2 := one_mul _

theorem variation_le_log_sq (L eps : ℕ) (hL : 2 ≤ L)
    (heps : eps = 0 ∨ eps = 1) :
    variation L eps ≤ Real.log (rightEndpoint L eps : ℝ) ^ 2 := by
  have hL1pos : (0 : ℝ) < L + 1 := by positivity
  have hsum :
      variation L eps ≤
        ∑ _n ∈ Finset.Ioc L (rightEndpoint L eps),
          Real.log (rightEndpoint L eps : ℝ) ^ 2 / (L + 1 : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnmem := Finset.mem_Ioc.mp hn
    have hnL : L + 1 ≤ n := by omega
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    calc
      weight n ^ 2 / (n : ℝ) ≤
          Real.log (rightEndpoint L eps : ℝ) ^ 2 / (n : ℝ) :=
        (div_le_div_iff_of_pos_right hnpos).2
          (weight_sq_le_log_sq n (rightEndpoint L eps) (by omega) hnmem.2)
      _ ≤ Real.log (rightEndpoint L eps : ℝ) ^ 2 / (L + 1 : ℝ) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hL1pos (by exact_mod_cast hnL)
  calc
    variation L eps ≤
        ∑ _n ∈ Finset.Ioc L (rightEndpoint L eps),
          Real.log (rightEndpoint L eps : ℝ) ^ 2 / (L + 1 : ℝ) := hsum
    _ = ((Finset.Ioc L (rightEndpoint L eps)).card : ℝ) *
          (Real.log (rightEndpoint L eps : ℝ) ^ 2 / (L + 1 : ℝ)) := by
      simp
    _ ≤ (L + 1 : ℝ) *
          (Real.log (rightEndpoint L eps : ℝ) ^ 2 / (L + 1 : ℝ)) := by
      have hcard : (Finset.Ioc L (rightEndpoint L eps)).card ≤ L + 1 := by
        simp [rightEndpoint]
        omega
      gcongr
      exact_mod_cast hcard
    _ = Real.log (rightEndpoint L eps : ℝ) ^ 2 := by
      field_simp

theorem paperP1_implies_block_drift (hP1 : paperP1) (L eps : ℕ)
    (hL : 2 ≤ L) (heps : eps = 0 ∨ eps = 1) :
    blockEnergy (rightEndpoint L eps) ≤
      blockEnergy L + 3 * Real.log (rightEndpoint L eps : ℝ) ^ 2 := by
  have hid := blockEnergy_identity L eps hL
  have hD : 0 ≤ paperD L eps := hP1 L hL eps heps
  have hp1 : growingEnergy L eps ≤ variation L eps := by
    rw [paperD_eq_variation_sub_growingEnergy] at hD
    linarith
  have hvariation := variation_le_log_sq L eps hL heps
  have hdefect := blockDefect_nonnegative L eps
  linarith

theorem paperP1_implies_binary_recurrence (hP1 : paperP1) (N : ℕ)
    (hN : 4 ≤ N) :
    blockEnergy N ≤
      blockEnergy (N / 2) + 3 * Real.log (N : ℝ) ^ 2 := by
  have hL : 2 ≤ N / 2 := by omega
  have heps : N % 2 = 0 ∨ N % 2 = 1 := Nat.mod_two_eq_zero_or_one N
  have hendpoint : rightEndpoint (N / 2) (N % 2) = N := by
    simpa [rightEndpoint] using Nat.div_add_mod N 2
  simpa [hendpoint] using
    paperP1_implies_block_drift hP1 (N / 2) (N % 2) hL heps

theorem blockEnergy_nonnegative (N : ℕ) (hN : 1 ≤ N) :
    0 ≤ blockEnergy N := by
  unfold blockEnergy
  exact div_nonneg (sq_nonneg _) (by positivity)

theorem binaryDepth_halving (N : ℕ) (hN : 4 ≤ N) :
    binaryDepth (N / 2) + 1 = binaryDepth N := by
  have hpow : 2 ^ (1 : ℕ) ≤ N := by omega
  have hlog : 1 ≤ Nat.log 2 N :=
    Nat.le_log_of_pow_le (by omega) hpow
  unfold binaryDepth
  rw [Nat.log_div_base]
  omega

theorem log_half_le_log (N : ℕ) (hN : 4 ≤ N) :
    Real.log ((N / 2 : ℕ) : ℝ) ≤ Real.log (N : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast (show 0 < N / 2 by omega)
  · exact_mod_cast Nat.div_le_self N 2

theorem binaryDepth_mul_log_two_le_log (N : ℕ) (hN : 1 ≤ N) :
    (binaryDepth N : ℝ) * Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
  have hpowNat : 2 ^ binaryDepth N ≤ N := by
    simpa [binaryDepth] using Nat.pow_log_le_self 2 (Nat.ne_of_gt (by omega : 0 < N))
  have hpowReal : (2 : ℝ) ^ binaryDepth N ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hlog :
      Real.log ((2 : ℝ) ^ binaryDepth N) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (pow_pos (by norm_num) _) hpowReal
  simpa [Real.log_pow] using hlog

theorem baseEnergy_nonnegative :
    0 ≤ baseEnergy := by
  exact le_max_of_le_left (blockEnergy_nonnegative 2 (by omega))

theorem paperP1_implies_recurrenceMajorant
    (hP1 : paperP1) :
    ∀ N : ℕ, 2 ≤ N → blockEnergy N ≤ recurrenceMajorant N := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
      intro hN
      by_cases h4 : 4 ≤ N
      · have hhalf_lt : N / 2 < N := Nat.div_lt_self (by omega) (by omega)
        have hhalf_ge : 2 ≤ N / 2 := by omega
        have hrec := paperP1_implies_binary_recurrence hP1 N h4
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
        unfold recurrenceMajorant at hih ⊢
        rw [hdepthR]
        nlinarith
      · have hcases : N = 2 ∨ N = 3 := by omega
        rcases hcases with rfl | rfl
        · have hb : blockEnergy 2 ≤ baseEnergy := le_max_left _ _
          have htail :
              0 ≤ 3 * (binaryDepth 2 : ℝ) * Real.log (2 : ℝ) ^ 2 := by
            positivity
          unfold recurrenceMajorant
          exact hb.trans (le_add_of_nonneg_right htail)
        · have hb : blockEnergy 3 ≤ baseEnergy := le_max_right _ _
          have htail :
              0 ≤ 3 * (binaryDepth 3 : ℝ) * Real.log (3 : ℝ) ^ 2 := by
            positivity
          unfold recurrenceMajorant
          exact hb.trans (le_add_of_nonneg_right htail)

/-- The discrete paper condition gives an explicit cubic bound at every endpoint. -/
theorem paperP1_implies_cubic_bound
    (hP1 : paperP1) (N : ℕ) (hN : 2 ≤ N) :
    blockEnergy N ≤ cubicConstant * Real.log (N : ℝ) ^ 3 := by
  have hmajor := paperP1_implies_recurrenceMajorant hP1 N hN
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogle : Real.log (2 : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  have hlogN : 0 < Real.log (N : ℝ) := hlog2.trans_le hlogle
  have hdepth := binaryDepth_mul_log_two_le_log N (by omega)
  have hcubes : Real.log (2 : ℝ) ^ 3 ≤ Real.log (N : ℝ) ^ 3 := by
    exact pow_le_pow_left₀ hlog2.le hlogle 3
  have hbasefactor : 0 ≤ baseEnergy / Real.log (2 : ℝ) ^ 3 := by
    exact div_nonneg baseEnergy_nonnegative (by positivity)
  have hbaseeq :
      baseEnergy =
        (baseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (2 : ℝ) ^ 3 := by
    field_simp [ne_of_gt hlog2]
  have hbase :
      baseEnergy ≤
        (baseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (N : ℝ) ^ 3 := by
    calc
      baseEnergy =
          (baseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (2 : ℝ) ^ 3 := hbaseeq
      _ ≤ (baseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (N : ℝ) ^ 3 :=
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
    blockEnergy N ≤ recurrenceMajorant N := hmajor
    _ = baseEnergy +
        3 * (binaryDepth N : ℝ) * Real.log (N : ℝ) ^ 2 := rfl
    _ ≤ (baseEnergy / Real.log (2 : ℝ) ^ 3) * Real.log (N : ℝ) ^ 3 +
        (3 / Real.log (2 : ℝ)) * Real.log (N : ℝ) ^ 3 :=
      add_le_add hbase htail
    _ = cubicConstant * Real.log (N : ℝ) ^ 3 := by
      unfold cubicConstant
      ring

end

end RiemannHypothesisProofFactory.SubpowerDyadicEnergy
