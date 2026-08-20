import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

/-- The number of distinct prime factors. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Rank pairing crosses a cutoff exactly at the ranks belonging to one prefix
but not the other. -/
def rankCrossingIndices (m positivePrefix negativePrefix : ℕ) : Finset ℕ :=
  (Finset.range m).filter fun i =>
    (i < positivePrefix) ≠ (i < negativePrefix)

theorem rankCrossingIndices_eq_Ico
    (m positivePrefix negativePrefix : ℕ)
    (hpositive : positivePrefix ≤ m)
    (hnegative : negativePrefix ≤ m) :
    rankCrossingIndices m positivePrefix negativePrefix =
      Finset.Ico (min positivePrefix negativePrefix)
        (max positivePrefix negativePrefix) := by
  rcases le_total positivePrefix negativePrefix with h | h
  · ext i
    simp only [rankCrossingIndices, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico, min_eq_left h, max_eq_right h]
    by_cases hp : i < positivePrefix <;>
      by_cases hn : i < negativePrefix <;>
      simp [hp, hn] <;> omega
  · ext i
    simp only [rankCrossingIndices, Finset.mem_filter, Finset.mem_range,
      Finset.mem_Ico, min_eq_right h, max_eq_left h]
    by_cases hp : i < positivePrefix <;>
      by_cases hn : i < negativePrefix <;>
      simp [hp, hn] <;> omega

theorem exact_rank_pair_crossing_count
    (m positivePrefix negativePrefix : ℕ)
    (hpositive : positivePrefix ≤ m)
    (hnegative : negativePrefix ≤ m) :
    (rankCrossingIndices m positivePrefix negativePrefix).card =
      Nat.dist positivePrefix negativePrefix := by
  rw [rankCrossingIndices_eq_Ico m positivePrefix negativePrefix hpositive hnegative]
  simp [Nat.dist_eq_max_sub_min]

theorem exact_rank_pair_crossing_balance
    (m positivePrefix negativePrefix : ℕ)
    (hpositive : positivePrefix ≤ m)
    (hnegative : negativePrefix ≤ m) :
    (rankCrossingIndices m positivePrefix negativePrefix).card =
      Int.natAbs ((positivePrefix : ℤ) - negativePrefix) := by
  rw [exact_rank_pair_crossing_count m positivePrefix negativePrefix
    hpositive hnegative]
  rcases le_total positivePrefix negativePrefix with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    omega

/-- Replacing a common divisor by the pairwise gcd can only remove residual
prime factors. This is the arithmetic inheritance step in fixed-budget pair
compression. -/
theorem common_core_residual_budget
    (a b g budget : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < g)
    (hga : g ∣ a) (hgb : g ∣ b)
    (haBudget : omega (a / g) ≤ budget)
    (hbBudget : omega (b / g) ≤ budget) :
    omega (a / Nat.gcd a b) ≤ budget ∧
      omega (b / Nat.gcd a b) ≤ budget := by
  have hggcd : g ∣ Nat.gcd a b := Nat.dvd_gcd hga hgb
  have haDiv : a / Nat.gcd a b ∣ a / g :=
    Nat.div_dvd_div_left (Nat.gcd_dvd_left a b) hggcd
  have hbDiv : b / Nat.gcd a b ∣ b / g :=
    Nat.div_dvd_div_left (Nat.gcd_dvd_right a b) hggcd
  have hagPos : 0 < a / g := Nat.div_pos (Nat.le_of_dvd ha hga) hg
  have hbgPos : 0 < b / g := Nat.div_pos (Nat.le_of_dvd hb hgb) hg
  constructor
  · exact le_trans (Finset.card_le_card
      (Nat.primeFactors_mono haDiv hagPos.ne')) haBudget
  · exact le_trans (Finset.card_le_card
      (Nat.primeFactors_mono hbDiv hbgPos.ne')) hbBudget

end RiemannHypothesisProofFactory.MobiusResidualComplexity
