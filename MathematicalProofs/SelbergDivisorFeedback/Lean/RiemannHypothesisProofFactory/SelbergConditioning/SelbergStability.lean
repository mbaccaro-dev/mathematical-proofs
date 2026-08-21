import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace RiemannHypothesisProofFactory.SelbergConditioning

/-- The ordered hyperbola sum used in Selberg's feedback statistic. -/
noncomputable def orderedHyperbolaSum
    (f g : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 (N / m), f m * g n

/-- The logarithmic first moment of a perturbation. -/
noncomputable def logarithmicMoment (e : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, e n * Real.log n

/-- The finite harmonic mass controlling the perturbation's hyperbola sums. -/
noncomputable def harmonicMass (e : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |e n| / (n : ℝ)

/-- The exact perturbation term in the ordered Selberg statistic. -/
noncomputable def selbergPerturbation
    (base e : ℕ → ℝ) (N : ℕ) : ℝ :=
  logarithmicMoment e N +
    2 * orderedHyperbolaSum e base N + orderedHyperbolaSum e e N

private theorem inner_abs_sum_le_harmonicMass
    (e : ℕ → ℝ) (N m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
    ∑ n ∈ Finset.Icc 1 (N / m), |e n| ≤
      ((N : ℝ) / m) * harmonicMass e N := by
  classical
  have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
  have hsub : Finset.Icc 1 (N / m) ⊆ Finset.Icc 1 N := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans (Nat.div_le_self N m)⟩
  have htruncated :
      ∑ n ∈ Finset.Icc 1 (N / m), |e n| / (n : ℝ) ≤
        harmonicMass e N := by
    unfold harmonicMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro n hnS hnT
      exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  calc
    ∑ n ∈ Finset.Icc 1 (N / m), |e n| ≤
        ∑ n ∈ Finset.Icc 1 (N / m),
          ((N : ℝ) / m) * (|e n| / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hnle : (n : ℝ) ≤ (N : ℝ) / m := by
        calc
          (n : ℝ) ≤ (N / m : ℕ) := by
            exact_mod_cast (Finset.mem_Icc.mp hn).2
          _ ≤ (N : ℝ) / m := Nat.cast_div_le
      calc
        |e n| = (n : ℝ) * (|e n| / (n : ℝ)) := by
          field_simp
        _ ≤ ((N : ℝ) / m) * (|e n| / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hnle
            (div_nonneg (abs_nonneg _) hnpos.le)
    _ = ((N : ℝ) / m) *
        (∑ n ∈ Finset.Icc 1 (N / m), |e n| / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ ((N : ℝ) / m) * harmonicMass e N := by
      exact mul_le_mul_of_nonneg_left htruncated
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

private theorem cross_term_abs_le
    (base e : ℕ → ℝ) (N : ℕ) (C : ℝ)
    (hC : 0 ≤ C)
    (hbase_nonneg : ∀ n, 0 ≤ base n)
    (hbase_prefix : ∀ y ≤ N,
      ∑ n ∈ Finset.Icc 1 y, base n ≤ C * (y : ℝ)) :
    |orderedHyperbolaSum e base N| ≤
      C * (N : ℝ) * harmonicMass e N := by
  classical
  unfold orderedHyperbolaSum
  calc
    |∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 (N / m), e m * base n| ≤
        ∑ m ∈ Finset.Icc 1 N,
          |∑ n ∈ Finset.Icc 1 (N / m), e m * base n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        |e m| * (C * (N / m : ℕ)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hinner_nonneg :
          0 ≤ ∑ n ∈ Finset.Icc 1 (N / m), base n := by
        apply Finset.sum_nonneg
        intro n hn
        exact hbase_nonneg n
      calc
        |∑ n ∈ Finset.Icc 1 (N / m), e m * base n| =
            |e m| * (∑ n ∈ Finset.Icc 1 (N / m), base n) := by
          rw [← Finset.mul_sum, abs_mul, abs_of_nonneg hinner_nonneg]
        _ ≤ |e m| * (C * (N / m : ℕ)) :=
          mul_le_mul_of_nonneg_left
            (hbase_prefix (N / m) (Nat.div_le_self N m)) (abs_nonneg _)
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        C * (N : ℝ) * (|e m| / (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : (0 : ℝ) < m := by
        exact_mod_cast (Finset.mem_Icc.mp hm).1
      calc
        |e m| * (C * (N / m : ℕ)) =
            (|e m| * C) * (N / m : ℕ) := by ring
        _ ≤ (|e m| * C) * ((N : ℝ) / m) :=
          mul_le_mul_of_nonneg_left Nat.cast_div_le
            (mul_nonneg (abs_nonneg _) hC)
        _ = C * (N : ℝ) * (|e m| / (m : ℝ)) := by
          field_simp
    _ = C * (N : ℝ) * harmonicMass e N := by
      unfold harmonicMass
      rw [Finset.mul_sum]

private theorem quadratic_term_abs_le
    (e : ℕ → ℝ) (N : ℕ) :
    |orderedHyperbolaSum e e N| ≤
      (N : ℝ) * (harmonicMass e N) ^ 2 := by
  classical
  have hmass_nonneg : 0 ≤ harmonicMass e N := by
    unfold harmonicMass
    positivity
  unfold orderedHyperbolaSum
  calc
    |∑ m ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 (N / m), e m * e n| ≤
        ∑ m ∈ Finset.Icc 1 N,
          |∑ n ∈ Finset.Icc 1 (N / m), e m * e n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 N,
        |e m| * (((N : ℝ) / m) * harmonicMass e N) := by
      apply Finset.sum_le_sum
      intro m hm
      calc
        |∑ n ∈ Finset.Icc 1 (N / m), e m * e n| ≤
            ∑ n ∈ Finset.Icc 1 (N / m), |e m * e n| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = |e m| * (∑ n ∈ Finset.Icc 1 (N / m), |e n|) := by
          simp only [abs_mul]
          rw [Finset.mul_sum]
        _ ≤ |e m| * (((N : ℝ) / m) * harmonicMass e N) :=
          mul_le_mul_of_nonneg_left (inner_abs_sum_le_harmonicMass e N m hm)
            (abs_nonneg _)
    _ = (N : ℝ) * harmonicMass e N *
        (∑ m ∈ Finset.Icc 1 N, |e m| / (m : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmne : (m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
      field_simp
    _ = (N : ℝ) * (harmonicMass e N) ^ 2 := by
      unfold harmonicMass
      ring

/-- A finite quantitative form of the Selberg-feedback stability argument.
The logarithmic perturbation moment, a linear prefix bound for the nonnegative
base weight, and the perturbation's harmonic mass together control the complete
ordered linear and quadratic feedback terms with the manuscript's constants. -/
theorem finite_selberg_feedback_stability
    (base e : ℕ → ℝ) (N : ℕ) (B C D : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hlog : |logarithmicMoment e N| ≤ B * (N : ℝ))
    (hbase_nonneg : ∀ n, 0 ≤ base n)
    (hbase_prefix : ∀ y ≤ N,
      ∑ n ∈ Finset.Icc 1 y, base n ≤ C * (y : ℝ))
    (hharmonic : harmonicMass e N ≤ D) :
    |selbergPerturbation base e N| ≤
      (B + 2 * C * D + D ^ 2) * (N : ℝ) := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmass_nonneg : 0 ≤ harmonicMass e N := by
    unfold harmonicMass
    positivity
  have hcross := cross_term_abs_le base e N C hC hbase_nonneg hbase_prefix
  have hquad := quadratic_term_abs_le e N
  have hmass_linear :
      C * (N : ℝ) * harmonicMass e N ≤ C * (N : ℝ) * D :=
    mul_le_mul_of_nonneg_left hharmonic (mul_nonneg hC hN)
  have hmass_square : (harmonicMass e N) ^ 2 ≤ D ^ 2 := by
    nlinarith
  unfold selbergPerturbation
  calc
    |logarithmicMoment e N + 2 * orderedHyperbolaSum e base N +
        orderedHyperbolaSum e e N| ≤
        |logarithmicMoment e N| +
          2 * |orderedHyperbolaSum e base N| +
          |orderedHyperbolaSum e e N| := by
      calc
        |logarithmicMoment e N + 2 * orderedHyperbolaSum e base N +
            orderedHyperbolaSum e e N| ≤
            |logarithmicMoment e N + 2 * orderedHyperbolaSum e base N| +
              |orderedHyperbolaSum e e N| := abs_add_le _ _
        _ ≤ (|logarithmicMoment e N| +
              |2 * orderedHyperbolaSum e base N|) +
              |orderedHyperbolaSum e e N| := by
            gcongr
            exact abs_add_le _ _
        _ = |logarithmicMoment e N| +
              2 * |orderedHyperbolaSum e base N| +
              |orderedHyperbolaSum e e N| := by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ B * (N : ℝ) + 2 * (C * (N : ℝ) * harmonicMass e N) +
          (N : ℝ) * (harmonicMass e N) ^ 2 := by
      gcongr
    _ ≤ B * (N : ℝ) + 2 * (C * (N : ℝ) * D) +
          (N : ℝ) * D ^ 2 := by
      gcongr
    _ = (B + 2 * C * D + D ^ 2) * (N : ℝ) := by ring

end RiemannHypothesisProofFactory.SelbergConditioning
