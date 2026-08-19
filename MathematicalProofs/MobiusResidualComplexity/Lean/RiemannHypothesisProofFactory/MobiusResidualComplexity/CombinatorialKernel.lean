import Mathlib.Tactic

/-!
# Finite kernel for the Möbius residual-complexity paper

This module checks the finite algebra used by the matching identity, the
zero-sum cell balance, the terminal exponent contradiction, the square-root
constant, and the endpoint-doubling connector. It does not formalize the
paper's analytic number theory or its full matching and compression theorems.
-/

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

/-- Two opposite unit signs cancel when both endpoints lie below a cutoff. -/
theorem opposite_sign_pair_cancel (sign : ℤ) : sign + (-sign) = 0 := by
  ring

/-- A finite collection of terms of absolute value at most one has total
absolute value at most its cardinality. -/
theorem abs_sum_le_card
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hunit : ∀ i ∈ s, |f i| ≤ 1) :
    |∑ i ∈ s, f i| ≤ s.card := by
  calc
    |∑ i ∈ s, f i| ≤ ∑ i ∈ s, |f i| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, (1 : ℝ) := by
      exact Finset.sum_le_sum fun i hi => hunit i hi
    _ = s.card := by simp

/-- Once complete pairs have canceled, crossing pairs and uncovered vertices
give the matching bound printed in the paper. -/
theorem finite_matching_bound
    {ι : Type*} [DecidableEq ι]
    (crossing uncovered : Finset ι) (contribution : ι → ℝ) (total : ℝ)
    (hcrossing : ∀ i ∈ crossing, |contribution i| ≤ 1)
    (huncovered : ∀ i ∈ uncovered, |contribution i| ≤ 1)
    (hdecomp : total =
      ∑ i ∈ crossing, contribution i + ∑ i ∈ uncovered, contribution i) :
    |total| ≤ crossing.card + uncovered.card := by
  have hc : |∑ i ∈ crossing, contribution i| ≤ crossing.card :=
    abs_sum_le_card crossing contribution hcrossing
  have hu : |∑ i ∈ uncovered, contribution i| ≤ uncovered.card :=
    abs_sum_le_card uncovered contribution huncovered
  rw [hdecomp]
  calc
    |∑ i ∈ crossing, contribution i +
        ∑ i ∈ uncovered, contribution i| ≤
        |∑ i ∈ crossing, contribution i| +
          |∑ i ∈ uncovered, contribution i| := abs_add_le _ _
    _ ≤ crossing.card + uncovered.card := add_le_add hc hu

/-- A zero-sum cell of positive and negative unit signs has equally many of
each, so increasing-rank pairing uses every vertex. -/
theorem zero_sum_unit_cell_balanced
    (positive negative : ℕ)
    (hzero : (positive : ℤ) - (negative : ℤ) = 0) :
    positive = negative := by
  omega

/-- The strict lower and weak upper sides of the key exponent sandwich cannot
hold once the upper exponent is no larger than the lower exponent. -/
theorem strict_exponent_sandwich_impossible
    (lower middle upper : ℝ)
    (hlower : lower < middle)
    (hmiddle : middle ≤ upper)
    (hupper : upper ≤ lower) : False := by
  linarith

/-- Substituting the square-root exponents into the general threshold gives
the displayed constant before taking the limit in epsilon. -/
theorem square_root_threshold_identity (ε : ℝ) :
    (1 - (1 / 2 + ε)) * (1 - (1 / 2 + ε)) =
      1 / 4 - ε + ε ^ 2 := by
  ring

/-- The endpoint connector used in the sparse-jump repair: an endpoint within
half the cell maximum forces the cell maximum below twice that endpoint. -/
theorem cell_max_le_twice_endpoint
    (cellMax endpoint : ℝ)
    (hgap : cellMax - endpoint ≤ cellMax / 2) :
    cellMax ≤ 2 * endpoint := by
  linarith

/-- The preceding connector lifts an endpoint cutoff to the doubled cutoff
used in the jump count. -/
theorem cell_max_le_doubled_cutoff
    (cellMax endpoint cutoff : ℝ)
    (hcell : cellMax ≤ 2 * endpoint)
    (hendpoint : endpoint ≤ cutoff) :
    cellMax ≤ 2 * cutoff := by
  linarith

end RiemannHypothesisProofFactory.MobiusResidualComplexity
