import RiemannHypothesisProofFactory.PrimeLocalWeil.ArithmeticBudget

/-!
# From local positivity costs to an infinite scalar budget

This file formalizes the second implication in the paper: once every local
block pays at least twice its exact Weil weight, the ordinary scalar budget
must diverge.
-/

open Filter Finset
open scoped BigOperators Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

/-- Partial sums of an arbitrary scalar budget, using the paper's positive
integer indexing convention. -/
noncomputable def scalarPartialSum (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, b n

/-- The exact local lower costs force the scalar budget to positive infinity. -/
theorem scalarPartialSum_tendsto_atTop
    (b : ℕ → ℝ) (hcost : ∀ n, 2 * weilWeight n ≤ b n) :
    Tendsto (scalarPartialSum b) atTop atTop := by
  have htwice : Tendsto (fun N => 2 * weightedPartialSum N) atTop atTop :=
    weightedPartialSum_tendsto_atTop.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ htwice
  filter_upwards with N
  calc
    2 * weightedPartialSum N = ∑ n ∈ Ioc 0 N, 2 * weilWeight n := by
      simp [weightedPartialSum, mul_sum]
    _ ≤ ∑ n ∈ Ioc 0 N, b n := by
      exact sum_le_sum fun n _ => hcost n
    _ = scalarPartialSum b N := rfl

end RiemannHypothesisProofFactory.PrimeLocalWeil
