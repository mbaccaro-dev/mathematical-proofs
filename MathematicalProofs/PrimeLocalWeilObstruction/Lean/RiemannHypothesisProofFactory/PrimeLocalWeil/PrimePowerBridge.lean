import RiemannHypothesisProofFactory.PrimeLocalWeil.ArithmeticBudget

/-!
# Exact prime-power indexing bridge

The manuscript sums over prime powers.  The arithmetic kernel naturally sums
the von Mangoldt function over positive integers; this file proves that the
two finite-prefix conventions are definitionally connected by the support of
the von Mangoldt function.
-/

open Filter Finset
open scoped ArithmeticFunction BigOperators Nat.Prime Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

/-- The exact positive-integer prefix filtered to prime powers. -/
noncomputable def primePowerPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter IsPrimePow, weilWeight n

/-- Terms outside the prime powers vanish, so filtering changes no prefix. -/
theorem weightedPartialSum_eq_primePowerPartialSum (N : ℕ) :
    weightedPartialSum N = primePowerPartialSum N := by
  classical
  unfold weightedPartialSum primePowerPartialSum
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hnpp : ¬IsPrimePow n := by
    simpa only [Finset.mem_filter, hn, true_and] using hnot
  simp [weilWeight, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnpp]

/-- The manuscript-indexed prime-power partial sums tend to positive
infinity. -/
theorem primePowerPartialSum_tendsto_atTop :
    Tendsto primePowerPartialSum atTop atTop := by
  exact weightedPartialSum_tendsto_atTop.congr'
    (Filter.Eventually.of_forall weightedPartialSum_eq_primePowerPartialSum)

end RiemannHypothesisProofFactory.PrimeLocalWeil
