import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter Finset
open scoped ArithmeticFunction BigOperators Nat.Prime Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

variable {E : Type*} [SeminormedAddCommGroup E]

noncomputable def localBlock (T : E → E) (w b : ℝ) (x : E) : ℝ :=
  w * ‖x - T x‖ ^ 2 + (b - 2 * w) * ‖x‖ ^ 2

noncomputable def weilWeight (n : ℕ) : ℝ :=
  Λ n / Real.sqrt n

noncomputable def weightedPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, weilWeight n

noncomputable def primePowerPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ (Ioc 0 N).filter IsPrimePow, weilWeight n

noncomputable def scalarPartialSum (b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, b n

theorem localBlock_nonnegative_iff
    (T : E → E) (w b : ℝ) (hw : 0 < w) (η : ℕ → E)
    (hη_norm : ∀ n, ‖η n‖ = 1)
    (hη_fixed : Tendsto (fun n => ‖η n - T (η n)‖) atTop (𝓝 0)) :
    (∀ x, 0 ≤ localBlock T w b x) ↔ 2 * w ≤ b := by
  sorry

theorem weightedPartialSum_tendsto_atTop :
    Tendsto weightedPartialSum atTop atTop := by
  sorry

theorem primePowerPartialSum_tendsto_atTop :
    Tendsto primePowerPartialSum atTop atTop := by
  sorry

theorem scalarPartialSum_tendsto_atTop
    (b : ℕ → ℝ) (hcost : ∀ n, 2 * weilWeight n ≤ b n) :
    Tendsto (scalarPartialSum b) atTop atTop := by
  sorry

end RiemannHypothesisProofFactory.PrimeLocalWeil
