import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Adjacent-regime controls

These are the paper's two negative controls: finite actual prefixes remain
positive, and infinite synthetic blocks converge when their weights are
summable.
-/

open Finset
open scoped BigOperators Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

variable {E : Type*} [SeminormedAddCommGroup E]

/-- A first-difference term before scalar completion. -/
noncomputable def firstDifferenceTerm (c : ℝ) (T : E → E) (x : E) : ℝ :=
  c * ‖x - T x‖ ^ 2

/-- Every finite prefix with nonnegative weights is nonnegative. -/
theorem finitePrefix_nonnegative
    (s : Finset ℕ) (c : ℕ → ℝ) (T : ℕ → E → E)
    (hc : ∀ j, 0 ≤ c j) (x : E) :
    0 ≤ ∑ j ∈ s, firstDifferenceTerm (c j) (T j) x := by
  exact sum_nonneg fun j _ => mul_nonneg (hc j) (sq_nonneg _)

/-- The exact comparison estimate used by the summable-weight control. -/
theorem firstDifferenceTerm_le
    (c : ℝ) (hc : 0 ≤ c) (T : E → E)
    (hT : ∀ y, ‖T y‖ = ‖y‖) (x : E) :
    firstDifferenceTerm c T x ≤ 4 * ‖x‖ ^ 2 * c := by
  have hnorm : ‖x - T x‖ ≤ 2 * ‖x‖ := by
    calc
      ‖x - T x‖ ≤ ‖x‖ + ‖T x‖ := norm_sub_le _ _
      _ = 2 * ‖x‖ := by rw [hT]; ring
  have hsquare : ‖x - T x‖ ^ 2 ≤ 4 * ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg (x - T x), norm_nonneg x]
  unfold firstDifferenceTerm
  nlinarith

/-- Summable nonnegative weights make the infinite synthetic control
convergent for every vector. -/
theorem summable_firstDifferenceTerm
    (c : ℕ → ℝ) (hc_nonneg : ∀ j, 0 ≤ c j) (hc : Summable c)
    (T : ℕ → E → E) (hT : ∀ j y, ‖T j y‖ = ‖y‖) (x : E) :
    Summable (fun j => firstDifferenceTerm (c j) (T j) x) := by
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (hc_nonneg j) (sq_nonneg _))
    (fun j => firstDifferenceTerm_le (c j) (hc_nonneg j) (T j) (hT j) x) ?_
  exact hc.mul_left (4 * ‖x‖ ^ 2)

/-- The convergent synthetic control has a nonnegative ordinary sum. -/
theorem tsum_firstDifferenceTerm_nonnegative
    (c : ℕ → ℝ) (hc_nonneg : ∀ j, 0 ≤ c j)
    (T : ℕ → E → E) (x : E) :
    0 ≤ ∑' j, firstDifferenceTerm (c j) (T j) x := by
  exact tsum_nonneg fun j => mul_nonneg (hc_nonneg j) (sq_nonneg _)

end RiemannHypothesisProofFactory.PrimeLocalWeil
