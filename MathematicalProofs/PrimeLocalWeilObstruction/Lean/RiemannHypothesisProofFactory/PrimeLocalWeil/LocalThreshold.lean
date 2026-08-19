import Mathlib.Analysis.Normed.Module.Basic

/-!
# The sharp local first-difference threshold

This file isolates the functional-analytic kernel of the prime-local Weil
obstruction.  The only input needed for sharpness is a normalized sequence
that becomes invariant under the selected translation.
-/

open Filter
open scoped Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The scalar-completed first-difference block used in the paper. -/
noncomputable def localBlock (T : E → E) (w b : ℝ) (x : E) : ℝ :=
  w * ‖x - T x‖ ^ 2 + (b - 2 * w) * ‖x‖ ^ 2

private theorem threshold_of_approximate_fixed_vectors
    (T : E → E) (w b : ℝ) (η : ℕ → E)
    (hη_norm : ∀ n, ‖η n‖ = 1)
    (hη_fixed : Tendsto (fun n => ‖η n - T (η n)‖) atTop (𝓝 0))
    (hnonneg : ∀ n, 0 ≤ localBlock T w b (η n)) :
    2 * w ≤ b := by
  have hblock : Tendsto (fun n => localBlock T w b (η n)) atTop (𝓝 (b - 2 * w)) := by
    have hfirst :
        Tendsto (fun n => w * ‖η n - T (η n)‖ ^ 2) atTop (𝓝 0) := by
      simpa using (hη_fixed.pow 2).const_mul w
    have hsecond :
        Tendsto (fun n => (b - 2 * w) * ‖η n‖ ^ 2) atTop (𝓝 (b - 2 * w)) := by
      simp [hη_norm]
    simpa [localBlock] using hfirst.add hsecond
  have hlimit_nonneg : 0 ≤ b - 2 * w := by
    exact isClosed_Ici.mem_of_tendsto hblock
      (Filter.Eventually.of_forall hnonneg)
  linarith

/-- An approximate fixed-vector family forces the exact scalar threshold.
No spectral theorem or completion of the test space is used. -/
theorem localBlock_nonnegative_iff
    (T : E → E) (w b : ℝ) (hw : 0 < w) (η : ℕ → E)
    (hη_norm : ∀ n, ‖η n‖ = 1)
    (hη_fixed : Tendsto (fun n => ‖η n - T (η n)‖) atTop (𝓝 0)) :
    (∀ x, 0 ≤ localBlock T w b x) ↔ 2 * w ≤ b := by
  constructor
  · intro hnonneg
    exact threshold_of_approximate_fixed_vectors T w b η hη_norm hη_fixed
      fun n => hnonneg (η n)
  · intro hb x
    unfold localBlock
    positivity

/-- Set-restricted version used by the manuscript: it is enough that all
members of the approximate fixed-vector family remain in the test space. -/
theorem localBlock_nonnegative_on_iff
    (S : Set E) (T : E → E) (w b : ℝ) (hw : 0 < w) (η : ℕ → E)
    (hη_mem : ∀ n, η n ∈ S) (hη_norm : ∀ n, ‖η n‖ = 1)
    (hη_fixed : Tendsto (fun n => ‖η n - T (η n)‖) atTop (𝓝 0)) :
    (∀ x ∈ S, 0 ≤ localBlock T w b x) ↔ 2 * w ≤ b := by
  constructor
  · intro hnonneg
    exact threshold_of_approximate_fixed_vectors T w b η hη_norm hη_fixed
      fun n => hnonneg (η n) (hη_mem n)
  · intro hb x _
    unfold localBlock
    positivity

end RiemannHypothesisProofFactory.PrimeLocalWeil
