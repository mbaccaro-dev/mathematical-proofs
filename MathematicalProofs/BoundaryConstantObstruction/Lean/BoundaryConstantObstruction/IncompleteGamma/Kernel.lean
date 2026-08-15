import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- The `n`th summand of the finite Riemann kernel after the logarithmic
change of variables.  The paper numbers summands from one, hence `n + 1`. -/
def kernelTerm (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2 - Real.pi * (n + 1 : ℝ) ^ 2 * Real.exp (2 * u))

/-- The finite kernel `S_N` in equation (3.1) of the manuscript. -/
def S (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, kernelTerm n u

/-- The explicit form of `S_N'' - S_N / 4` for one summand. -/
def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  let a := Real.pi * (n + 1 : ℝ) ^ 2
  Real.exp (u / 2 - a * Real.exp (2 * u)) *
    (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u))

/-- The finite cosine-transform kernel `Φ_N`. -/
def Phi (N : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, phiTerm n u

/-- The positive tail summand in the manuscript's exact formula for `c_N`. -/
def boundaryTerm (n : ℕ) : ℝ :=
  (4 * Real.pi * (n : ℝ) ^ 2 - 1) *
    Real.exp (-Real.pi * (n : ℝ) ^ 2)

/-- The manuscript's boundary constant, normalized by its exact positive-tail
formula. The index `k` represents the manuscript index `n = N + 1 + k`. -/
def boundaryConstant (N : ℕ) : ℝ :=
  ∑' k : ℕ, boundaryTerm (N + 1 + k)

/-- The exact cosine-transform term `H_N`. -/
def H (N : ℕ) (z : ℂ) : ℂ :=
  2 * ∫ u in Ioi (0 : ℝ),
    (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))

/-- The positive constant-shift family from the manuscript. -/
def F (N : ℕ) (t : ℝ) (z : ℂ) : ℂ :=
  H N z + (t * boundaryConstant N : ℝ)

/-- The direct symmetrized approximant is the endpoint `t = 1`. -/
def Xi (N : ℕ) (z : ℂ) : ℂ := F N 1 z

lemma nat_cast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
      nlinarith

lemma exp_neg_pi_sq_le_exp_neg_nat (n : ℕ) :
    Real.exp (-Real.pi * (n : ℝ) ^ 2) ≤ Real.exp (-(n : ℝ)) := by
  apply Real.exp_le_exp.mpr
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hn := nat_cast_le_sq n
  nlinarith [mul_le_mul_of_nonneg_left hn (le_trans (by positivity) hpi)]

lemma boundaryTerm_norm_bound (n : ℕ) :
    ‖boundaryTerm n‖ ≤
      (4 * Real.pi * (n : ℝ) ^ 2 + 1) * Real.exp (-(n : ℝ)) := by
  rw [boundaryTerm, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp := exp_neg_pi_sq_le_exp_neg_nat n
  have hcoeff :
      |4 * Real.pi * (n : ℝ) ^ 2 - 1| ≤
        4 * Real.pi * (n : ℝ) ^ 2 + 1 := by
    rw [abs_le]
    constructor <;> nlinarith [Real.pi_pos, sq_nonneg (n : ℝ)]
  exact mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by positivity)

lemma summable_boundary_majorant :
    Summable (fun n : ℕ ↦
      (4 * Real.pi * (n : ℝ) ^ 2 + 1) * Real.exp (-(n : ℝ))) := by
  have h2 : Summable (fun n : ℕ ↦ (n : ℝ) ^ 2 * Real.exp (-1 * (n : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul 2 (by norm_num)
  have h0 : Summable (fun n : ℕ ↦ Real.exp (-1 * (n : ℝ))) := by
    simpa only [neg_one_mul] using Real.summable_exp_neg_nat
  simpa only [add_mul, one_mul, neg_one_mul, mul_assoc] using
    (h2.mul_left (4 * Real.pi)).add h0

lemma summable_boundaryTerm : Summable boundaryTerm := by
  exact summable_boundary_majorant.of_norm_bounded boundaryTerm_norm_bound

lemma summable_boundaryTail (N : ℕ) :
    Summable (fun k : ℕ ↦ boundaryTerm (N + 1 + k)) := by
  exact summable_boundaryTerm.comp_injective (fun _ _ h => by omega)

lemma boundaryTerm_pos {n : ℕ} (hn : 1 ≤ n) : 0 < boundaryTerm n := by
  rw [boundaryTerm]
  have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have : 1 < 4 * Real.pi * (n : ℝ) ^ 2 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ((n : ℝ) - 1)]
  positivity

theorem boundaryConstant_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < boundaryConstant N := by
  rw [boundaryConstant]
  exact (summable_boundaryTail N).tsum_pos
    (fun k ↦ (boundaryTerm_pos (n := N + 1 + k) (by omega)).le)
    0 (by simpa using boundaryTerm_pos (n := N + 1) (by omega))

@[simp] theorem Xi_eq_F_one (N : ℕ) : Xi N = F N 1 := rfl

end IncompleteGammaApproximant
