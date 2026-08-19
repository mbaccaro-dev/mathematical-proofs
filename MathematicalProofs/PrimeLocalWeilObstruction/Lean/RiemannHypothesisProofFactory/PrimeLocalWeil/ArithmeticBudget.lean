import Mathlib.NumberTheory.Chebyshev
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The actual prime-power scalar budget

This file is an isolated formal candidate for the arithmetic seam in the
prime-local Weil obstruction paper.  It proves the divergence of the exact
weights `Lambda(n) / sqrt(n)` through Chebyshev's elementary lower bound.
-/

open Filter Finset
open scoped ArithmeticFunction BigOperators Nat.Prime Topology

namespace RiemannHypothesisProofFactory.PrimeLocalWeil

/-- The scalar weight attached to the integer `n`.  It vanishes away from
prime powers because the von Mangoldt function does. -/
noncomputable def weilWeight (n : ℕ) : ℝ :=
  Λ n / Real.sqrt n

/-- The weighted partial sum through `N`, with the zero index omitted. -/
noncomputable def weightedPartialSum (N : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, weilWeight n

theorem weilWeight_nonneg (n : ℕ) : 0 ≤ weilWeight n := by
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- Each weighted partial sum dominates `psi(N) / sqrt(N)`. -/
theorem psi_div_sqrt_le_weightedPartialSum (N : ℕ) :
    Chebyshev.psi N / Real.sqrt N ≤ weightedPartialSum N := by
  rw [Chebyshev.psi]
  simp only [Nat.floor_natCast]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
  have hsqrt : Real.sqrt n ≤ Real.sqrt N := by
    exact Real.sqrt_le_sqrt (by exact_mod_cast hnN)
  exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
    (Real.sqrt_pos.2 (by exact_mod_cast (Finset.mem_Ioc.mp hn).1)) hsqrt

private theorem log_nat_succ_le_four_mul_sqrt (N : ℕ) (hN : 1 ≤ N) :
    Real.log (N + 1) ≤ 4 * Real.sqrt N := by
  have hlog := Real.log_le_rpow_div (x := (N + 1 : ℝ)) (by positivity)
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hcast : (N + 1 : ℝ) ≤ 4 * N := by
    exact_mod_cast (show N + 1 ≤ 4 * N by omega)
  have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
    calc
      Real.sqrt (4 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 := Real.sqrt_sq (by norm_num)
  have hsqrt : Real.sqrt (N + 1) ≤ 2 * Real.sqrt N := by
    calc
      Real.sqrt (N + 1) ≤ Real.sqrt (4 * N) := Real.sqrt_le_sqrt hcast
      _ = 2 * Real.sqrt N := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        rw [hsqrt_four]
  rw [← Real.sqrt_eq_rpow] at hlog
  norm_num at hlog
  nlinarith

/-- Chebyshev's lower bound already forces the weighted budget above a
positive multiple of `sqrt N`, up to an absolute constant. -/
theorem sqrt_lower_le_psi_div_sqrt (N : ℕ) (hN : 1 ≤ N) :
    Real.log 2 * Real.sqrt N - 4 ≤ Chebyshev.psi N / Real.sqrt N := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hsqrt_pos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  rw [le_div_iff₀ hsqrt_pos]
  have hsquare : Real.sqrt N ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  calc
    (Real.log 2 * Real.sqrt N - 4) * Real.sqrt N =
        Real.log 2 * (Real.sqrt N * Real.sqrt N) - 4 * Real.sqrt N := by ring
    _ = (N : ℝ) * Real.log 2 - 4 * Real.sqrt N := by
      rw [← pow_two, hsquare]
      ring
    _ ≤ (N : ℝ) * Real.log 2 - Real.log (N + 1) := by
      linarith [log_nat_succ_le_four_mul_sqrt N hN]
    _ ≤ Chebyshev.psi N := Chebyshev.psi_ge N

/-- The lower comparison used for the exact divergence statement tends to
positive infinity. -/
private theorem sqrt_lower_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log 2 * Real.sqrt N - 4) atTop atTop := by
  have hsqrt : Tendsto (fun N : ℕ => Real.sqrt N) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmul : Tendsto (fun N : ℕ => Real.log 2 * Real.sqrt N) atTop atTop :=
    hsqrt.const_mul_atTop hlog
  simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-4 : ℝ) hmul

/-- The exact prime-power scalar budget in the paper diverges.  This is a
direct formal replacement for the manuscript's zeta-limit argument. -/
theorem weightedPartialSum_tendsto_atTop :
    Tendsto weightedPartialSum atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ sqrt_lower_tendsto_atTop
  filter_upwards [eventually_atTop.2 ⟨1, fun N hN => hN⟩] with N hN
  exact (sqrt_lower_le_psi_div_sqrt N hN).trans
    (psi_div_sqrt_le_weightedPartialSum N)

end RiemannHypothesisProofFactory.PrimeLocalWeil
