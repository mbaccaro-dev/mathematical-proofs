import BoundaryConstantObstruction.IncompleteGamma.OrderOneGrowth
import Mathlib.Topology.Order.Compact

open Asymptotics Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- The closed-disk maximum modulus used in the manuscript's growth statement. -/
def diskMaxNorm (N : ℕ) (t R : ℝ) : ℝ :=
  sSup ((fun z : ℂ => ‖F N t z‖) '' Metric.closedBall 0 R)

lemma diskNormRange_bddAbove {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    BddAbove ((fun z : ℂ => ‖F N t z‖) '' Metric.closedBall 0 R) := by
  refine ⟨Real.exp (orderOneGrowthBound N R), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact norm_F_le_orderOneGrowthBound hN ht0 ht1 hR z (by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz)

lemma diskNormRange_nonempty (N : ℕ) (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    ((fun z : ℂ => ‖F N t z‖) '' Metric.closedBall 0 R).Nonempty := by
  refine ⟨‖F N t 0‖, 0, ?_, rfl⟩
  simpa [Metric.mem_closedBall] using hR

lemma diskMaxNorm_le_exp_orderOneGrowthBound {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    diskMaxNorm N t R ≤ Real.exp (orderOneGrowthBound N R) := by
  unfold diskMaxNorm
  exact csSup_le (diskNormRange_nonempty N t hR) (by
    rintro y ⟨z, hz, rfl⟩
    exact norm_F_le_orderOneGrowthBound hN ht0 ht1 hR z (by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz))

/-- A radius-independent positive value witnessed at `i / 2`. -/
def diskLowerBound (N : ℕ) : ℝ :=
  1 / 2 - boundaryConstant N

lemma diskLowerBound_pos {N : ℕ} (hN : 1 ≤ N) : 0 < diskLowerBound N := by
  unfold diskLowerBound
  linarith [boundaryConstant_lt_half hN]

lemma diskLowerBound_le_norm_F_I_div_two {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    diskLowerBound N ≤ ‖F N t (Complex.I / 2)‖ := by
  have hc : 0 ≤ boundaryConstant N := (boundaryConstant_pos hN).le
  have hvalue : 0 ≤ 1 / 2 - (1 - t) * boundaryConstant N := by
    have htc : 0 ≤ t * boundaryConstant N := mul_nonneg ht0 hc
    nlinarith [boundaryConstant_lt_half hN]
  rw [F_I_div_two, norm_real, Real.norm_eq_abs, abs_of_nonneg hvalue]
  unfold diskLowerBound
  nlinarith [mul_nonneg ht0 hc]

lemma diskLowerBound_le_diskMaxNorm {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
    diskLowerBound N ≤ diskMaxNorm N t R := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hz : Complex.I / 2 ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    norm_num
    linarith
  exact (diskLowerBound_le_norm_F_I_div_two hN ht0 ht1).trans
    (le_csSup (diskNormRange_bddAbove hN ht0 ht1 hR0) ⟨_, hz, rfl⟩)

lemma diskMaxNorm_pos {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
    0 < diskMaxNorm N t R :=
  (diskLowerBound_pos hN).trans_le (diskLowerBound_le_diskMaxNorm hN ht0 ht1 hR)

lemma log_diskMaxNorm_le_orderOneGrowthBound {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
    Real.log (diskMaxNorm N t R) ≤ orderOneGrowthBound N R := by
  apply (Real.log_le_iff_le_exp (diskMaxNorm_pos hN ht0 ht1 hR)).2
  exact diskMaxNorm_le_exp_orderOneGrowthBound hN ht0 ht1 (zero_le_one.trans hR)

lemma log_diskLowerBound_le_log_diskMaxNorm {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 1 ≤ R) :
    Real.log (diskLowerBound N) ≤ Real.log (diskMaxNorm N t R) := by
  exact Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr (diskLowerBound_pos hN))
    (Set.mem_Ioi.mpr (diskMaxNorm_pos hN ht0 ht1 hR))
    (diskLowerBound_le_diskMaxNorm hN ht0 ht1 hR)

/-- The exact closed-disk maximum statement printed in the manuscript. -/
theorem log_diskMaxNorm_F_isBigO {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (fun R : ℝ => Real.log (diskMaxNorm N t R)) =O[atTop]
      (fun R : ℝ => R * Real.log (2 + R)) := by
  let A : ℝ := 1 + 2 * orderOneMoment N + boundaryConstant N
  let C : ℝ := A + |Real.log (diskLowerBound N)| + 1
  have hA : 0 ≤ A := by
    dsimp only [A]
    have hM := orderOneMoment_nonneg N
    have hc := (boundaryConstant_pos hN).le
    linarith
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  rw [Asymptotics.isBigO_iff]
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with R hR
  have hexpone : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hR1 : 1 ≤ R := hexpone.trans hR
  have harg : 0 < 2 + R := by linarith
  have hlog : 1 ≤ Real.log (2 + R) := by
    exact (Real.le_log_iff_exp_le harg).2 (by linarith)
  let S : ℝ := R * Real.log (2 + R)
  have hS1 : 1 ≤ S := by
    dsimp only [S]
    nlinarith [mul_nonneg (sub_nonneg.mpr hR1) (sub_nonneg.mpr hlog)]
  have hupper : Real.log (diskMaxNorm N t R) ≤ A + S := by
    have h := log_diskMaxNorm_le_orderOneGrowthBound hN ht0 ht1 hR1
    simpa only [orderOneGrowthBound, A, S] using h
  have hlower := log_diskLowerBound_le_log_diskMaxNorm hN ht0 ht1 hR1
  have hAS : A + S ≤ C * S := by
    have hprod : 0 ≤ (A + |Real.log (diskLowerBound N)|) * (S - 1) :=
      mul_nonneg (add_nonneg hA (abs_nonneg _)) (sub_nonneg.mpr hS1)
    have hid :
        C * S - (A + |Real.log (diskLowerBound N)| + S) =
          (A + |Real.log (diskLowerBound N)|) * (S - 1) := by
      dsimp only [C]
      ring
    have hwide : A + |Real.log (diskLowerBound N)| + S ≤ C * S := by
      rw [← sub_nonneg, hid]
      exact hprod
    linarith [abs_nonneg (Real.log (diskLowerBound N))]
  have habsBudget : |Real.log (diskLowerBound N)| ≤ C * S := by
    have hCS : C ≤ C * S := by
      nlinarith [mul_nonneg hC (sub_nonneg.mpr hS1)]
    dsimp only [C] at hCS
    linarith
  have habs : |Real.log (diskMaxNorm N t R)| ≤ C * S := by
    apply abs_le.2
    constructor
    · have hnegabs : -|Real.log (diskLowerBound N)| ≤
          Real.log (diskLowerBound N) := neg_abs_le _
      linarith
    · exact hupper.trans hAS
  simpa only [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hS1), S] using habs

end IncompleteGammaApproximant
