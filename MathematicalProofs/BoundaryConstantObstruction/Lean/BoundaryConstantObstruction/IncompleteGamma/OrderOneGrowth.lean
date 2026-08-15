import BoundaryConstantObstruction.IncompleteGamma.Growth

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- A Young-type envelope tuned to the manuscript's `R log (2 + R)` scale. -/
lemma radius_times_u_le_log_envelope {R u : ℝ} (hR : 0 ≤ R) :
    R * u ≤ (R / 2) * Real.log (1 + R) + Real.exp (2 * u) / 2 := by
  have hden : 0 < 1 + R := by linarith
  have hx : 0 < Real.exp (2 * u) / (1 + R) := div_pos (Real.exp_pos _) hden
  have hlog := Real.log_le_sub_one_of_pos hx
  rw [Real.log_div (Real.exp_ne_zero _) hden.ne', Real.log_exp] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog (show 0 ≤ R / 2 by positivity)
  have hfrac : R / (1 + R) ≤ 1 := (div_le_one hden).2 (by linarith)
  have hexp0 : 0 ≤ Real.exp (2 * u) / 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfrac hexp0
  field_simp at hscaled hmul ⊢
  nlinarith

lemma integrableOn_phiTerm_mul_orderOneWeight (n : ℕ) :
    IntegrableOn
      (fun u : ℝ => phiTerm n u * Real.exp (Real.exp (2 * u) / 2))
      (Ioi 0) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  have ha' : 0 < a - 1 / 2 := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [Real.pi_gt_three, sq_nonneg ((n + 1 : ℝ) - 1)]
  let major : ℝ → ℝ := fun u =>
    4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - (a - 1 / 2) * Real.exp (2 * u)) +
      6 * a * Real.exp ((5 / 2 : ℝ) * u - (a - 1 / 2) * Real.exp (2 * u))
  have h9 :=
    (integrableOn_exp_linear_sub_exp_two (9 / 2 : ℝ) (a - 1 / 2) (by norm_num) ha').const_mul
      (4 * a ^ 2)
  have h5 :=
    (integrableOn_exp_linear_sub_exp_two (5 / 2 : ℝ) (a - 1 / 2) (by norm_num) ha').const_mul
      (6 * a)
  have hmajor : IntegrableOn major (Ioi 0) := h9.add h5
  refine hmajor.mono'
    ((phiTerm_continuous n).mul (by fun_prop) |>.aestronglyMeasurable) ?_
  filter_upwards with u
  have h9exp :
      Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) *
          Real.exp (Real.exp (2 * u) / 2) =
        Real.exp ((9 / 2 : ℝ) * u - (a - 1 / 2) * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5exp :
      Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) *
          Real.exp (Real.exp (2 * u) / 2) =
        Real.exp ((5 / 2 : ℝ) * u - (a - 1 / 2) * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), phiTerm_eq_exp_sub_exp]
  change
    |4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) -
        6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))| *
        Real.exp (Real.exp (2 * u) / 2) ≤ major u
  calc
    _ ≤ (4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) +
          6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))) *
          Real.exp (Real.exp (2 * u) / 2) := by
      gcongr
      let X := 4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u))
      let Y := 6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))
      have hX : 0 < X := by dsimp only [X]; positivity
      have hY : 0 < Y := by dsimp only [Y, a]; positivity
      change |X - Y| ≤ X + Y
      calc
        |X - Y| ≤ |X| + |Y| := abs_sub X Y
        _ = X + Y := by rw [abs_of_pos hX, abs_of_pos hY]
    _ = 4 * a ^ 2 *
          (Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) *
            Real.exp (Real.exp (2 * u) / 2)) +
        6 * a *
          (Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) *
            Real.exp (Real.exp (2 * u) / 2)) := by ring
    _ = major u := by rw [h9exp, h5exp]

lemma integrableOn_Phi_mul_orderOneWeight (N : ℕ) :
    IntegrableOn
      (fun u : ℝ => Phi N u * Real.exp (Real.exp (2 * u) / 2))
      (Ioi 0) := by
  rw [show
      (fun u : ℝ => Phi N u * Real.exp (Real.exp (2 * u) / 2)) =
        ∑ n ∈ Finset.range N,
          (fun u : ℝ => phiTerm n u * Real.exp (Real.exp (2 * u) / 2)) by
    funext u
    simp [Phi, Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.range N)
    (fun n _ => integrableOn_phiTerm_mul_orderOneWeight n)

/-- Fixed weighted `L¹` moment controlling the manuscript-scale disk bound. -/
def orderOneMoment (N : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), |Phi N u| * Real.exp (Real.exp (2 * u) / 2)

lemma integrableOn_abs_Phi_mul_orderOneWeight (N : ℕ) :
    IntegrableOn
      (fun u : ℝ => |Phi N u| * Real.exp (Real.exp (2 * u) / 2))
      (Ioi 0) := by
  change Integrable
    (fun u : ℝ => |Phi N u| * Real.exp (Real.exp (2 * u) / 2))
      (volume.restrict (Ioi 0))
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    (integrableOn_Phi_mul_orderOneWeight N).norm

lemma orderOneMoment_nonneg (N : ℕ) : 0 ≤ orderOneMoment N := by
  unfold orderOneMoment
  exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)

lemma norm_H_le_orderOneMoment (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖H N z‖ ≤
      2 * Real.exp ((R / 2) * Real.log (1 + R)) * orderOneMoment N := by
  let c : ℝ := Real.exp ((R / 2) * Real.log (1 + R))
  let g : ℝ → ℝ := fun u =>
    c * (|Phi N u| * Real.exp (Real.exp (2 * u) / 2))
  have hg : IntegrableOn g (Ioi 0) :=
    (integrableOn_abs_Phi_mul_orderOneWeight N).const_mul c
  have hpoint : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi 0)),
      ‖(Phi N u : ℂ) * Complex.cos (z * (u : ℂ))‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (R * u) := by
      refine (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]
      exact mul_le_mul_of_nonneg_right hz hu0
    have henv := radius_times_u_le_log_envelope (R := R) (u := u) hR
    have hexp :
        Real.exp (R * u) ≤
          Real.exp ((R / 2) * Real.log (1 + R)) *
            Real.exp (Real.exp (2 * u) / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr henv
    simp only [norm_mul, norm_real, Real.norm_eq_abs]
    dsimp only [g, c]
    calc
      |Phi N u| * ‖Complex.cos (z * (u : ℂ))‖ ≤
          |Phi N u| * Real.exp (R * u) := by gcongr
      _ ≤ |Phi N u| *
          (Real.exp ((R / 2) * Real.log (1 + R)) *
            Real.exp (Real.exp (2 * u) / 2)) := by gcongr
      _ = Real.exp ((R / 2) * Real.log (1 + R)) *
          (|Phi N u| * Real.exp (Real.exp (2 * u) / 2)) := by ring
  have hint := norm_integral_le_of_norm_le hg hpoint
  calc
    ‖H N z‖ = 2 * ‖∫ u in Ioi (0 : ℝ),
        (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))‖ := by
      rw [H, norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (∫ u in Ioi (0 : ℝ), g u) := by gcongr
    _ = 2 * Real.exp ((R / 2) * Real.log (1 + R)) * orderOneMoment N := by
      dsimp only [g, c, orderOneMoment]
      rw [integral_const_mul]
      ring

lemma half_radius_log_one_add_le_orderOneScale {R : ℝ} (hR : 0 ≤ R) :
    (R / 2) * Real.log (1 + R) ≤ R * Real.log (2 + R) := by
  have hlog0 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + R) ≤ Real.log (2 + R) := by
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (by linarith))
      (Set.mem_Ioi.mpr (by linarith))
      (by linarith)
  calc
    (R / 2) * Real.log (1 + R) ≤ R * Real.log (1 + R) := by nlinarith
    _ ≤ R * Real.log (2 + R) := mul_le_mul_of_nonneg_left hlog hR

/-- An explicit disk exponent with the manuscript's `R log (2 + R)` scale. -/
def orderOneGrowthBound (N : ℕ) (R : ℝ) : ℝ :=
  1 + 2 * orderOneMoment N + boundaryConstant N + R * Real.log (2 + R)

lemma norm_F_le_orderOneGrowthBound {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖F N t z‖ ≤ Real.exp (orderOneGrowthBound N R) := by
  let M : ℝ := orderOneMoment N
  let K : ℝ := t * boundaryConstant N
  let C : ℝ := (R / 2) * Real.log (1 + R)
  let D : ℝ := R * Real.log (2 + R)
  have hM : 0 ≤ M := orderOneMoment_nonneg N
  have hc : 0 ≤ boundaryConstant N := (boundaryConstant_pos hN).le
  have hK : 0 ≤ K := mul_nonneg ht0 hc
  have hKc : K ≤ boundaryConstant N := by
    dsimp only [K]
    nlinarith [mul_nonneg (sub_nonneg.mpr ht1) hc]
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hCD : C ≤ D := by
    dsimp only [C, D]
    exact half_radius_log_one_add_le_orderOneScale hR
  have heC : 1 ≤ Real.exp C := Real.one_le_exp hC
  have hsumexp : 2 * M + boundaryConstant N ≤
      Real.exp (2 * M + boundaryConstant N) := by
    refine le_trans ?_ (Real.add_one_le_exp (2 * M + boundaryConstant N))
    linarith
  have hH := norm_H_le_orderOneMoment N hR z hz
  have htri : ‖F N t z‖ ≤ ‖H N z‖ + K := by
    change ‖H N z + (K : ℂ)‖ ≤ ‖H N z‖ + K
    calc
      ‖H N z + (K : ℂ)‖ ≤ ‖H N z‖ + ‖(K : ℂ)‖ := norm_add_le _ _
      _ = ‖H N z‖ + K := by
        simp only [norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  calc
    ‖F N t z‖ ≤ ‖H N z‖ + K := htri
    _ ≤ 2 * Real.exp C * M + K := by
      dsimp only [C, M]
      gcongr
    _ ≤ Real.exp C * (2 * M + boundaryConstant N) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr heC) hc]
    _ ≤ Real.exp C * Real.exp (2 * M + boundaryConstant N) := by gcongr
    _ = Real.exp (C + (2 * M + boundaryConstant N)) :=
      (Real.exp_add C (2 * M + boundaryConstant N)).symm
    _ ≤ Real.exp (orderOneGrowthBound N R) := by
      apply Real.exp_le_exp.mpr
      dsimp only [orderOneGrowthBound]
      dsimp only [M, D] at hCD
      linarith

end IncompleteGammaApproximant
