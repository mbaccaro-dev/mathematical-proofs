import HaglundK1ZeroTrajectory.IncompleteGamma.Nonconstant
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

lemma cubic_third_le_exp_two_div_four {u : ℝ} (hu : 0 ≤ u) :
    u ^ 3 / 3 ≤ Real.exp (2 * u) / 4 := by
  have h := Real.pow_div_factorial_le_exp (2 * u) (by positivity) 3
  norm_num [Nat.factorial] at h ⊢
  nlinarith

lemma phiTerm_eq_exp_sub_exp (n : ℕ) (u : ℝ) :
    let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
    phiTerm n u =
      4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) -
        6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  change
    Real.exp (u / 2 - a * Real.exp (2 * u)) *
        (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u)) =
      4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) -
        6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))
  have h9 :
      Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (4 * u) =
        Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 :
      Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (2 * u) =
        Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show
      Real.exp (u / 2 - a * Real.exp (2 * u)) *
          (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u)) =
        4 * a ^ 2 *
            (Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (4 * u)) -
          6 * a *
            (Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (2 * u)) by ring]
  rw [h9, h5]

lemma integrableOn_phiTerm_mul_cubicWeight (n : ℕ) :
    IntegrableOn (fun u : ℝ => phiTerm n u * Real.exp (u ^ 3 / 3)) (Ioi 0) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have ha' : 0 < a - 1 / 4 := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [Real.pi_gt_three, sq_nonneg ((n + 1 : ℝ) - 1)]
  let major : ℝ → ℝ := fun u =>
    4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - (a - 1 / 4) * Real.exp (2 * u)) +
      6 * a * Real.exp ((5 / 2 : ℝ) * u - (a - 1 / 4) * Real.exp (2 * u))
  have h9 :=
    (integrableOn_exp_linear_sub_exp_two (9 / 2 : ℝ) (a - 1 / 4) (by norm_num) ha').const_mul
      (4 * a ^ 2)
  have h5 :=
    (integrableOn_exp_linear_sub_exp_two (5 / 2 : ℝ) (a - 1 / 4) (by norm_num) ha').const_mul
      (6 * a)
  have hmajor : IntegrableOn major (Ioi 0) := by
    exact h9.add h5
  refine hmajor.mono'
    ((phiTerm_continuous n).mul (by fun_prop) |>.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  have hcubic := cubic_third_le_exp_two_div_four hu0
  have h9exp :
      Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) * Real.exp (u ^ 3 / 3) ≤
        Real.exp ((9 / 2 : ℝ) * u - (a - 1 / 4) * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h5exp :
      Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) * Real.exp (u ^ 3 / 3) ≤
        Real.exp ((5 / 2 : ℝ) * u - (a - 1 / 4) * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), phiTerm_eq_exp_sub_exp]
  change
    |4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) -
        6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))| *
        Real.exp (u ^ 3 / 3) ≤ major u
  calc
    _ ≤ (4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) +
          6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))) *
          Real.exp (u ^ 3 / 3) := by
      gcongr
      let X := 4 * a ^ 2 * Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u))
      let Y := 6 * a * Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u))
      have hX : 0 < X := by dsimp only [X]; positivity
      have hY : 0 < Y := by dsimp only [Y]; positivity
      change |X - Y| ≤ X + Y
      calc
        |X - Y| ≤ |X| + |Y| := abs_sub X Y
        _ = X + Y := by rw [abs_of_pos hX, abs_of_pos hY]
    _ = 4 * a ^ 2 *
          (Real.exp ((9 / 2 : ℝ) * u - a * Real.exp (2 * u)) * Real.exp (u ^ 3 / 3)) +
        6 * a *
          (Real.exp ((5 / 2 : ℝ) * u - a * Real.exp (2 * u)) * Real.exp (u ^ 3 / 3)) := by
      ring
    _ ≤ major u := by
      dsimp only [major]
      gcongr

lemma integrableOn_Phi_mul_cubicWeight (N : ℕ) :
    IntegrableOn (fun u : ℝ => Phi N u * Real.exp (u ^ 3 / 3)) (Ioi 0) := by
  rw [show (fun u : ℝ => Phi N u * Real.exp (u ^ 3 / 3)) =
      ∑ n ∈ Finset.range N,
        (fun u : ℝ => phiTerm n u * Real.exp (u ^ 3 / 3)) by
    funext u
    simp [Phi, Finset.sum_mul]]
  exact integrable_finsetSum' (Finset.range N)
    (fun n _ => integrableOn_phiTerm_mul_cubicWeight n)

lemma young_three_halves_three {R u : ℝ} (hR : 0 ≤ R) (hu : 0 ≤ u) :
    R * u ≤ (2 / 3 : ℝ) * R ^ (3 / 2 : ℝ) + u ^ 3 / 3 := by
  have hc : (3 / 2 : ℝ).HolderConjugate 3 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have h := Real.young_inequality_of_nonneg hR hu hc
  norm_num [Real.rpow_natCast] at h ⊢
  nlinarith

/-- The fixed weighted `L¹` moment that controls every complex disk. -/
def cubicMoment (N : ℕ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), |Phi N u| * Real.exp (u ^ 3 / 3)

lemma integrableOn_abs_Phi_mul_cubicWeight (N : ℕ) :
    IntegrableOn (fun u : ℝ => |Phi N u| * Real.exp (u ^ 3 / 3)) (Ioi 0) := by
  change Integrable
    (fun u : ℝ => |Phi N u| * Real.exp (u ^ 3 / 3)) (volume.restrict (Ioi 0))
  simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
    (integrableOn_Phi_mul_cubicWeight N).norm

lemma cubicMoment_nonneg (N : ℕ) : 0 ≤ cubicMoment N := by
  unfold cubicMoment
  exact integral_nonneg fun u => mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)

lemma norm_H_le_cubicMoment (N : ℕ) {R : ℝ} (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖H N z‖ ≤
      2 * Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) * cubicMoment N := by
  let c : ℝ := Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ))
  let g : ℝ → ℝ := fun u => c * (|Phi N u| * Real.exp (u ^ 3 / 3))
  have hg : IntegrableOn g (Ioi 0) := by
    exact (integrableOn_abs_Phi_mul_cubicWeight N).const_mul c
  have hpoint : ∀ᵐ u : ℝ ∂(volume.restrict (Ioi 0)),
      ‖(Phi N u : ℂ) * Complex.cos (z * (u : ℂ))‖ ≤ g u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (R * u) := by
      refine (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]
      exact mul_le_mul_of_nonneg_right hz hu0
    have hyoung := young_three_halves_three hR hu0
    have hexp :
        Real.exp (R * u) ≤
          Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) * Real.exp (u ^ 3 / 3) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hyoung
    simp only [norm_mul, norm_real, Real.norm_eq_abs]
    dsimp only [g, c]
    calc
      |Phi N u| * ‖Complex.cos (z * (u : ℂ))‖ ≤
          |Phi N u| * Real.exp (R * u) := by gcongr
      _ ≤ |Phi N u| *
          (Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) * Real.exp (u ^ 3 / 3)) := by
        gcongr
      _ = Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) *
          (|Phi N u| * Real.exp (u ^ 3 / 3)) := by ring
  have hint := norm_integral_le_of_norm_le hg hpoint
  calc
    ‖H N z‖ = 2 * ‖∫ u in Ioi (0 : ℝ),
        (Phi N u : ℂ) * Complex.cos (z * (u : ℂ))‖ := by
      rw [H, norm_mul, Complex.norm_ofNat]
    _ ≤ 2 * (∫ u in Ioi (0 : ℝ), g u) := by gcongr
    _ = 2 * Real.exp ((2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)) * cubicMoment N := by
      dsimp only [g, c, cubicMoment]
      rw [integral_const_mul]
      ring

/-- Explicit subquadratic disk-growth exponent used by the Hadamard layer. -/
def growthBound (N : ℕ) (t R : ℝ) : ℝ :=
  1 + 2 * cubicMoment N + |t * boundaryConstant N| +
    (2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)

lemma growthBound_pos (N : ℕ) (t : ℝ) {R : ℝ} (hR : 0 < R) :
    0 < growthBound N t R := by
  unfold growthBound
  have hM := cubicMoment_nonneg N
  have hpow : 0 ≤ R ^ (3 / 2 : ℝ) := Real.rpow_nonneg hR.le _
  positivity

lemma norm_F_le_growthBound (N : ℕ) (t : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖F N t z‖ ≤ Real.exp (growthBound N t R) := by
  let M : ℝ := cubicMoment N
  let K : ℝ := |t * boundaryConstant N|
  let C : ℝ := (2 / 3 : ℝ) * R ^ (3 / 2 : ℝ)
  have hM : 0 ≤ M := cubicMoment_nonneg N
  have hK : 0 ≤ K := abs_nonneg _
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg hR _)
  have heC : 1 ≤ Real.exp C := Real.one_le_exp hC
  have hsumexp : 2 * M + K ≤ Real.exp (2 * M + K) := by
    exact (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (2 * M + K))
  have hH := norm_H_le_cubicMoment N hR z hz
  have htri : ‖F N t z‖ ≤ ‖H N z‖ + K := by
    refine (norm_add_le _ _).trans_eq ?_
    simp only [norm_real, Real.norm_eq_abs]
    rfl
  calc
    ‖F N t z‖ ≤ ‖H N z‖ + K := htri
    _ ≤ 2 * Real.exp C * M + K := by
      dsimp only [C, M]
      gcongr
    _ = Real.exp C * (2 * M) + K := by ring
    _ ≤ Real.exp C * (2 * M + K) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr heC) hK]
    _ ≤ Real.exp C * Real.exp (2 * M + K) := by gcongr
    _ = Real.exp (C + (2 * M + K)) := (Real.exp_add C (2 * M + K)).symm
    _ ≤ Real.exp (growthBound N t R) := by
      apply Real.exp_le_exp.mpr
      dsimp only [C, M, K, growthBound]
      linarith

lemma tendsto_affine_rpow_three_halves_div_sq (d : ℝ) (hd : 0 ≤ d) :
    Tendsto
      (fun R : ℝ => (2 * R + d) ^ (3 / 2 : ℝ) / R ^ 2)
      atTop (nhds 0) := by
  have hupper : Tendsto
      (fun R : ℝ => 3 ^ (3 / 2 : ℝ) * R ^ (-1 / 2 : ℝ))
      atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
      (3 ^ (3 / 2 : ℝ)) using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0)) hupper
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact div_nonneg (Real.rpow_nonneg (by linarith) _) (sq_nonneg R)
  · filter_upwards [eventually_ge_atTop d, eventually_gt_atTop (0 : ℝ)] with R hRd hR
    have hbase0 : 0 ≤ 2 * R + d := by linarith
    have hbase : 2 * R + d ≤ 3 * R := by linarith
    have hpow :
        (2 * R + d) ^ (3 / 2 : ℝ) ≤ (3 * R) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hbase0 hbase (by norm_num)
    calc
      (2 * R + d) ^ (3 / 2 : ℝ) / R ^ 2 ≤
          (3 * R) ^ (3 / 2 : ℝ) / R ^ 2 :=
        div_le_div_of_nonneg_right hpow (sq_nonneg R)
      _ = 3 ^ (3 / 2 : ℝ) * R ^ (-1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hR.le, mul_div_assoc]
        congr 1
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_sub hR]
        norm_num

lemma tendsto_const_div_sq_zero (c : ℝ) :
    Tendsto (fun R : ℝ => c / R ^ 2) atTop (nhds 0) := by
  have hlim : Tendsto (fun R : ℝ => c * R ^ (-2 : ℝ)) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2)).const_mul c
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [Real.rpow_neg hR.le]
  simp only [div_eq_mul_inv]
  exact congrArg (fun x : ℝ => c * x) (congrArg Inv.inv (Real.rpow_natCast R 2))

lemma growthBound_subquadratic (N : ℕ) (t : ℝ) (d e : ℝ)
    (hd : 0 ≤ d) (_he : 0 ≤ e) :
    Tendsto
      (fun R : ℝ => (2 * growthBound N t (2 * R + d) + e) / R ^ 2)
      atTop (nhds 0) := by
  let A : ℝ := 1 + 2 * cubicMoment N + |t * boundaryConstant N|
  have hconst := tendsto_const_div_sq_zero (2 * A + e)
  have hpow :=
    (tendsto_affine_rpow_three_halves_div_sq d hd).const_mul (4 / 3 : ℝ)
  have hlim := hconst.add hpow
  have heq :
      (fun R : ℝ => (2 * A + e) / R ^ 2 +
        (4 / 3 : ℝ) * ((2 * R + d) ^ (3 / 2 : ℝ) / R ^ 2)) =ᶠ[atTop]
      (fun R : ℝ => (2 * growthBound N t (2 * R + d) + e) / R ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    dsimp only [growthBound, A]
    field_simp
    ring
  simpa using hlim.congr' heq

end IncompleteGammaApproximant
