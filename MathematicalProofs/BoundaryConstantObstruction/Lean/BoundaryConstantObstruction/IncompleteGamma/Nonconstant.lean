import BoundaryConstantObstruction.IncompleteGamma.Analysis
import BoundaryConstantObstruction.IncompleteGamma.ThetaIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Basic

open Complex Filter MeasureTheory Real Set Topology

noncomputable section

namespace IncompleteGammaApproximant

/-- The elementary integration-by-parts primitive for one kernel summand. -/
def qTerm (n : ℕ) (u : ℝ) : ℝ :=
  let a := Real.pi * (n + 1 : ℝ) ^ 2
  (1 / 2) * Real.exp (0 * u - a * Real.exp (2 * u)) -
    (a * Real.exp (2 * u - a * Real.exp (2 * u)) +
      a * Real.exp (3 * u - a * Real.exp (2 * u)))

lemma exp_linear_sub_exp_two_hasDerivAt (k a u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp (k * v - a * Real.exp (2 * v)))
      ((k - 2 * a * Real.exp (2 * u)) *
        Real.exp (k * u - a * Real.exp (2 * u))) u := by
  have h2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v))
      (2 * Real.exp (2 * u)) u := by
    simpa only [id_eq, one_mul, mul_one, mul_comm] using
      (((hasDerivAt_id u).mul_const (2 : ℝ)).exp)
  have hk : HasDerivAt (fun v : ℝ => k * v) k u := by
    exact ((hasDerivAt_id u).const_mul k).congr_deriv (by ring)
  have hin : HasDerivAt (fun v : ℝ => k * v - a * Real.exp (2 * v))
      (k - 2 * a * Real.exp (2 * u)) u := by
    exact (hk.sub (h2.const_mul a)).congr_deriv (by ring)
  exact hin.exp.congr_deriv (by ring)

lemma phiTerm_mul_cosh_eq (n : ℕ) (u : ℝ) :
    phiTerm n u * Real.cosh (u / 2) =
      -(Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u) *
          Real.exp (-(Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u)) -
        (Real.pi * (n + 1 : ℝ) ^ 2) *
          (2 - 2 * (Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u)) *
          Real.exp (2 * u - (Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u)) -
        (Real.pi * (n + 1 : ℝ) ^ 2) *
          (3 - 2 * (Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u)) *
          Real.exp (3 * u - (Real.pi * (n + 1 : ℝ) ^ 2) * Real.exp (2 * u)) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  change
    Real.exp (u / 2 - a * Real.exp (2 * u)) *
        (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u)) *
        Real.cosh (u / 2) =
      -a * Real.exp (2 * u) * Real.exp (-a * Real.exp (2 * u)) -
        a * (2 - 2 * a * Real.exp (2 * u)) *
          Real.exp (2 * u - a * Real.exp (2 * u)) -
        a * (3 - 2 * a * Real.exp (2 * u)) *
          Real.exp (3 * u - a * Real.exp (2 * u))
  rw [Real.cosh_eq]
  have hkpos : Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (u / 2) =
      Real.exp (u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hkneg : Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (-(u / 2)) =
      Real.exp (-a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h5 : Real.exp (4 * u) * Real.exp (u - a * Real.exp (2 * u)) =
      Real.exp (5 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : Real.exp (4 * u) * Real.exp (-a * Real.exp (2 * u)) =
      Real.exp (4 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (2 * u) * Real.exp (u - a * Real.exp (2 * u)) =
      Real.exp (3 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (2 * u) * Real.exp (-a * Real.exp (2 * u)) =
      Real.exp (2 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h23 : Real.exp (2 * u) * Real.exp (3 * u - a * Real.exp (2 * u)) =
      Real.exp (5 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h22 : Real.exp (2 * u) * Real.exp (2 * u - a * Real.exp (2 * u)) =
      Real.exp (4 * u - a * Real.exp (2 * u)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfirst :
      -a * Real.exp (2 * u) * Real.exp (-a * Real.exp (2 * u)) =
        -a * Real.exp (2 * u - a * Real.exp (2 * u)) := by
    calc
      _ = -a * (Real.exp (2 * u) * Real.exp (-a * Real.exp (2 * u))) := by ring
      _ = _ := by rw [h2]
  rw [show
      Real.exp (u / 2 - a * Real.exp (2 * u)) *
          (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u)) *
          ((Real.exp (u / 2) + Real.exp (-(u / 2))) / 2) =
        (2 * a ^ 2 * Real.exp (4 * u) - 3 * a * Real.exp (2 * u)) *
          (Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (u / 2) +
            Real.exp (u / 2 - a * Real.exp (2 * u)) * Real.exp (-(u / 2))) by ring]
  rw [hkpos, hkneg]
  rw [show
      (2 * a ^ 2 * Real.exp (4 * u) - 3 * a * Real.exp (2 * u)) *
          (Real.exp (u - a * Real.exp (2 * u)) +
            Real.exp (-a * Real.exp (2 * u))) =
        2 * a ^ 2 * (Real.exp (4 * u) * Real.exp (u - a * Real.exp (2 * u))) +
        2 * a ^ 2 * (Real.exp (4 * u) * Real.exp (-a * Real.exp (2 * u))) -
        3 * a * (Real.exp (2 * u) * Real.exp (u - a * Real.exp (2 * u))) -
        3 * a * (Real.exp (2 * u) * Real.exp (-a * Real.exp (2 * u))) by ring]
  rw [h5, h4, h3, h2, hfirst]
  have hrhs :
      -a * Real.exp (2 * u - a * Real.exp (2 * u)) -
          a * (2 - 2 * a * Real.exp (2 * u)) *
            Real.exp (2 * u - a * Real.exp (2 * u)) -
          a * (3 - 2 * a * Real.exp (2 * u)) *
            Real.exp (3 * u - a * Real.exp (2 * u)) =
        -3 * a * Real.exp (2 * u - a * Real.exp (2 * u)) -
          3 * a * Real.exp (3 * u - a * Real.exp (2 * u)) +
          2 * a ^ 2 *
            (Real.exp (2 * u) * Real.exp (2 * u - a * Real.exp (2 * u))) +
          2 * a ^ 2 *
            (Real.exp (2 * u) * Real.exp (3 * u - a * Real.exp (2 * u))) := by
    ring
  rw [hrhs, h22, h23]
  ring

lemma qTerm_hasDerivAt (n : ℕ) (u : ℝ) :
    HasDerivAt (qTerm n) (phiTerm n u * Real.cosh (u / 2)) u := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  change HasDerivAt
    (fun v : ℝ =>
      (1 / 2) * Real.exp (0 * v - a * Real.exp (2 * v)) -
        (a * Real.exp (2 * v - a * Real.exp (2 * v)) +
          a * Real.exp (3 * v - a * Real.exp (2 * v))))
    (phiTerm n u * Real.cosh (u / 2)) u
  have h0 := (exp_linear_sub_exp_two_hasDerivAt 0 a u).const_mul (1 / 2 : ℝ)
  have h2 := (exp_linear_sub_exp_two_hasDerivAt 2 a u).const_mul a
  have h3 := (exp_linear_sub_exp_two_hasDerivAt 3 a u).const_mul a
  have hq := h0.sub (h2.add h3)
  apply hq.congr_deriv
  rw [phiTerm_mul_cosh_eq]
  dsimp only [a]
  ring

lemma tendsto_exp_linear_sub_exp_two_atTop (k a : ℝ) (ha : 0 < a) (hk : k < 2 * a) :
    Tendsto (fun u : ℝ => Real.exp (k * u - a * Real.exp (2 * u))) atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  rw [tendsto_atBot]
  intro b
  have hlin : Tendsto (fun u : ℝ => (k - 2 * a) * u - a) atTop atBot :=
    tendsto_atBot_add_const_right atTop (-a)
      (tendsto_id.const_mul_atTop_of_neg (by linarith))
  rw [tendsto_atBot] at hlin
  filter_upwards [hlin b] with u hu
  refine le_trans ?_ hu
  have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (2 * u)) ha.le
  nlinarith

lemma qTerm_tendsto_atTop (n : ℕ) : Tendsto (qTerm n) atTop (nhds 0) := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  change Tendsto
    (fun u : ℝ =>
      (1 / 2) * Real.exp (0 * u - a * Real.exp (2 * u)) -
        (a * Real.exp (2 * u - a * Real.exp (2 * u)) +
          a * Real.exp (3 * u - a * Real.exp (2 * u)))) atTop (nhds 0)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha3 : 3 < 2 * a := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [Real.pi_gt_three, sq_nonneg ((n + 1 : ℝ) - 1)]
  have h0 := tendsto_exp_linear_sub_exp_two_atTop 0 a ha (by linarith)
  have h2 := tendsto_exp_linear_sub_exp_two_atTop 2 a ha (by linarith)
  have h3 := tendsto_exp_linear_sub_exp_two_atTop 3 a ha ha3
  have hsum := (h0.const_mul (1 / 2 : ℝ)).sub
    ((h2.const_mul a).add (h3.const_mul a))
  simpa using hsum

@[simp] lemma qTerm_zero (n : ℕ) :
    qTerm n 0 = -(boundaryTerm (n + 1)) / 2 := by
  simp [qTerm, boundaryTerm]
  ring

lemma integrableOn_phiTerm_mul_cosh (n : ℕ) :
    IntegrableOn (fun u : ℝ => phiTerm n u * Real.cosh (u / 2)) (Ioi 0) := by
  have hp :=
    (integrableOn_phiTerm_mul_exp n (1 / 2 : ℝ) (by norm_num)).const_mul (1 / 2 : ℝ)
  have hm :=
    (integrableOn_phiTerm_mul_exp n (-1 / 2 : ℝ) (by norm_num)).const_mul (1 / 2 : ℝ)
  refine (hp.add hm).congr (Filter.Eventually.of_forall fun u => ?_)
  change
    (1 / 2 : ℝ) * (phiTerm n u * Real.exp ((1 / 2 : ℝ) * u)) +
        (1 / 2 : ℝ) * (phiTerm n u * Real.exp ((-1 / 2 : ℝ) * u)) =
      phiTerm n u * Real.cosh (u / 2)
  rw [Real.cosh_eq]
  have hpos : Real.exp ((1 / 2 : ℝ) * u) = Real.exp (u / 2) := by
    congr 1
    ring
  have hneg : Real.exp ((-1 / 2 : ℝ) * u) = Real.exp (-(u / 2)) := by
    congr 1
    ring
  rw [hpos, hneg]
  ring

lemma integral_phiTerm_mul_cosh (n : ℕ) :
    ∫ u in Ioi (0 : ℝ), phiTerm n u * Real.cosh (u / 2) =
      boundaryTerm (n + 1) / 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (f := qTerm n)
    (f' := fun u : ℝ => phiTerm n u * Real.cosh (u / 2)) (m := (0 : ℝ))
    (fun u _ => qTerm_hasDerivAt n u)
    (integrableOn_phiTerm_mul_cosh n)
    (qTerm_tendsto_atTop n)
  rw [qTerm_zero] at h
  convert h using 1 <;> ring

lemma two_mul_integral_Phi_mul_cosh (N : ℕ) :
    2 * (∫ u in Ioi (0 : ℝ), Phi N u * Real.cosh (u / 2)) =
      ∑ n ∈ Finset.range N, boundaryTerm (n + 1) := by
  rw [show (fun u : ℝ => Phi N u * Real.cosh (u / 2)) =
      (fun u : ℝ => ∑ n ∈ Finset.range N,
        phiTerm n u * Real.cosh (u / 2)) by
    funext u
    simp [Phi, Finset.sum_mul]]
  rw [MeasureTheory.integral_finsetSum (Finset.range N)
    (fun n _ => integrableOn_phiTerm_mul_cosh n)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [integral_phiTerm_mul_cosh]
  ring

lemma H_I_div_two (N : ℕ) :
    H N (Complex.I / 2) =
      ((∑ n ∈ Finset.range N, boundaryTerm (n + 1) : ℝ) : ℂ) := by
  rw [H]
  have hintegrand :
      (fun u : ℝ =>
        (Phi N u : ℂ) * Complex.cos ((Complex.I / 2) * (u : ℂ))) =
      (fun u : ℝ => ((Phi N u * Real.cosh (u / 2) : ℝ) : ℂ)) := by
    funext u
    have hz : (Complex.I / 2) * (u : ℂ) = ((u / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hz, Complex.cos_mul_I, ← Complex.ofReal_cosh]
    norm_cast
  rw [hintegrand]
  have hofReal :
      (∫ u in Ioi (0 : ℝ), ((Phi N u * Real.cosh (u / 2) : ℝ) : ℂ)) =
        ((∫ u in Ioi (0 : ℝ), Phi N u * Real.cosh (u / 2) : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hofReal]
  norm_cast
  exact two_mul_integral_Phi_mul_cosh N

lemma H_I_div_two_eq_half_sub_boundaryConstant (N : ℕ) :
    H N (Complex.I / 2) = ((1 / 2 - boundaryConstant N : ℝ) : ℂ) := by
  rw [H_I_div_two, boundaryConstant_eq_partial]
  push_cast
  ring

/-- The exact manuscript witness separating `F N t` from its real-axis tail. -/
theorem F_I_div_two (N : ℕ) (t : ℝ) :
    F N t (Complex.I / 2) =
      ((1 / 2 - (1 - t) * boundaryConstant N : ℝ) : ℂ) := by
  rw [F, H_I_div_two_eq_half_sub_boundaryConstant]
  push_cast
  ring

theorem F_I_div_two_sub_tail (N : ℕ) (t : ℝ) :
    F N t (Complex.I / 2) - ((t * boundaryConstant N : ℝ) : ℂ) =
      ((1 / 2 - boundaryConstant N : ℝ) : ℂ) := by
  rw [F_I_div_two]
  push_cast
  ring

lemma boundaryPartialSum_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < ∑ n ∈ Finset.range N, boundaryTerm (n + 1) := by
  apply Finset.sum_pos
  · intro n hn
    exact boundaryTerm_pos (by omega)
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem F_nonconstant {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ¬ ∃ C : ℂ, ∀ z : ℂ, F N t z = C := by
  rintro ⟨C, hC⟩
  have hconst : Tendsto (fun x : ℝ => F N t (x : ℂ)) atTop (nhds C) := by
    simpa only [hC] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => C) atTop (nhds C))
  have htail : (t * boundaryConstant N : ℂ) = C :=
    tendsto_nhds_unique (F_tendsto_atTop N t) hconst
  have htail' : ((t * boundaryConstant N : ℝ) : ℂ) = C := by
    norm_cast at htail ⊢
  have hpoint := hC (Complex.I / 2)
  rw [F, H_I_div_two, htail'] at hpoint
  have hsum_ne :
      ((∑ n ∈ Finset.range N, boundaryTerm (n + 1) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (boundaryPartialSum_pos hN).ne'
  exact hsum_ne (add_eq_right.mp hpoint)

end IncompleteGammaApproximant
