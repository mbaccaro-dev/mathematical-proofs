import HaglundK1ZeroTrajectory.IncompleteGamma.Frontend
import HaglundK1ZeroTrajectory.IncompleteGamma.Growth
import HaglundK1ZeroTrajectory.IncompleteGamma.LocalZeroMotion

/-!
# Analytic reduction for the first Haglund pencil

This module fixes the literal `k = 1` pencil and proves the exact analytic
interface used by the accompanying paper: the interval-certificate bridge,
imaginary-axis exclusion, an explicit no-escape bound, the local analytic
zero branch with its velocity, and the direction contradiction at a real
collision.  The numerical interval atlas and the construction of the full
Weierstrass--Puiseux collision multiset remain outside this Lean development.
-/

open Complex Filter MeasureTheory Real Set Topology
open scoped ComplexConjugate

noncomputable section

namespace HaglundK1ZeroTrajectory

open IncompleteGammaApproximant

/-- The manuscript's literal incomplete-gamma cosine integral. -/
def manuscriptG (z : ℂ) (a b : ℝ) : ℂ :=
  4 * ∫ u in Ioi (0 : ℝ),
    Complex.cos (2 * z * (u : ℂ)) *
      (Real.exp (2 * b * u - a * Real.exp (2 * u)) : ℂ)

/-- The individual Haglund summand, with the manuscript's one-based index. -/
def manuscriptPhi (n : ℕ) (z : ℂ) : ℂ :=
  (2 * Real.pi ^ 2 * (n : ℝ) ^ 4 : ℝ) *
      manuscriptG (z / 2) ((n : ℝ) ^ 2 * Real.pi) (9 / 4) -
    (3 * Real.pi * (n : ℝ) ^ 2 : ℝ) *
      manuscriptG (z / 2) ((n : ℝ) ^ 2 * Real.pi) (5 / 4)

lemma integrableOn_exp_mul_cos (A c : ℝ) (z : ℂ) (hA : 0 < A) (hc : 0 < c) :
    IntegrableOn
      (fun u : ℝ =>
        (Real.exp (c * u - A * Real.exp (2 * u)) : ℂ) *
          Complex.cos (z * (u : ℂ)))
      (Ioi 0) := by
  have hmajor : Integrable
      (fun u : ℝ => Real.exp ((c + ‖z‖) * u - A * Real.exp (2 * u)))
      (volume.restrict (Ioi 0)) :=
    integrableOn_exp_linear_sub_exp_two (c + ‖z‖) A
      (by linarith [norm_nonneg z]) hA
  refine hmajor.mono' (by fun_prop) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (c * u - A * Real.exp (2 * u)) *
        ‖Complex.cos (z * (u : ℂ))‖ ≤
      Real.exp (c * u - A * Real.exp (2 * u)) * Real.exp (‖z‖ * u) := by
        gcongr
        exact (norm_cos_le_exp_norm _).trans (Real.exp_le_exp.mpr (by
          rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu]))
    _ = Real.exp ((c + ‖z‖) * u - A * Real.exp (2 * u)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem manuscriptG_half_eq_weighted_cos (z : ℂ) (A b : ℝ) :
    manuscriptG (z / 2) A b =
      4 * ∫ u in Ioi (0 : ℝ),
        (Real.exp (2 * b * u - A * Real.exp (2 * u)) : ℂ) *
          Complex.cos (z * (u : ℂ)) := by
  unfold manuscriptG
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  change Complex.cos (2 * (z / 2) * (u : ℂ)) *
      (Real.exp (2 * b * u - A * Real.exp (2 * u)) : ℂ) =
    (Real.exp (2 * b * u - A * Real.exp (2 * u)) : ℂ) *
      Complex.cos (z * (u : ℂ))
  have hz : 2 * (z / 2) * (u : ℂ) = z * (u : ℂ) := by ring
  rw [hz]
  ring

theorem manuscriptPhi_succ_eq_single_integral (n : ℕ) (z : ℂ) :
    manuscriptPhi (n + 1) z =
      2 * ∫ u in Ioi (0 : ℝ),
        (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  let A : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have h9 := integrableOn_exp_mul_cos A (9 / 2) z hA (by norm_num)
  have h5 := integrableOn_exp_mul_cos A (5 / 2) z hA (by norm_num)
  have h9c : IntegrableOn
      (fun u : ℝ => (4 * A ^ 2 : ℝ) *
        ((Real.exp ((9 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (Ioi 0) := by
    apply (h9.const_mul (4 * A ^ 2 : ℂ)).congr
    filter_upwards [] with u
    push_cast
    ring
  have h5c : IntegrableOn
      (fun u : ℝ => (6 * A : ℝ) *
        ((Real.exp ((5 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
          Complex.cos (z * (u : ℂ)))) (Ioi 0) := by
    apply (h5.const_mul (6 * A : ℂ)).congr
    filter_upwards [] with u
    push_cast
    ring
  have hdecomp :
      (fun u : ℝ =>
        (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))) =
      fun u : ℝ =>
        (4 * A ^ 2 : ℝ) *
            ((Real.exp ((9 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
              Complex.cos (z * (u : ℂ))) -
          (6 * A : ℝ) *
            ((Real.exp ((5 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
              Complex.cos (z * (u : ℂ))) := by
    funext u
    rw [phiTerm_eq_exp_sub_exp]
    dsimp only [A]
    push_cast
    ring
  let I9 : ℂ := ∫ u in Ioi (0 : ℝ),
    (Real.exp ((9 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
      Complex.cos (z * (u : ℂ))
  let I5 : ℂ := ∫ u in Ioi (0 : ℝ),
    (Real.exp ((5 / 2 : ℝ) * u - A * Real.exp (2 * u)) : ℂ) *
      Complex.cos (z * (u : ℂ))
  have hrhs :
      2 * ∫ u in Ioi (0 : ℝ),
          (phiTerm n u : ℂ) * Complex.cos (z * (u : ℂ)) =
        (8 * A ^ 2 : ℂ) * I9 - (12 * A : ℂ) * I5 := by
    rw [hdecomp, integral_sub h9c h5c, integral_const_mul, integral_const_mul]
    dsimp only [I9, I5]
    push_cast
    ring
  have hscale : ((n + 1 : ℕ) : ℝ) ^ 2 * Real.pi = A := by
    dsimp only [A]
    push_cast
    ring
  have hc9 :
      2 * Real.pi ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 4) = 2 * A ^ 2 := by
    dsimp only [A]
    push_cast
    ring
  have hc5 :
      3 * Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2) = 3 * A := by
    dsimp only [A]
    push_cast
    ring
  rw [hrhs, manuscriptPhi, manuscriptG_half_eq_weighted_cos,
    manuscriptG_half_eq_weighted_cos, hscale, hc9, hc5]
  norm_num only
  change ((2 * A ^ 2 : ℝ) : ℂ) * (4 * I9) -
      ((3 * A : ℝ) : ℂ) * (4 * I5) =
    (8 * A ^ 2 : ℂ) * I9 - (12 * A : ℂ) * I5
  push_cast
  ring

/-- The first summand in the Haglund interpolation. -/
def phiOne (z : ℂ) : ℂ := H 1 z

/-- The second summand in the Haglund interpolation. -/
def phiTwo (z : ℂ) : ℂ := H 2 z - H 1 z

/-- The manuscript's literal first pencil. -/
def manuscriptPencil (z τ : ℂ) : ℂ :=
  manuscriptPhi 1 z + τ * manuscriptPhi 2 z

/-- The complexified first Haglund interpolation parameter. -/
def pencil (z τ : ℂ) : ℂ := phiOne z + τ * phiTwo z

/-- The manuscript's real-parameter pencil. -/
def realPencil (z : ℂ) (t : ℝ) : ℂ := pencil z (t : ℂ)

theorem phiOne_eq_single_integral (z : ℂ) :
    phiOne z = 2 * ∫ u in Ioi (0 : ℝ),
      (phiTerm 0 u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  simp [phiOne, H, Phi]

theorem phiTwo_eq_single_integral (z : ℂ) :
    phiTwo z = 2 * ∫ u in Ioi (0 : ℝ),
      (phiTerm 1 u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  rw [phiTwo, H, H, integral_Phi_mul_cos_eq_sum,
    integral_Phi_mul_cos_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  ring

theorem phiOne_eq_manuscriptPhi (z : ℂ) :
    phiOne z = manuscriptPhi 1 z := by
  rw [phiOne_eq_single_integral, ← manuscriptPhi_succ_eq_single_integral 0 z]

theorem phiTwo_eq_manuscriptPhi (z : ℂ) :
    phiTwo z = manuscriptPhi 2 z := by
  rw [phiTwo_eq_single_integral, ← manuscriptPhi_succ_eq_single_integral 1 z]

theorem pencil_eq_manuscriptPencil (z τ : ℂ) :
    pencil z τ = manuscriptPencil z τ := by
  simp only [pencil, manuscriptPencil, phiOne_eq_manuscriptPhi,
    phiTwo_eq_manuscriptPhi]

theorem pencil_eq_H (z τ : ℂ) :
    pencil z τ = H 1 z + τ * (H 2 z - H 1 z) := by
  rfl

theorem realPencil_eq_H (z : ℂ) (t : ℝ) :
    realPencil z t = H 1 z + (t : ℂ) * (H 2 z - H 1 z) := by
  rfl

theorem phiOne_even (z : ℂ) : phiOne (-z) = phiOne z := by
  exact H_even 1 z

theorem phiTwo_even (z : ℂ) : phiTwo (-z) = phiTwo z := by
  simp only [phiTwo, H_even]

theorem pencil_even (z τ : ℂ) : pencil (-z) τ = pencil z τ := by
  simp only [pencil, phiOne_even, phiTwo_even]

theorem phiOne_conj (z : ℂ) : phiOne (conj z) = conj (phiOne z) := by
  exact H_conj 1 z

theorem phiTwo_conj (z : ℂ) : phiTwo (conj z) = conj (phiTwo z) := by
  simp only [phiTwo, H_conj, map_sub]

theorem realPencil_conj (z : ℂ) (t : ℝ) :
    realPencil (conj z) t = conj (realPencil z t) := by
  simp only [realPencil, pencil, phiOne_conj, phiTwo_conj, map_add, map_mul,
    conj_ofReal]

theorem phiOne_differentiable : Differentiable ℂ phiOne := by
  exact H_differentiable 1

theorem phiTwo_differentiable : Differentiable ℂ phiTwo := by
  exact (H_differentiable 2).sub (H_differentiable 1)

theorem pencil_differentiable (τ : ℂ) : Differentiable ℂ (fun z => pencil z τ) := by
  exact phiOne_differentiable.add (phiTwo_differentiable.const_mul τ)

theorem realPencil_differentiable (t : ℝ) :
    Differentiable ℂ (fun z => realPencil z t) := by
  exact pencil_differentiable (t : ℂ)

theorem deriv_realPencil (z : ℂ) (t : ℝ) :
    deriv (fun w => realPencil w t) z =
      deriv phiOne z + (t : ℂ) * deriv phiTwo z := by
  have hP : HasDerivAt phiOne (deriv phiOne z) z :=
    phiOne_differentiable.differentiableAt.hasDerivAt
  have hQ : HasDerivAt phiTwo (deriv phiTwo z) z :=
    phiTwo_differentiable.differentiableAt.hasDerivAt
  change deriv (phiOne + fun w => (t : ℂ) * phiTwo w) z = _
  exact (hP.add (hQ.const_mul (t : ℂ))).deriv

/-- The numerator controlling the imaginary velocity of a simple zero. -/
def delta (z : ℂ) (t : ℝ) : ℝ :=
  ((-phiTwo z) * conj (deriv (fun w => realPencil w t) z)).im

/-- The inverse-parameter map away from the zeros of `phiTwo`. -/
def parameterMap (z : ℂ) : ℂ := -phiOne z / phiTwo z

/-- The phase height whose zero set contains the real-parameter pencil zeros. -/
def phaseHeight (z : ℂ) : ℝ := -(phiOne z * conj (phiTwo z)).im

/-- The horizontal derivative of `phaseHeight`, written using the complex
derivatives of the two entire summands. -/
def phaseSlope (z : ℂ) : ℝ :=
  -(deriv phiOne z * conj (phiTwo z) +
      phiOne z * conj (deriv phiTwo z)).im

/-- The exact formal velocity of a simple zero. -/
def zeroVelocity (z : ℂ) (t : ℝ) : ℂ :=
  -phiTwo z / deriv (fun w => realPencil w t) z

theorem zeroVelocity_im (z : ℂ) (t : ℝ) :
    (zeroVelocity z t).im =
      delta z t / Complex.normSq (deriv (fun w => realPencil w t) z) := by
  simp only [zeroVelocity, delta, Complex.div_im, Complex.mul_im, neg_re, neg_im,
    conj_re, conj_im]
  ring

theorem phaseHeight_eq_normSq_mul_parameterMap_im {z : ℂ}
    (hQ : phiTwo z ≠ 0) :
    phaseHeight z = Complex.normSq (phiTwo z) * (parameterMap z).im := by
  simp only [phaseHeight, parameterMap, Complex.div_im, Complex.mul_im, conj_re, conj_im,
    neg_re, neg_im]
  have hn : Complex.normSq (phiTwo z) ≠ 0 :=
    (Complex.normSq_eq_zero.not.mpr hQ)
  field_simp
  ring

theorem realPencil_eq_zero_iff_parameterMap {z : ℂ} (t : ℝ)
    (hQ : phiTwo z ≠ 0) :
    realPencil z t = 0 ↔ parameterMap z = (t : ℂ) := by
  simp only [realPencil, pencil, parameterMap]
  constructor
  · intro h
    apply (div_eq_iff hQ).2
    linear_combination -h
  · intro h
    have hm := (div_eq_iff hQ).1 h
    linear_combination -hm

theorem realPencil_zero_phaseHeight {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) : phaseHeight z = 0 := by
  have hzero' : phiOne z + (t : ℂ) * phiTwo z = 0 := by
    simpa only [realPencil, pencil] using hzero
  have hP : phiOne z = -(t : ℂ) * phiTwo z := by
    linear_combination hzero'
  rw [phaseHeight, hP]
  simp [Complex.mul_im]
  ring

theorem delta_eq_neg_phaseSlope_at_zero {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) : delta z t = -phaseSlope z := by
  have hzero' : phiOne z + (t : ℂ) * phiTwo z = 0 := by
    simpa only [realPencil, pencil] using hzero
  have hP : phiOne z = -(t : ℂ) * phiTwo z := by
    linear_combination hzero'
  rw [delta, phaseSlope, deriv_realPencil, hP]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    conj_re, conj_im, neg_re, neg_im, ofReal_re, ofReal_im, zero_mul, add_zero,
    sub_zero]
  ring

/-- The real numerator of the inverse parameter `-phiOne / phiTwo`. -/
def levelNumerator (z : ℂ) : ℝ :=
  -(phiOne z * conj (phiTwo z)).re

/-- The excess of the inverse-parameter numerator over `|phiTwo|^2`.
Positivity rules out parameters in `[0, 1]`. -/
def levelExcess (z : ℂ) : ℝ :=
  -((phiOne z + phiTwo z) * conj (phiTwo z)).re

/-- The horizontal derivative of `Im (phiOne * conj phiTwo)`.  At a physical
zero this is exactly the numerator controlling imaginary zero velocity. -/
def rawPhaseSlope (z : ℂ) : ℝ :=
  (deriv phiOne z * conj (phiTwo z) +
      phiOne z * conj (deriv phiTwo z)).im

theorem rawPhaseSlope_eq_neg_phaseSlope (z : ℂ) :
    rawPhaseSlope z = -phaseSlope z := by
  simp only [rawPhaseSlope, phaseSlope]
  ring

theorem levelNumerator_at_zero {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) :
    levelNumerator z = t * Complex.normSq (phiTwo z) := by
  have hzero' : phiOne z + (t : ℂ) * phiTwo z = 0 := by
    simpa only [realPencil, pencil] using hzero
  have hP : phiOne z = -(t : ℂ) * phiTwo z := by
    linear_combination hzero'
  rw [levelNumerator, hP]
  simp only [Complex.mul_re, Complex.mul_im, neg_re, neg_im, ofReal_re,
    ofReal_im, conj_re, conj_im, Complex.normSq_apply]
  ring

theorem levelExcess_at_zero {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) :
    levelExcess z = (t - 1) * Complex.normSq (phiTwo z) := by
  have hzero' : phiOne z + (t : ℂ) * phiTwo z = 0 := by
    simpa only [realPencil, pencil] using hzero
  have hP : phiOne z = -(t : ℂ) * phiTwo z := by
    linear_combination hzero'
  rw [levelExcess, hP]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    neg_re, neg_im,
    ofReal_re, ofReal_im, conj_re, conj_im,
    Complex.normSq_apply]
  ring

theorem rawPhaseSlope_eq_delta_at_zero {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) : rawPhaseSlope z = delta z t := by
  rw [rawPhaseSlope_eq_neg_phaseSlope, delta_eq_neg_phaseSlope_at_zero hzero]

/-- The four exact terminal alternatives used by the interval atlas.  The
first three exclude a physical zero with parameter in `[0, 1]`; the fourth
proves strict downward velocity at every physical zero in the box. -/
def AtlasLeafConclusion (z : ℂ) : Prop :=
  phaseHeight z ≠ 0 ∨
  levelNumerator z < 0 ∨
  0 < levelExcess z ∨
  rawPhaseSlope z < 0

/-- Pointwise certificate-to-theorem bridge for a terminal interval leaf. -/
theorem atlasLeaf_zero_simple_descending {z : ℂ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hQ : phiTwo z ≠ 0)
    (hleaf : AtlasLeafConclusion z)
    (hzero : realPencil z t = 0) :
    deriv (fun w => realPencil w t) z ≠ 0 ∧
      (zeroVelocity z t).im < 0 := by
  have hphase : phaseHeight z = 0 := realPencil_zero_phaseHeight hzero
  have hnorm : 0 < Complex.normSq (phiTwo z) :=
    Complex.normSq_pos.mpr hQ
  rcases hleaf with hphaseNe | hnumNeg | hexcessPos | hslope
  · exact (hphaseNe hphase).elim
  · rw [levelNumerator_at_zero hzero] at hnumNeg
    exact (not_lt_of_ge (mul_nonneg ht0 hnorm.le) hnumNeg).elim
  · rw [levelExcess_at_zero hzero] at hexcessPos
    have : (t - 1) * Complex.normSq (phiTwo z) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht1) hnorm.le
    exact (not_lt_of_ge this hexcessPos).elim
  · have hdelta : delta z t < 0 := by
      rw [← rawPhaseSlope_eq_delta_at_zero hzero]
      exact hslope
    have hderiv : deriv (fun w => realPencil w t) z ≠ 0 := by
      intro hz
      have : delta z t = 0 := by simp [delta, hz]
      linarith
    refine ⟨hderiv, ?_⟩
    rw [zeroVelocity_im]
    exact div_neg_of_neg_of_pos hdelta (Complex.normSq_pos.mpr hderiv)

/-- A point set is certified when every point has a nonvanishing denominator
and satisfies one of the four exact terminal atlas alternatives. -/
def AtlasCovers (S : Set ℂ) : Prop :=
  ∀ z ∈ S, phiTwo z ≠ 0 ∧ AtlasLeafConclusion z

/-- A finite atlas proves the simple-zero and strict-descent conclusion at
every physical zero in the set that it covers. -/
theorem atlasCovers_zero_simple_descending {S : Set ℂ}
    (hcover : AtlasCovers S) {z : ℂ} (hz : z ∈ S) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hzero : realPencil z t = 0) :
    deriv (fun w => realPencil w t) z ≠ 0 ∧
      (zeroVelocity z t).im < 0 := by
  exact atlasLeaf_zero_simple_descending ht0 ht1
    (hcover z hz).1 (hcover z hz).2 hzero

/-- The open upper first quadrant, with the imaginary axis assigned to the
separate exact boundary theorem below. -/
def openFirstQuadrant : Set ℂ :=
  {z | 0 < z.re ∧ 0 < z.im}

/-- Exact certificate interface for the full nonreal first-quadrant theorem. -/
def FirstQuadrantCertificate : Prop := AtlasCovers openFirstQuadrant

theorem firstQuadrantCertificate_zero_simple_descending
    (hcert : FirstQuadrantCertificate) {z : ℂ}
    (hzre : 0 < z.re) (hzim : 0 < z.im) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hzero : realPencil z t = 0) :
    deriv (fun w => realPencil w t) z ≠ 0 ∧
      (zeroVelocity z t).im < 0 := by
  exact atlasCovers_zero_simple_descending hcert ⟨hzre, hzim⟩
    ht0 ht1 hzero

lemma phiTerm_pos_of_nonneg (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    0 < phiTerm n u := by
  let a : ℝ := Real.pi * (n + 1 : ℝ) ^ 2
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ha : 3 < a := by
    dsimp only [a]
    nlinarith [Real.pi_gt_three, sq_nonneg ((n + 1 : ℝ) - 1)]
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp_iff.mpr (by linarith)
  have hX : 3 < 2 * a * Real.exp (2 * u) := by
    have ha0 : 0 < a := lt_trans (by norm_num) ha
    nlinarith [mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * a)]
  have hfactor :
      4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u) =
        (2 * a * Real.exp (2 * u)) *
          (2 * a * Real.exp (2 * u) - 3) := by
    have hexp : Real.exp (4 * u) = Real.exp (2 * u) ^ 2 := by
      rw [show 4 * u = 2 * u + 2 * u by ring, Real.exp_add]
      ring
    rw [hexp]
    ring
  change 0 < Real.exp (u / 2 - a * Real.exp (2 * u)) *
    (4 * a ^ 2 * Real.exp (4 * u) - 6 * a * Real.exp (2 * u))
  rw [hfactor]
  positivity

/-- Every individual source summand is strictly positive on the imaginary
axis.  This is one exact, nonnumerical boundary component of the global
certificate. -/
theorem singleSummand_imaginaryAxis_pos (n : ℕ) (y : ℝ) :
    0 < ∫ u in Ioi (0 : ℝ), phiTerm n u * Real.cosh (y * u) := by
  let f : ℝ → ℝ := fun u => phiTerm n u * Real.cosh (y * u)
  have hcomplex := integrableOn_phiTerm_mul_cos n
    (Complex.I * (y : ℂ))
  have heq :
      (fun u : ℝ =>
        (phiTerm n u : ℂ) *
          Complex.cos ((Complex.I * (y : ℂ)) * (u : ℂ))) =
        fun u : ℝ => (f u : ℂ) := by
    funext u
    have hz : (Complex.I * (y : ℂ)) * (u : ℂ) =
        ((y * u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hz, Complex.cos_mul_I, ← Complex.ofReal_cosh]
    simp only [f, ofReal_mul]
  have hfComplex : IntegrableOn (fun u : ℝ => (f u : ℂ)) (Ioi 0) := by
    rw [← heq]
    exact hcomplex
  have hf : IntegrableOn f (Ioi 0) := by
    have hre := Complex.reCLM.integrable_comp hfComplex
    change Integrable f (volume.restrict (Ioi 0))
    simpa only [Function.comp_apply, Complex.reCLM_apply, ofReal_re] using hre
  have hcont : Continuous f := by
    dsimp only [f]
    exact (phiTerm_continuous n).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (phiTerm_pos_of_nonneg n hu.le).le (Real.cosh_pos _).le
  rw [integral_pos_iff_support_of_nonneg_ae hnonneg hf]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support f := by
    intro u hu
    exact ne_of_gt (mul_pos (phiTerm_pos_of_nonneg n hu.1.le)
      (Real.cosh_pos _))
  have hinterval : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo]
    norm_num [Ioo_inter_Ioi]
  exact hinterval.trans_le (measure_mono hsub)

theorem singleSummand_imaginaryAxis_eq (n : ℕ) (y : ℝ) :
    2 * ∫ u in Ioi (0 : ℝ),
        (phiTerm n u : ℂ) *
          Complex.cos ((Complex.I * (y : ℂ)) * (u : ℂ)) =
      ((2 * ∫ u in Ioi (0 : ℝ),
        phiTerm n u * Real.cosh (y * u) : ℝ) : ℂ) := by
  have heq :
      (fun u : ℝ =>
        (phiTerm n u : ℂ) *
          Complex.cos ((Complex.I * (y : ℂ)) * (u : ℂ))) =
        fun u : ℝ => ((phiTerm n u * Real.cosh (y * u) : ℝ) : ℂ) := by
    funext u
    have hz : (Complex.I * (y : ℂ)) * (u : ℂ) =
        ((y * u : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hz, Complex.cos_mul_I, ← Complex.ofReal_cosh]
    norm_cast
  rw [heq]
  have hofReal :
      (∫ u in Ioi (0 : ℝ),
          ((phiTerm n u * Real.cosh (y * u) : ℝ) : ℂ)) =
        ((∫ u in Ioi (0 : ℝ),
          phiTerm n u * Real.cosh (y * u) : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hofReal]
  norm_num

theorem phiOne_imaginaryAxis_eq (y : ℝ) :
    phiOne (Complex.I * (y : ℂ)) =
      ((2 * ∫ u in Ioi (0 : ℝ),
        phiTerm 0 u * Real.cosh (y * u) : ℝ) : ℂ) := by
  rw [phiOne_eq_single_integral]
  exact singleSummand_imaginaryAxis_eq 0 y

theorem phiTwo_imaginaryAxis_eq (y : ℝ) :
    phiTwo (Complex.I * (y : ℂ)) =
      ((2 * ∫ u in Ioi (0 : ℝ),
        phiTerm 1 u * Real.cosh (y * u) : ℝ) : ℂ) := by
  rw [phiTwo_eq_single_integral]
  exact singleSummand_imaginaryAxis_eq 1 y

/-- The literal `k = 1` pencil has no zero anywhere on the imaginary axis
for every nonnegative interpolation parameter, in particular for `[0, 1]`. -/
theorem realPencil_imaginaryAxis_ne_zero (y : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    realPencil (Complex.I * (y : ℂ)) t ≠ 0 := by
  have h0 := singleSummand_imaginaryAxis_pos 0 y
  have h1 := singleSummand_imaginaryAxis_pos 1 y
  rw [realPencil, pencil, phiOne_imaginaryAxis_eq,
    phiTwo_imaginaryAxis_eq]
  intro hzero
  have hre := congrArg Complex.re hzero
  simp only [Complex.add_re, Complex.mul_re, ofReal_re, ofReal_im,
    zero_mul, sub_zero, zero_re] at hre
  nlinarith [mul_nonneg ht h1.le]

/-- The exact outer-cone conclusion used by the verified asymptotic module. -/
def InOuterCone (z : ℂ) : Prop :=
  256 ≤ ‖z‖ → (3 / 2 : ℝ) * Real.log ‖z‖ < z.im

/-- Pointwise core of the no-forward-escape argument.  Once imaginary height
is bounded above by `H`, the outer cone forces an explicit radial bound. -/
theorem norm_lt_escapeRadius {z : ℂ} {H : ℝ}
    (him : z.im ≤ H) (hcone : InOuterCone z) :
    ‖z‖ < max 256 (Real.exp (2 * H / 3)) := by
  by_cases hr : ‖z‖ < 256
  · exact hr.trans_le (le_max_left _ _)
  · have hr256 : 256 ≤ ‖z‖ := le_of_not_gt hr
    have hrpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hr256
    have hlogScaled : (3 / 2 : ℝ) * Real.log ‖z‖ < H :=
      (hcone hr256).trans_le him
    have hlog : Real.log ‖z‖ < 2 * H / 3 := by
      nlinarith
    have hexp : ‖z‖ < Real.exp (2 * H / 3) :=
      (Real.log_lt_iff_lt_exp hrpos).1 hlog
    exact hexp.trans_le (le_max_right _ _)

/-- Uniform boundedness of a branch follows pointwise from a uniform height
ceiling and the outer-cone certificate. -/
theorem branch_uniformly_bounded
    (z : ℝ → ℂ) (I : Set ℝ) (H : ℝ)
    (him : ∀ t ∈ I, (z t).im ≤ H)
    (hcone : ∀ t ∈ I, InOuterCone (z t)) :
    ∀ t ∈ I, ‖z t‖ < max 256 (Real.exp (2 * H / 3)) := by
  intro t ht
  exact norm_lt_escapeRadius (him t ht) (hcone t ht)

/-- A positive limiting coefficient against a positive local scale fixes the
eventual sign.  This is the analytic sign step used after choosing the first
nonreal Puiseux coefficient at a collision. -/
theorem eventually_pos_of_scaled_tendsto
    {v scale : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hscale : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < scale s)
    (hlim : Tendsto (fun s => v s / scale s)
      (𝓝[>] (0 : ℝ)) (𝓝 c)) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < v s := by
  have hquot : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < v s / scale s :=
    hlim.eventually (Ioi_mem_nhds hc)
  filter_upwards [hscale, hquot] with s hs hq
  have hmul := mul_pos hq hs
  rw [div_mul_cancel₀ _ hs.ne'] at hmul
  exact hmul

/-- The collision-direction contradiction in its exact asymptotic form.  A
Puiseux branch entering the upper half-plane to the right has positive height
and positive imaginary velocity near the collision, contradicting the
certified strict-descent law. -/
theorem no_right_upper_emergence_of_scaled_limits
    {height velocity heightScale velocityScale : ℝ → ℝ}
    {heightCoeff velocityCoeff : ℝ}
    (hhc : 0 < heightCoeff) (hvc : 0 < velocityCoeff)
    (hhs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < heightScale s)
    (hvs : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < velocityScale s)
    (hhlim : Tendsto (fun s => height s / heightScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 heightCoeff))
    (hvlim : Tendsto (fun s => velocity s / velocityScale s)
      (𝓝[>] (0 : ℝ)) (𝓝 velocityCoeff))
    (hdescent : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      0 < height s → velocity s < 0) : False := by
  have hhpos := eventually_pos_of_scaled_tendsto hhc hhs hhlim
  have hvpos := eventually_pos_of_scaled_tendsto hvc hvs hvlim
  have hbad : ∀ᶠ s in 𝓝[>] (0 : ℝ), False := by
    filter_upwards [hhpos, hvpos, hdescent] with s hh hv hd
    exact (not_lt_of_ge hv.le) (hd hh)
  exact (Filter.Eventually.exists hbad).choose_spec

theorem realPencil_eq_zero_iff_phase_parameter {z : ℂ} (t : ℝ)
    (hQ : phiTwo z ≠ 0) :
    realPencil z t = 0 ↔ phaseHeight z = 0 ∧ parameterMap z = (t : ℂ) := by
  constructor
  · intro hzero
    exact ⟨realPencil_zero_phaseHeight hzero,
      (realPencil_eq_zero_iff_parameterMap t hQ).1 hzero⟩
  · exact fun h => (realPencil_eq_zero_iff_parameterMap t hQ).2 h.2

theorem parameterMap_hasStrictDerivAt_at_zero {z : ℂ} {t : ℝ}
    (hzero : realPencil z t = 0) (hQ : phiTwo z ≠ 0) :
    HasStrictDerivAt parameterMap
      (-deriv (fun w => realPencil w t) z / phiTwo z) z := by
  have hPstrict : HasStrictDerivAt phiOne (deriv phiOne z) z :=
    (phiOne_differentiable.analyticAt z).contDiffAt.hasStrictDerivAt one_ne_zero
  have hQstrict : HasStrictDerivAt phiTwo (deriv phiTwo z) z :=
    (phiTwo_differentiable.analyticAt z).contDiffAt.hasStrictDerivAt one_ne_zero
  have hraw := hPstrict.neg.div hQstrict hQ
  have hzero' : phiOne z + (t : ℂ) * phiTwo z = 0 := by
    simpa only [realPencil, pencil] using hzero
  have hP : phiOne z = -(t : ℂ) * phiTwo z := by
    linear_combination hzero'
  have hder :
      (-deriv phiOne z * phiTwo z - (-phiOne) z * deriv phiTwo z) /
          phiTwo z ^ 2 =
        -deriv (fun w => realPencil w t) z / phiTwo z := by
    simp only [Pi.neg_apply]
    rw [deriv_realPencil, hP]
    field_simp
    ring
  change HasStrictDerivAt (-phiOne / phiTwo)
    (-deriv (fun w => realPencil w t) z / phiTwo z) z
  rw [← hder]
  exact hraw

/-- A simple pencil zero has a locally unique holomorphic continuation with
the manuscript's exact velocity. -/
theorem exists_local_zero_motion {z₀ τ₀ : ℂ}
    (hzero : pencil z₀ τ₀ = 0) (hQ : phiTwo z₀ ≠ 0)
    (hsimple : deriv (fun z => pencil z τ₀) z₀ ≠ 0) :
    ∃ z : ℂ → ℂ,
      z τ₀ = z₀ ∧
      (∀ᶠ τ in 𝓝 τ₀, pencil (z τ) τ = 0) ∧
      HasStrictDerivAt z
        (-phiTwo z₀ / deriv (fun w => pencil w τ₀) z₀) τ₀ ∧
      (∀ᶠ w in 𝓝 z₀, z (parameterMap w) = w) := by
  have hzeroRealShape :
      phiOne z₀ + τ₀ * phiTwo z₀ = 0 := by
    simpa only [pencil] using hzero
  have hcenter : parameterMap z₀ = τ₀ := by
    apply (div_eq_iff hQ).2
    linear_combination -hzeroRealShape
  have hPstrict : HasStrictDerivAt phiOne (deriv phiOne z₀) z₀ :=
    (phiOne_differentiable.analyticAt z₀).contDiffAt.hasStrictDerivAt one_ne_zero
  have hQstrict : HasStrictDerivAt phiTwo (deriv phiTwo z₀) z₀ :=
    (phiTwo_differentiable.analyticAt z₀).contDiffAt.hasStrictDerivAt one_ne_zero
  have hparamRaw := hPstrict.neg.div hQstrict hQ
  have hderPencil :
      deriv (fun z => pencil z τ₀) z₀ =
        deriv phiOne z₀ + τ₀ * deriv phiTwo z₀ := by
    have hP : HasDerivAt phiOne (deriv phiOne z₀) z₀ :=
      phiOne_differentiable.differentiableAt.hasDerivAt
    have hQ' : HasDerivAt phiTwo (deriv phiTwo z₀) z₀ :=
      phiTwo_differentiable.differentiableAt.hasDerivAt
    change deriv (phiOne + fun w => τ₀ * phiTwo w) z₀ = _
    exact (hP.add (hQ'.const_mul τ₀)).deriv
  have hPvalue : phiOne z₀ = -τ₀ * phiTwo z₀ := by
    linear_combination hzeroRealShape
  have hder :
      (-deriv phiOne z₀ * phiTwo z₀ - (-phiOne) z₀ * deriv phiTwo z₀) /
          phiTwo z₀ ^ 2 =
        -deriv (fun z => pencil z τ₀) z₀ / phiTwo z₀ := by
    simp only [Pi.neg_apply]
    rw [hderPencil, hPvalue]
    field_simp
    ring
  have hparam : HasStrictDerivAt parameterMap
      (-deriv (fun z => pencil z τ₀) z₀ / phiTwo z₀) z₀ := by
    change HasStrictDerivAt (-phiOne / phiTwo)
      (-deriv (fun z => pencil z τ₀) z₀ / phiTwo z₀) z₀
    rw [← hder]
    exact hparamRaw
  have hpne : -deriv (fun z => pencil z τ₀) z₀ / phiTwo z₀ ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hsimple) hQ
  let z : ℂ → ℂ := hparam.localInverse parameterMap
    (-deriv (fun z => pencil z τ₀) z₀ / phiTwo z₀) z₀ hpne
  have hzstrict := hparam.to_localInverse hpne
  have hzstrict' : HasStrictDerivAt z
      (-phiTwo z₀ / deriv (fun w => pencil w τ₀) z₀) τ₀ := by
    rw [hcenter] at hzstrict
    apply hzstrict.congr_deriv
    field_simp
  have hzcenter : z τ₀ = z₀ := by
    rw [← hcenter]
    exact (hparam.eventually_left_inverse hpne).self_of_nhds
  refine ⟨z, hzcenter, ?_, hzstrict', ?_⟩
  · have hright := hparam.eventually_right_inverse hpne
    rw [hcenter] at hright
    have hQevent : ∀ᶠ τ in 𝓝 τ₀, phiTwo (z τ) ≠ 0 := by
      have hcont : ContinuousAt (fun τ => phiTwo (z τ)) τ₀ :=
        phiTwo_differentiable.continuous.continuousAt.comp
          hzstrict'.hasDerivAt.continuousAt
      exact hcont.eventually_ne (by simpa only [hzcenter] using hQ)
    filter_upwards [hright, hQevent] with τ hτ hQτ
    change parameterMap (z τ) = τ at hτ
    have hm : -phiOne (z τ) = τ * phiTwo (z τ) :=
      (div_eq_iff hQτ).1 hτ
    change phiOne (z τ) + τ * phiTwo (z τ) = 0
    linear_combination -hm
  · exact hparam.eventually_left_inverse hpne

/-- Full local certificate bridge for the literal real-parameter pencil.  A
certified terminal leaf supplies simplicity, the analytic zero branch, its
exact velocity, and strict downward imaginary motion. -/
theorem exists_local_descending_zero_motion
    {z₀ : ℂ} {t₀ : ℝ}
    (ht0 : 0 ≤ t₀) (ht1 : t₀ ≤ 1)
    (hQ : phiTwo z₀ ≠ 0)
    (hleaf : AtlasLeafConclusion z₀)
    (hzero : realPencil z₀ t₀ = 0) :
    ∃ z : ℂ → ℂ,
      z (t₀ : ℂ) = z₀ ∧
      (∀ᶠ τ in 𝓝 (t₀ : ℂ), pencil (z τ) τ = 0) ∧
      HasStrictDerivAt z (zeroVelocity z₀ t₀) (t₀ : ℂ) ∧
      (∀ᶠ w in 𝓝 z₀, z (parameterMap w) = w) ∧
      (zeroVelocity z₀ t₀).im < 0 := by
  have hcert := atlasLeaf_zero_simple_descending ht0 ht1 hQ hleaf hzero
  have hzeroComplex : pencil z₀ (t₀ : ℂ) = 0 := by
    simpa only [realPencil] using hzero
  have hsimpleComplex : deriv (fun w => pencil w (t₀ : ℂ)) z₀ ≠ 0 := by
    simpa only [realPencil] using hcert.1
  obtain ⟨z, hz0, hz, hzderiv, hzinv⟩ :=
    exists_local_zero_motion hzeroComplex hQ hsimpleComplex
  refine ⟨z, hz0, hz, ?_, hzinv, hcert.2⟩
  simpa only [zeroVelocity, realPencil] using hzderiv

end HaglundK1ZeroTrajectory
