import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open Filter Real
open scoped Topology

/-- The explicit Chebyshev expression used for the fixed band `(y, 8y]`. -/
noncomputable def octupleChebyshevLower (x : ℝ) : ℝ :=
  (8 * x * log 2 - log (8 * x + 1)) / log (8 * x) -
    (log 4 * x / log √x + √x)

private theorem octupleChebyshevLower_pointwise
    {x : ℝ} (hx : 1 < x)
    (hscale : 3 * log 8 ≤ log x)
    (herr : log (8 * x + 1) ≤ log 2 * x)
    (hsqrt : 4 * √x * log x ≤ log 2 * x) :
    log 2 * x / log x ≤ octupleChebyshevLower x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < log x := log_pos hx
  have h8x : 0 < 8 * x := mul_pos (by norm_num) hx0
  have hlog8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, log_pow]
    norm_num
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
  have hlogsqrt : log √x = log x / 2 := log_sqrt hx0.le
  have hlogmul : log (8 * x) = log 8 + log x := by
    rw [log_mul (by norm_num : (8 : ℝ) ≠ 0) hx0.ne']
  have hdenom : log (8 * x) ≤ (4 / 3 : ℝ) * log x := by
    rw [hlogmul]
    have : log 8 ≤ log x / 3 := by linarith
    linarith
  have hdenom_pos : 0 < log (8 * x) := log_pos (by nlinarith)
  have hnum_nonneg : 0 ≤ 8 * x * log 2 - log (8 * x + 1) := by
    have hlog2 : 0 < log 2 := log_pos one_lt_two
    nlinarith
  have hfirst :
      (21 / 4 : ℝ) * (log 2 * x / log x) ≤
        (8 * x * log 2 - log (8 * x + 1)) / log (8 * x) := by
    apply (le_div_iff₀ hdenom_pos).2
    have hquot_nonneg : 0 ≤ log 2 * x / log x := by positivity
    calc
      (21 / 4 : ℝ) * (log 2 * x / log x) * log (8 * x)
          ≤ (21 / 4 : ℝ) * (log 2 * x / log x) *
              ((4 / 3 : ℝ) * log x) := by gcongr
      _ = 7 * log 2 * x := by field_simp; ring
      _ ≤ 8 * x * log 2 - log (8 * x + 1) := by nlinarith
  have hsqrt' : √x ≤ (1 / 4 : ℝ) * (log 2 * x / log x) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hlogx).2
    nlinarith
  rw [octupleChebyshevLower, hlog4, hlogsqrt]
  have hupper :
      (2 * log 2) * x / (log x / 2) + √x ≤
        (17 / 4 : ℝ) * (log 2 * x / log x) := by
    calc
      (2 * log 2) * x / (log x / 2) + √x
          = 4 * (log 2 * x / log x) + √x := by field_simp; ring
      _ ≤ 4 * (log 2 * x / log x) +
          (1 / 4 : ℝ) * (log 2 * x / log x) := by gcongr
      _ = (17 / 4 : ℝ) * (log 2 * x / log x) := by ring
  linarith

private theorem eventually_octuple_error_small :
    ∀ᶠ x : ℝ in atTop, log (8 * x + 1) ≤ log 2 * x := by
  have hroot : Tendsto (fun x : ℝ ↦ log 2 * √x) atTop atTop :=
    Real.tendsto_sqrt_atTop.const_mul_atTop (log_pos one_lt_two)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hroot.eventually_ge_atTop 6] with x hx hlarge
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hz0 : 0 ≤ 8 * x + 1 := by positivity
  have hsquare : (√x) ^ 2 = x := sq_sqrt hx0
  have hband : √(8 * x + 1) ≤ 3 * √x := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  have hlog := Real.log_le_rpow_div hz0 (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hlog' : log (8 * x + 1) ≤ 2 * √(8 * x + 1) := by
    nlinarith
  calc
    log (8 * x + 1) ≤ 2 * √(8 * x + 1) := hlog'
    _ ≤ 6 * √x := by nlinarith
    _ ≤ log 2 * x := by
      have hmul := mul_le_mul_of_nonneg_right hlarge (Real.sqrt_nonneg x)
      rw [mul_assoc, ← pow_two, hsquare] at hmul
      simpa [mul_comm, mul_left_comm] using hmul

private theorem eventually_octuple_sqrt_small :
    ∀ᶠ x : ℝ in atTop, 4 * √x * log x ≤ log 2 * x := by
  have hsmall :=
    (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (c := log 2 / 4) (div_pos (log_pos one_lt_two) (by norm_num))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with x hx hsmallx
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hlogx : 0 ≤ log x := (log_pos hx).le
  have hrpow : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogx,
    abs_of_nonneg hrpow, ← Real.sqrt_eq_rpow] at hsmallx
  have hlin : 4 * log x ≤ log 2 * √x := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.sqrt_nonneg x)
  calc
    4 * √x * log x = 4 * log x * √x := by ring
    _ ≤ log 2 * √x * √x := hmul
    _ = log 2 * x := by rw [mul_assoc, ← pow_two, sq_sqrt hx0]

/-- The explicit fixed-band Chebyshev lower expression has a positive
`x / log x` margin.  The factor `8` is chosen because the pinned explicit
upper estimate contributes `2 log 4 = 4 log 2` to the leading coefficient. -/
theorem eventually_octupleChebyshevLower_ge :
    ∀ᶠ x : ℝ in atTop, log 2 * x / log x ≤ octupleChebyshevLower x := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    tendsto_log_atTop.eventually_ge_atTop (3 * log 8),
    eventually_octuple_error_small, eventually_octuple_sqrt_small]
      with x hx hscale herr hsqrt
  exact octupleChebyshevLower_pointwise hx hscale herr hsqrt

private theorem eventually_rpow_le_log_two_mul_div
    {delta : ℝ} (hdelta1 : delta < 1) :
    ∀ᶠ x : ℝ in atTop, x ^ delta ≤ log 2 * x / log x := by
  have hgap : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hsmall := (isLittleO_log_rpow_atTop hgap).bound
    (c := log 2) (log_pos one_lt_two)
  filter_upwards [eventually_gt_atTop (1 : ℝ), hsmall] with x hx hsmallx
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hlogx : 0 < log x := log_pos hx
  have hrpowgap : 0 ≤ x ^ (1 - delta) := Real.rpow_nonneg hx0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogx,
    abs_of_nonneg hrpowgap] at hsmallx
  apply (le_div_iff₀ hlogx).2
  have hmul := mul_le_mul_of_nonneg_left hsmallx (Real.rpow_nonneg hx0 delta)
  calc
    x ^ delta * log x
        ≤ x ^ delta * (log 2 * x ^ (1 - delta)) := hmul
    _ = log 2 * (x ^ delta * x ^ (1 - delta)) := by ring
    _ = log 2 * x ^ (delta + (1 - delta)) := by
      rw [Real.rpow_add (zero_lt_one.trans hx)]
    _ = log 2 * x := by ring_nf; simp

/-- For every sublinear exponent, the exact Chebyshev expression for the
fixed band `(y, 8y]` eventually dominates the integer threshold
`floor(y^delta)`. -/
theorem eventually_octupleChebyshev_dominates_floor
    {delta : ℝ} (_hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ y : ℕ in atTop,
      ((⌊(y : ℝ) ^ delta⌋₊ : ℕ) : ℝ) ≤
        (((8 * y : ℕ) : ℝ) * log 2 - log (((8 * y : ℕ) : ℝ) + 1)) /
            log ((8 * y : ℕ) : ℝ) -
          (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ)) := by
  have hreal : ∀ᶠ x : ℝ in atTop, x ^ delta ≤ octupleChebyshevLower x :=
    by
      filter_upwards [eventually_rpow_le_log_two_mul_div hdelta1,
        eventually_octupleChebyshevLower_ge] with x hx hcheb
      exact hx.trans hcheb
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hreal] with y hy
  have hfloor : ((⌊(y : ℝ) ^ delta⌋₊ : ℕ) : ℝ) ≤ (y : ℝ) ^ delta :=
    Nat.floor_le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ y) delta)
  refine hfloor.trans ?_
  simpa [octupleChebyshevLower, Nat.cast_mul] using hy

/-- Consequently, for every `0 < delta < 1`, the fixed band `(y, 8y]`
eventually contains at least `floor(y^delta)` primes.  Its squarefree products
of that many distinct primes have the exact binomial cardinality and the
standard explicit factorial lower bound. -/
theorem eventually_octuplePrimeBand_product_population
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∀ᶠ y : ℕ in atTop,
      let k := ⌊(y : ℝ) ^ delta⌋₊
      k ≤ (widePrimeBand 8 y).card ∧
        (primeBandProducts (widePrimeBand 8 y) k).card =
          Nat.choose (widePrimeBand 8 y).card k ∧
        ((((widePrimeBand 8 y).card + 1 - k : ℕ) : ℝ) ^ k /
            (k.factorial : ℝ)) ≤
          (primeBandProducts (widePrimeBand 8 y) k).card := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_octupleChebyshev_dominates_floor hdelta0 hdelta1]
      with y hy hdom
  exact chebyshev_widePrimeBand_product_population 8 y ⌊(y : ℝ) ^ delta⌋₊
    (by norm_num) (by omega) hdom

end RiemannHypothesisProofFactory.MobiusResidualComplexity
