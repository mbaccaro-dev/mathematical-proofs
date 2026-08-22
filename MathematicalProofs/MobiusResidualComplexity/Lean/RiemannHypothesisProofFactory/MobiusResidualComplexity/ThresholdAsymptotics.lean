import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandAsymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open Filter Real Asymptotics
open scoped Topology

/-- The manuscript's sparse prime-product rank at continuous scale `x`. -/
noncomputable def thresholdCount (delta x : ℝ) : ℕ :=
  ⌊ x ^ delta ⌋₊

noncomputable def thresholdCountReal (delta x : ℝ) : ℝ :=
  thresholdCount delta x

/-- Twice the fixed-band product scale.  The factor two is the one appearing
in the normalized residual-complexity budget. -/
noncomputable def thresholdScale (delta x : ℝ) : ℝ :=
  2 * (8 * x) ^ thresholdCount delta x

private theorem thresholdCount_div_rpow_tendsto
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ ↦ thresholdCountReal delta x / x ^ delta)
      atTop (nhds 1) := by
  have hpow : Tendsto (fun x : ℝ ↦ x ^ delta) atTop atTop :=
    tendsto_rpow_atTop hdelta
  have h := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hpow
  convert h using 1
  ext x
  rfl

private theorem log_fixed_mul_isEquivalent_log (A : ℝ) (hA : 0 < A) :
    (fun x : ℝ ↦ log (A * x)) ~[atTop] (fun x : ℝ ↦ log x) := by
  have hbase :
      (fun x : ℝ ↦ log A + log x) ~[atTop] (fun x : ℝ ↦ log x) :=
    (IsEquivalent.refl.const_add_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp tendsto_log_atTop))
  apply hbase.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Pi.sub_apply]
  rw [log_mul hA.ne' hx.ne']

private theorem rpow_mul_log_tendsto_atTop
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ ↦ x ^ delta * log x) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [(tendsto_rpow_atTop hdelta).eventually_ge_atTop (max b 0),
    tendsto_log_atTop.eventually_ge_atTop 1] with x hx hlog
  have hrpow_nonneg : 0 ≤ x ^ delta := le_trans (le_max_right b 0) hx
  calc
    b ≤ max b 0 := le_max_left _ _
    _ ≤ x ^ delta := hx
    _ ≤ x ^ delta * log x := by nlinarith

private theorem log_thresholdScale_isEquivalent
    {delta : ℝ} (hdelta : 0 < delta) :
    (fun x : ℝ ↦ log (thresholdScale delta x)) ~[atTop]
      (fun x : ℝ ↦ x ^ delta * log x) := by
  have hcount :
      (fun x : ℝ ↦ thresholdCountReal delta x) ~[atTop]
        (fun x : ℝ ↦ x ^ delta) := by
    apply (isEquivalent_iff_tendsto_one ?_).2
    · exact thresholdCount_div_rpow_tendsto hdelta
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (Real.rpow_pos_of_pos hx delta).ne'
  have hlog := log_fixed_mul_isEquivalent_log 8 (by norm_num)
  have hprod :
      (fun x : ℝ ↦ thresholdCountReal delta x * log (8 * x)) ~[atTop]
        (fun x : ℝ ↦ x ^ delta * log x) := by
    refine (hcount.mul hlog).congr' ?_ ?_
    · exact Eventually.of_forall (fun _ ↦ rfl)
    · exact Eventually.of_forall (fun _ ↦ rfl)
  have hsum :
      (fun x : ℝ ↦ log 2 + thresholdCountReal delta x * log (8 * x)) ~[atTop]
        (fun x : ℝ ↦ x ^ delta * log x) :=
    hprod.const_add_of_norm_tendsto_atTop
      (tendsto_norm_atTop_atTop.comp (rpow_mul_log_tendsto_atTop hdelta))
  apply hsum.congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Pi.sub_apply]
  have h8x : 8 * x ≠ 0 := mul_ne_zero (by norm_num) hx.ne'
  rw [thresholdScale,
    log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ h8x), log_pow]
  change log 2 + thresholdCountReal delta x * log (8 * x) -
      x ^ delta * log x =
    log 2 + thresholdCountReal delta x * log (8 * x) -
      x ^ delta * log x
  ring

private theorem log_rpow_mul_log_div_log_tendsto
    {delta : ℝ} (_hdelta : 0 < delta) :
    Tendsto (fun x : ℝ ↦ log (x ^ delta * log x) / log x)
      atTop (nhds delta) := by
  have hsmall0 := isLittleO_log_id_atTop.comp_tendsto tendsto_log_atTop
  have hsmall :
      Tendsto (fun x : ℝ ↦ log (log x) / log x) atTop (nhds 0) := by
    have hraw := hsmall0.tendsto_div_nhds_zero
    convert hraw using 1
    ext x
    rfl
  have hsum :
      Tendsto (fun x : ℝ ↦ delta + log (log x) / log x)
        atTop (nhds (delta + 0)) := tendsto_const_nhds.add hsmall
  rw [add_zero] at hsum
  apply (tendsto_congr' ?_).2 hsum
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [log_mul (Real.rpow_pos_of_pos (zero_lt_one.trans hx) delta).ne'
      (log_pos hx).ne', Real.log_rpow (zero_lt_one.trans hx) delta]
  field_simp [(log_pos hx).ne']

private theorem log_log_thresholdScale_div_log_tendsto
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : ℝ ↦ log (log (thresholdScale delta x)) / log x)
      atTop (nhds delta) := by
  have hrefTop := rpow_mul_log_tendsto_atTop hdelta
  have hrefLogTop := tendsto_log_atTop.comp hrefTop
  have hequiv := (log_thresholdScale_isEquivalent hdelta).log hrefTop
  have hratio :
      Tendsto
        (fun x : ℝ ↦
          log (log (thresholdScale delta x)) / log (x ^ delta * log x))
        atTop (nhds 1) := by
    have hz : ∀ᶠ x : ℝ in atTop, log (x ^ delta * log x) ≠ 0 := by
      simpa only [Function.comp_apply] using hrefLogTop.eventually_ne_atTop 0
    have hraw := (isEquivalent_iff_tendsto_one hz).1 hequiv
    convert hraw using 1
    ext x
    rfl
  have hproduct := hratio.mul (log_rpow_mul_log_div_log_tendsto hdelta)
  have heq :
      (fun x : ℝ ↦ log (log (thresholdScale delta x)) / log x) =ᶠ[atTop]
        (fun x : ℝ ↦
          log (log (thresholdScale delta x)) / log (x ^ delta * log x) *
            (log (x ^ delta * log x) / log x)) := by
    filter_upwards [hrefLogTop.eventually_ne_atTop 0,
      tendsto_log_atTop.eventually_ne_atTop 0] with x href hlog
    have href' : log (log x * x ^ delta) ≠ 0 := by
      simpa only [Function.comp_apply, mul_comm] using href
    field_simp [href']
  simpa using (tendsto_congr' heq).2 hproduct

/-- Exact logarithmic scale conversion for the manuscript's choice
`k = floor(x^delta)` and `2 X = 2 (8x)^k`.  The normalized logarithmic budget
is asymptotic to `k / delta`, with no hidden loss in the leading constant. -/
theorem threshold_logarithmic_scale_conversion
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto
      (fun x : ℝ ↦
        (log (thresholdScale delta x) /
            log (log (thresholdScale delta x))) /
          (thresholdCount delta x : ℝ))
      atTop (nhds (1 / delta)) := by
  have hrefTop := rpow_mul_log_tendsto_atTop hdelta
  have hnumEquiv := log_thresholdScale_isEquivalent hdelta
  have hnum :
      Tendsto
        (fun x : ℝ ↦ log (thresholdScale delta x) / (x ^ delta * log x))
        atTop (nhds 1) := by
    have hz : ∀ᶠ x : ℝ in atTop, x ^ delta * log x ≠ 0 :=
      hrefTop.eventually_ne_atTop 0
    have hraw := (isEquivalent_iff_tendsto_one hz).1 hnumEquiv
    convert hraw using 1
    ext x
    rfl
  have hden := log_log_thresholdScale_div_log_tendsto hdelta
  have hcount := thresholdCount_div_rpow_tendsto hdelta
  have hcountInv :
      Tendsto (fun x : ℝ ↦ (thresholdCountReal delta x / x ^ delta)⁻¹)
        atTop (nhds 1) := by
    simpa using hcount.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hcombined := (hnum.div hden hdelta.ne').mul hcountInv
  have hkTop : Tendsto (fun x : ℝ ↦ thresholdCount delta x) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hdelta)
  have hloglogTop :
      Tendsto (fun x : ℝ ↦ log (log (thresholdScale delta x))) atTop atTop :=
    tendsto_log_atTop.comp
      ((log_thresholdScale_isEquivalent hdelta).symm.tendsto_atTop hrefTop)
  have heq :
      (fun x : ℝ ↦
        (log (thresholdScale delta x) / log (log (thresholdScale delta x))) /
          (thresholdCount delta x : ℝ)) =ᶠ[atTop]
        (fun x : ℝ ↦
          (log (thresholdScale delta x) / (x ^ delta * log x)) /
              (log (log (thresholdScale delta x)) / log x) *
            (thresholdCountReal delta x / x ^ delta)⁻¹) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hkTop.eventually_ge_atTop 1,
      hloglogTop.eventually_ne_atTop 0]
        with x hx hk hscaleLog
    have hxpow : x ^ delta ≠ 0 :=
      (Real.rpow_pos_of_pos (zero_lt_one.trans hx) delta).ne'
    have hlog : log x ≠ 0 := (log_pos hx).ne'
    have hkreal : thresholdCountReal delta x ≠ 0 := by
      simp only [thresholdCountReal, Nat.cast_ne_zero]
      omega
    simp only [thresholdCountReal]
    field_simp
  simpa using (tendsto_congr' heq).2 hcombined

private theorem thresholdScale_tendsto_atTop
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (thresholdScale delta) atTop atTop := by
  have hrefTop := rpow_mul_log_tendsto_atTop hdelta
  have hlogScaleTop :
      Tendsto (fun x : ℝ ↦ log (thresholdScale delta x)) atTop atTop :=
    (log_thresholdScale_isEquivalent hdelta).symm.tendsto_atTop hrefTop
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hlogScaleTop.eventually_ge_atTop (log (max b 1)),
    eventually_gt_atTop (0 : ℝ)] with x hlog hx
  have hscalePos : 0 < thresholdScale delta x := by
    exact mul_pos (by norm_num) (pow_pos (mul_pos (by norm_num) hx) _)
  have hmaxPos : 0 < max b 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact (le_max_left b 1).trans ((log_le_log_iff hmaxPos hscalePos).1 hlog)

/-- The eventual form of a strict limsup budget is enough to force the exact
rank separation used in the obstruction proof.  This theorem does not assume
the desired separation: it derives it from the normalized budget and the
proved logarithmic scale conversion. -/
theorem eventually_threshold_budget_separation
    (R : ℝ → ℝ) {delta r q : ℝ}
    (hdelta : 0 < delta) (hr : 0 < r) (hq : r / delta < q)
    (hbudget : ∀ᶠ X : ℝ in atTop,
      R X * log (log X) / log X < r) :
    ∀ᶠ x : ℝ in atTop,
      R (thresholdScale delta x) < q * thresholdCountReal delta x := by
  have hscale := thresholdScale_tendsto_atTop hdelta
  have hbudgetScale := hscale.eventually hbudget
  have hconversion := threshold_logarithmic_scale_conversion hdelta
  have hlimitPos : 0 < 1 / delta := one_div_pos.mpr hdelta
  have hupperGap : 1 / delta < q / r := by
    apply (lt_div_iff₀ hr).2
    calc
      1 / delta * r = r / delta := by field_simp
      _ < q := hq
  have hconversionPos :
      ∀ᶠ x : ℝ in atTop, 0 <
        (log (thresholdScale delta x) /
            log (log (thresholdScale delta x))) /
          thresholdCountReal delta x :=
    (tendsto_order.1 hconversion).1 0 hlimitPos
  have hconversionUpper :
      ∀ᶠ x : ℝ in atTop,
        (log (thresholdScale delta x) /
            log (log (thresholdScale delta x))) /
          thresholdCountReal delta x < q / r :=
    (tendsto_order.1 hconversion).2 (q / r) hupperGap
  have hkTop : Tendsto (fun x : ℝ ↦ thresholdCount delta x) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hdelta)
  have hrefTop := rpow_mul_log_tendsto_atTop hdelta
  have hlogScaleTop :
      Tendsto (fun x : ℝ ↦ log (thresholdScale delta x)) atTop atTop :=
    (log_thresholdScale_isEquivalent hdelta).symm.tendsto_atTop hrefTop
  have hloglogScaleTop :
      Tendsto (fun x : ℝ ↦ log (log (thresholdScale delta x))) atTop atTop :=
    tendsto_log_atTop.comp hlogScaleTop
  filter_upwards [hbudgetScale, hconversionPos, hconversionUpper,
    hkTop.eventually_ge_atTop 1,
    hlogScaleTop.eventually_gt_atTop 0,
    hloglogScaleTop.eventually_gt_atTop 0]
      with x hB hconvPos hconvUpper hk hlogPos hloglogPos
  have hkreal : 0 < thresholdCountReal delta x := by
    simp only [thresholdCountReal, Nat.cast_pos]
    omega
  have hproduct :
      (R (thresholdScale delta x) *
          log (log (thresholdScale delta x)) /
        log (thresholdScale delta x)) *
          ((log (thresholdScale delta x) /
              log (log (thresholdScale delta x))) /
            thresholdCountReal delta x) < q := by
    calc
      _ < r *
          ((log (thresholdScale delta x) /
              log (log (thresholdScale delta x))) /
            thresholdCountReal delta x) :=
        mul_lt_mul_of_pos_right hB hconvPos
      _ ≤ r * (q / r) :=
        mul_le_mul_of_nonneg_left hconvUpper.le hr.le
      _ = q := by field_simp
  have hquot : R (thresholdScale delta x) / thresholdCountReal delta x < q := by
    have heq :
        R (thresholdScale delta x) / thresholdCountReal delta x =
          (R (thresholdScale delta x) *
              log (log (thresholdScale delta x)) /
            log (thresholdScale delta x)) *
              ((log (thresholdScale delta x) /
                  log (log (thresholdScale delta x))) /
                thresholdCountReal delta x) := by
      field_simp [hlogPos.ne', hloglogPos.ne', hkreal.ne']
    rw [heq]
    exact hproduct
  exact (div_lt_iff₀ hkreal).1 hquot

end RiemannHypothesisProofFactory.MobiusResidualComplexity
