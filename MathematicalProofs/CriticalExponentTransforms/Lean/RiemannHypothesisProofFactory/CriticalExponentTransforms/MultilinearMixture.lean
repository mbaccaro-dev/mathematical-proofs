import RiemannHypothesisProofFactory.CriticalExponentTransforms.FiniteMixture
import RiemannHypothesisProofFactory.CriticalExponentTransforms.PurePowerGap
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open Filter Finset Fintype Real Topology
open scoped BigOperators

namespace RiemannHypothesisProofFactory.CriticalExponentTransforms

abbrev Signal := PosReal → ℝ

abbrev Observable (V : Type*) := PosReal → V

noncomputable def powerTuple (d : ℕ) (tau : Fin d → ℝ) : Fin d → Signal :=
  fun i ↦ powerMode (tau i)

/-- Dilation covariance determines the value of a multilinear observable on
every tuple of pure powers from its value at one. -/
theorem multilinear_power_tuple_law
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (tau : Fin d → ℝ) (kappa : ℝ)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      B (powerTuple d tau) x =
        (x.1 ^ ((∑ i, tau i) - kappa)) •
          B (powerTuple d tau) ⟨1, by positivity⟩ := by
  intro x
  have hinput :
      (fun i ↦ inputDilation x.1 x.2 (powerMode (tau i))) =
        fun i ↦ (x.1 ^ tau i) • powerMode (tau i) := by
    funext i y
    rw [inputDilation_powerMode]
    rfl
  have hdilate := congrFun
    (hcov x.1 x.2 (fun i ↦ powerMode (tau i))) (⟨1, by positivity⟩ : PosReal)
  rw [hinput, B.map_smul_univ] at hdilate
  simp only [outputDilation, mul_one] at hdilate
  rw [← Real.rpow_sum_of_pos x.2 tau Finset.univ] at hdilate
  change (x.1 ^ (∑ i, tau i)) •
      B (fun i ↦ powerMode (tau i)) ⟨1, by positivity⟩ =
    (x.1 ^ kappa) • B (fun i ↦ powerMode (tau i)) x at hdilate
  have hkpos : 0 < x.1 ^ kappa := Real.rpow_pos_of_pos x.2 kappa
  apply smul_right_injective V (ne_of_gt hkpos)
  change (x.1 ^ kappa) • B (fun i ↦ powerMode (tau i)) x =
    (x.1 ^ kappa) •
      ((x.1 ^ ((∑ i, tau i) - kappa)) •
        B (fun i ↦ powerMode (tau i)) ⟨1, by positivity⟩)
  rw [← hdilate, smul_smul]
  congr 1
  rw [← Real.rpow_add x.2]
  ring_nf

noncomputable def slotExponents (d : ℕ) (I : Finset (Fin d))
    (sigma rho : ℝ) : Fin d → ℝ :=
  fun i ↦ if i ∈ I then rho else sigma

noncomputable def slotPowers (d : ℕ) (I : Finset (Fin d))
    (sigma rho : ℝ) : Fin d → Signal :=
  fun i ↦ powerMode (slotExponents d I sigma rho i)

noncomputable def operatorDifference
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c : ℝ) : Observable V :=
  fun x ↦
    B (fun _ ↦ powerMode sigma + c • powerMode rho) x -
      B (fun _ ↦ powerMode sigma) x

noncomputable def subsetCoefficient
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho : ℝ) (I : Finset (Fin d)) : V :=
  B (slotPowers d I sigma rho) ⟨1, by positivity⟩

noncomputable def subsetExponent (d : ℕ) (I : Finset (Fin d))
    (sigma rho kappa : ℝ) : ℝ :=
  (∑ i, slotExponents d I sigma rho i) - kappa

lemma sum_slotExponents (d : ℕ) (I : Finset (Fin d)) (sigma rho : ℝ) :
    (∑ i, slotExponents d I sigma rho i) =
      (I.card : ℝ) * rho + ((d - I.card : ℕ) : ℝ) * sigma := by
  classical
  simp only [slotExponents]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.filter_mem_eq_inter]
  have hfilter :
      (Finset.univ : Finset (Fin d)).filter (fun i ↦ i ∉ I) =
        (Finset.univ : Finset (Fin d)) \ I := by
    ext i
    simp
  rw [hfilter, Finset.card_sdiff]
  simp

/-- The order of a slot subset.  The codomain includes zero so that the full
binary expansion can be grouped before its baseline term is removed. -/
def subsetOrder (d : ℕ) (I : Finset (Fin d)) : Fin (d + 1) :=
  ⟨I.card, by
    simpa using Nat.lt_succ_of_le (Finset.card_le_univ I)⟩

lemma subsetExponent_eq_mixtureExponent (d : ℕ) (I : Finset (Fin d))
    (sigma rho kappa : ℝ) :
    subsetExponent d I sigma rho kappa =
      mixtureExponent d I.card sigma rho kappa := by
  unfold subsetExponent mixtureExponent
  rw [sum_slotExponents]
  have hcard : I.card ≤ d := by simpa using Finset.card_le_univ I
  rw [Nat.cast_sub hcard]
  ring

/-- The paper's order-`r` coefficient: the sum of every ordered slot choice
with exactly `r` perturbation slots.  The empty subset has already been
removed, so order zero is identically zero. -/
noncomputable def orderCoefficient
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho : ℝ) (r : Fin (d + 1)) : V :=
  ∑ I ∈ ((Finset.univ : Finset (Finset (Fin d))).erase ∅) with
      subsetOrder d I = r,
    subsetCoefficient d B sigma rho I

/-- The exact binary expansion of the perturbed diagonal observable is derived
from multilinearity and dilation covariance; the coefficient vectors are not
assumed as input. -/
theorem multilinear_operator_expansion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      operatorDifference d B sigma rho c x =
        ∑ s ∈ ((Finset.univ : Finset (Finset (Fin d))).erase ∅),
          (c ^ s.card) •
            ((x.1 ^ subsetExponent d s sigma rho kappa) •
              subsetCoefficient d B sigma rho s) := by
  classical
  intro x
  let base : Fin d → Signal := fun _ ↦ powerMode sigma
  let perturb : Fin d → Signal := fun _ ↦ c • powerMode rho
  have hexpand := B.map_add_univ perturb base
  have htuple : ∀ I : Finset (Fin d),
      I.piecewise perturb base =
        I.piecewise (fun i ↦ c • slotPowers d I sigma rho i)
          (slotPowers d I sigma rho) := by
    intro I
    funext i y
    by_cases hi : i ∈ I <;> simp [perturb, base, slotPowers, slotExponents, hi]
  have hterm : ∀ I : Finset (Fin d),
      B (I.piecewise perturb base) x =
        (c ^ I.card) •
          ((x.1 ^ subsetExponent d I sigma rho kappa) •
            subsetCoefficient d B sigma rho I) := by
    intro I
    rw [htuple I, B.map_piecewise_smul]
    simp only [Finset.prod_const, subsetCoefficient]
    change (c ^ I.card) • B (slotPowers d I sigma rho) x = _
    have hpower := multilinear_power_tuple_law d B
      (slotExponents d I sigma rho) kappa hcov x
    change B (fun i ↦ powerMode (slotExponents d I sigma rho i)) x =
      (x.1 ^ ((∑ i, slotExponents d I sigma rho i) - kappa)) •
        B (fun i ↦ powerMode (slotExponents d I sigma rho i))
          ⟨1, by positivity⟩ at hpower
    have hpower' : B (slotPowers d I sigma rho) x =
        (x.1 ^ subsetExponent d I sigma rho kappa) •
          B (slotPowers d I sigma rho) ⟨1, by positivity⟩ := by
      change B (fun i ↦ powerMode (slotExponents d I sigma rho i)) x =
        (x.1 ^ ((∑ i, slotExponents d I sigma rho i) - kappa)) •
          B (fun i ↦ powerMode (slotExponents d I sigma rho i))
            ⟨1, by positivity⟩
      exact hpower
    rw [hpower']
  change B (fun _ ↦ powerMode sigma + c • powerMode rho) x -
      B (fun _ ↦ powerMode sigma) x = _
  rw [show (fun _ : Fin d ↦ powerMode sigma + c • powerMode rho) =
      perturb + base by
    funext i y
    simp [perturb, base, add_comm]]
  change B (perturb + base) x - B base x = _
  rw [hexpand]
  simp only [Finset.sum_apply]
  let U : Finset (Finset (Fin d)) := Finset.univ
  let f : Finset (Fin d) → V := fun I ↦ B (I.piecewise perturb base) x
  change U.sum f - B base x = _
  have hempty : (∅ : Finset (Fin d)) ∈ U := by simp [U]
  have hsplit : (U.erase ∅).sum f + f ∅ = U.sum f :=
    Finset.sum_erase_add U f hempty
  rw [← hsplit]
  have hfempty : f ∅ = B base x := by simp [f]
  rw [hfempty, add_sub_cancel_right]
  apply Finset.sum_congr
  · simp [U]
  · intro I hI
    exact hterm I

/-- Grouping the binary slot expansion by cardinality gives the exact finite
mixture printed in the paper.  In particular, the coefficient vectors are
derived from the multilinear operator rather than supplied as assumptions. -/
theorem multilinear_grouped_expansion
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      operatorDifference d B sigma rho c x =
        ∑ r : Fin (d + 1),
          (c ^ r.1) •
            ((x.1 ^ mixtureExponent d r.1 sigma rho kappa) •
              orderCoefficient d B sigma rho r) := by
  classical
  intro x
  rw [multilinear_operator_expansion d B sigma rho c kappa hcov x]
  let S : Finset (Finset (Fin d)) :=
    (Finset.univ : Finset (Finset (Fin d))).erase ∅
  let term : Finset (Fin d) → V := fun I ↦
    (c ^ I.card) •
      ((x.1 ^ subsetExponent d I sigma rho kappa) •
        subsetCoefficient d B sigma rho I)
  change S.sum term = _
  rw [← Finset.sum_fiberwise S (subsetOrder d) term]
  apply Finset.sum_congr rfl
  intro r _hr
  change
    ∑ I ∈ S with subsetOrder d I = r, term I =
      (c ^ r.1) •
        ((x.1 ^ mixtureExponent d r.1 sigma rho kappa) •
          orderCoefficient d B sigma rho r)
  rw [orderCoefficient, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr
  · rfl
  · intro I hI
    have horder : subsetOrder d I = r := (Finset.mem_filter.mp hI).2
    have hcard : I.card = r.1 := congrArg Fin.val horder
    simp only [term]
    rw [subsetExponent_eq_mixtureExponent, hcard]

lemma orderCoefficient_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho : ℝ) :
    orderCoefficient d B sigma rho (0 : Fin (d + 1)) = 0 := by
  classical
  unfold orderCoefficient
  apply Finset.sum_eq_zero
  intro I hI
  have hmem := Finset.mem_filter.mp hI
  have horder : subsetOrder d I = (0 : Fin (d + 1)) := hmem.2
  have hcard : I.card = 0 := congrArg Fin.val horder
  have hIempty : I = ∅ := Finset.card_eq_zero.mp hcard
  exact False.elim ((Finset.mem_erase.mp hmem.1).1 hIempty)

/-- The grouped operator difference is exactly the explicit finite mixture
whose first-visible-order limit is proved in `FiniteMixture`. -/
theorem operatorDifference_eq_finitePowerMixture
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      operatorDifference d B sigma rho c x =
        finitePowerMixture d c sigma rho kappa
          (fun i ↦ orderCoefficient d B sigma rho i.succ) x.1 := by
  intro x
  rw [multilinear_grouped_expansion d B sigma rho c kappa hcov x]
  rw [Fin.sum_univ_succ, orderCoefficient_zero]
  simp only [smul_zero, zero_add, finitePowerMixture]
  apply Finset.sum_congr rfl
  intro i _hi
  rfl

/-- The operator difference after division by its first visible power. -/
noncomputable def normalizedOperatorDifference
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ) (r0 : Fin d) (x : PosReal) : V :=
  (x.1 ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa)) •
    operatorDifference d B sigma rho c x

lemma normalizedOperatorDifference_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ) (r0 : Fin d)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x) :
    ∀ x : PosReal,
      normalizedOperatorDifference d B sigma rho c kappa r0 x =
        normalizedFinitePowerMixture d c sigma rho kappa
          (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 x.1 := by
  classical
  intro x
  rw [normalizedOperatorDifference,
    operatorDifference_eq_finitePowerMixture d B sigma rho c kappa hcov x]
  unfold finitePowerMixture normalizedFinitePowerMixture
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [smul_smul, smul_smul, smul_smul]
  congr 1
  calc
    x.1 ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa) *
          c ^ (i.1 + 1) *
          x.1 ^ mixtureExponent d (i.1 + 1) sigma rho kappa =
        c ^ (i.1 + 1) *
          (x.1 ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa) *
            x.1 ^ mixtureExponent d (i.1 + 1) sigma rho kappa) := by ring_nf
    _ = c ^ (i.1 + 1) *
          x.1 ^ (-mixtureExponent d (r0.1 + 1) sigma rho kappa +
            mixtureExponent d (i.1 + 1) sigma rho kappa) := by
          rw [Real.rpow_add x.2]
    _ = c ^ (i.1 + 1) *
          x.1 ^ (mixtureExponent d (i.1 + 1) sigma rho kappa -
            mixtureExponent d (r0.1 + 1) sigma rho kappa) := by ring_nf

lemma tendsto_posReal_coe_atTop :
    Tendsto (fun x : PosReal ↦ x.1) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  let y : PosReal := ⟨max b 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _)⟩
  filter_upwards [eventually_ge_atTop y] with x hx
  exact le_trans (le_max_left _ _) hx

/-- The first nonzero grouped coefficient gives the exact leading norm of the
multilinear operator difference.  The expansion is derived from the operator
and its dilation covariance rather than supplied as coefficient data. -/
theorem multilinear_operator_norm_limit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (d : ℕ)
    (B : MultilinearMap ℝ (fun _ : Fin d ↦ Signal) (Observable V))
    (sigma rho c kappa : ℝ) (r0 : Fin d)
    (hcov : ∀ (a : ℝ) (ha : 0 < a) f,
      B (fun i ↦ inputDilation a ha (f i)) =
        fun x ↦ (a ^ kappa) • outputDilation a ha (B f) x)
    (hc : c ≠ 0) (hsigmaRho : rho < sigma)
    (hvanish : ∀ i : Fin d, i < r0 →
      orderCoefficient d B sigma rho i.succ = 0)
    (hvisible : orderCoefficient d B sigma rho r0.succ ≠ 0) :
    Tendsto
      (fun x : PosReal ↦
        ‖normalizedOperatorDifference d B sigma rho c kappa r0 x‖)
      atTop
      (nhds (‖(c ^ (r0.1 + 1)) •
        orderCoefficient d B sigma rho r0.succ‖)) ∧
      0 < ‖(c ^ (r0.1 + 1)) •
        orderCoefficient d B sigma rho r0.succ‖ := by
  have hbase := normalized_finitePowerMixture_norm_tendsto_pos
    d c sigma rho kappa
    (fun i ↦ orderCoefficient d B sigma rho i.succ) r0
    hc hsigmaRho hvanish hvisible
  constructor
  · rw [show (fun x : PosReal ↦
        ‖normalizedOperatorDifference d B sigma rho c kappa r0 x‖) =
      (fun X : ℝ ↦ ‖normalizedFinitePowerMixture d c sigma rho kappa
        (fun i ↦ orderCoefficient d B sigma rho i.succ) r0 X‖) ∘
        (fun x : PosReal ↦ x.1) by
        funext x
        simp only [Function.comp_apply]
        rw [normalizedOperatorDifference_eq d B sigma rho c kappa r0 hcov x]]
    exact hbase.1.comp tendsto_posReal_coe_atTop
  · exact hbase.2

end RiemannHypothesisProofFactory.CriticalExponentTransforms
