import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannHypothesisProofFactory.MobiusResidualComplexity.ExactCompression

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The positive Möbius vertices of a finite cell. -/
def positiveVertices (H : Finset ℕ) : Finset ℕ :=
  H.filter fun n => μ n = 1

/-- The negative Möbius vertices of a finite cell. -/
def negativeVertices (H : Finset ℕ) : Finset ℕ :=
  H.filter fun n => μ n = -1

/-- The signed Möbius mass of a finite cell. -/
def cellMass (H : Finset ℕ) : ℤ :=
  ∑ n ∈ H, μ n

/-- The genuine common core of a finite cell. -/
def cellGCD (H : Finset ℕ) : ℕ := H.gcd id

theorem squarefree_cell_mass_eq_card_sub_card
    (H : Finset ℕ)
    (hsquarefree : ∀ n ∈ H, Squarefree n) :
    cellMass H = (positiveVertices H).card - (negativeVertices H).card := by
  have hvalues : ∀ n ∈ H, μ n = 1 ∨ μ n = -1 := by
    intro n hn
    exact ArithmeticFunction.moebius_ne_zero_iff_eq_or.mp
      (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr (hsquarefree n hn))
  have hdisjoint : Disjoint (positiveVertices H) (negativeVertices H) := by
    refine Finset.disjoint_left.mpr ?_
    intro n hnpos hnneg
    simp only [positiveVertices, Finset.mem_filter] at hnpos
    simp only [negativeVertices, Finset.mem_filter] at hnneg
    omega
  have hunion : positiveVertices H ∪ negativeVertices H = H := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_union.mp hn with hn | hn
      · exact (Finset.mem_filter.mp hn).1
      · exact (Finset.mem_filter.mp hn).1
    · intro hn
      rcases hvalues n hn with hpos | hneg
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, hpos⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, hneg⟩)
  have hpositive : (∑ n ∈ positiveVertices H, μ n) =
      ((positiveVertices H).card : ℤ) := by
    calc
      (∑ n ∈ positiveVertices H, μ n) =
          ∑ _n ∈ positiveVertices H, (1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact (Finset.mem_filter.mp hn).2
      _ = ((positiveVertices H).card : ℤ) := by simp
  have hnegative : (∑ n ∈ negativeVertices H, μ n) =
      -((negativeVertices H).card : ℤ) := by
    calc
      (∑ n ∈ negativeVertices H, μ n) =
          ∑ _n ∈ negativeVertices H, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact (Finset.mem_filter.mp hn).2
      _ = -((negativeVertices H).card : ℤ) := by simp
  change (∑ n ∈ H, μ n) =
    (positiveVertices H).card - (negativeVertices H).card
  calc
    (∑ n ∈ H, μ n) =
        ∑ n ∈ positiveVertices H ∪ negativeVertices H, μ n := by rw [hunion]
    _ = (∑ n ∈ positiveVertices H, μ n) +
        ∑ n ∈ negativeVertices H, μ n := Finset.sum_union hdisjoint
    _ = (positiveVertices H).card - (negativeVertices H).card := by
      rw [hpositive, hnegative]
      omega

theorem zero_mass_squarefree_cell_balanced
    (H : Finset ℕ)
    (hsquarefree : ∀ n ∈ H, Squarefree n)
    (hzero : cellMass H = 0) :
    (positiveVertices H).card = (negativeVertices H).card := by
  rw [squarefree_cell_mass_eq_card_sub_card H hsquarefree] at hzero
  omega

private theorem positiveVertices_filter_le (H : Finset ℕ) (X : ℝ) :
    positiveVertices (H.filter (fun n : ℕ => (n : ℝ) ≤ X)) =
      (positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X) := by
  ext n
  simp [positiveVertices, and_comm, and_left_comm, and_assoc]

private theorem negativeVertices_filter_le (H : Finset ℕ) (X : ℝ) :
    negativeVertices (H.filter (fun n : ℕ => (n : ℝ) ≤ X)) =
      (negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X) := by
  ext n
  simp [negativeVertices, and_comm, and_left_comm, and_assoc]

private theorem orderEmbOfFin_le_iff_lt_card_filter
    (s : Finset ℕ) {k : ℕ} (h : s.card = k) (X : ℝ) (i : Fin k) :
    ((s.orderEmbOfFin h i : ℕ) : ℝ) ≤ X ↔
      i.val < (s.filter fun n : ℕ => (n : ℝ) ≤ X).card := by
  classical
  constructor
  · intro hi
    have hsubset :
        (Finset.Iic i).map (s.orderEmbOfFin h).toEmbedding ⊆
          s.filter (fun n : ℕ => (n : ℝ) ≤ X) := by
      intro n hn
      rcases Finset.mem_map.mp hn with ⟨j, hj, rfl⟩
      have hji : j ≤ i := Finset.mem_Iic.mp hj
      exact Finset.mem_filter.mpr
          ⟨Finset.orderEmbOfFin_mem s h j,
          le_trans (by exact_mod_cast (s.orderEmbOfFin h).monotone hji) hi⟩
    have hcard := Finset.card_le_card hsubset
    simpa using hcard
  · intro hi
    by_contra hnot
    have hXi : X < ((s.orderEmbOfFin h i : ℕ) : ℝ) := lt_of_not_ge hnot
    have hsubset :
        s.filter (fun n : ℕ => (n : ℝ) ≤ X) ⊆
          (Finset.Iio i).map (s.orderEmbOfFin h).toEmbedding := by
      intro n hn
      have hns : n ∈ s := (Finset.mem_filter.mp hn).1
      have hnX : (n : ℝ) ≤ X := (Finset.mem_filter.mp hn).2
      let j : Fin k := (s.orderIsoOfFin h).symm ⟨n, hns⟩
      have hjn : s.orderEmbOfFin h j = n := by
        exact congrArg Subtype.val ((s.orderIsoOfFin h).apply_symm_apply ⟨n, hns⟩)
      have hji : j < i := by
        by_contra hji
        have hij : i ≤ j := le_of_not_gt hji
        have hmono : s.orderEmbOfFin h i ≤ s.orderEmbOfFin h j :=
          (s.orderEmbOfFin h).monotone hij
        rw [hjn] at hmono
        have : (((s.orderEmbOfFin h i : ℕ) : ℝ) ≤ (n : ℝ)) := by
          exact_mod_cast hmono
        linarith
      exact Finset.mem_map.mpr ⟨j, Finset.mem_Iio.mpr hji, hjn⟩
    have hcard := Finset.card_le_card hsubset
    have hle : (s.filter fun n : ℕ => (n : ℝ) ≤ X).card ≤ i.val := by
      simpa using hcard
    omega

/-- Increasing-rank pairing compresses an exact zero-sum squarefree Möbius
cell into opposite-sign pairs. The pairwise gcd inherits the common-core
prime-factor budget, every pair stays within the cell diameter, and the exact
number of ranks crossing every cutoff equals the absolute signed cell mass
below that cutoff. -/
theorem exact_fixed_budget_pair_compression
    (H : Finset ℕ) (g budget : ℕ)
    (hnonempty : H.Nonempty)
    (hsquarefree : ∀ n ∈ H, Squarefree n)
    (hpositive : ∀ n ∈ H, 0 < n)
    (hzero : cellMass H = 0)
    (hg : 0 < g)
    (hcommon : ∀ n ∈ H, g ∣ n)
    (hbudget : ∀ n ∈ H, omega (n / g) ≤ budget) :
    ∃ hcard : (positiveVertices H).card = (negativeVertices H).card,
      (∀ i : Fin (positiveVertices H).card,
        let a := (positiveVertices H).orderEmbOfFin rfl i
        let b := (negativeVertices H).orderEmbOfFin hcard.symm i
        a ∈ H ∧ b ∈ H ∧ μ a = 1 ∧ μ b = -1 ∧
          omega (a / Nat.gcd a b) ≤ budget ∧
          omega (b / Nat.gcd a b) ≤ budget ∧
          Nat.dist a b ≤ H.max' hnonempty - H.min' hnonempty) ∧
      (∀ X : ℝ,
        (rankCrossingIndices (positiveVertices H).card
          ((positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card
          ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card).card =
        Int.natAbs (cellMass (H.filter (fun n : ℕ => (n : ℝ) ≤ X)))) ∧
      ∀ (X : ℝ) (i : Fin (positiveVertices H).card),
        (i.val ∈ rankCrossingIndices (positiveVertices H).card
          ((positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card
          ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card) ↔
        (((((positiveVertices H).orderEmbOfFin rfl i : ℕ) : ℝ) ≤ X) ≠
          ((((negativeVertices H).orderEmbOfFin hcard.symm i : ℕ) : ℝ) ≤ X)) := by
  let hcard := zero_mass_squarefree_cell_balanced H hsquarefree hzero
  refine ⟨hcard, ?_, ?_, ?_⟩
  · intro i
    let a := (positiveVertices H).orderEmbOfFin rfl i
    let b := (negativeVertices H).orderEmbOfFin hcard.symm i
    have haPos : a ∈ positiveVertices H :=
      Finset.orderEmbOfFin_mem (positiveVertices H) rfl i
    have hbNeg : b ∈ negativeVertices H :=
      Finset.orderEmbOfFin_mem (negativeVertices H) hcard.symm i
    have haH : a ∈ H := (Finset.mem_filter.mp haPos).1
    have hbH : b ∈ H := (Finset.mem_filter.mp hbNeg).1
    have haMu : μ a = 1 := (Finset.mem_filter.mp haPos).2
    have hbMu : μ b = -1 := (Finset.mem_filter.mp hbNeg).2
    have hresidual := common_core_residual_budget a b g budget
      (hpositive a haH) (hpositive b hbH) hg
      (hcommon a haH) (hcommon b hbH)
      (hbudget a haH) (hbudget b hbH)
    have haMin : H.min' hnonempty ≤ a := H.min'_le a haH
    have haMax : a ≤ H.max' hnonempty := H.le_max' a haH
    have hbMin : H.min' hnonempty ≤ b := H.min'_le b hbH
    have hbMax : b ≤ H.max' hnonempty := H.le_max' b hbH
    have hdiameter : Nat.dist a b ≤ H.max' hnonempty - H.min' hnonempty := by
      unfold Nat.dist
      omega
    exact ⟨haH, hbH, haMu, hbMu, hresidual.1, hresidual.2,
      hdiameter⟩
  · intro X
    have hposCard :
        ((positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card ≤
          (positiveVertices H).card := Finset.card_filter_le _ _
    have hnegCardRaw :
        ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card ≤
          (negativeVertices H).card := Finset.card_filter_le _ _
    have hnegCard :
        ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card ≤
          (positiveVertices H).card := by simpa [hcard] using hnegCardRaw
    rw [exact_rank_pair_crossing_balance _ _ _ hposCard hnegCard]
    rw [squarefree_cell_mass_eq_card_sub_card]
    · rw [positiveVertices_filter_le, negativeVertices_filter_le]
    · intro n hn
      exact hsquarefree n (Finset.mem_filter.mp hn).1
  · intro X i
    simp only [rankCrossingIndices, Finset.mem_filter, Finset.mem_range,
      i.isLt, true_and]
    rw [← orderEmbOfFin_le_iff_lt_card_filter (positiveVertices H) rfl X i,
      ← orderEmbOfFin_le_iff_lt_card_filter (negativeVertices H) hcard.symm X i]

/-- The canonical version of fixed-budget pair compression.  The common core
is the gcd of the whole cell, so it is constructed from the cell rather than
supplied as an auxiliary witness. -/
theorem exact_cell_gcd_pair_compression
    (H : Finset ℕ) (budget : ℕ)
    (hnonempty : H.Nonempty)
    (hsquarefree : ∀ n ∈ H, Squarefree n)
    (hpositive : ∀ n ∈ H, 0 < n)
    (hzero : cellMass H = 0)
    (hbudget : ∀ n ∈ H, omega (n / cellGCD H) ≤ budget) :
    ∃ hcard : (positiveVertices H).card = (negativeVertices H).card,
      (∀ i : Fin (positiveVertices H).card,
        let a := (positiveVertices H).orderEmbOfFin rfl i
        let b := (negativeVertices H).orderEmbOfFin hcard.symm i
        a ∈ H ∧ b ∈ H ∧ μ a = 1 ∧ μ b = -1 ∧
          omega (a / Nat.gcd a b) ≤ budget ∧
          omega (b / Nat.gcd a b) ≤ budget ∧
          Nat.dist a b ≤ H.max' hnonempty - H.min' hnonempty) ∧
      (∀ X : ℝ,
        (rankCrossingIndices (positiveVertices H).card
          ((positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card
          ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card).card =
        Int.natAbs (cellMass (H.filter (fun n : ℕ => (n : ℝ) ≤ X)))) ∧
      ∀ (X : ℝ) (i : Fin (positiveVertices H).card),
        (i.val ∈ rankCrossingIndices (positiveVertices H).card
          ((positiveVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card
          ((negativeVertices H).filter (fun n : ℕ => (n : ℝ) ≤ X)).card) ↔
        (((((positiveVertices H).orderEmbOfFin rfl i : ℕ) : ℝ) ≤ X) ≠
          ((((negativeVertices H).orderEmbOfFin hcard.symm i : ℕ) : ℝ) ≤ X)) := by
  have hgNe : cellGCD H ≠ 0 := by
    rw [cellGCD, Finset.gcd_ne_zero_iff]
    rcases hnonempty with ⟨n, hn⟩
    exact ⟨n, hn, (hpositive n hn).ne'⟩
  have hg : 0 < cellGCD H := Nat.pos_of_ne_zero hgNe
  have hcommon : ∀ n ∈ H, cellGCD H ∣ n := by
    intro n hn
    simpa [cellGCD] using (Finset.gcd_dvd (f := id) hn)
  exact exact_fixed_budget_pair_compression H (cellGCD H) budget
    hnonempty hsquarefree hpositive hzero hg hcommon hbudget

end RiemannHypothesisProofFactory.MobiusResidualComplexity
