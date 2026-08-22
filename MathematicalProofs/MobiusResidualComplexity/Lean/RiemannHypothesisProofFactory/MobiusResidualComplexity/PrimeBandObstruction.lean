import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Dist
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import RiemannHypothesisProofFactory.MobiusResidualComplexity.ExactCompression

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open scoped BigOperators
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega

/-- Products formed from all `k`-element subsets of a finite prime band. -/
def primeBandProducts (Q : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Q.powersetCard k).image fun P ↦ ∏ p ∈ P, p

/-- A product indexed by a finite set of primes is squarefree. -/
theorem squarefree_primeBand_product
    (P : Finset ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (∏ p ∈ P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun _ hp _ hq hpq ↦ ?_)
    (fun p hp ↦ (hprime p hp).squarefree)
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (hprime _ hp) (hprime _ hq)).mpr hpq

/-- Unique factorization makes the prime-subset product map injective, so the
product family has exactly the expected binomial cardinality. -/
theorem primeBandProducts_card
    (Q : Finset ℕ) (k : ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p) :
    (primeBandProducts Q k).card = Nat.choose Q.card k := by
  unfold primeBandProducts
  rw [Finset.card_image_iff.mpr]
  · exact Finset.card_powersetCard k Q
  · intro P hP R hR hprod
    have hPsub : P ⊆ Q := (Finset.mem_powersetCard.mp hP).1
    have hRsub : R ⊆ Q := (Finset.mem_powersetCard.mp hR).1
    have hprimeP : ∀ p ∈ P, Nat.Prime p := fun p hp ↦ hprime p (hPsub hp)
    have hprimeR : ∀ p ∈ R, Nat.Prime p := fun p hp ↦ hprime p (hRsub hp)
    calc
      P = (∏ p ∈ P, p).primeFactors := (Nat.primeFactors_prod hprimeP).symm
      _ = (∏ p ∈ R, p).primeFactors := congrArg Nat.primeFactors hprod
      _ = R := Nat.primeFactors_prod hprimeR

/-- Every product in a fixed-cardinality prime band has the same Möbius sign.
This prevents cancellation inside the population used by the obstruction. -/
theorem moebius_primeBand_product
    (P : Finset ℕ) (k : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcard : P.card = k) :
    ArithmeticFunction.moebius (∏ p ∈ P, p) = (-1 : ℤ) ^ k := by
  have hsquarefree := squarefree_primeBand_product P hprime
  have hnonzero : ∏ p ∈ P, p ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun p hp ↦ (hprime p hp).ne_zero
  rw [ArithmeticFunction.moebius_apply_of_squarefree hsquarefree]
  congr 1
  have hdistinct :
      ArithmeticFunction.cardDistinctFactors (∏ p ∈ P, p) = P.card := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors, Nat.primeFactors_prod hprime]
  have hOmega :
      ArithmeticFunction.cardFactors (∏ p ∈ P, p) =
        ArithmeticFunction.cardDistinctFactors (∏ p ∈ P, p) := by
    exact (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree hnonzero).mpr
      hsquarefree |>.symm
  omega

/-- Products of `k` primes from the interval `[y,z]` lie between the exact
endpoint powers. -/
theorem primeBandProducts_scale
    (Q : Finset ℕ) (k y z : ℕ)
    (hband : ∀ p ∈ Q, y ≤ p ∧ p ≤ z) :
    ∀ a ∈ primeBandProducts Q k, y ^ k ≤ a ∧ a ≤ z ^ k := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨P, hP, rfl⟩
  have hPsub : P ⊆ Q := (Finset.mem_powersetCard.mp hP).1
  have hPcard : P.card = k := (Finset.mem_powersetCard.mp hP).2
  constructor
  · simpa [hPcard] using
      (Finset.pow_card_le_prod P id y fun p hp ↦ (hband p (hPsub hp)).1)
  · simpa [hPcard] using
      (Finset.prod_le_pow_card P id z fun p hp ↦ (hband p (hPsub hp)).2)

/-- If a squarefree integer is built from `k` primes at least `y`, and at most
`budget` of those primes remain outside the gcd with a partner, then the gcd
retains a product of at least `k - budget` band primes. -/
theorem primeBand_gcd_lower_bound
    (a b y k budget : ℕ)
    (ha : Squarefree a)
    (hb : 0 < b)
    (hy : 0 < y)
    (hcard : omega a = k)
    (hlarge : ∀ p ∈ a.primeFactors, y ≤ p)
    (hbudget : omega (a / Nat.gcd a b) ≤ budget) :
    y ^ (k - budget) ≤ Nat.gcd a b := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne'
  have hdiff :
      (a.primeFactors \ b.primeFactors).card ≤ budget := by
    simpa [omega, Nat.primeFactors_div_gcd ha hb0] using hbudget
  have hpartition := Finset.card_sdiff_add_card_inter a.primeFactors b.primeFactors
  have hinterCard :
      k - budget ≤ (a.primeFactors ∩ b.primeFactors).card := by
    unfold omega at hcard
    omega
  have hpowCard :
      y ^ (a.primeFactors ∩ b.primeFactors).card ≤
        ∏ p ∈ a.primeFactors ∩ b.primeFactors, p := by
    exact Finset.pow_card_le_prod _ _ _ (fun p hp => hlarge p (Finset.mem_inter.mp hp).1)
  have hpowMono :
      y ^ (k - budget) ≤ y ^ (a.primeFactors ∩ b.primeFactors).card := by
    exact Nat.pow_le_pow_right hy hinterCard
  have hgSquare : Squarefree (Nat.gcd a b) :=
    ha.squarefree_of_dvd (Nat.gcd_dvd_left a b)
  have hprod :
      (∏ p ∈ a.primeFactors ∩ b.primeFactors, p) = Nat.gcd a b := by
    rw [← Nat.primeFactors_gcd ha0 hb0]
    exact Nat.prod_primeFactors_of_squarefree hgSquare
  exact hpowMono.trans (hpowCard.trans_eq hprod)

/-- The retained-prime lower bound contradicts any edge ceiling below it.
This is the finite arithmetic obstruction used in the logarithmic
residual-complexity theorem. -/
theorem no_short_edge_of_primeBand_residual_budget
    (a b y k budget edgeCeiling : ℕ)
    (ha : Squarefree a)
    (hb : 0 < b)
    (hy : 0 < y)
    (hne : a ≠ b)
    (hcard : omega a = k)
    (hlarge : ∀ p ∈ a.primeFactors, y ≤ p)
    (hbudget : omega (a / Nat.gcd a b) ≤ budget)
    (hedge : Nat.dist a b ≤ edgeCeiling)
    (hceiling : edgeCeiling < y ^ (k - budget)) : False := by
  have hgcdLower :=
    primeBand_gcd_lower_bound a b y k budget ha hb hy hcard hlarge hbudget
  have hgcdGap : Nat.gcd a b ≤ Nat.dist a b := by
    apply Nat.le_of_dvd (Nat.dist_pos_of_ne hne)
    rcases le_total a b with hab | hba
    · rw [Nat.dist_eq_sub_of_le hab]
      exact (Nat.dvd_sub_iff_left hab (Nat.gcd_dvd_left a b)).2
        (Nat.gcd_dvd_right a b)
    · rw [Nat.dist_eq_sub_of_le_right hba]
      exact (Nat.dvd_sub_iff_left hba (Nat.gcd_dvd_right a b)).2
        (Nat.gcd_dvd_left a b)
  omega

/-- A product of distinct primes from one band cannot have a distinct partner
whose residual cofactor uses at most `budget` primes and whose edge is shorter
than the retained-prime product. This is the exact finite obstruction applied
to the large fixed-sign product family in the manuscript. -/
theorem no_short_edge_from_primeBand_product
    (P : Finset ℕ) (b y budget edgeCeiling : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p)
    (hband : ∀ p ∈ P, y ≤ p)
    (hb : 0 < b)
    (hy : 0 < y)
    (hne : ∏ p ∈ P, p ≠ b)
    (hbudget : omega ((∏ p ∈ P, p) / Nat.gcd (∏ p ∈ P, p) b) ≤ budget)
    (hedge : Nat.dist (∏ p ∈ P, p) b ≤ edgeCeiling)
    (hceiling : edgeCeiling < y ^ (P.card - budget)) : False := by
  have hsquarefree := squarefree_primeBand_product P hprime
  have hprimeFactors : (∏ p ∈ P, p).primeFactors = P :=
    Nat.primeFactors_prod hprime
  apply no_short_edge_of_primeBand_residual_budget
    (∏ p ∈ P, p) b y P.card budget edgeCeiling hsquarefree hb hy hne
  · simp [omega, hprimeFactors]
  · intro p hp
    exact hband p (by simpa [hprimeFactors] using hp)
  · exact hbudget
  · exact hedge
  · exact hceiling

/-- Every member of the fixed-cardinality prime-band family is forced to be
unmatched whenever the residual budget and edge ceiling violate the retained
prime lower bound. Together with `primeBandProducts_card`, this is the finite
population mechanism in the logarithmic residual-complexity barrier. -/
theorem primeBandProducts_forced_unmatched
    (Q : Finset ℕ) (k y budget edgeCeiling : ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p)
    (hband : ∀ p ∈ Q, y ≤ p)
    (hy : 0 < y)
    (hceiling : edgeCeiling < y ^ (k - budget)) :
    ∀ a ∈ primeBandProducts Q k,
      ¬ ∃ b : ℕ,
        0 < b ∧ a ≠ b ∧
        omega (a / Nat.gcd a b) ≤ budget ∧
        Nat.dist a b ≤ edgeCeiling := by
  intro a ha
  rcases Finset.mem_image.mp ha with ⟨P, hP, rfl⟩
  have hPsub : P ⊆ Q := (Finset.mem_powersetCard.mp hP).1
  have hPcard : P.card = k := (Finset.mem_powersetCard.mp hP).2
  intro hex
  rcases hex with ⟨b, hb, hne, hbudget, hedge⟩
  apply no_short_edge_from_primeBand_product P b y budget edgeCeiling
  · intro p hp
    exact hprime p (hPsub hp)
  · intro p hp
    exact hband p (hPsub hp)
  · exact hb
  · exact hy
  · exact hne
  · exact hbudget
  · exact hedge
  · simpa [hPcard] using hceiling

/-- A partner map satisfying the stated edge conditions is undefined on every
member of the obstructed prime-band family. -/
theorem primeBandProducts_mate_eq_none
    (mate : ℕ → Option ℕ)
    (Q : Finset ℕ) (k y budget edgeCeiling : ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p)
    (hband : ∀ p ∈ Q, y ≤ p)
    (hy : 0 < y)
    (hceiling : edgeCeiling < y ^ (k - budget))
    (hmatched : ∀ a ∈ primeBandProducts Q k, ∀ b,
      mate a = some b →
      0 < b ∧ a ≠ b ∧
      omega (a / Nat.gcd a b) ≤ budget ∧
      Nat.dist a b ≤ edgeCeiling) :
    ∀ a ∈ primeBandProducts Q k, mate a = none := by
  intro a ha
  cases hmate : mate a with
  | none => rfl
  | some b =>
      exfalso
      apply primeBandProducts_forced_unmatched Q k y budget edgeCeiling hprime
        hband hy hceiling a ha
      exact ⟨b, (hmatched a ha b hmate).1, (hmatched a ha b hmate).2.1,
        (hmatched a ha b hmate).2.2.1, (hmatched a ha b hmate).2.2.2⟩

/-- Exact population form of the prime-band obstruction.  The family has
binomial size, occupies a controlled multiplicative scale, has one Möbius
sign, and every member is forced to remain unmatched under a residual budget
whose retained-prime product exceeds the edge ceiling. -/
theorem primeBand_population_obstruction
    (Q : Finset ℕ) (k y z budget edgeCeiling : ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p)
    (hband : ∀ p ∈ Q, y ≤ p ∧ p ≤ z)
    (hy : 0 < y)
    (hceiling : edgeCeiling < y ^ (k - budget)) :
    (primeBandProducts Q k).card = Nat.choose Q.card k ∧
      ∀ a ∈ primeBandProducts Q k,
        y ^ k ≤ a ∧ a ≤ z ^ k ∧
        ArithmeticFunction.moebius a = (-1 : ℤ) ^ k ∧
        ¬ ∃ b : ℕ,
          0 < b ∧ a ≠ b ∧
          omega (a / Nat.gcd a b) ≤ budget ∧
          Nat.dist a b ≤ edgeCeiling := by
  refine ⟨primeBandProducts_card Q k hprime, ?_⟩
  intro a ha
  have hscale := primeBandProducts_scale Q k y z hband a ha
  rcases Finset.mem_image.mp ha with ⟨P, hP, hprod⟩
  have hPsub : P ⊆ Q := (Finset.mem_powersetCard.mp hP).1
  have hPcard : P.card = k := (Finset.mem_powersetCard.mp hP).2
  have hsign : ArithmeticFunction.moebius a = (-1 : ℤ) ^ k := by
    rw [← hprod]
    exact moebius_primeBand_product P k (fun p hp ↦ hprime p (hPsub hp)) hPcard
  exact ⟨hscale.1, hscale.2, hsign,
    primeBandProducts_forced_unmatched Q k y budget edgeCeiling hprime
      (fun p hp ↦ (hband p hp).1) hy hceiling a ha⟩

/-- Squarefree integers through `X` left unmatched by a proposed partner map. -/
def unmatchedSquarefreeThrough (mate : ℕ → Option ℕ) (X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 X).filter fun n ↦ Squarefree n ∧ mate n = none

/-- The prime-band obstruction forces a binomial lower bound on the unmatched
population of any partner map satisfying the residual and edge constraints on
the band family.  This is the finite-scale contradiction used before the
manuscript's prime-counting and logarithmic scale conversion. -/
theorem primeBand_unmatched_lower_bound
    (mate : ℕ → Option ℕ)
    (Q : Finset ℕ) (k y z budget edgeCeiling : ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p)
    (hband : ∀ p ∈ Q, y ≤ p ∧ p ≤ z)
    (hy : 0 < y)
    (hceiling : edgeCeiling < y ^ (k - budget))
    (hmatched : ∀ a ∈ primeBandProducts Q k, ∀ b,
      mate a = some b →
      0 < b ∧ a ≠ b ∧
      omega (a / Nat.gcd a b) ≤ budget ∧
      Nat.dist a b ≤ edgeCeiling) :
    Nat.choose Q.card k ≤ (unmatchedSquarefreeThrough mate (z ^ k)).card := by
  rw [← primeBandProducts_card Q k hprime]
  apply Finset.card_le_card
  intro a ha
  have hscale := primeBandProducts_scale Q k y z hband a ha
  rcases Finset.mem_image.mp ha with ⟨P, hP, hprod⟩
  have hPsub : P ⊆ Q := (Finset.mem_powersetCard.mp hP).1
  have hsquarefree : Squarefree a := by
    rw [← hprod]
    exact squarefree_primeBand_product P (fun p hp ↦ hprime p (hPsub hp))
  have haPos : 0 < a := Nat.pos_of_ne_zero hsquarefree.ne_zero
  have hnone : mate a = none :=
    primeBandProducts_mate_eq_none mate Q k y budget edgeCeiling hprime
      (fun p hp ↦ (hband p hp).1) hy hceiling hmatched a ha
  simp only [unmatchedSquarefreeThrough, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨haPos, hscale.2⟩, hsquarefree, hnone⟩

end RiemannHypothesisProofFactory.MobiusResidualComplexity
