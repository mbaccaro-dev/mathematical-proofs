import RiemannHypothesisProofFactory.MobiusResidualComplexity.PrimeBandObstruction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Choose.Bounds

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open scoped Nat.Prime
open Real

/-- The primes in the fixed multiplicative band `(y, A * y]`. -/
def widePrimeBand (A y : ℕ) : Finset ℕ :=
  Nat.primesLE (A * y) \ Nat.primesLE y

theorem mem_widePrimeBand {A y p : ℕ} :
    p ∈ widePrimeBand A y ↔ y < p ∧ p ≤ A * y ∧ Nat.Prime p := by
  simp only [widePrimeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpAy, hpPrime⟩, hpNotY⟩
    exact ⟨lt_of_not_ge (fun hpy ↦ hpNotY ⟨hpy, hpPrime⟩), hpAy, hpPrime⟩
  · rintro ⟨hyp, hpAy, hpPrime⟩
    exact ⟨⟨hpAy, hpPrime⟩, fun hpY ↦ (not_le_of_gt hyp) hpY.1⟩

theorem prime_of_mem_widePrimeBand {A y p : ℕ} (hp : p ∈ widePrimeBand A y) :
    Nat.Prime p :=
  (mem_widePrimeBand.mp hp).2.2

theorem widePrimeBand_bounds {A y p : ℕ} (hp : p ∈ widePrimeBand A y) :
    y ≤ p ∧ p ≤ A * y := by
  exact ⟨(mem_widePrimeBand.mp hp).1.le, (mem_widePrimeBand.mp hp).2.1⟩

/-- Exact count of primes in `(y, A * y]`. -/
theorem widePrimeBand_card (A y : ℕ) (hA : 1 ≤ A) :
    (widePrimeBand A y).card = Nat.primeCounting (A * y) - Nat.primeCounting y := by
  have hyAy : y ≤ A * y := by
    simpa only [one_mul] using Nat.mul_le_mul_right y hA
  rw [widePrimeBand, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Nat.primesLE_mono hyAy)]
  simp only [Nat.primesLE_card_eq_primeCounting]

/-- The explicit Chebyshev lower bound for the number of primes in
`(y, A * y]`.  Taking a fixed `A > 4` leaves a positive leading coefficient;
unlike a dyadic band, this requires no prime number theorem. -/
theorem chebyshev_lower_bound_widePrimeBand
    (A y : ℕ) (hA : 1 ≤ A) (hy : 1 < y) :
    (((A * y : ℕ) : ℝ) * log 2 - log (((A * y : ℕ) : ℝ) + 1)) /
          log ((A * y : ℕ) : ℝ) -
        (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ))
      ≤ ((widePrimeBand A y).card : ℝ) := by
  have hAy : 1 < A * y := by
    exact lt_of_lt_of_le hy (by
      simpa only [one_mul] using Nat.mul_le_mul_right y hA)
  have hlower := Chebyshev.pi_ge (A * y)
  have hupper := Chebyshev.pi_le_log4_mul_div (x := (y : ℝ)) (by exact_mod_cast hy)
  have hcard := widePrimeBand_card A y hA
  have hcount :
      ((widePrimeBand A y).card : ℝ) =
        (Nat.primeCounting (A * y) : ℝ) - (Nat.primeCounting y : ℝ) := by
    rw [hcard]
    rw [Nat.cast_sub (Nat.monotone_primeCounting (by
      simpa only [one_mul] using Nat.mul_le_mul_right y hA))]
  rw [hcount]
  norm_num at hupper
  exact sub_le_sub hlower hupper

/-- A numerical consequence of the Chebyshev band bound: whenever its explicit
lower expression reaches `k`, the band actually contains at least `k` primes. -/
theorem widePrimeBand_has_at_least
    (A y k : ℕ) (hA : 1 ≤ A) (hy : 1 < y)
    (hk : (k : ℝ) ≤
      (((A * y : ℕ) : ℝ) * log 2 - log (((A * y : ℕ) : ℝ) + 1)) /
          log ((A * y : ℕ) : ℝ) -
        (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ))) :
    k ≤ (widePrimeBand A y).card := by
  have hreal : (k : ℝ) ≤ ((widePrimeBand A y).card : ℝ) :=
    hk.trans (chebyshev_lower_bound_widePrimeBand A y hA hy)
  exact_mod_cast hreal

/-- The fixed wide band supplies the prime-product population without assuming
its cardinality.  Chebyshev gives enough primes, unique factorization gives the
exact binomial population, and the standard factorial bound gives an explicit
lower bound for that population. -/
theorem chebyshev_widePrimeBand_product_population
    (A y k : ℕ) (hA : 1 ≤ A) (hy : 1 < y)
    (hk : (k : ℝ) ≤
      (((A * y : ℕ) : ℝ) * log 2 - log (((A * y : ℕ) : ℝ) + 1)) /
          log ((A * y : ℕ) : ℝ) -
        (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ))) :
    k ≤ (widePrimeBand A y).card ∧
      (primeBandProducts (widePrimeBand A y) k).card =
        Nat.choose (widePrimeBand A y).card k ∧
      ((((widePrimeBand A y).card + 1 - k : ℕ) : ℝ) ^ k /
          (k.factorial : ℝ))
        ≤ (primeBandProducts (widePrimeBand A y) k).card := by
  have hprime : ∀ p ∈ widePrimeBand A y, Nat.Prime p :=
    fun _ hp ↦ prime_of_mem_widePrimeBand hp
  have hcard := primeBandProducts_card (widePrimeBand A y) k hprime
  refine ⟨widePrimeBand_has_at_least A y k hA hy hk, hcard, ?_⟩
  rw [hcard]
  exact Nat.pow_le_choose k (widePrimeBand A y).card

/-- Chebyshev's wide-band supply, the exact prime-subset count, and the finite
residual obstruction combine into an unconditional population lower bound for
the unmatched vertices of any proposed partner map satisfying the local edge
conditions.  The only numerical hypotheses are the explicit Chebyshev test and
the retained-prime separation inequality. -/
theorem chebyshev_widePrimeBand_unmatched_population
    (mate : ℕ → Option ℕ)
    (A y k budget edgeCeiling : ℕ)
    (hA : 1 ≤ A) (hy : 1 < y)
    (hk : (k : ℝ) ≤
      (((A * y : ℕ) : ℝ) * log 2 - log (((A * y : ℕ) : ℝ) + 1)) /
          log ((A * y : ℕ) : ℝ) -
        (log 4 * (y : ℝ) / log √(y : ℝ) + √(y : ℝ)))
    (hceiling : edgeCeiling < y ^ (k - budget))
    (hmatched : ∀ a ∈ primeBandProducts (widePrimeBand A y) k, ∀ b,
      mate a = some b →
      0 < b ∧ a ≠ b ∧
      omega (a / Nat.gcd a b) ≤ budget ∧
      Nat.dist a b ≤ edgeCeiling) :
    k ≤ (widePrimeBand A y).card ∧
      Nat.choose (widePrimeBand A y).card k ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card ∧
      ((((widePrimeBand A y).card + 1 - k : ℕ) : ℝ) ^ k /
          (k.factorial : ℝ)) ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card := by
  have hprime : ∀ p ∈ widePrimeBand A y, Nat.Prime p :=
    fun _ hp ↦ prime_of_mem_widePrimeBand hp
  have hband : ∀ p ∈ widePrimeBand A y, y ≤ p ∧ p ≤ A * y :=
    fun _ hp ↦ widePrimeBand_bounds hp
  have hchoose :
      Nat.choose (widePrimeBand A y).card k ≤
        (unmatchedSquarefreeThrough mate ((A * y) ^ k)).card :=
    primeBand_unmatched_lower_bound mate (widePrimeBand A y) k y (A * y)
      budget edgeCeiling hprime hband (by omega) hceiling hmatched
  refine ⟨widePrimeBand_has_at_least A y k hA hy hk, hchoose, ?_⟩
  exact (Nat.pow_le_choose k (widePrimeBand A y).card).trans
    (by exact_mod_cast hchoose)

end RiemannHypothesisProofFactory.MobiusResidualComplexity
