import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import RiemannHypothesisProofFactory.MobiusResidualComplexity.ExactCompression

namespace RiemannHypothesisProofFactory.MobiusResidualComplexity

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

def positiveVertices (H : Finset ℕ) : Finset ℕ :=
  H.filter fun n => μ n = 1

def negativeVertices (H : Finset ℕ) : Finset ℕ :=
  H.filter fun n => μ n = -1

def cellMass (H : Finset ℕ) : ℤ :=
  ∑ n ∈ H, μ n

def cellGCD (H : Finset ℕ) : ℕ := H.gcd id

/-- A zero-sum squarefree cell whose genuine gcd leaves a fixed residual
prime-factor budget admits an exact increasing-rank compression into
opposite-sign pairs. Each pair preserves the residual budget, stays within
the cell diameter, and crosses a real cutoff exactly when its rank belongs to
the counted crossing set. -/
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
  sorry

end RiemannHypothesisProofFactory.MobiusResidualComplexity
