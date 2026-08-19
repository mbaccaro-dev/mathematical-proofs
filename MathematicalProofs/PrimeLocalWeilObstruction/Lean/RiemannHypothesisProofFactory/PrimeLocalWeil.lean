import RiemannHypothesisProofFactory.PrimeLocalWeil.ArithmeticBudget
import RiemannHypothesisProofFactory.PrimeLocalWeil.BudgetObstruction
import RiemannHypothesisProofFactory.PrimeLocalWeil.Controls
import RiemannHypothesisProofFactory.PrimeLocalWeil.LocalThreshold
import RiemannHypothesisProofFactory.PrimeLocalWeil.PrimePowerBridge

/-!
# Prime-local Weil obstruction formal-assurance surface

This aggregate exposes the proved Lean portion of the standalone paper.  The
formal scope is deliberately narrower than the complete manuscript: it covers
the exact prime-power arithmetic divergence and indexing, the abstract local
threshold, the scalar-budget implication, and the two adjacent-regime
controls.  The concrete `C_c^∞` dilation construction, compact-support tail
argument, and explicit-formula normalization remain mathematical proofs in
the manuscript and are not claimed as kernel-checked here.
-/
