import RiemannHypothesisProofFactory.MobiusResidualComplexity.PairCompression

/-!
# Möbius residual-complexity paper certificate

The imported modules check the exact fixed-budget compression of a finite
zero-sum squarefree cell into increasing-rank opposite-sign pairs. The formal
result includes the pairwise-gcd residual budgets, the cell-diameter bound, and
the exact crossing count at every real cutoff. The asymptotic lower bound and
the global sparse-jump argument remain manuscript-level proofs.
-/

#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.squarefree_cell_mass_eq_card_sub_card
#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.zero_mass_squarefree_cell_balanced
#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.common_core_residual_budget
#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.exact_rank_pair_crossing_balance
#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.exact_fixed_budget_pair_compression
#print axioms RiemannHypothesisProofFactory.MobiusResidualComplexity.exact_cell_gcd_pair_compression
