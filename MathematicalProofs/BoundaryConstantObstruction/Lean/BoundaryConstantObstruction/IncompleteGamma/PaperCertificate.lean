import BoundaryConstantObstruction.IncompleteGamma.ClassicalXiConvergence
import BoundaryConstantObstruction.IncompleteGamma.DiskMaximumGrowth
import BoundaryConstantObstruction.IncompleteGamma.LocalZeroMotion
import BoundaryConstantObstruction.IncompleteGamma.PaperTheorem

/-!
# Paper-wide mathematical certificate

This module is the single Lean entry point for the standalone incomplete-gamma
approximant paper.  It imports the exact finite definitions, theta boundary
identity, entire/cosine analysis, nonconstancy witness, quantitative disk
growth estimate, reflection-factorization contradiction, upper-incomplete-
gamma endpoint, simple-zero local motion, and local-uniform convergence to the
classical completed Xi.

The printed declarations below make the trusted-kernel boundary explicit.
Literature attribution, novelty, prose, and publication decisions are not
mathematical kernel claims.
-/

#print axioms IncompleteGammaApproximant.classicalXiCompletion_eq_printed_formula
#print axioms IncompleteGammaApproximant.XiIncompleteGamma_tendstoLocallyUniformly
#print axioms IncompleteGammaApproximant.boundaryConstant_mem_Ioo
#print axioms IncompleteGammaApproximant.F_I_div_two_sub_tail
#print axioms IncompleteGammaApproximant.F_differentiable
#print axioms IncompleteGammaApproximant.F_tendsto_atTop
#print axioms IncompleteGammaApproximant.F_tendsto_atBot
#print axioms IncompleteGammaApproximant.log_diskMaxNorm_F_isBigO
#print axioms IncompleteGammaApproximant.F_zero_symmetry_orbit
#print axioms IncompleteGammaApproximant.exists_local_zero_motion
#print axioms IncompleteGammaApproximant.theorem_A
#print axioms IncompleteGammaApproximant.exists_nonreal_zero_XiIncompleteGamma
