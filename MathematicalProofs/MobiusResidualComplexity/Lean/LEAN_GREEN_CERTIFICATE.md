# Lean verification certificate

Status: **PASS**

Verification date: 2026-08-21

## Pinned environment

- Lean 4.33.0
- Lake 5.0.0
- Mathlib 4.33.0 at commit `db584cd6d46c92f209a44c0f1c829460d327499d`

## Checks

From the `Lean` directory:

```text
lake build --wfail
lake env lean Challenge.lean
lake env lean Solution.lean
lake env lean RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
```

The pinned project build and the direct challenge, solution, and certificate
checks completed successfully. The four `sorry` declarations are the intended
theorem holes in `Challenge.lean`; the solution and implementation contain
none.

The certificate prints four axiom reports. Each contains only the standard
Lean/Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`. A source
scan excluding `Challenge.lean` found no `sorry`, `admit`, `unsafe`, explicit
`axiom`, `partial`, `sorryAx`, `Lean.ofReduceBool`, `set_option`, or
`decreasing_by` use.

## Independent statement checks

The comparator configuration selects the exact four-theorem Challenge/Solution
surface. A local replay passed Comparator at commit
`68a064109f01c08f47c8edc9f51d6a2bbffaa188`, Lean4export at commit
`15f6055e299ad5b89345e533cc2192f4cc00f659`, the Lean default kernel, and
NanoDa at commit `68d5ca9db226849b41a6fff59d796ff19d0a8840`. The local replay ran
without Linux Landrun isolation. The repository workflow is configured to run
the same pinned checks under Landrun isolation for its committed SHA.

## Verified scope

Lean proves the finite residual-budget barrier and its all-large-scale form for
the fixed prime band `(y, 8y]`. Under the stated reciprocal global-matching,
residual, parity, endpoint, and gap hypotheses, either the permitted edge
ceiling reaches the retained-prime product or every member of the explicit
squarefree prime-product family is individually unmatched. Chebyshev estimates
and unique factorization give the exact binomial population and an explicit
factorial lower bound. Lean also proves the exact logarithmic conversion for
the product scale and transports a normalized logarithmic residual budget into
a strict rank bound.

The final comparison showing that this sparse binomial population eventually
exceeds an arbitrary `O(X^beta)` unmatched-set allowance remains a manuscript
proof. Consequently, the full asymptotic limsup contradiction is not included
in the formal claim.

## Exact artifact hashes

SHA-256:

```text
03e8c25d8e3d6153ae6f409587101c9109eac5be903b4fb2db46e99cf1018236  Manuscript/mobius_residual_complexity_baccaro_20260818.pdf
946c9429272d6d27886d2e8fe0c686468f0ed70679ee8854023cd80973005b57  Manuscript/paper.tex
549f9ccab57d9a7ad304e975ad802f9424921e1387b4f88a599fd8db326b1026  Manuscript/references.bib
57a25208918a32866cab3f80a9c51b215c7ba9e2524b2391d6056338f3947d53  Lean/lake-manifest.json
302cd63c54178885b89e669f33b38f12f4dd7ae7e5cac537b3203e3768d8fb2b  Lean/lean-toolchain
5fc3e18ac5ca1890066e00c7456e75e89bd424c0b6cd75a61faa5ca13153ca2d  Lean/lakefile.toml
94dc9ceae7a1109c92515edeb9a447f4c24529806d9a495c17b9a03853eb2a14  Lean/Challenge.lean
2cfc75f7c00412111e67221704f71623523592a623751b27e35c6993d4eb131e  Lean/RiemannHypothesisProofFactory.lean
6ec7d7ee7ff2eefd6315f1a78fa6d8d7b3091ab3665db9c69f33901f96131aca  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity.lean
0cc02375dd76e63f17eafd841d94ea39a736c292b53643e5d0f587a148dcc0ff  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/CombinatorialKernel.lean
164214a01546aa76a57e4199a196f4d556c1485cfa717bbd69cf90a3d972f4c6  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/ExactCompression.lean
ecabdde84a71a124b40e476f691e051652d558ca5d947c88458e00ace97adbdc  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/GlobalMatchingObstruction.lean
3f696d5cfb9b7b4c95362cf93af8e5cd8b3f7c63f9a3a91388e2887aab1d269d  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PairCompression.lean
b3d447ef9550f188b97f8789d981f7a80d3fd54a3727a2155f6ed4c589371fdf  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PaperCertificate.lean
f38d8a36397ba7a3087962f606105369bbbcd42534a90bb27b931b987aeaba4f  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PrimeBandAsymptotics.lean
015df4962775db09d48a46dd563dd2c11f579fcfd3729e9fb11e5f2015c7bbe8  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PrimeBandGrowth.lean
e9140a0945b87d817b5037e85d92cf13e2b541ac778ed418955b36fa16c7aaa2  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/PrimeBandObstruction.lean
d17b0ec9450361724889bef5f90e523a370ccc7503b01e99dc72b3b19b2040c9  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/ResearchBarrierCertificate.lean
cfd635746736420acd5a59da457d080974b3d254d3ccd2d25c72381eb3333c08  Lean/RiemannHypothesisProofFactory/MobiusResidualComplexity/ThresholdAsymptotics.lean
edc1c6c305d3d0532ee0af714e8fd56b8387438ea43fa800ff272fe226cbf5be  Lean/Solution.lean
f23df60652e2558e87b13e2efa7c413e5cbfdf8acbe016860897037e9a8b7258  Lean/comparator.json
3fefc6f6b886ef1d3ad3e9b83543ab80b040d6fead719adf59e66d74f337f78a  Lean/formalization.yaml
```
