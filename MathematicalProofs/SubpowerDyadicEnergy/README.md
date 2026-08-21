# Subpower Energy and Dyadic Defect Criteria for the Riemann Hypothesis

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22038521.svg)](https://doi.org/10.5281/zenodo.22038521)

The paper gives equivalent formulations of the Riemann hypothesis using
weighted square energy of the prefixes of `-mu(n) log n`, Mellin transforms,
and exact dyadic-defect identities. It also proves conditional consequences of
an eventual dyadic sign hypothesis. The paper does not prove that hypothesis
and does not prove the Riemann hypothesis.

## Formal result in plain words

The Lean project checks four discrete steps from the paper:

- expanding the square of a weighted prefix sum gives the paper's exact
  dyadic identity, including both possible right endpoints;
- if the stated two-endpoint defect condition holds, one large prefix is
  bounded by the prefix at half its length plus the energy in the intervening
  block;
- the same estimate can be iterated along repeated halvings; and
- this iteration gives an explicit cubic logarithmic bound for the normalized
  prefix energy.

The two-endpoint condition is an assumption of the formal result. The Lean
project does not prove it.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex) - LaTeX source.
- [`Manuscript/subpower_dyadic_mobius_mangoldt_equivalence_baccaro_20260820.pdf`](Manuscript/subpower_dyadic_mobius_mangoldt_equivalence_baccaro_20260820.pdf) - typeset paper.
- [`Lean`](Lean/) - pinned Lean 4 verification project for the discrete theorem core.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md) - exact local verification record.

## Verification

The Lean project checks the exact dyadic prefix-square identity, the sharp
one-step recurrence, its binary form, and the explicit cubic prefix-energy
bound under the paper's universal two-endpoint condition. The analytic
equivalence with the Riemann hypothesis, Mellin-Plancherel argument,
continuation of reciprocal zeta, zero-simplicity argument, and residue budget
remain manuscript-level proofs.

## Cite the paper

Mayk Loide Baccaro, *Subpower Energy and Dyadic Defect Criteria for the
Riemann Hypothesis*, 2026. DOI:
[10.5281/zenodo.22038521](https://doi.org/10.5281/zenodo.22038521).

```bibtex
@article{baccaro2026subpowerenergy,
  author = {Baccaro, Mayk Loide},
  title = {Subpower Energy and Dyadic Defect Criteria for the Riemann Hypothesis},
  year = {2026},
  doi = {10.5281/zenodo.22038521},
  url = {https://doi.org/10.5281/zenodo.22038521}
}
```
