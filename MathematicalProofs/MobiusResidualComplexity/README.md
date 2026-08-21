# Logarithmic Residual-Complexity Barriers for Local Möbius Cancellation

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22006119.svg)](https://doi.org/10.5281/zenodo.22006119)

The paper proves a necessary complexity bound for a class of local
Möbius-cancellation certificates. Short opposite-sign pairings with few
unmatched squarefree integers require a residual prime-factor budget that
grows at least logarithmically along a subsequence. At square-root scale, the
normalized lower bound is `1/4`. The paper also proves that finite,
vertex-disjoint, unit-weight zero-sum cells with a common gcd compress to
opposite-sign pairs, with an explicit correction when the budget changes at
sparse endpoints.

The result supplies no matching, no estimate for the Mertens function, and no
proof or disproof of the Riemann hypothesis.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex) - LaTeX source.
- [`Manuscript/references.bib`](Manuscript/references.bib) - bibliography.
- [`Manuscript/mobius_residual_complexity_baccaro_20260818.pdf`](Manuscript/mobius_residual_complexity_baccaro_20260818.pdf) - typeset paper.
- [`Lean`](Lean/) - pinned Lean 4 formal-assurance project.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md) - exact
  formal scope, commands, results, and artifact hashes.

## Verification

The GitHub release metadata records DOI
[10.5281/zenodo.22006119](https://doi.org/10.5281/zenodo.22006119). The
manuscript intentionally omits repository-deposit metadata. The Lean project
proves the exact finite fixed-budget pair-compression theorem using the gcd of
the cell, including sign pairing, pairwise-gcd budget preservation,
cell-diameter control, and the exact cutoff-crossing pairs. The analytic number theory, asymptotic counting, and
global sparse-jump argument remain manuscript-level proof obligations. GitHub
Actions repeats the pinned Lean build and public-certificate check.

## Cite the paper

Mayk Loide Baccaro, *Logarithmic Residual-Complexity Barriers for Local
Möbius Cancellation*, 2026. DOI:
[10.5281/zenodo.22006119](https://doi.org/10.5281/zenodo.22006119).

```bibtex
@article{baccaro2026mobiusresidual,
  author = {Baccaro, Mayk Loide},
  title = {Logarithmic Residual-Complexity Barriers for Local M{\"o}bius Cancellation},
  year = {2026},
  doi = {10.5281/zenodo.22006119},
  url = {https://doi.org/10.5281/zenodo.22006119}
}
```
