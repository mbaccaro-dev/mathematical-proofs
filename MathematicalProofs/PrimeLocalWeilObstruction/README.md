# An Obstruction to Prime-Local First-Difference Decompositions of Weil's Quadratic Form

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22005240.svg)](https://doi.org/10.5281/zenodo.22005240)

The paper isolates a natural prime-local positive-block construction inside
Weil's quadratic form. It proves that each block is nonnegative exactly when
its scalar completion pays at least twice the corresponding Weil weight, and
that the actual prime-power weights make the total required budget diverge. The
lower bound is imposed at every natural-number index; away from prime powers,
where the Weil weight vanishes, it requires the scalar completion to remain
nonnegative. Thus the specified ordinary, uncoupled, fixed-scalar assembly
cannot work.
The result does not prove or disprove the Riemann hypothesis and does not
exclude cross-prime, nonlocal, operator-valued, test-dependent, or separately
renormalized constructions.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex): LaTeX source.
- [`Manuscript/references.bib`](Manuscript/references.bib): bibliography.
- [`Manuscript/prime_local_weil_obstruction_baccaro_20260818.pdf`](Manuscript/prime_local_weil_obstruction_baccaro_20260818.pdf): typeset paper.
- [`Lean`](Lean/): pinned Lean 4 formal-assurance project.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md): exact local verification record.

## Verification

GitHub Actions rebuilds the pinned Lean project and checks the public axiom
report on every push and pull request. The certificate states the exact scope:
Lean verifies the formal kernel listed there, while the remaining analytic
bridges are proved in the manuscript.

## Cite the paper

Mayk Loide Baccaro, “An Obstruction to Prime-Local First-Difference
Decompositions of Weil's Quadratic Form,” Zenodo, 2026.
[doi:10.5281/zenodo.22005240](https://doi.org/10.5281/zenodo.22005240).

```bibtex
@misc{baccaro2026primelocalweil,
  author    = {Baccaro, Mayk Loide},
  title     = {An Obstruction to Prime-Local First-Difference Decompositions of Weil's Quadratic Form},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22005240},
  url       = {https://doi.org/10.5281/zenodo.22005240}
}
```

The DOI identifies the paper. The repository supplies its source and formal
assurance; it does not broaden the theorem stated in the manuscript.
