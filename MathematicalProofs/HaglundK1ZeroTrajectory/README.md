# Haglund's Zero-Trajectory Conjecture for the First Riemann Xi Approximant

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22059236.svg)](https://doi.org/10.5281/zenodo.22059236)

The paper proves the first case of Haglund's zero-trajectory conjecture. For
the interpolation between the first two incomplete-gamma approximants, every
nonreal zero is simple and moves strictly toward the real axis. Its branch
cannot escape forward, and after any finite-multiplicity real collision the
complete local multiset stays real on the forward side. The proof combines
exact analytic identities with a reproducible interval-arithmetic certificate.
The cases with index at least two remain open, and no result about Xi zeros or
the Riemann hypothesis is claimed.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex): LaTeX source.
- [`Manuscript/references.bib`](Manuscript/references.bib): bibliography.
- [`Manuscript/hc4_k1_zero_trajectory_theorem_baccaro_20260822.pdf`](Manuscript/hc4_k1_zero_trajectory_theorem_baccaro_20260822.pdf): typeset paper.
- [`Lean`](Lean/): pinned Lean 4 formal-assurance project.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md): exact local verification record.

## Verification

The selected Lean theorem covers the literal incomplete-gamma pencil and the
nonreal analytic consequence of the paper's first-quadrant certificate. It
proves every certified zero simple and gives it a locally unique analytic descending branch,
proves real strict positivity on the imaginary axis, and gives strict descent
with an explicit no-escape radius for certified forward branches. The interval
atlas and the full Weierstrass--Puiseux multiset construction remain verified
outside Lean as described in the paper. GitHub Actions replays the pinned
Comparator, Lean kernel, and NanoDa checks for the formalized scope.

## Cite the paper

Mayk Loide Baccaro, “Haglund's Zero-Trajectory Conjecture for the First
Riemann Xi Approximant,” Zenodo, 2026.
[doi:10.5281/zenodo.22059236](https://doi.org/10.5281/zenodo.22059236).

```bibtex
@misc{baccaro2026haglundk1,
  author    = {Baccaro, Mayk Loide},
  title     = {Haglund's Zero-Trajectory Conjecture for the First Riemann Xi Approximant},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22059236},
  url       = {https://doi.org/10.5281/zenodo.22059236}
}
```

The DOI identifies the paper. The repository supplies its source, certificate
interface, and formal assurance without enlarging the theorem.
