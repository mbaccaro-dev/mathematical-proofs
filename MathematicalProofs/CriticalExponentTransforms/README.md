# Scale-Covariant Transforms Preserve Critical-Exponent Gaps

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22005931.svg)](https://doi.org/10.5281/zenodo.22005931)

The paper gives exact exponent-gap laws for five admitted classes of
scale-covariant transforms: finite multilinear observables, nonlinear phase
orbits, positive homogeneous maps, bounded Mellin dilations, and stable
pointwise normalizations. It also records annihilation and conditioning
boundaries. The theorem package concerns fixed transform classes. Actual
prime-counting estimates and conclusions about the Riemann hypothesis remain
outside its scope.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex) - LaTeX source.
- [`Manuscript/references.bib`](Manuscript/references.bib) - bibliography.
- [`Manuscript/critical_exponent_scale_transforms_baccaro_20260818.pdf`](Manuscript/critical_exponent_scale_transforms_baccaro_20260818.pdf) - typeset paper.
- [`Lean`](Lean/) - pinned Lean 4 formal-assurance project.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md) - exact local verification record.

## Verification

GitHub Actions rebuilds the pinned Lean project and checks the public axiom
report on every push and pull request. The certificate states the exact scope:
Lean verifies the algebraic kernel listed there, while the paper's analytic and
vector-valued results remain manuscript-level proof obligations.

## Cite the paper

Mayk Loide Baccaro, “Scale-Covariant Transforms Preserve Critical-Exponent
Gaps,” Zenodo, 2026.
[doi:10.5281/zenodo.22005931](https://doi.org/10.5281/zenodo.22005931).

```bibtex
@misc{baccaro2026criticalexponent,
  author    = {Baccaro, Mayk Loide},
  title     = {Scale-Covariant Transforms Preserve Critical-Exponent Gaps},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22005931},
  url       = {https://doi.org/10.5281/zenodo.22005931}
}
```

The DOI identifies the paper. The repository supplies its source and formal
assurance without broadening the theorem stated in the manuscript.
