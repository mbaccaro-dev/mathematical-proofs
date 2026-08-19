# Selberg Feedback and Approximate Divisor Data Do Not Stably Determine Square-Root Prime Error

Mayk Loide Baccaro, 2026.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22005767.svg)](https://doi.org/10.5281/zenodo.22005767)

The paper constructs positive weights on the actual prime powers, constant on
each prime-power chain, whose divisor residuals are uniformly small while
their summatory outputs separate at nearly linear scale. The same weights
retain Selberg's classical `O(x)` remainder and controlled generalized von
Mangoldt recursions. The result is a conditioning obstruction for recovery
from approximate arithmetic summaries. It does not estimate the actual
prime-counting error or prove or disprove the Riemann hypothesis.

## Contents

- [`Manuscript/paper.tex`](Manuscript/paper.tex) - LaTeX source.
- [`Manuscript/references.bib`](Manuscript/references.bib) - bibliography.
- [`Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf`](Manuscript/selberg_feedback_approximate_divisor_data_baccaro_20260818.pdf) - typeset paper.
- [`Lean`](Lean/) - pinned Lean 4 formal-assurance project.
- [`Lean/LEAN_GREEN_CERTIFICATE.md`](Lean/LEAN_GREEN_CERTIFICATE.md) - exact local verification record.

## Verification

GitHub Actions rebuilds the pinned Lean project and checks the public axiom
report on every push and pull request. The certificate states the exact scope:
Lean verifies the finite algebraic conditioning kernel listed there, while the
paper's analytic number theory remains a manuscript-level proof obligation.

## Cite the paper

Mayk Loide Baccaro, “Selberg Feedback and Approximate Divisor Data Do Not Stably
Determine Square-Root Prime Error,” Zenodo, 2026.
[doi:10.5281/zenodo.22005767](https://doi.org/10.5281/zenodo.22005767).

```bibtex
@misc{baccaro2026selbergfeedback,
  author    = {Baccaro, Mayk Loide},
  title     = {Selberg Feedback and Approximate Divisor Data Do Not Stably Determine Square-Root Prime Error},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.22005767},
  url       = {https://doi.org/10.5281/zenodo.22005767}
}
```

The DOI identifies the paper. The repository supplies its source and formal
assurance; it does not broaden the theorem stated in the manuscript.
