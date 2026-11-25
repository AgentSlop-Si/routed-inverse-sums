# Paper 5: Independently Routed Inverse Sums and Common-Rectangle Obstructions for Flat Unitary and Fourier Matrices

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript.
- `references.bib` — Clean BibTeX bibliography.
- `verify_routed_inverse_sums.py` — Standalone Python 3 (stdlib only) verifier checking all 16,124 column-two matrices over $\mathbb{F}_2$ ($N\le 4$) and $\mathbb{F}_3$ ($N\le 3$) (6,417 invertible instances, 68,685 nonempty inverse-row restrictions, 2,418 instances with row degree $>2$), 876 swapped-complement nullity identities, 192,524 balanced two-color red/blue count pairs ($u\le 100$), 5,400 strict cutoff legality tests (including $N\le 3697$), consecutive-row Vandermonde minors at composite orders, and the $N=4$ over $\mathbb{F}_5$ non-consecutive singular minor control.
- `RoutedInverseSums.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry` and pure kernel reduction) symbolically proving ordered strict separation, the exact two-color $1/3$-retention inequality and sharpness, sparse-elimination survival, the exact cutoff expansion, non-circular recurrence legality, strict contradiction $(N-c)^2 > NB$, and the exact-field cell-pigeonhole bound; plus pure-kernel finite verifications over $\mathbb{F}_2, \mathbb{F}_3, \mathbb{F}_5$.

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.CO` (Combinatorics) / `cs.CC` (Computational Complexity)
- **MSC 2020:** Primary `15A03`, `15A09`; Secondary `05C50`, `15B10`, `68Q17`
- **Target journals (zero-fee):** *Linear Algebra and its Applications*, *Discrete Mathematics*.

## Verify Computations and Lean Proofs
```bash
python3 verify_routed_inverse_sums.py
lean RoutedInverseSums.lean
```
