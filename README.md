# Waring's problem and the Waring–Siegel problem

Two preprints by Morley Davidson on representations of large integers by sums of powers.

| Manuscript | PDF | LaTeX |
| --- | --- | --- |
| Linear bounds and restricted moments in Waring’s problem | [Read](manuscript/waring_classical_preprint.pdf) | [Source](manuscript/waring_classical_preprint.tex) |
| Efficient differencing and linear bounds in the Waring–Siegel problem | [Read](manuscript/waring-siegel_preprint.pdf) | [Source](manuscript/waring-siegel_preprint.tex) |

The classical paper gives $G(k)<6.873k$, with $G(8)\le 38$ and $G(9)\le 44$. Its final section treats the positive density problem for three positive cubes and identifies the hypotheses behind its conditional estimates.

The number-field paper develops efficient differencing for arbitrary class number and treats seven cubes and the local densities for three and four cubes. For $k\ge3$ its linear estimate is $G_{\mathbb K}(k)\le \max\{H_{\mathbb K}(k),\lfloor6.873k\rfloor\}$, where $H_{\mathbb K}(k)$ is the maximum primitive local width. The paper determines cases where this local term dominates and gives a distinct uniform linear bound for consecutive exponents.

## Reproducing the calculations

- The [classical numerical certificates](supplements/classical/README.md) verify the finite inequalities and limiting coefficients with rational arithmetic.
- The [small-powers supplement](supplements/number-field/small-powers/waring-siegel_small_powers.pdf) gives the detailed number-field proofs. Run its [verification program](supplements/number-field/small-powers/verify.py) to reproduce its exact numerical tables.
- The [number-field linear calculations](supplements/number-field/linear/) give the conductor estimates, including the explicit large-degree cutoff. The [cubic computations](supplements/cubes/) accompany the discussion of three positive cubes.
- The [Lean project](lean/README.md) contains the formal proofs and replay instructions. Its [scope statement](lean/FORMALIZATION.md) identifies the declarations checked and the analytic steps still needed for the global linear representation theorems.
- The [degree-eleven-and-higher supplement](supplements/lean-addendum/README.md) joins the finite and infinite number-field schedules into one conditional representation theorem. Its replay script accepts a working copy of the repository's `lean/` directory as the base project.

Each main LaTeX file contains its own bibliography and builds independently with pdfLaTeX. A typical build command is `latexmk -pdf manuscript/waring_classical_preprint.tex`, with the analogous command for the number-field paper.

## Earlier proofs

The [research chronology](HISTORY.md) links the dated working drafts, including both quartic proofs, the seventh-power investigation, the November 22 manuscript on eighth and ninth powers, and the earlier transfers to number fields.

## arXiv sources

The [two submission packages](arxiv/README.md) contain the classical paper and the number-field paper with its small-powers supplement.

## License

The manuscripts and original exposition are available under CC BY 4.0. Original software and numerical certificate data are available under Apache 2.0. The [license notice](LICENSE) gives the scope of each license and identifies third-party notices.
