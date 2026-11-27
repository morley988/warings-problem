# arXiv submission packages

| Submission | Source archive | Top-level documents, in compilation order |
| --- | --- | --- |
| Linear bounds and restricted moments in Waring’s problem | [Classical sources](waring-classical.zip) | `waring_classical_preprint.tex` |
| Efficient differencing and linear bounds in the Waring–Siegel problem | [Number-field sources](waring-siegel.zip) | `waring-siegel_preprint.tex`, then `waring-siegel_small_powers.tex` |

Upload each ZIP as the source for its own **math.NT** submission. Each archive contains a `00README.json` selecting pdfLaTeX. On **Review Files**, confirm that the top-level files appear in the order above. Inspect the generated PDF before submitting. For the number-field paper, the references to the main article should be followed by the title page of *Supporting estimates for small powers in the Waring–Siegel problem*. The supplement belongs to the same submission. [arXiv’s TeX submission guide](https://info.arxiv.org/help/submit_tex.html) · [Compilation instructions](https://info.arxiv.org/help/00README.html)

The `anc/` directories contain supporting calculations, their data and applicable license notices. The full Lean development is available from the [repository](../lean/README.md). Select **Creative Commons Attribution 4.0 International (CC BY 4.0)** in each arXiv submission to match the manuscript license.
