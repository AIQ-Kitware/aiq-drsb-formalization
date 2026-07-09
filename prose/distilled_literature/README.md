# Distilled literature proof notes

This directory contains first-pass LaTeX proof-target notes distilled from the PDFs in `papers.zip`.

Each `.tex` file is standalone and cites the paper it distills via `references.bib`. The notes are intended to become a bridge between the original literature and Lean theorem targets. They are not claimed to be a substitute for the full papers; each file includes a `Distillation gaps` section with anchors that still need exact page/theorem verification.

## Files

- `CGP2021_sinkhorn_schrodinger_bridge.tex`
- `Leonard2014_schrodinger_survey.tex`
- `SinkhornKnopp1967_matrix_scaling.tex`
- `FranklinLorenz1989_matrix_scaling.tex`
- `Carroll2004_birkhoff_contraction.tex`
- `EvesonNussbaum1995_birkhoff_hopf.tex`
- `BlanchetMurthy2019_model_risk_ot.tex`
- `GaoKleywegt2023_wasserstein_drso.tex`
- `MohajerinEsfahaniKuhn2018_data_driven_wdro.tex`
- `WangGaoXie2025_sinkhorn_dro.tex`
- `Alquier2024_pac_bayes.tex`
- `Girsanov1960_change_of_measure.tex`
- `CameronMartin1945_wiener_transformations.tex`
- `Yeh1978_conditional_wiener_translation.tex`
- `Kakutani1948_product_measures.tex`
- `DSBM2023_diffusion_schrodinger_bridge_matching.tex`
- `GSBM2024_generalized_schrodinger_bridge_matching.tex`
- `AdjointMatching2025_memoryless_soc.tex`

## Suggested workflow

1. Compile a note you care about:

   ```bash
   pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
   bibtex CGP2021_sinkhorn_schrodinger_bridge
   pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
   pdflatex CGP2021_sinkhorn_schrodinger_bridge.tex
   ```

2. Replace each `TODO` with exact theorem/page anchors after checking the PDF.
3. For each Lean theorem, add a line pointing to the exact distilled note section.
4. For the current compactness frontier, prioritize:
   - `FranklinLorenz1989_matrix_scaling.tex`
   - `Carroll2004_birkhoff_contraction.tex`
   - `CGP2021_sinkhorn_schrodinger_bridge.tex`
