# Manuscript

This directory contains Sam van der Poel's **Excluding an induced star in
dense random graphs**, copied from manuscript revision
`339111b0475e8dc7586223cb060ee5cabf509198`. The source checkout was clean
at that revision.

The 19 manuscript files have SHA-256 manifest digest
`3789fea9f70ad477d232c71eb346161f05073dbd0f8a2766d7228d55d94ec2f6`.
This uses the [release manifest algorithm](../README.md#files-and-pins),
with paths relative to this directory and excluding this README.

[main.pdf](main.pdf) is copied byte-for-byte from that manuscript snapshot.
Its SHA-256 is
`cef85c31be84a481cdfeb806c1c743d765f6bcc78768c4af5fa6280251f695ad`.
It was not rebuilt or rendered during release preparation.

The source uses the AMS `amsart` class and includes all manuscript TeX
inputs, `ref.bib`, and the two included figures (`graphons.pdf` and
`rate-functions.pdf`). Their standalone TikZ/PGFPlots sources and PDFs are in
[Graphics/](Graphics/).

## Optional typesetting

From the repository root, with a full recent TeX Live or MiKTeX installation:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

The bibliography uses Biber and BibLaTeX. A full TeX distribution supplies
the AMS class and packages, TikZ/PGFPlots, thmtools/thm-restate, cleveref,
and the other dependencies listed in [preamble.tex](preamble.tex).

**TeX is unnecessary for Lean verification.** Run
`python3 scripts/verify.py` from the repository root to check the formalization.
