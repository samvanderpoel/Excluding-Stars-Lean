# Excluding an induced star in dense random graphs

This repository provides a **Lean formalization of the main results of the
induced-stars paper, conditional on explicitly identified prior-literature
results**. It makes the actual theorem statements, formal proofs, supporting
mathematical implementation, and exact external assumptions available for
inspection and checking. The [main-results index](docs/RESULTS.md) connects the
manuscript's colored extremal and stability results, graphon variational
problems and optimizer classifications, entropy and large-deviation formulas,
typical structures, and induced-C4 results to their Lean declarations. Each
entry states the relevant hypotheses and parameter regime.

The typical-structure theorem includes the full base-two critical window for
every fixed real window parameter, including the transition endpoint. The
subcritical proof uses the unified H/M entropy-deficit argument. The separate
first-order co-partite enumeration formula with its exact lattice prefactor
remains unformalized; see the [coverage limitation](docs/RESULTS.md#coverage-limitation).

The [manuscript PDF](paper/main.pdf) and its source are included. The
[axiom guide](docs/axioms/README.md) explains the assumption boundary, and the
[translation guide](docs/axioms/TRANSLATIONS.md) records how the cited
literature supports each formal interface.

## Check the formalization

Install Git, Python 3.9 or later, and
[elan](https://github.com/leanprover/elan#installation), Lean's toolchain
manager. No Python packages are required. After publication, the quick start is:

```sh
git clone https://github.com/samvanderpoel/Excluding-Stars-Lean.git
cd Excluding-Stars-Lean
lake exe cache get
python3 scripts/verify.py
```

For a local copy, enter its directory and run the last two commands; no remote
repository is required. `lake exe cache get` is optional: it downloads compiled
**pinned external dependencies**, including Mathlib. The verification command
builds both exported mathematical libraries from their sources, checks all
advertised declarations, checks that every shipped implementation module is
reachable through the curated roots, and audits actual transitive axiom
dependencies, including dependencies through private declarations. It exits
nonzero on failure. Project build artifacts from the research checkout are
neither included nor required.

Lean and Lake use the version in `lean-toolchain`. Initial setup needs network
access for the public dependencies. Verification needs neither TeX nor
literature PDFs, Lean Blueprint, Codex, ChatGPT, or the research repository.

## What the checks establish

The Lean build checks formal proofs of the declared statements. The axiom
audit reports and checks their external assumption boundary against a fixed
allowlist: fourteen prior-literature axioms and the foundational assumptions
`propext`, `Classical.choice`, and `Quot.sound`. It rejects `sorryAx` and
unlisted assumptions.

Mathematical review of the source-to-axiom translations is a separate task:
it checks whether the published results justify those assumptions. A
successful build or axiom audit does not prove the literature axioms.
The translation guide preserves the existing AI-assisted review status;
it is not independent human certification.

## Files and pins

- `DenseGraph/` and `InducedStars/`, with their root imports: mathematical libraries.
- `verification/` and `scripts/verify.py`: public declarations and assumption checks.
- `docs/`: main results and prior-literature translations.
- `paper/`: manuscript source, figures, PDF, and optional typesetting instructions.
- `.github/workflows/verify.yml`: CI running the same verification command.

Source revision base: `bca688515f1ff41e1c2e572ee0493a6eee9be3ef`, with the
subsequent proof and manuscript synchronization included in this release.
The final mathematical source tree comprises 663 Lean files: the
`DenseGraph/` and `InducedStars/` trees plus their root files
`DenseGraph.lean` and `InducedStars.lean`.
Its SHA-256 manifest digest is
`9c37991ff450296d6c58f2f4679d2e12a46a7a5c95624fd3525fe827db58e061`.

To reproduce this digest, sort the relative POSIX paths lexicographically.
For each file, concatenate its path, a NUL byte, its lowercase SHA-256,
and a newline. Hash the resulting UTF-8 records with SHA-256. The
[manuscript provenance](paper/README.md) records the separately identified
paper snapshot and copied PDF.

Lean: `leanprover/lean4:v4.34.0-rc2`.
Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
Other dependency revisions are locked in `lake-manifest.json`.

Existing notices are retained. No new license is granted here; the author's
code and manuscript license remains to be specified.
