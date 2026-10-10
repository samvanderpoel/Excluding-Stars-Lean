# Excluding an induced star in dense random graphs

This repository contains a Lean formalization of the main results of *Excluding an induced star in dense random graphs*. It exposes the theorem statements, proofs, and mathematical infrastructure needed for the current paper. The formalization is **conditional on fourteen explicitly identified prior-literature assumptions**, in addition to Lean's standard foundational assumptions.

The formalized results cover the colored extremal and stability theorems, the graphon variational problems and their optimizers, entropy and large-deviation rates, typical structure at fixed edge density and in conditioned G(n,p), and the induced-C4 conclusions. The [results index](docs/RESULTS.md) gives the hypotheses, normalizations, parameter ranges, and Lean declaration for each result.

This repository distributes the formalization and its documentation. **The manuscript, its source, bibliography, figures, and PDF are not included.** The [source map](docs/SOURCE_MAP.md) records the relation between the mathematical modules and the current paper. Documentation uses the paper's labels as identifiers and links directly to the Lean implementation.

## Mathematical scope

Throughout the induced-star results, k ≥ 3 and K₁,ₖ has k leaves and k + 1 vertices. The finite graphs are labeled. A co-r-partite graph admits a partition into r cliques. Entropy and rate limits are normalized by choose(n,2) and use base-two logarithms.

| Result family | Formalized content |
| --- | --- |
| Colored graphs | The kth-order Mantel inequality and quantitative stability for the red–green–blue extremal problem. |
| Fixed-density graphons | The entropy value, complete optimizer classification up to the specified graphon equivalence, and the uniqueness versus multiplicity transition. |
| Conditioned graphons | The relative-entropy value and optimizer classification for every 0 < p < 1, including the transition p = pₖ. |
| Finite-graph entropy | The limiting count at every density 0 < γ < 1 and the G(n,p) induced-star-free probability exponent. |
| Fixed-density structure | All three density regimes: co-(k−1)-partite structure above γₖ; a co-(k−1)-partite core and a remainder of O(log n) vertices at the exact edge count floor(γₖ choose(n,2)); and the stated core with a sparse remainder below γₖ. |
| Conditioned G(n,p) structure | Co-(k−1)-partite structure above pₖ and vanishing edge density at and below pₖ. |
| Induced C4 | Almost-all split structure, an exponential count comparison with split graphs, and the entropy formula. |

The subcritical proof fixes the remainder graph H before counting completions and uses the unified H/M entropy-deficit estimate. Its standalone weighted residual estimate ranges over every admissible residual graph, with an arbitrary fixed real edge-weight coefficient; it does not require the graph to arise from a profile. At the critical edge count, the conclusion supplies a positive constant L depending only on k and, with probability tending to one, a literal disjoint union of a co-(k−1)-partite core and a remainder of at most ceil(L log₂ n) vertices. There are no edges between these two graphs. The same decomposition supplies the structure and the size bound.

Two coverage qualifications remain. The separate first-order co-r-partite enumeration formula with its exact lattice Gaussian prefactor is not formalized. The supporting fixed-remainder bound used by the critical proof is formalized at γₖ, uniformly in the finite edge count; the paper's separate formulation for every fixed strictly supercritical density is not claimed as a literal Lean interface. The arbitrary-density supercritical main theorem has a direct proved argument. The [coverage details](docs/RESULTS.md#coverage-limitations) identify both boundaries.

## Verify a checkout

Install Git, Python 3.9 or later, and [elan](https://github.com/leanprover/elan#installation), Lean's toolchain manager. No Python packages are required. From the repository root, run:

```sh
lake exe cache get
python3 scripts/verify.py
```

The cache command is optional. It obtains compiled artifacts for pinned external dependencies, including Mathlib. The verification command builds the two project libraries from their Lean sources, checks the advertised declarations and their assumptions, checks import reachability, and audits the transitive assumptions of every project declaration, including private declarations and generated auxiliaries. It also checks the complete Lean inventory and file hashes against the source map and rejects manuscript assets or excluded private directories. It exits nonzero if a check fails.

The toolchain and dependency pins are:

| Component | Pin |
| --- | --- |
| Lean and Lake | `leanprover/lean4:v4.34.0-rc2` |
| Mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |
| Other dependencies | Exact revisions in [lake-manifest.json](lake-manifest.json) |

The first setup requires network access to obtain the toolchain and external dependencies. Verification needs neither the manuscript nor TeX, literature PDFs, Lean Blueprint, generated documentation, an AI tool, or the private research repository. No project build artifacts are distributed.

For a source build without downloading a dependency cache, omit `lake exe cache get`. To inspect the main declarations after building, run:

```sh
lake env lean verification/Main.lean
lake env lean verification/Audit.lean
```

CI runs the same public verification command in [.github/workflows/verify.yml](.github/workflows/verify.yml). Importing the library from another Lean file uses:

```lean
import InducedStars

#check InducedStars.inducedStarAlmostAll
#print axioms InducedStars.inducedStarAlmostAll
```

The package and namespaces retain the names `InducedStars` and `DenseGraph`. The repository name is `Excluding-Stars-Lean`.

## What is trusted

Lean checks proof terms against their declared types. The fourteen literature axioms supply external mathematical results; their proofs are not reconstructed here. The remaining permitted assumptions are `propext`, `Classical.choice`, and `Quot.sound`. The fixed [allowlist](verification/allowed-axioms.txt) contains these seventeen names. The audit rejects `sorryAx` and every unlisted assumption.

[PriorLiterature.lean](InducedStars/PriorLiterature.lean) contains the actual literature axioms and some locally proved adapters. A declaration's namespace or imported modules do not determine its assumptions; the audit follows its actual proof dependencies. [PriorInstances.lean](InducedStars/PriorInstances.lean) packages the inputs into theorem-valued records without adding assumptions.

The [axiom guide](docs/axioms/README.md) explains this boundary and how to inspect it. The detailed [translation dossier](docs/axioms/TRANSLATIONS.md) gives all fourteen interfaces, precise published locators, normalization conventions, complete mathematical translation arguments, and expanded record fields. Some interfaces are direct translations; others include specializations or deductions from published results within the assumed proposition.

A successful build and axiom audit establish formal derivability from this boundary. Whether the cited publications justify the assumed interfaces requires separate mathematical review. The dossier records an AI-assisted source review; it is not independent human certification, and this release does not claim a newly repeated literature review.

## Navigate the source

| Path | Purpose |
| --- | --- |
| [InducedStars.lean](InducedStars.lean) | Curated root for the paper's formalization. |
| [DenseGraph.lean](DenseGraph.lean) | Curated root for supporting finite-graph, graphon, probability, and analytic infrastructure, without project-specific axioms. |
| [InducedStars/Main/](InducedStars/Main/) | Main theorem statements and their assembly from the detailed proofs. |
| [InducedStars/Structure/](InducedStars/Structure/) | Fixed-density and conditioned typical-structure proofs. |
| [InducedStars/Graphon/](InducedStars/Graphon/) | Graphon definitions, candidates, optimization, and classification. |
| [InducedStars/EdgeColoring/](InducedStars/EdgeColoring/) | Colored extremal and stability arguments. |
| [InducedStars/C4/](InducedStars/C4/) | Induced-C4 and split-graph arguments. |
| [verification/](verification/) | Main-declaration checks, full environment audit, and fixed assumption allowlist. |
| [docs/RESULTS.md](docs/RESULTS.md) | Precise result index and coverage qualifications. |
| [docs/SOURCE_MAP.md](docs/SOURCE_MAP.md) | Current-paper correspondence and retained-module roles. |
| [docs/axioms/](docs/axioms/) | External assumptions and their published-source translations. |

The exported corpus contains the current proofs and the infrastructure used to state or establish them. Obsolete alternate proof branches, compatibility APIs with no current role, manuscript assets, private development notes, and generated research artifacts are excluded. The verifier checks import reachability and the source map's complete inventory, per-file SHA-256 values, and aggregate digest. The map's explanations record the separate mathematical reason for retaining each module; hashes and reachability do not establish that semantic correspondence.

## Release provenance

The mathematical libraries comprise 582 Lean files, counting both roots and all files under `DenseGraph/` and `InducedStars/`. Their SHA-256 manifest digest is:

```text
07045fd439fe25afbce69087f039351e6a328fe133829c2681f8af029e82b4ca
```

To reproduce this digest, sort their relative POSIX paths lexicographically. For each file, concatenate its path, a NUL byte, its lowercase SHA-256, and a newline. Hash the resulting UTF-8 records with SHA-256.

The current-paper reference was the author's root-level K1s-Free working tree, at the reconciled source state based on commit `a9dd4784e0e746a0949eff1c7cea0b78332edc14`. Its separately retained snapshot has digest `f53fa09c9931ffb96e87e31819d84693f88036d54844ce69a68dd7156cf2a1ae`. This identifies the reference used for reconciliation; the manuscript snapshot is not distributed here.

The full release audit reports 20413 project declarations, including 1027 private declarations, and the seventeen permitted assumptions. These counts describe this source tree; rerunning the audit obtains the counts from the compiled environment.

Existing notices are retained. No new license is granted here; the author's code license remains to be specified.
