# Correspondence with the current paper

This release contains Lean statements, proofs, and infrastructure for the current paper *Excluding an induced star in dense random graphs*. The manuscript reference is identified in the [release provenance](../README.md#release-provenance). The manuscript itself is not part of this repository.

The [results index](RESULTS.md) maps the principal results to exact Lean declarations. The [module map](current-source-map.json) records a current-paper role for every retained mathematical module. A role can be a stated result, a step of its current proof, a mathematical definition, a proved supporting lemma, an external-input interface, or a curated import root. Standard infrastructure need not have a numbered counterpart in the manuscript, but its role in the current development must be identified.

## Proof organization

| Current-paper argument | Principal implementation |
| --- | --- |
| Colored extremal inequality and stability | [EdgeColoring/](../InducedStars/EdgeColoring/), using finite graph and regularity infrastructure. |
| Candidate graphons and variational classification | [Graphon/](../InducedStars/Graphon/) and [Analysis/](../InducedStars/Analysis/), using the explicit cut-distance, entropy, approximation, and compactness interfaces. |
| Entropy and probability rates | [Asymptotics/](../InducedStars/Asymptotics/) and [Main/AsymptoticConsequences.lean](../InducedStars/Main/AsymptoticConsequences.lean). |
| Supercritical typical structure | [Structure/Supercritical/](../InducedStars/Structure/Supercritical/), with completion and cover-counting estimates. |
| Critical completion counts, defects, and large remainders | [Structure/Critical/](../InducedStars/Structure/Critical/), culminating in the critical theorem at the exact edge count with an O(log n) remainder. |
| Subcritical fixed-H completion and profile counting | [Structure/Subcritical/](../InducedStars/Structure/Subcritical/), including the unified H/M penalty and the weighted sum over all admissible residual graphs. |
| Conditioned G(n,p) structure | [Structure/Gnp/](../InducedStars/Structure/Gnp/), transferring the density and structural estimates to the conditional law. |
| Induced C4 and split-graph counts | [C4/](../InducedStars/C4/). |
| Published assumptions and their proved packaging | [PriorLiterature.lean](../InducedStars/PriorLiterature.lean), [PriorInstances.lean](../InducedStars/PriorInstances.lean), and [axiom translations](axioms/TRANSLATIONS.md). |

The `DenseGraph` root excludes the project's literature-axiom instances and the induced-star extremal and structural arguments. Shared graphon definitions remain in the `InducedStars` namespace; their namespace does not make them paper-specific results. The generic matrix induced-density calculation is isolated in [MatrixInducedDensity.lean](../InducedStars/Graphon/MatrixInducedDensity.lean).

## Inclusion criterion

The release keeps the mathematics required to state and prove the current results, including finite identities, probability models, analytic estimates, graphon constructions, and genuine supporting lemmas. It excludes unused alternate proof branches and adapters whose only purpose is compatibility with superseded interfaces. Explanatory comments describe their current mathematical role.

The corpus review and the automated checks answer different questions. The module map records why a source belongs in this formalization. The verifier requires its inventory to equal the shipped mathematical corpus, checks every file's SHA-256 and the aggregate digest, and rejects unmapped Lean source, manuscript assets, and excluded private directories. Import reachability verifies that the curated roots include every retained module. The Lean build checks the proofs, and the environment audit checks their actual transitive assumptions. Hashes and reachability do not establish mathematical relevance; the recorded roles and paper correspondences require mathematical review.

The current correspondence qualifications are the two explicit coverage limitations in [RESULTS.md](RESULTS.md#coverage-limitations). The code does not claim the exact first-order co-partite prefactor or a literal fixed-remainder endpoint over every strictly supercritical density.

The repository contains no manuscript TeX, PDF, bibliography, figures, typesetting configuration, or manuscript build output. Its documentation summarizes the formal statements and their correspondence without reproducing the paper.
