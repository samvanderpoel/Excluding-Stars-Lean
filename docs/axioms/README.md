# Prior-literature assumptions

The formalization is conditional on fourteen named results from prior
literature, together with Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. All fourteen project-specific axioms are declared in
[InducedStars/PriorLiterature.lean](../../InducedStars/PriorLiterature.lean).
Their exact statements, published sources, normalizations, and
source-to-interface derivations are in [TRANSLATIONS.md](TRANSLATIONS.md).
The fixed [allowlist](../../verification/allowed-axioms.txt) distinguishes
the foundational and literature assumptions.

A successful Lean build checks the formal proofs of the declared statements.
An axiom audit identifies the assumptions on which those proofs depend and
rejects assumptions outside the stated boundary. Neither operation proves
the literature axioms or verifies that a published theorem implies its Lean
interface. That last step is mathematical review of the translation.

## What the interfaces assume

`PriorLiterature.lean` mixes actual axiom declarations and locally proved
adapters; its introductory comments are not an additional assumption list.
In particular, `erdosSimonovitsStability` is proved locally from
`furediCliqueFreePartiteSubgraph` and local finite-graph results. It is not a
fifteenth external axiom.

[PriorInstances.lean](../../InducedStars/PriorInstances.lean) packages the
named axioms into theorem-valued records using ordinary proved definitions.
Its seven packages provide homogeneous subpartitions, cut-zero
homomorphism-density equality, common pullbacks, entropy semicontinuity,
sequential compactness, finite weighted alignment, and principal Janson.
They add no external assumption. The full base-two critical window and the
unified subcritical H/M proof use this same assumption boundary; their local
proof revisions introduce no new literature axiom.

The records are declared in
[DenseGraph/Graphon/Inputs.lean](../../DenseGraph/Graphon/Inputs.lean),
[DenseGraph/Regularity/Inputs.lean](../../DenseGraph/Regularity/Inputs.lean), and
[DenseGraph/FiniteModels/Janson.lean](../../DenseGraph/FiniteModels/Janson.lean).
Declaring a structure `S : Prop` specifies what a witness would prove; it
does not assert that such a witness exists. A theorem taking `S` as an
argument is conditional on that argument.

Two actual axioms have record-valued types:
`bclsvFiniteWeightedAlignment : DenseGraph.FiniteWeightedAlignmentInput`
and `riordanWarnkePrincipalJanson : DenseGraph.PrincipalJansonInput`.
Reading only those type names hides the quantifiers and strength of the
assumptions. Read the full `align` and `avoidance_le` fields, expanded in
[TRANSLATIONS.md](TRANSLATIONS.md#appendix-expanded-theorem-valued-interfaces).
The other expanded records show exactly what the packages expose.

## Inspect the formal assumption boundary

From the repository root, run the public verification command:

```sh
python3 scripts/verify.py
```

[verification/Main.lean](../../verification/Main.lean) contains readable
`#check` and `#print axioms` commands for the advertised results. After the
build, its reports can also be inspected directly:

```sh
lake env lean verification/Main.lean
```

For another theorem, create a Lean file in this checkout containing:

```lean
import InducedStars
#print axioms InducedStars.inducedStarAlmostAll
```

Then run `lake env lean path/to/that-file.lean`. Replace the final declaration
name to inspect another proof. `#print axioms` follows transitive proof
dependencies, including private declarations; importing an axiom's module
does not itself mean that every theorem uses that axiom.

The public [environment audit](../../verification/Audit.lean) checks
assumptions against the fixed allowlist. `sorryAx` and every unlisted
assumption are rejected. The allowlist is not regenerated from the proofs
under examination. See the [results index](../RESULTS.md) for the exact
public theorem statements and their source links.

## Review a source-to-axiom translation

The translation guide preserves the historical dossier's mathematical
arguments and statuses, with its original provenance identified separately
from the current release. It was prepared with automated assistance and is
**not independent human certification**. This release does not claim a new
literature audit. No unresolved source-to-axiom mismatch is recorded in
that dossier; its specific terminology and normalization qualifications
remain visible in the guide.

A mathematician can review each A01–A14 entry by obtaining the cited
published version through its DOI or journal link, locating the result and
convention passages, and checking the complete implication to the stated
mathematical restatement. A public bibliographic link identifies the source;
it does not mean that its full text is freely accessible. If the publication
cannot be inspected, that independent review remains incomplete.

A Lean-literate reviewer should then compare the restatement with the exact
declaration and every field of a record-valued type, following the linked
definitions. Check the domain, quantifier order, strictness, constants,
zero cases, normalization, and equivalence relation. Distinguish adapters
proved in Lean from specializations or derived consequences included inside
the external assumption itself. Finally, run the public audit to check that
the inspected proof uses only the documented boundary.

Particular review points are A04's one simultaneous probability-one
selection; A05's alignment radius uniform in graph order; A10's two
possibly noninvertible measure-preserving maps; A11's arbitrary labeled
families and their limit set; and A14's ordered-versus-unordered overlap sum
and degenerate cases. The guide gives the full arguments for each.

| Lean notation | Meaning here |
| --- | --- |
| `∀`, `∃`, `→` | For every, there exists, implication; quantifier order matters. |
| `Tendsto f atTop (nhds L)` | The sequence `f n` tends to `L`. |
| `∀ᶠ n in atTop, P n` | `P n` holds for all sufficiently large `n`. |
| `∀ᵐ x ∂μ, P x` | `P x` holds almost everywhere for measure `μ`. |
| `Fin n`, `Finset` | The labels `0,…,n−1`, and a finite set. |
| `MeasurePreserving` | A measurable map with the stated pushforward measure; invertibility is not implied. |
| `StrictMono σ` | A strictly increasing subsequence index. |
| `: Prop where` | A proposition described by its fields, without an assumed witness. |
