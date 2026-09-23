# Main results

This index identifies the main declarations exposed by the release of
*Excluding an induced star in dense random graphs*. Their statements and proofs
are in the linked Lean files; their transitive external assumptions are checked
by [verification/Main.lean](../verification/Main.lean) and explained in the
[axiom guide](axioms/README.md). The formalization is conditional on those
explicit prior-literature assumptions.

Manuscript labels refer to the included [paper](../paper/main.pdf). Throughout,
`k ≥ 3`, and `inducedStar k` is the star with **k leaves and k + 1 vertices**.
Finite graphs are labeled. The entropy, rate, and critical-window statements
use base-two logarithms. Entropy and rate are normalized by
`completeEdgeCount n = n.choose 2`.
`HasAsymptoticEdgeDensity m γ` means
`m(n) / choose(n,2) → γ`.
A co-`r`-partite graph has a partition into `r` cliques.

The transition parameters are

$$
p_k=(1-p_k)^{k-1},\qquad 0<p_k<1,\qquad
\gamma_k=\frac{1+(k-2)p_k}{k-1}.
$$

They are `pK k` and `gammaK k` in
[ScalarOptimization.lean](../InducedStars/Analysis/ScalarOptimization.lean).

## Colored extremal and stability results

| Manuscript result | Statement and Lean declaration |
| --- | --- |
| Lemma `lemma:kthOrderMantel` | For every `C ∈ Ck k n`, the objective `e_red(C) − (k−2)e_blue(C)` is at most `floor((k−2)n/2)`. There is no extra hypothesis `k ≤ n`. [`InducedStars.ColoredGraph.kthOrderMantel`](../InducedStars/EdgeColoring/Extremal.lean#L1894). |
| Theorem `thm:kth-order-stability` | For every `ε > 0`, there exist `δ > 0` and `n₀` such that, for `n ≥ n₀`, every `C ∈ Ck k n` with objective at least `−δ n²` differs on at most `ε n²` unordered edges from a member of the exact extremal family. [`InducedStars.ColoredGraph.kthOrderStability`](../InducedStars/EdgeColoring/Stability.lean#L4213). |

Here `Ck k n` excludes the colored patterns on `k` vertices with all
center-to-leaf edges red and all leaf-to-leaf edges red or green. The extremal
family consists of disjoint regular cores, with all other edges green. A core
is an equitable blow-up of a connected `(k−2)`-regular graph, with blue cluster
interiors, red edges corresponding to reduced-graph edges, and green edges
between nonadjacent clusters. The exact definitions accompany the theorems.

## Graphon variational problems and optimizer classification

Graphon entropy is the integral of binary entropy over the unit square.
The fixed-density feasible set has edge density `γ` and zero induced-star
density. The conditioned variational problem minimizes integrated binary
relative entropy over all induced-star-free graphons.

The actual equivalence relation `GraphonEquivalent U W` requires
measure-preserving maps `φ, ψ : [0,1] → [0,1]` such that
`U(φ(x),φ(y)) = W(ψ(x),ψ(y))` almost everywhere. Set classifications use
**cut-distance-zero saturation**: every optimizer has cut distance zero from
an explicit candidate, and every graphon at cut distance zero from a candidate
is an optimizer. The common-pullback formulation is provided separately.

| Manuscript result | Statement and Lean declaration |
| --- | --- |
| Fixed-density variational problem `eqn:var-prob-intro-gamma` | For `0 < γ < 1`, its supremum equals the explicit `entropyDensity k γ`. [`InducedStars.fixedDensityEntropyValue_eq`](../InducedStars/Main/VariationalConsequences.lean#L48). |
| Proposition `prop:graphon-char-fixed-gamma` | For `0 < γ < 1`, membership in `fixedDensityOptimizers k γ` is equivalent to cut distance zero from some member of `candidateOptimizerFamily k γ`. [`InducedStars.graphonCharacterizationFixedDensity`](../InducedStars/Graphon/OptimizerClassification.lean#L111). |
| Proposition `prop:graphon-char-fixed-gamma`, common-pullback formulation | Every candidate is an optimizer, and every optimizer is `GraphonEquivalent` to a candidate. [`InducedStars.graphonCharacterizationFixedDensity_upToEquivalence`](../InducedStars/Graphon/OptimizerClassification.lean#L123). |
| Theorem `thm:ent-graphons` | The fixed-density optimizer set is nonempty and unique up to `GraphonEquivalent` for `γ_k ≤ γ < 1`; for each `0 < γ < γ_k`, there is a sequence of pairwise nonequivalent optimizers. [`InducedStars.fixedDensityOptimizerMultiplicity`](../InducedStars/Main/VariationalConsequences.lean#L114). |
| Conditioned variational problem `eqn:var-prob-intro-p` | For `0 < p < 1`, its infimum equals the explicit `rateFunction k p`. [`InducedStars.gnpGraphonVariationalValue_eq_rateFunction`](../InducedStars/Main/VariationalConsequences.lean#L263). |
| Display `eqn:CpStarFormalDef` | The optimizer set is the cut saturation of: the zero graphon for `p < p_k`; the zero graphon together with all fixed-density candidates at `0 < γ ≤ γ_k` for `p = p_k`; or the candidates at `γ_p = p + (1−p)/(k−1)` for `p > p_k`. [`InducedStars.gnpGraphonOptimizerSet_eq`](../InducedStars/Main/VariationalConsequences.lean#L479). |
| Theorem `thm:gnp-graphons` | The conditioned optimizer is unique up to `GraphonEquivalent` on `0 < p < p_k` and on `p_k < p < 1`; at `p = p_k` there is a sequence of pairwise nonequivalent optimizers. [`InducedStars.gnpGraphonOptimizerMultiplicity`](../InducedStars/Main/VariationalConsequences.lean#L608). |

The [candidate family](../InducedStars/Graphon/Candidates.lean#L393) has two
branches. At and above `γ_k`, it is the balanced `(k−1)`-block graphon with
value one within blocks and value `((k−1)γ−1)/(k−2)` between them. Below
`γ_k`, it is the admissible block-sequence family `WLambda`, with block
lengths `α_i`, connected `(k−2)`-regular reduced graphs `H_i`, zero values
between distinct blocks and on the remainder, and the exact mass constraint
`Σ_i α_i² / |V(H_i)| = γ / (1+(k−2)p_k)`.

## Entropy and large-deviation rate

Let `H` be binary entropy. The functions appearing in these endpoints are

$$
\mathcal E_k(\gamma)=
\begin{cases}
\dfrac{(k-2)\gamma}{1+(k-2)p_k}H(p_k),&\gamma\leq\gamma_k,\\
\dfrac{k-2}{k-1}H\!\left(\dfrac{(k-1)\gamma-1}{k-2}\right),
&\gamma\geq\gamma_k,
\end{cases}
$$
$$
\mathcal R_k(p)=
\begin{cases}
\log_2\dfrac1{1-p},&p\leq p_k,\\
\dfrac1{k-1}\log_2\dfrac1p,&p\geq p_k.
\end{cases}
$$

The two formulas in each definition agree at the transition.

| Manuscript result | Statement and Lean declaration |
| --- | --- |
| Theorem `thm:main-entropy` | For every `0 < γ < 1` and every asymptotic-density sequence `m`, the normalized logarithm of the number of induced-star-free graphs on `n` vertices with exactly `m(n)` edges tends to `𝓔_k(γ)`. [`InducedStars.inducedStarFixedDensityEntropyAsymptotic`](../InducedStars/Main/AsymptoticConsequences.lean#L88). |
| Theorem `thm:main-rate` | For every `0 < p < 1`, the normalized logarithm of the probability that `G(n,p)` is induced-star-free tends to `−𝓡_k(p)`. [`InducedStars.inducedStarGnpLargeDeviationRate`](../InducedStars/Main/AsymptoticConsequences.lean#L126). |

## Fixed-density typical structure

**Theorem `thm:main-almostall`.**
[`InducedStars.inducedStarAlmostAll`](../InducedStars/Main/TypicalStructure.lean#L24)
assembles the following three assertions for the uniform distribution on
labeled induced-star-free graphs with the specified exact edge count.

- **Supercritical:** for `γ_k < γ < 1` and every `m(n)/choose(n,2) → γ`,
  the probability of being co-`(k−1)`-partite tends to one.
- **Critical window:** for every fixed `a ∈ ℝ`, use the exact sequence
  `m(n) = floor((γ_k + a log₂(n)/n) choose(n,2))` and set
  `a_* = (k−2)p_k(1−p_k) ln(2) / ((k−1)γ_k)`.
  If `a ≤ a_*`, then for every `ε > 0`, with probability tending to one
  there is a disjoint union of a co-`(k−1)`-partite core and a remainder
  `S` satisfying `abs(|S|/log₂(n) − (a_*−a)/(2γ_k)) ≤ ε`.
  The same decomposition supplies the structure and size estimate.
  Equality `a = a_*` gives a remainder of size `o(log₂ n)`.
  If `a > a_*`, the probability of being co-`(k−1)`-partite tends to one.
- **Subcritical:** for `0 < γ < γ_k`, there exists `c > 0` such that,
  for every `ξ > 0` and every `m(n)/choose(n,2) → γ`, with probability
  tending to one there is a disjoint union `G = G₁ ⊔ G₂` with
  `G₁` co-`(k−1)`-partite,
  `||V(G₁)|/n − sqrt(γ/γ_k)| ≤ ξ`, and
  `c n ≤ e(G₂) ≤ ξ n²`. The same decomposition satisfies all bounds,
  and `c` is chosen before `ξ` and the edge-count sequence.

The critical clause is
[`InducedStars.inducedStarCriticalWindowBase2AlmostAll`](../InducedStars/Structure/Critical/WindowBase2.lean#L155).
Its [exact edge count and event](../InducedStars/Structure/Critical/WindowBase2.lean#L28)
use the paper's base-two normalization. The proof's internal natural-log
parameter is `a/ln(2)`; [proved conversion identities](../InducedStars/Structure/Critical/WindowBase2.lean#L54)
transport the counts and event, including the tolerance `ε/ln(2)`.

The subcritical [local compensation theorem](../InducedStars/Structure/Subcritical/LocalCompensation.lean#L202)
uses the [unified H/M entropy-deficit bound](../InducedStars/Structure/Subcritical/UnifiedRootPenalty.lean#L24).
The earlier four-case adapter remains available for compatibility.

## Conditioned G(n,p) typical structure

**Theorem `thm:gnp-typ-struc`.**
[`InducedStars.inducedStarGnpTypicalStructure`](../InducedStars/Structure/Gnp/Main.lean#L42)
uses the binomial graph law conditioned on induced-star-freeness, for
`0 < p < 1`.

- For `p_k < p < 1`, co-`(k−1)`-partite structure and convergence of the
  unordered-edge density to `p + (1−p)/(k−1)` hold jointly with probability
  tending to one.
- For `0 < p ≤ p_k`, **including equality**, for every `ξ > 0` the
  conditional probability of `e(G) ≤ ξ n²` tends to one.

Thus the critical finite-graph conclusion is sparse edge mass. The critical
graphon variational problem above still has infinitely many nonequivalent
optimizers.

## Induced C4-free graphs

Here `0 < γ < 1` and `m(n)/choose(n,2) → γ`. A split graph admits a
partition into a clique and an independent set.

| Manuscript result | Statement and Lean declaration |
| --- | --- |
| Theorem `thm:c4-main`, split structure | The uniform probability that an induced-`C₄`-free graph with exactly `m(n)` edges is split tends to one. [`InducedStars.inducedC4AlmostAllSplit`](../InducedStars/C4/AlmostAll.lean#L117). |
| Theorem `thm:c4-main`, count comparison | There is `c > 0`, chosen before the asymptotic-density sequence, such that eventually `|N_C₄(n,m(n))/N_split(n,m(n)) − 1| ≤ exp(−c n)`. [`InducedStars.inducedC4CountComparison`](../InducedStars/C4/AlmostAll.lean#L99). |
| Equation `eqn:c4-entropy-main` | The normalized base-two logarithm of the induced-`C₄`-free count tends to the scalar supremum below. [`InducedStars.inducedC4Entropy_eq_scalarMax`](../InducedStars/C4/AlmostAll.lean#L140). |

The last endpoint gives the explicit feasible interval:

$$
\sup_{\,1-\sqrt{1-\gamma}\leq x\leq\sqrt\gamma}
2x(1-x)H\!\left(\frac{\gamma-x^2}{2x(1-x)}\right).
$$

Here `x` is the clique proportion. The interval ensures that the cross-edge
density lies in `[0,1]`; the supremum is attained, as established in the
[scalar optimization implementation](../InducedStars/C4/SplitSizeEnumeration.lean#L135).

## Coverage limitation

The independent first-order asymptotic formula for the number of co-`r`-partite
graphs, displayed after Theorem `thm:main-almostall` in the
[manuscript introduction](../paper/introduction.tex#L83), remains unformalized.
This is the formula with the exact zero-sum lattice Gaussian prefactor,
`1/r!`, balanced multinomial, and binomial slice. The proved constant-factor
comparisons used in the critical window do not establish that exact prefactor.
The results indexed above do not depend on claiming this additional formula.
