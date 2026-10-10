# Main results

This index identifies the main declarations exposed by the release of
*Excluding an induced star in dense random graphs*. Their statements and proofs
are in the linked Lean files; their transitive external assumptions are checked
by [verification/Main.lean](../verification/Main.lean) and explained in the
[axiom guide](axioms/README.md). The formalization is conditional on those
explicit prior-literature assumptions.

Manuscript labels identify results in the current paper; the manuscript is not distributed in this repository. Throughout,
`k ≥ 3`, and `inducedStar k` is the star with **k leaves and k + 1 vertices**.
Finite graphs are labeled. The entropy, rate, and critical remainder bound
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
| Lemma `lemma:kthOrderMantel` | For every `C ∈ Ck k n`, the objective `e_red(C) − (k−2)e_blue(C)` is at most `floor((k−2)n/2)`. There is no extra hypothesis `k ≤ n`. [`InducedStars.ColoredGraph.kthOrderMantel`](../InducedStars/EdgeColoring/Extremal.lean). |
| Theorem `thm:kth-order-stability` | For every `ε > 0`, there exist `δ > 0` and `n₀` such that, for `n ≥ n₀`, every `C ∈ Ck k n` with objective at least `−δ n²` differs on at most `ε n²` unordered edges from a member of the exact extremal family. [`InducedStars.ColoredGraph.kthOrderStability`](../InducedStars/EdgeColoring/Stability.lean). |

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
| Fixed-density variational problem `eqn:var-prob-intro-gamma` | For `0 < γ < 1`, its supremum equals the explicit `entropyDensity k γ`. [`InducedStars.fixedDensityEntropyValue_eq`](../InducedStars/Main/VariationalConsequences.lean). |
| Proposition `prop:graphon-char-fixed-gamma` | For `0 < γ < 1`, membership in `fixedDensityOptimizers k γ` is equivalent to cut distance zero from some member of `candidateOptimizerFamily k γ`. [`InducedStars.graphonCharacterizationFixedDensity`](../InducedStars/Graphon/OptimizerClassification.lean). |
| Proposition `prop:graphon-char-fixed-gamma`, common-pullback formulation | Every candidate is an optimizer, and every optimizer is `GraphonEquivalent` to a candidate. [`InducedStars.graphonCharacterizationFixedDensity_upToEquivalence`](../InducedStars/Graphon/OptimizerClassification.lean). |
| Theorem `thm:ent-graphons` | The fixed-density optimizer set is nonempty and unique up to `GraphonEquivalent` for `γ_k ≤ γ < 1`; for each `0 < γ < γ_k`, there is a sequence of pairwise nonequivalent optimizers. [`InducedStars.fixedDensityOptimizerMultiplicity`](../InducedStars/Main/VariationalConsequences.lean). |
| Conditioned variational problem `eqn:var-prob-intro-p` | For `0 < p < 1`, its infimum equals the explicit `rateFunction k p`. [`InducedStars.gnpGraphonVariationalValue_eq_rateFunction`](../InducedStars/Main/VariationalConsequences.lean). |
| Display `eqn:CpStarFormalDef` | The optimizer set is the cut saturation of: the zero graphon for `p < p_k`; the zero graphon together with all fixed-density candidates at `0 < γ ≤ γ_k` for `p = p_k`; or the candidates at `γ_p = p + (1−p)/(k−1)` for `p > p_k`. [`InducedStars.gnpGraphonOptimizerSet_eq`](../InducedStars/Main/VariationalConsequences.lean). |
| Theorem `thm:gnp-graphons` | The conditioned optimizer is unique up to `GraphonEquivalent` on `0 < p < p_k` and on `p_k < p < 1`; at `p = p_k` there is a sequence of pairwise nonequivalent optimizers. [`InducedStars.gnpGraphonOptimizerMultiplicity`](../InducedStars/Main/VariationalConsequences.lean). |

The [candidate family](../InducedStars/Graphon/Candidates.lean) has two
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
| Theorem `thm:main-entropy` | For every `0 < γ < 1` and every asymptotic-density sequence `m`, the normalized logarithm of the number of induced-star-free graphs on `n` vertices with exactly `m(n)` edges tends to `𝓔_k(γ)`. [`InducedStars.inducedStarFixedDensityEntropyAsymptotic`](../InducedStars/Main/AsymptoticConsequences.lean). |
| Theorem `thm:main-entropy`, equation `eqn:main-rate` | For every `0 < p < 1`, the normalized logarithm of the probability that `G(n,p)` is induced-star-free tends to `−𝓡_k(p)`. [`InducedStars.inducedStarGnpLargeDeviationRate`](../InducedStars/Main/AsymptoticConsequences.lean). |

## Fixed-density typical structure

**Theorem `thm:main-almostall`.**
[`InducedStars.inducedStarAlmostAll`](../InducedStars/Main/TypicalStructure.lean)
assembles the following three assertions for the uniform distribution on
labeled induced-star-free graphs with the specified exact edge count.

- **Supercritical:** for `γ_k < γ < 1` and every `m(n)/choose(n,2) → γ`,
  the probability of being co-`(k−1)`-partite tends to one.
- **Critical:** for the exact sequence
  `m(n) = floor(γ_k choose(n,2))`, there exists `L > 0`, depending only on `k`,
  such that with probability tending to one there is a disjoint union
  `G = G₁ ⊔ G₂` with `G₁` co-`(k−1)`-partite and
  `|V(G₂)| ≤ ceil(L log₂ n)`. The two graphs have complementary vertex
  sets and no edges between them; the structural conclusion and size bound
  use one common decomposition.
- **Subcritical:** for `0 < γ < γ_k`, there exists `c > 0` such that,
  for every `ξ > 0` and every `m(n)/choose(n,2) → γ`, with probability
  tending to one there is a disjoint union `G = G₁ ⊔ G₂` with
  `G₁` co-`(k−1)`-partite,
  `||V(G₁)|/n − sqrt(γ/γ_k)| ≤ ξ`, and
  `c n ≤ e(G₂) ≤ ξ n²`. The same decomposition satisfies all bounds,
  and `c` is chosen before `ξ` and the edge-count sequence.

The critical clause is
[`InducedStars.inducedStarCriticalAlmostAll`](../InducedStars/Structure/Critical/AlmostAll.lean).
The [exact edge count and structural witness](../InducedStars/Structure/Critical/Basic.lean)
are `criticalEdgeCount` and `CriticalStructureWitness`.
The event `HasCriticalStructure k bound G` requires one such witness whose
exceptional vertex set has cardinality at most `bound`.
The [probability](../InducedStars/Structure/Critical/AlmostAll.lean)
`criticalStructuredProbability k n bound` is the uniform proportion of this
event among all induced-star-free graphs with exactly `criticalEdgeCount k n`
edges. Thus the finite bound is an integer ceiling and the logarithm is
`Real.logb 2 (n : ℝ)`. The ceiling changes the bound by less than one and
gives the paper's `O(log n)` conclusion.

The counting argument first bounds all completions of a balanced core after
choosing a remainder vertex set and its graph. Vandermonde's identity combines
the choices of remainder edges with the core completion count. A binomial
tail estimate supplies quadratic decay in the remainder order; after summing
over vertex sets, remainders larger than a sufficiently large multiple of
`log n` contribute a vanishing proportion. The fixed-remainder defect bound
eliminates the remaining defects, so the conclusion is an actual disjoint
union. This is the role of Lemma `lemma:critical-large-remainders` in the
current proof.

| Supporting manuscript result | Statement and Lean declaration |
| --- | --- |
| Lemma `lemma:critical-large-remainders`, equation `eqn:critical-large-s-negligible` | For each `k ≥ 3` there exist `ξ, L, C > 0` such that the sum of `Q_s` over `L log₂ n ≤ s ≤ ξn`, divided by the actual co-`(k−1)`-partite count at `m(n) = floor(γ_k choose(n,2))`, tends to zero. For all sufficiently large `n`, the sum over `0 ≤ s ≤ ξn` is at most `2^(C(log₂ n)²)` times that same count. [`InducedStars.criticalLargeRemainders`](../InducedStars/Structure/Critical/Totals.lean). |

The finite quantity `Q_s` is [`criticalRemainderCompletionCount`](../InducedStars/Structure/Critical/CompletionCounting.lean). It multiplies the number of choices of the `s` remainder vertices, the `(k−1)^(n−s)` part-labeling bound, and the binomial completion count for a balanced core with all remainder pairs also available. Its definition gives zero when the forced within-part edges exceed the prescribed total edge count. [`eventually_criticalRemainderCompletionCount_eq`](../InducedStars/Structure/Critical/Totals.lean) proves that this guard is satisfied throughout the small-remainder range for all sufficiently large orders. The sums [`criticalRemainderCompletionSum` and `criticalRemainderCompletionTail`](../InducedStars/Structure/Critical/Totals.lean) range over integer `s ∈ {0,…,n}` with the displayed real inequalities; both use the same exact edge count. The proof uses explicit polynomial overhead in its intermediate cover and binomial comparisons, then absorbs it in the two stated conclusions.

The subcritical [local compensation theorem](../InducedStars/Structure/Subcritical/LocalCompensation.lean)
uses the [unified H/M entropy-deficit bound](../InducedStars/Structure/Subcritical/UnifiedRootPenalty.lean).
The fixed-H profile estimate is [`InducedStars.subcriticalProfileBound_fixedRemainder`](../InducedStars/Structure/Subcritical/FixedRemainderAggregation.lean). It absorbs the polynomial counting factor and gives separate negative root and matching exponents before profiles are summed.

The standalone residual estimate in Lemma `lemma:residual-matching-estimate-K1k` and equation `eqn:sub-residual-weighted-sum-K1k` is exposed by [`InducedStars.subcriticalResidualMatchingAllAdmissible`](../InducedStars/Structure/Subcritical/AdmissibleResidualEstimate.lean). Fix `k ≥ 3`, `0 < η ≤ 1`, `R₀ ≥ 1`, and any real weight coefficient `w`. There is a positive degree bound `d₀` and an order threshold such that the estimate holds for every sufficiently large `n` and every `0 ≤ d ≤ d₀`, uniformly over the division, root set `B`, fixed remainder graph `H`, edge count, matching size `ℓ ≥ 1`, and narrow-window parameters satisfying the explicit geometric conditions. The positive binary matching constant `c_bin` depends on `k, η, R₀` and is independent of `w`; the degree bound and order threshold may depend on `w`.

Here `λ = η/(4R₀)` and `κ = ceil(10R₀²/η²)`. Each retained part has at least `ηn/(2R₀)` vertices, `|B| ≤ λn/2`, and the quota tolerance is at most half the positive palette gap. The sum ranges over **all** graphs `R` whose edges have a retained endpoint and lie outside the active pairs, avoid `B`, have maximum degree at most `dn`, and have matching number `ℓ`. With `q(R)` the maximum residual-safety probability over the entire narrow quota window (defined as zero when the window is empty), the bound is `Σ_R 2^(w e(R)) q(R) ≤ 2^(−c_bin ℓ n/(2κ))`. Residual safety excludes induced stars avoiding `B` that contain both endpoints of an edge of `R`. The binomial model fixes `H` and uses the supplied graph `R` as its defect pattern; no profile realization or induced-freeness hypothesis is imposed on `R`.

The version [`exists_subcriticalAdmissibleResidualMatchingEstimate`](../InducedStars/Structure/Subcritical/AdmissibleResidualEstimate.lean) takes the principal-Janson input explicitly; the headline declaration supplies it from the approved Riordan–Warnke assumption. The finite form [`subcriticalAdmissibleResidualMatchingEstimate_baseTwo`](../InducedStars/Structure/Subcritical/AdmissibleResidualEstimate.lean) states the size and entropy-reserve inequalities explicitly, while the existential form chooses a uniform degree interval and eventual order threshold. At `ℓ = 0` the admissible family consists only of the empty graph. The separate [`subcriticalAdmissibleResidualSafetySum_zero_baseTwo`](../InducedStars/Structure/Subcritical/AdmissibleResidualEstimate.lean) gives sum one when the quota window is nonempty, stating that condition explicitly.

## Conditioned G(n,p) typical structure

**Theorem `thm:gnp-typ-struc`.**
[`InducedStars.inducedStarGnpTypicalStructure`](../InducedStars/Structure/Gnp/Main.lean)
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
| Theorem `thm:c4-main`, split structure | The uniform probability that an induced-`C₄`-free graph with exactly `m(n)` edges is split tends to one. [`InducedStars.inducedC4AlmostAllSplit`](../InducedStars/C4/AlmostAll.lean). |
| Theorem `thm:c4-main`, count comparison | There is `c > 0`, chosen before the asymptotic-density sequence, such that eventually `|N_C₄(n,m(n))/N_split(n,m(n)) − 1| ≤ exp(−c n)`. [`InducedStars.inducedC4CountComparison`](../InducedStars/C4/AlmostAll.lean). |
| Equation `eqn:c4-entropy-main` | The normalized base-two logarithm of the induced-`C₄`-free count tends to the scalar supremum below. [`InducedStars.inducedC4Entropy_eq_scalarMax`](../InducedStars/C4/AlmostAll.lean). |

The last endpoint gives the explicit feasible interval:

$$
\sup_{\,1-\sqrt{1-\gamma}\leq x\leq\sqrt\gamma}
2x(1-x)H\!\left(\frac{\gamma-x^2}{2x(1-x)}\right).
$$

Here `x` is the clique proportion. The interval ensures that the cross-edge
density lies in `[0,1]`; the supremum is attained, as established in the
[scalar optimization implementation](../InducedStars/C4/SplitSizeEnumeration.lean).

## Coverage limitations

The separate first-order asymptotic formula for the number of co-r-partite graphs, displayed after Theorem `thm:main-almostall` in the current introduction, remains unformalized. It includes the exact zero-sum lattice Gaussian prefactor, `1/r!`, balanced multinomial, and binomial slice. The polynomial-factor comparisons used in the critical proof do not establish that exact prefactor. None of the results indexed above relies on claiming this additional formula.

The paper's Lemma `lemma:super-fixed-remainder` states a supporting fixed-remainder estimate throughout the supercritical density range. The declaration [`eventually_criticalFixedRemainderDefect_le_reference`](../InducedStars/Structure/Critical/FixedRemainderTotal.lean) specializes this estimate to γₖ and is uniform in the finite edge count, as required for the exact critical floor sequence. The separate paper lemma over every fixed supercritical density is not claimed as a literal Lean endpoint. The full supercritical typical-structure theorem is proved directly by the division-counting argument, so this supporting-interface limitation does not restrict its density range.

