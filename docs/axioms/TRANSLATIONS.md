# Prior-literature translations

These fourteen records adapt the substantive mathematical arguments of the
existing source-to-axiom dossier and its supporting source records at the
historical export snapshot `d757fd1d2116abe57a8ef218ea64b3a093a3dd06`.
That identifier records the dossier's provenance, not the current release's
source revision; see the [current release provenance](../../README.md#files-and-pins).
This release does not claim a new literature audit. The dossier was prepared
with automated assistance for mathematical peer review; its findings are **not independent
human certification**. The uppercase findings and PASS entries below retain
that dossier's review status, not a stronger release certification.

The dossier records two direct translations, six specializations or
weakenings, four derived consequences, and two combinations of published
results. Its recorded verdicts are two verified exactly, six verified as
weaker specializations, and six verified as derived consequences. It records
no unresolved mathematical **source-to-axiom** mismatch. The convention
bridges and derivations accepted inside an axiom remain outside the
kernel-checked derivations; they require mathematical review.

All fourteen actual axiom declarations and the expanded record interfaces
are reproduced at the end. The linked axiom declarations and displayed record
interfaces are unchanged in this release, although local proofs elsewhere
have been revised. The bibliography uses public publication links. No
prior-literature PDF or screenshot is distributed with this package or
required for Lean verification.
For the review procedure and live dependency checks, see the
[axiom guide](README.md).

## Interface register

| ID | Exact declaration (all in `InducedStars.PriorLiterature`) | Interface | Recorded status |
| --- | --- | --- | --- |
| A01 | [`furediCliqueFreePartiteSubgraph`](../../InducedStars/PriorLiterature.lean#L139) | Direct translation | Verified exactly |
| A02 | [`btwHomogeneousSubpartition`](../../InducedStars/PriorLiterature.lean#L86) | Derived consequence | Verified as derived consequence |
| A03 | [`lovaszSzegedyNestedMatrixLimit`](../../InducedStars/PriorLiterature.lean#L571) | Direct translation | Verified exactly |
| A04 | [`existsInducedFreeApproximatingGraphSequence`](../../InducedStars/PriorLiterature.lean#L604) | Derived consequence | Verified as derived consequence |
| A05 | [`bclsvFiniteWeightedAlignment`](../../InducedStars/PriorLiterature.lean#L414) | Combination of published results | Verified as derived consequence |
| A06 | [`bclsvWRandomGraphCutConvergenceInProbability`](../../InducedStars/PriorLiterature.lean#L510) | Combination of published results | Verified as derived consequence |
| A07 | [`bclsvGraphonSequentialCompactness`](../../InducedStars/PriorLiterature.lean#L533) | Derived consequence | Verified as derived consequence |
| A08 | [`bclsvCutConvergence_of_homDensityConvergence`](../../InducedStars/PriorLiterature.lean#L622) | Specialization / weakening | Verified as weaker specialization |
| A09 | [`bclsvHomDensity_eq_of_cutDist_eq_zero`](../../InducedStars/PriorLiterature.lean#L645) | Specialization / weakening | Verified as weaker specialization |
| A10 | [`borgsChayesLovaszCommonPullback_of_homDensity_eq`](../../InducedStars/PriorLiterature.lean#L664) | Specialization / weakening | Verified as weaker specialization |
| A11 | [`hatamiJansonSzegedyLabeledEntropyUpperBound`](../../InducedStars/PriorLiterature.lean#L463) | Derived consequence | Verified as derived consequence |
| A12 | [`hatamiJansonSzegedyEntropyUpperSemicontinuous`](../../InducedStars/PriorLiterature.lean#L485) | Specialization / weakening | Verified as weaker specialization |
| A13 | [`jansonWRandomGraphEntropyAsymptotic`](../../InducedStars/PriorLiterature.lean#L552) | Specialization / weakening | Verified as weaker specialization |
| A14 | [`riordanWarnkePrincipalJanson`](../../InducedStars/PriorLiterature.lean#L438) | Specialization / weakening | Verified as weaker specialization |

## Source and terminology qualifications

The following qualifications are retained from the dossier rather than
resolved by changing the protected Lean source:

- A12 uses HJS **Lemma 3(ii)**. Its displayed inequality is upper
  semicontinuity, despite the printed word “lower”; the source does not
  support the docstring's suggested alternative order convention.
- A13's entropy passage does not explicitly declare the logarithm base.
  The derivation below converts consistently to bits.
- A01 assumes Füredi's actual subgraph theorem. The subsequent local
  stability adapter supplies the finite Turán rounding term; the unrounded
  balancing sentence is not an additional assumption.

## Common normalization dictionary

- Finite graphs are simple, undirected, and labeled by a specified finite
  type; `Fin n` has vertices $0,\ldots,n-1$. `edgeFinset.card` counts an
  unordered edge once. Proper colorings need not use every color.
- A `Graphon` is an $L^1$ almost-everywhere class on $[0,1]^2$, symmetric
  and in $[0,1]$ almost everywhere. It is **not** already a cut-zero class.
  `Graphon.value` is a measurable, pointwise bounded symmetric version of
  that same class. Finite edge products use this version.
- `cutNorm K=\sup_{S,T}|\int_{S\times T}K|` is the rectangle norm.
  `cutDist` takes its infimum over measurable measure-preserving bijections.
  Common-pullback conclusions instead use two possibly noninvertible
  measure-preserving maps. The detailed source arguments do not conflate
  these notions or silently exchange this norm with the operator norm.
- `graphonHomDensity` is the integral of one kernel factor per unordered
  edge. `graphonInducedDensity` also includes a $1-W$ factor per unordered
  nonedge. `graphHomDensity` counts **all** homomorphisms, not just
  embeddings, divided by the number of all vertex maps.
- An $n$-vertex adjacency graphon has edge density $2e(G)/n^2$.
  Enumeration and Shannon-entropy limits here use $\binom n2$ instead.
  These normalizations are not equal at finite $n$.
- `log2 x=\ln(x)/\ln2`. `graphonEntropy=\int h_{\rm nat}(W)/\ln2` and
  finite Shannon entropy both use bits. Natural exponentials in Janson
  retain natural logarithm units. Totalized arithmetic at a zero
  denominator is handled separately whenever it occurs.

# Füredi (2015)

## A01. Füredi's clique-free partite-subgraph theorem

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity:** `InducedStars.PriorLiterature.furediCliqueFreePartiteSubgraph`, [InducedStars/PriorLiterature.lean:139](../../InducedStars/PriorLiterature.lean#L139).

**Verdict:** VERIFIED EXACTLY. **Interface classification:** DIRECT TRANSLATION. Restricting graph labels to `Fin n`, expressing exact deficit additively, and representing an at-most-r-colorable subgraph by a proper `Fin r` coloring are finite encodings of the published statement.

### Published source and locator

Zoltán Füredi, *A proof of the stability of extremal graphs, Simonovits' stability from Szemerédi's regularity*, Journal of Combinatorial Theory, Series B **115** (2015), 66--71; DOI [10.1016/j.jctb.2015.05.001](https://doi.org/10.1016/j.jctb.2015.05.001). Theorem 2 is on printed p. 68, PDF page 3; its proof is on printed p. 69, PDF page 4. The convention `n,p>=1` is recorded on printed p. 67, PDF page 2.

For positive integers n and r, if G is an n-vertex `K_(r+1)`-free graph and `e(G)=t_r(n)-t` with `t>=0`, Theorem 2 supplies an at-most-r-chromatic subgraph H of G with `e(H)>=e(G)-t`. Its proof actually constructs a partition with at most t internal edges, but the axiom needs only the displayed subgraph assertion. The published theorem uses ordinary, not induced, clique containment. The source uses a negated containment sign.

### Lean definitions and exact-deficit conversion

`SimpleGraph.turanNumber n r` is the edge count of the balanced complete r-partite graph. `G.CliqueFree (r+1)` excludes a clique with r+1 vertices. `G.edgeFinset.card` counts each undirected edge once. A `G.Subgraph` is an actual vertex-and-edge subgraph of G. Its graph `S.coe` lives on its own vertex subtype; it is not asserted to span all n vertices. `S.coe.Coloring (Fin r)` is a proper map from those vertices to r indexed colors, so every subgraph edge has differently colored endpoints; empty color classes are permitted.

The hypothesis `e(G)+t=t_r(n)` with natural t is exactly the nonnegative deficit equation. Over integers it is equivalent to the printed `e(G)=t_r(n)-t`; the additive formulation introduces no truncated-subtraction ambiguity. The conclusion's natural subtraction `e(G)-t<=e(S)` is also equivalent to the ordinary real/integer edge lower bound: if `t<=e(G)` subtraction agrees with ordinary subtraction, and if `e(G)<t`, the real lower bound is negative and therefore automatic, while the natural lower bound is zero and also automatic. In both cases the consequence `e(G)-e(S)<=t` follows, since S is a subgraph.

### End-to-end implication and the local stability adapter

1. Apply published Theorem 2 with `p=r`. Positive n and r are explicit Lean hypotheses. Its H becomes a `G.Subgraph`; its at-most-r-colorability gives a proper map into `Fin r`. This proves the exact axiom with no balancing or spanning conclusion added.
2. The theorem `erdosSimonovitsStability` is **locally proved**, not a second external assumption. It sets `t=t_r(n)-e(G)`. Mathlib's clique-free Turán bound supplies `e(G)<=t_r(n)`, hence the exact natural equality `e(G)+t=t_r(n)`.
3. Apply the axiom, extend H by isolated vertices to all vertices of G, and assign color zero to each added vertex. The private `furediSpanningColoring` implements this extension using `r>0`; `furediSpanning_edgeFinset_card` proves that the extension does not change its edge count.
4. Its r color fibers are disjoint and cover all vertices, including empty fibers. Every G-edge internal to a color fiber is absent from H. Their disjoint union has at most `e(G)-e(H)<=t` edges. This is proved by `DenseGraph.sum_internal_edges_coloringParts_le`.
5. Put `a_i=|P_i|` and `C(a)=sum_(i<j) a_i a_j`. Proper colorability gives `C(a)>=e(H)>=t_r(n)-2t`. The exact identity is

   \[
   \sum_i(a_i-n/r)^2=n^2-\frac{n^2}{r}-2C(a).
   \]

   Writing `b=n mod r`, the finite Turán formula is

   \[
   t_r(n)=\left(1-\frac1r\right)\frac{n^2}{2}-\frac{b(r-b)}{2r}.
   \]

   Since `0<=b<r`, `b(r-b)/r<=r/4`. Consequently

   \[
   \sum_i(a_i-n/r)^2\leq 4t+\frac r4.
   \]

   These are local theorems `DenseGraph.turanNumber_rounding_le`, `sum_sq_sub_average_eq`, and `sum_sq_sub_average_le_of_turan_deficit`, not added external facts. This distinction matters: the unnumbered balancing sentence after Corollary 3 on p. 68 prints a bound without the rounding term, which fails for a balanced Turán graph when r does not divide n. The Lean axiom does not assume that sentence.
6. The adapter chooses

   \[
   \delta=\min\{\varepsilon/2,\varepsilon^2/16\},\qquad
   n_0=\left\lceil r/\varepsilon^2\right\rceil+1.
   \]

   From the near-extremal hypothesis, `t<=delta n^2`. For `n>=n0`, `n>=1` and `r<=epsilon^2 n^2`. Thus internal edges are at most `epsilon n^2`, and each squared part deviation is at most `4t+r/4<=epsilon^2 n^2/2<=epsilon^2 n^2`; taking nonnegative square roots gives the required `|a_i-n/r|<=epsilon n`. The finite-type transport `erdosSimonovitsStabilityFiniteOfFin` is also proved locally.

### No-stronger-than-source checklist

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | Positive n,r; ordinary clique-free; exact nonnegative deficit. |
| Conclusion | PASS | Actual properly colored subgraph; no balance or spanning field assumed. |
| Quantifier order | PASS | Finite assertion for every admissible n,r,t,G. |
| Constants/factors | PASS | Loss at most t; equivalent retained lower bound `t_r(n)-2t`. |
| Normalization | PASS | Unordered edge cardinalities throughout. |
| Label convention | PASS | `Fin n` is only a labeling of an n-vertex graph. |
| Strictness | PASS | Non-strict deficit and retained-edge inequalities match. |
| Measure equivalence | PASS | Not applicable: entirely finite. |

# Böttcher--Taraz--Würfl (2012)

## A02. Böttcher--Taraz--Würfl homogeneous subpartition

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity:** `InducedStars.PriorLiterature.btwHomogeneousSubpartition`, [InducedStars/PriorLiterature.lean:86](../../InducedStars/PriorLiterature.lean#L86).

**Verdict:** VERIFIED AS DERIVED CONSEQUENCE. **Interface classification:** DERIVED CONSEQUENCE. This classification accounts explicitly for the harmless extensions to all natural `q` and all positive real tolerances; it is not a claim that the axiom assumes an additional embedding or type theorem.

### Published source and locator

Julia Böttcher, Anusch Taraz, and Andreas Würfl, *Perfect Graphs of Fixed Density: Counting and Homogeneous Sets*, Combinatorics, Probability and Computing **21** (2012), 661--682; DOI [10.1017/S0963548312000181](https://doi.org/10.1017/S0963548312000181). Lemma 2.5 and the immediately preceding subpartition definition are on printed p. 668, PDF page 8. The density and regular-pair definitions are in section 2.2, printed p. 666, PDF page 6.

The published lemma says that for every number of parts and regularity tolerance there is a positive constant mu such that every graph with at least `1/mu` vertices has either a sparse or a dense `(mu, epsilon, q)`-subpartition. The surrounding regularity definitions place their tolerances in `[0,1]`; only strictly positive tolerances are needed here. The published lemma gives a subpartition, not a covering partition, and does not require equal part sizes.

### Exact mathematical meaning of the Lean definitions

For disjoint finite vertex sets A and B,

\[
d_G(A,B)=\frac{e_G(A,B)}{|A||B|}.
\]

An edge between the two disjoint sets is counted once. This is neither an ordered-pair factor-two density nor the whole-graph normalization by `choose(n,2)`. `IsRegularPair G epsilon A B` says that every `A' subset A`, `B' subset B` satisfying `|A'| >= epsilon |A|` and `|B'| >= epsilon |B|` has density within **at most** epsilon of that of `(A,B)`. This is the same non-strict tolerance and the same non-strict size cutoff as the printed definition.

`HomogeneousSubpartition G parent mu epsilon q` contains:

- a family `parts : Fin q -> Finset V`;
- containment of every part in `parent`;
- pairwise disjointness;
- `mu |parent| <= |parts i|` for every i;
- epsilon-regularity of every pair of distinct parts.

`IsSparse` means all distinct part-pair densities are **strictly below** `1/2`; `IsDense` means they are **at least** `1/2`. In the axiom `parent=univ`, so the lower size bound is precisely `mu n`, not `mu` times a chosen cluster. If `mu>0` and `n>=1/mu`, all existing parts are nonempty, since `mu n>=1`. Densities on empty pairs therefore do not intervene.

`DenseGraph.HomogeneousSubpartitionInput.homogeneousSubpartition` is exactly this same quantified proposition; it is a theorem-valued field, not another axiom. `InducedStars.PriorInstances.homogeneousSubpartitionInput` fills that field from the one published input. Explicitly its quantifier order is: for every natural q and positive epsilon, there is one mu>0, after which **all** finite vertex types and graphs of size at least `1/mu` are covered. No graph-dependent mu is allowed.

### End-to-end implication

1. For `q>=2` and `0<epsilon<=1`, apply published Lemma 2.5. Its definition supplies exactly the five fields above and its sparse/dense alternative uses exactly the same strict/non-strict split at `1/2`.
2. Finite vertex labels make no difference: enumerate an arbitrary finite vertex set, apply the published finite-graph assertion, and transport subsets, adjacency and cardinalities back along the bijection. The constant mu depends only on q and epsilon, not on the enumeration or graph.
3. To avoid extending the source's standing tolerance convention silently, for arbitrary `epsilon>0` one may first use `epsilon0=min(epsilon,1/2)`. An epsilon0-regular pair is epsilon-regular: an epsilon-large subpair is also epsilon0-large and its error is at most `epsilon0<=epsilon`. The sparse/dense density test is unchanged. The project proves this monotonicity as `IsRegularPair.mono`; the published-to-axiom extension itself is accepted within the axiom rather than separately wrapped in Lean.
4. For `q=0`, choose `mu=1` and the empty indexed family. Every field and both pairwise alternatives are vacuous. For `q=1`, choose `mu=1` and the sole part equal to the whole vertex set. Its size bound is equality and pairwise regularity and homogeneity are vacuous. These cases therefore do not require reading an implicit positive-integer convention as including zero.
5. No parent-cluster enhancement has been inserted into the assumption. The local theorem `btwHomogeneousSubpartitionInside` applies the axiom to the induced graph on a parent subtype and transports the result back. The reusable counterpart is `DenseGraph.HomogeneousSubpartitionInput.inside`. The induced embedding and enhanced type constructions are further local proofs, not additional conclusions supplied by Lemma 2.5.

### No-stronger-than-source checklist

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | Positive epsilon; large-graph threshold; trivial q=0,1 and tolerance extension explained. |
| Conclusion | PASS | Only homogeneous subpartition, no covering, equipartition, embedding, or type conclusion. |
| Quantifier order | PASS | One mu for fixed q and epsilon before graph and vertex labels. |
| Constants/factors | PASS | Same mu, inverse-size threshold and density threshold 1/2. |
| Normalization | PASS | Once-counted cross edges divided by product of set sizes. |
| Label convention | PASS | A graph property transported by any finite bijection. |
| Strictness | PASS | Sparse `<1/2`, dense `>=1/2`, regularity error `<=epsilon`. |
| Measure equivalence | PASS | Not applicable: entirely finite. |

# Lovász--Szegedy (2006)

**Published source.** László Lovász and Balázs Szegedy, *Limits of dense graph
sequences*, Journal of Combinatorial Theory, Series B **96** (2006),
933--957. DOI: [10.1016/j.jctb.2006.05.002](https://doi.org/10.1016/j.jctb.2006.05.002).
Printed page 933 is PDF page 1.

## A03. Nested density-matrix limit

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.lovaszSzegedyNestedMatrixLimit`,
[InducedStars/PriorLiterature.lean:571](../../InducedStars/PriorLiterature.lean#L571). Its exact declaration and the full `NestedDensityMatrices`
record appear in the appendices.

**Published statement.** Lemma 5.2, printed pp. 949--950 (PDF pp. 17--18),
with proof through p. 951 (PDF p. 19), assumes positive integers $k_m$ and
matrices satisfying Lemma 5.1(i)--(ii), printed pp. 948--949 (PDF pp. 16--17).
Each $Q_m$ is a symmetric $k_m\times k_m$ matrix in $[0,1]$; whenever $i<j$,
$k_i$ divides $k_j$ and $Q_i$ is obtained by averaging consecutive square
blocks of $Q_j$. There is a symmetric measurable $W:[0,1]^2\to[0,1]$ such
that $W_{Q_m}\to W$ almost everywhere and
$$
 (Q_m)_{ij}=k_m^2\int_{(i-1)/k_m}^{i/k_m}
                         \int_{(j-1)/k_m}^{j/k_m}W(x,y)\,dy\,dx.
$$
No requirement that $k_m\to\infty$ is added. The source proof uses the
bounded martingale of successive matrix values and dominated convergence
on each fixed coarse block.

**Lean mathematical restatement and definitions.** `NestedDensityMatrices`
has a positive natural size at every index, symmetric real entries in
$[0,1]$, divisibility at all ordered levels, and exact block-average
compatibility. `matrixBlockAverage` divides the sum of the fine entries by
$(k_j/k_i)^2$; `refinementIndex` is the zero-based consecutive-block index.
`nestedMatrixGraphon Q m` is the equal-cell step graphon with those entries,
including diagonal cells. `equalCell i` is the interval from $i/k_m$ to
$(i+1)/k_m$ with an endpoint convention irrelevant to integration. Lean
asks for the same almost-everywhere convergence and the same $k_m^2$ times
block integral. The integral is over product probability Lebesgue measure,
not a sum over unordered cells and not normalized by $\binom{k_m}{2}$.

**Translation/adaptation argument.** Shift the source indices by one to
match Lean's indices starting at zero. The all-level Lean compatibility
implies the source strict-level condition. Apply Lemma 5.2. Regard its
bounded symmetric measurable function as an integrable function and take
its $L^1$ equivalence class, which is a Lean `Graphon`. The local theorem
`matrixGraphon_ae_eq_kernel` identifies each Lean step graphon with the
source step function almost everywhere. Intersect these full-measure sets
over the countably many levels, and also use `Graphon.coe_ofFun` for the
limit representative. On that common full-measure set the asserted
convergence is unchanged. Replacing interval endpoints changes no block
integral; replacing the representative on a null set changes no integral.
Thus the published identity gives the exact Lean block identity, with no
missing scaling factor. This representation conversion is accepted inside
the axiom, not a separately kernel-proved source translation. The further
$L^1$ convergence conclusion is genuinely local:
`lovaszSzegedyNestedMatrixLimit_l1` invokes the proved dominated-convergence
lemma `graphonL1Dist_tendsto_zero_of_ae`.

**Interface classification:** DIRECT TRANSLATION.

**Audit finding:** VERIFIED EXACTLY, up to the explicitly described
representation and indexing conventions.

**No-stronger checklist.** Hypotheses PASS; conclusion PASS; quantifier order
PASS; constants/factors PASS; normalizations PASS; labeling PASS (matrix
indices only); strict/non-strict PASS; measure-theoretic equivalence PASS.

## A04. One induced-free deterministic approximating sequence

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.existsInducedFreeApproximatingGraphSequence`,
[InducedStars/PriorLiterature.lean:604](../../InducedStars/PriorLiterature.lean#L604). Exact declaration: appendix.

**Published statement.** Section 2.6 and Corollary 2.6 on printed p. 941
(PDF p. 9) define $G(N,W)$ by independent uniform latent vertices and,
conditional on them, independent unordered edges of probabilities
$W(X_i,X_j)$. The entire sequence converges to $W$ with probability one:
for every finite simple $H$, $t(H,G(N,W))\to t(H,W)$ simultaneously.
The printed proof explicitly takes the countable intersection over all
finite graphs after applying the summable concentration bounds of
Theorem 2.5 and Borel--Cantelli. The definition of induced densities is
also inspected in the source's Sections 2.4--2.5.

**Lean mathematical restatement and definitions.** Fix any finite simple
$F$ and graphon $W$ with $t_{\mathrm{ind}}(F,W)=0$. There is a deterministic
sequence $G_n$ on exactly $n+1$ labeled vertices such that every $G_n$ is
induced-$F$-free and, for every finite simple $H$, its ordinary homomorphism
density converges to $t(H,W)$. `Regularity.InducedEmbeds` is strong/induced
graph embedding, not ordinary containment. `graphHomDensity H G` is the
number of all homomorphisms divided by $|V(G)|^{|V(H)|}$; maps need not be
injective. `graphonHomDensity` integrates the product of one $W$ factor per
unordered edge. `graphonInducedDensity` additionally multiplies one
$1-W$ factor per unordered nonedge, with distinct endpoints. There is no
automorphism factor. Both integrals use independent uniform vertex
coordinates and the canonical bounded symmetric representative `W.value`.

**Translation/adaptation argument.**

1. On a common probability space take countably many independent uniform
   latent variables $X_1,X_2,\ldots$ and independent uniform edge coins
   $U_{ij}$ for $i<j$. This realizes every finite $G(N,W)$ with exactly the
   source distribution. The published summable bounds and corollary apply
   to this coupling; independence between different orders is unnecessary.
2. Fix $N$ and an injection $\iota:V(F)\hookrightarrow[N]$. Conditional
   independence of the distinct unordered edge coins shows that the
   probability of the required complete induced pattern is exactly
   $t_{\mathrm{ind}}(F,W)=0$. This is true even when latent values coincide:
   the random vertices remain distinct labels, and the integral is the
   exact distributional computation. If $N<|V(F)|$, no injection exists.
3. There are finitely many injections for each $N$. The event that $G(N,W)$
   contains an induced copy is a finite union of null events, hence null.
   Taking the intersection of the complementary full-measure events over
   all positive integers $N$ gives a probability-one event on which
   **every** sampled graph is induced-$F$-free.
4. Intersect that event with the probability-one simultaneous convergence
   event from Corollary 2.6. The intersection still has probability one
   and is nonempty. Choose one outcome. This choice is the deterministic
   sequence; it is not a choice made separately for each test graph $H$.
5. Set $G_n=G(n+1,W)$ on that outcome. Dropping the zero-order term and
   shifting indices leaves all limits unchanged and supplies exactly
   `Fin (n + 1)`. Finite label transport is a bijection and changes neither
   induced containment nor the normalized homomorphism count. If $F$ has
   zero or one vertex, its induced density is one, so the premise is
   impossible and no exceptional zero-size construction is required.

The selection/countable-intersection argument is accepted inside this
external interface, not separately proved by Lean. Cut convergence is
**not** part of this axiom: `existsInducedFreeApproximatingGraphSequence_cut`
adds it locally using the BCLSV convergence input and the exact finite
adjacency-graphon density identity.

**Interface classification:** DERIVED CONSEQUENCE.

**Audit finding:** VERIFIED AS DERIVED CONSEQUENCE.

**No-stronger checklist.** Hypotheses PASS; conclusion PASS; quantifier order
PASS (one sequence works for all $H$); constants/factors PASS; normalizations
PASS; labeling PASS; strict/non-strict PASS; measure-theoretic equivalence PASS.

# Borgs--Chayes--Lovász--Sós--Vesztergombi (2008)

## Shared source and conventions for the five BCLSV inputs

**Published source.** Christian Borgs, Jennifer T. Chayes, László
Lovász, Vera T. Sós, and Katalin Vesztergombi, *Convergent sequences of dense
graphs I: Subgraph frequencies, metric properties and testing*, Advances in
Mathematics **219** (2008), 1801–1851,
DOI [10.1016/j.aim.2008.07.008](https://doi.org/10.1016/j.aim.2008.07.008).

PDF page 1 is printed page 1801.

All five declarations are in [PriorLiterature.lean](../../InducedStars/PriorLiterature.lean);
their exact declarations appear in the declaration appendix. Their conclusions
are assumptions, not locally proved consequences of a formally imported BCLSV theorem.

The following convention bridge is needed by all five audits, rather than
being an optional identification of similar-looking metrics.

1. `InducedStars.Graphon` is a symmetric, almost-everywhere `[0,1]`-valued
   element of real `L¹([0,1]²)`. It is a quotient only by equality almost
   everywhere, **not** by cut distance zero. The canonical `Graphon.value`
   is obtained by symmetrizing and clipping a measurable representative.
   It is pointwise symmetric, pointwise `[0,1]`-valued, and equals the
   original representative almost everywhere (`Graphon.value_ae_eq`).
   It is therefore a graphon in the source's `W_[0,1]`, defined on printed
   p. 1811/PDF 11.
2. `cutNorm K` is `sup_{S,T} |∫_(S×T) K|` over measurable rectangles, with
   no factor 2 or 4. This is source Eq. (3.3), printed p. 1812/PDF 12,
   **not** the different `L∞ → L¹` operator norm in Eq. (3.4).
3. `cutDist U W` is the infimum of `||U^φ-W||_square` over
   measure-preserving measurable **bijections** of `[0,1]` with measurable
   inverse. The source first defines distance by couplings on printed
   p. 1815/PDF 15. Lemma 3.5, Eq. (3.15), on that page identifies it with
   the bijection infimum. Moving the bijection from one kernel to the other
   is legitimate by taking its measure-preserving inverse.
4. The Lean interval carries its Borel measurable structure with volume,
   while the source allows Lebesgue-measurable cuts and relabelings. This
   does not create a stronger metric here. Every Lebesgue cut differs
   from a Borel cut by a null set, so the cut norms agree. A Borel
   measure-preserving bijection with Borel inverse extends to the
   completed sigma algebra. Conversely, source Eq. (3.16), printed
   p. 1816/PDF 16, obtains the same infimum using finite interval
   permutations, which are Borel measure-preserving bijections after
   the harmless endpoint convention is fixed. Thus restricting the
   infimum to Lean's relabelings leaves its value unchanged.
5. `graphonHomDensity F W` is
   `∫_[0,1]^f ∏_{ij∈E(F)} W.value(x_i,x_j) dx`, with each unordered edge
   included once and no factorial or edge-density prefactor. It is exactly
   source Eq. (3.1), printed p. 1811/PDF 11. Relabeling the finite vertex
   set identifies every finite simple graph with one on `Fin f`.
   Changing `W` on a square-null set changes no integral: each distinct
   coordinate pair has product-uniform distribution, and the union over
   the finitely many edges is null. An edgeless graph, including the
   empty graph, has density 1 in both conventions.
6. `graphGraphon G` is the equal-cell adjacency graphon, with cells of
   measure `1/n`; each off-diagonal matrix entry is the adjacency
   indicator and diagonal blocks have value zero. This is the source
   construction on printed p. 1812/PDF 12. In particular its edge
   density is `2e(G)/n²`, not `e(G)/choose(n,2)`. None of the five
   axioms silently substitutes the latter normalization. They involve
   no entropy or logarithm convention.

These bridges are ordinary mathematical deductions accepted inside the
external interfaces. The repository locally proves the representative
facts and numerous finite identities, but it does not separately formalize
BCLSV Lemma 3.5 or the published coupling-to-bijection equivalence.

## A05. Finite weighted alignment

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Audit finding: VERIFIED AS DERIVED CONSEQUENCE.**

**Lean identity.**
`InducedStars.PriorLiterature.bclsvFiniteWeightedAlignment`,
[InducedStars/PriorLiterature.lean:414](../../InducedStars/PriorLiterature.lean#L414).
Its declaration is `axiom bclsvFiniteWeightedAlignment :
DenseGraph.FiniteWeightedAlignmentInput`.

**Expanded assumption.** `DenseGraph.FiniteWeightedAlignmentInput.align`,
in `DenseGraph/Graphon/Inputs.lean`, asserts

\[
\forall\eta>0\;\exists\tau>0\;\forall n\in\mathbb N\;\forall A,B,
\quad \delta_\square(W_A,W_B)<\tau
\Longrightarrow \exists\pi\in S_n:\ d_\square(A,B^\pi)<\eta.
\]

Here `A,B : FiniteWeightedGraph (Fin n)` are symmetric matrices with
entries in `[0,1]`, **including arbitrary diagonal entries**; the type does
not require zero diagonal. Their graphons have equal cells of measure
`1/n`. `B.permute π` has entry `B_(π(i),π(j))`.

`FiniteWeightedGraph.finiteLabeledCutDist A B` is

\[
d_\square(A,B)=\frac1{n^2}
 \max_{S,T\subseteq[n]}
 \left|\sum_{i\in S}\sum_{j\in T}(A_{ij}-B_{ij})\right|.
\]

The pair sum is ordered: when `S` and `T` overlap, a non-loop edge can
contribute in both orientations. Loops contribute once when in the
rectangle. This is not unordered edge counting or edit distance. Lean
defines division by zero as zero, so for `n=0` this discrepancy is zero.

**Published statement and locator.** Theorem 2.3, printed p. 1807/PDF 7,
states that weighted graphs with edge weights in `[-1,1]` on the same
number of unweighted nodes satisfy

\[
\delta_\square(A,B)\leq\widehat\delta_\square(A,B)
 \leq32\,\delta_\square(A,B)^{1/67}.
\]

The definitions are Eq. (2.1), printed p. 1804/PDF 4; labeled distance
Eq. (2.4), permutation distance Eq. (2.6), printed p. 1806/PDF 6; and
fractional distance Definition 2.2/Eq. (2.7), printed p. 1807/PDF 7.
Weighted graphs explicitly allow loops on p. 1804. Eq. (3.13), printed
p. 1815/PDF 15, identifies finite fractional distance with the distance
of the corresponding step graphons. Lemma 3.5/Eqs. (3.15)–(3.16) supplies
the graphon-distance convention bridge above. The proof of Theorem 2.3
is on printed pp. 1831–1832/PDF 31–32. Its preliminary Lemma 5.1 has an
`n^6` loss; **that is not the theorem used here**.

**Classification: COMBINATION OF PUBLISHED RESULTS.** It combines the
uniform quantitative theorem with the finite/step-graphon and
coupling/bijection identities, and discards the quantitative modulus.

**End-to-end implication.** For a given `η>0`, take

\[
\tau=(\eta/64)^{67}>0.
\]

For `n>0`, give every vertex node weight 1. The entries `[0,1]` lie in
the allowed `[-1,1]`; arbitrary diagonal entries are allowed. Eq. (3.13)
and Lemma 3.5 identify the hypothesis's distance with the fractional
distance in Theorem 2.3. Thus

\[
\widehat\delta_\square(A,B)
 \leq32\delta_\square(A,B)^{1/67}
 <32\tau^{1/67}=\eta/2<\eta.
\]

There are finitely many permutations, so the minimum defining
`widehat δ` is attained. A permutation attaining it is the required
`π`; using its inverse if needed matches Lean's direction of reindexing.
For `n=0`, use the unique permutation and zero discrepancy. Consequently
the **same τ works for every n**, including the empty case. There is no
unmentioned lower bound on `n`, no `τ(n)`, and no appeal to asymptotic
sampling alone. This entire published implication, not a local proof of
Theorem 2.3, is encapsulated by the axiom.

**No stronger than source.**

| Check | Verdict | Reason |
|---|---|---|
| Hypotheses | PASS | `[0,1]` is a subrange of `[-1,1]`; equal unit node weights; loops allowed. |
| Conclusion | PASS | Only existence at prescribed error, weaker than the quantitative bound. |
| Quantifier order | PASS | Explicit `τ=(η/64)^67` independent of both matrices and `n`. |
| Constants/factors | PASS | Published `32` and `1/67`; slack gives a strict inequality. |
| Normalization | PASS | Ordered rectangle sum divided by `n²`, not `choose(n,2)`. |
| Labeling | PASS | A finite permutation attains the published overlay minimum. |
| Strictness | PASS | Strict distance hypothesis and positive slack imply strict conclusion. |
| Measure equivalence | PASS | Eq. (3.13) and Lemma 3.5; a.e. step representatives do not change norms. |

## A06. W-random cut convergence in probability

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Audit finding: VERIFIED AS DERIVED CONSEQUENCE.**

**Lean identity.**
`InducedStars.PriorLiterature.bclsvWRandomGraphCutConvergenceInProbability`,
[InducedStars/PriorLiterature.lean:510](../../InducedStars/PriorLiterature.lean#L510).

**Exact mathematical content.** For every graphon `W` and `ε>0`,

\[
\mathbb P\{\varepsilon\leq
 \delta_\square(W_{G(n,W)},W)\}\longrightarrow0.
\]

`wRandomConditionalWeight W x G` is the product of `W.value(x_i,x_j)`
over the unordered edges of the labeled simple graph `G`, times the
product of `1-W.value(x_i,x_j)` over its unordered nonedges. There are
no loop trials. `wRandomGraphMass W G` integrates this product over
independent uniform latent coordinates, and
`wRandomGraphEventProbability W A` sums that mass over `G∈A`. It is an
actual normalized finite labeled-graph probability law, not uniform
counting on a graph family. The local normalizing result is
`wRandomGraphMass_sum` in `InducedStars/FiniteModels/WRandom.lean`.

**Published statement and locator.** Theorem 4.5(b), printed
p. 1821/PDF 21, says the sequence `G(n,W)` converges almost surely to
`W` for `W∈W_[0,1]`. Section 4.4, printed pp. 1820–1821/PDF 20–21,
defines independent uniform latent points and independent Bernoulli
edges conditional on them. Theorem 3.8's final equivalence, printed
p. 1817/PDF 17, identifies homomorphism-density convergence to `W`
with cut convergence to `W`. Lemma 3.5 gives the metric bridge.

**Classification: COMBINATION OF PUBLISHED RESULTS.** The published
almost-sure sampling theorem, the convergence equivalence, and the
standard bounded-convergence implication yield this weaker probability
statement.

**End-to-end implication.** Apply Theorem 4.5(b) to `W.value`. Its law
at each `n` equals the finite Lean law by conditional independence and
integration of the displayed product. Values on null sets do not alter
that law. Almost-sure convergence is in finite simple-graph densities;
Theorem 3.8 gives almost-sure cut convergence. On each outcome in that
probability-one event, the indicator of
`{ε≤δ_square(W_Gn,W)}` eventually vanishes: convergence to zero gives
`δ_square<ε` eventually. The indicators lie in `[0,1]`, so bounded
convergence gives their expectations tending to zero. Those expectations
are exactly the Lean event probabilities. No choice of coupling across
different `n` affects these marginal probabilities. The Lean index
`n=0` and the source's initial positive index differ only by finitely
many terms and do not affect the `atTop` limit. No convergence rate,
uniformity over `W`, or almost-sure conclusion is assumed in Lean.

**No stronger than source.**

| Check | Verdict | Reason |
|---|---|---|
| Hypotheses | PASS | Symmetric measurable `[0,1]` kernel, positive ε. |
| Conclusion | PASS | In-probability tail convergence is weaker than almost sure convergence. |
| Quantifier order | PASS | `W,ε` fixed before the limit; no uniform rate claimed. |
| Constants/factors | PASS | No quantitative constants introduced. |
| Normalization | PASS | Equal-cell adjacency graphon; unordered Bernoulli trials once each. |
| Labeling | PASS | Source nodes `1,…,n` and Lean `Fin n` are bijectively identified. |
| Strictness | PASS | `ε≤distance` is the complement of the open ε-ball. |
| Measure equivalence | PASS | Canonical representative has the same law; Lemma 3.5 matches metrics. |

## A07. Graphon sequential compactness

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Audit finding: VERIFIED AS DERIVED CONSEQUENCE.**

**Lean identity.**
`InducedStars.PriorLiterature.bclsvGraphonSequentialCompactness`,
[InducedStars/PriorLiterature.lean:533](../../InducedStars/PriorLiterature.lean#L533).

**Exact mathematical content.** For every sequence of graphons `(W_n)`,
there exist a strictly increasing `σ:ℕ→ℕ` and a graphon `U` such that
`δ_square(W_(σ(n)),U)→0`. `PriorInstances.sequentialCompactnessInput`
packages this same proposition in
`DenseGraph.SequentialCompactnessInput.compact_subsequence`; it adds
no new conclusion.

**Published statement and locator.** Proposition 3.6, printed
p. 1816/PDF 16: for a fixed finite interval `I`, the graphons with
values in `I`, identified at cut distance zero, form a compact metric
space. The preceding paragraph explicitly distinguishes this quotient
from pointwise or a.e. equality. Lemma 3.5 on printed pp. 1815–1816
identifies the distance conventions.

**Classification: DERIVED CONSEQUENCE.** The source gives compactness
of a metric quotient; Lean asks for a subsequence and one representative
of its limit.

**End-to-end implication.** Take `I=[0,1]`. Map each Lean graphon's
canonical representative into the source quotient. A compact metric
space is sequentially compact, so its sequence of quotient classes has
a subsequence indexed by a strictly increasing function and converging
to a quotient class. By the definition of that quotient the limiting
class contains some symmetric measurable `[0,1]` graphon `U_0` on
`[0,1]`. Its boundedness makes it integrable. Taking its `L¹` class,
or using the construction `Graphon.ofFun`, produces a Lean `Graphon U`.
The quotient metric between each subsequence term and the limit class
is, by definition and Lemma 3.5, exactly Lean's `cutDist` to `U`.
Thus the required distances tend to zero. This does **not** assert
convergence in `L¹`, equality of representatives, or a sequence of
aligning bijections attaining each infimum. Representative selection is
ordinary classical choice, not an additional mathematical assumption.
The compactness-to-sequence deduction is accepted inside this axiom.

**No stronger than source.**

| Check | Verdict | Reason |
|---|---|---|
| Hypotheses | PASS | The fixed interval is `[0,1]`. |
| Conclusion | PASS | A representative of a subsequential quotient limit, not stronger convergence. |
| Quantifier order | PASS | `σ,U` may depend on the entire input sequence. |
| Constants/factors | PASS | None. |
| Normalization | PASS | The same rectangle cut distance. |
| Labeling | PASS | Graphon representatives, with no finite-label assertion. |
| Strictness | PASS | Ordinary real convergence to zero. |
| Measure equivalence | PASS | Quotient limit lifted to an `L¹` representative; no quotient confusion. |

## A08. Homomorphism convergence implies cut convergence

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Audit finding: VERIFIED AS WEAKER SPECIALIZATION.**

**Lean identity.**
`InducedStars.PriorLiterature.bclsvCutConvergence_of_homDensityConvergence`,
[InducedStars/PriorLiterature.lean:622](../../InducedStars/PriorLiterature.lean#L622).

**Exact mathematical content.** Given a graphon sequence `(W_n)` and a
graphon `W`, if `t(H,W_n)→t(H,W)` for every finite simple graph `H` on
every `Fin h`, then `δ_square(W_n,W)→0`.

**Published statement and locator.** Theorem 3.8, final sentence,
printed p. 1817/PDF 17, states that convergence of every finite
simple-graph homomorphism density to those of a specified graphon `W`
is equivalent to cut-distance convergence to `W`, for a sequence in a
fixed finite interval. Eq. (3.1), printed p. 1811/PDF 11, defines
the densities. Lemma 3.5 identifies the cut metric.

**Classification: SPECIALIZATION / WEAKENING.** Only one direction of
the published equivalence and the range `[0,1]` are retained.

**End-to-end implication.** Regard all canonical representatives as
members of the source's `W_[0,1]`. Every finite simple graph can be
relabeled onto `Fin h`; the integral is unchanged by permuting its
coordinates. Therefore the Lean hypothesis is exactly the all-finite-
simple-graphs hypothesis. Apply the forward direction of the final
equivalence in Theorem 3.8. Canonical representative changes are a.e.
changes and preserve all the densities and cut distances. Lemma 3.5
identifies its conclusion with the Lean real-valued cut distance.
No common relabeling, injective-density approximation, or rate of
convergence is needed. The generic theorem is axiomatized; the separate
finite-graph adapter is locally proved, as explained below.

**No stronger than source.**

| Check | Verdict | Reason |
|---|---|---|
| Hypotheses | PASS | A uniformly bounded `[0,1]` sequence and all finite simple tests. |
| Conclusion | PASS | One direction only. |
| Quantifier order | PASS | One fixed target W and convergence for each test graph separately. |
| Constants/factors | PASS | No error rate or constants claimed. |
| Normalization | PASS | Eq. (3.1) is the exact edge-product integral. |
| Labeling | PASS | Every finite simple graph is isomorphic to one on `Fin h`. |
| Strictness | PASS | Same limiting statement. |
| Measure equivalence | PASS | a.e. representatives and Lemma 3.5 preserve the quantities. |

## A09. Cut-zero homomorphism-density equality

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Audit finding: VERIFIED AS WEAKER SPECIALIZATION.**

**Lean identity.**
`InducedStars.PriorLiterature.bclsvHomDensity_eq_of_cutDist_eq_zero`,
[InducedStars/PriorLiterature.lean:645](../../InducedStars/PriorLiterature.lean#L645).

**Exact mathematical content.** For graphons `U,W`,
`δ_square(U,W)=0` implies `t(F,U)=t(F,W)` for every finite simple
graph `F`. `DenseGraph.CutZeroHomDensityInput.homDensity_eq` has exactly
this theorem-valued field, and
`PriorInstances.cutZeroHomDensityInput` packages the axiom into it.

**Published statement and locator.** Corollary 3.10, printed
p. 1817/PDF 17, says cut distance zero is equivalent to equality of
all finite simple-graph homomorphism densities. This is a more direct
published locator than the existing docstring's derivation from
Theorem 3.8 on the same page. Both verify the interface. Theorem 3.7(a),
printed p. 1816/PDF 16, additionally gives the quantitative bound
`|t(F,U)-t(F,W)|≤4m C^(m-1) δ_square(U,W)` for `m` edges and
`C=max(1,||U||∞,||W||∞)`.

**Classification: SPECIALIZATION / WEAKENING.** It is the forward
direction of Corollary 3.10, restricted to `[0,1]` graphons.

**End-to-end implication.** Apply Corollary 3.10 to `U.value,W.value`.
The convention bridge identifies its zero-distance hypothesis with
Lean's; Eq. (3.1) identifies each conclusion. Alternatively, to check
the exact route cited by the docstring, set `W_n=U` constantly. The
distances to `W` are constantly zero, hence tend to zero. The reverse
direction of Theorem 3.8 says the constant density sequence
`t(F,U)` tends to `t(F,W)`; uniqueness of real limits gives equality.
These are mathematical verifications of the axiom, not local proofs
installed in the project. No equality almost everywhere of `U` and
`W`, or bijection making them equal, is asserted.

**No stronger than source.**

| Check | Verdict | Reason |
|---|---|---|
| Hypotheses | PASS | Source accepts bounded graphons; Lean uses `[0,1]`. |
| Conclusion | PASS | Only the forward implication of the equivalence. |
| Quantifier order | PASS | Every finite test graph for the fixed cut-zero pair. |
| Constants/factors | PASS | Equality, with no lost normalization. |
| Normalization | PASS | Exact Eq. (3.1) density. |
| Labeling | PASS | `Fin f` is a choice of labels for the same finite tests. |
| Strictness | PASS | Exact cut distance zero, not merely a positive tolerance. |
| Measure equivalence | PASS | Only density equality, not a.e. equality or invertible equivalence. |

## BCLSV audit conclusion

The inherited dossier records all five interfaces as justified by the published source.
It records no source mismatch. In particular the potentially dangerous
uniform alignment quantifier is valid with the explicit modulus above.
This is the dossier's source-to-interface assessment, **not** a Lean proof
of the implications: all five remain external assumptions.

# Borgs--Chayes--Lovász (2010)

**Published source.** Christian Borgs, Jennifer Chayes, and László Lovász,
*Moments of Two-Variable Functions and the Uniqueness of Graph Limits*,
Geometric and Functional Analysis **19** (2010), 1597--1619.
DOI: [10.1007/s00039-010-0044-0](https://doi.org/10.1007/s00039-010-0044-0).
Printed page 1597 is PDF page 1.

## A10. Common pullbacks, not bijective equivalence

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.borgsChayesLovaszCommonPullback_of_homDensity_eq`,
[InducedStars/PriorLiterature.lean:664](../../InducedStars/PriorLiterature.lean#L664). Exact declaration and the equivalent
`DenseGraph.CommonPullbackInput.commonPullback` field are in the appendices.

**Published statement.** Corollary 2.2, printed p. 1601 (PDF p. 5), for bounded
symmetric measurable real functions $U,W$ on $[0,1]^2$, makes these assertions
equivalent: (a) equality of $t(F,U)$ and $t(F,W)$ for every finite simple
graph $F$; (d) there are two measure-preserving maps from $[0,1]$ into
$[0,1]$ whose pullbacks of the two functions agree almost everywhere.
These maps are **not required to be bijections**. The paper's example on
the same page explains why weak equivalence need not give isomorphism.
The hypotheses here do not require the almost-twin-free condition of the
different statement Theorem 2.1(i).

**Lean mathematical restatement and definitions.** Equality of all finite
simple-graph homomorphism densities of two $[0,1]$-valued Lean graphons
implies existence of measure-preserving $\phi,\psi:[0,1]\to[0,1]$ with
$$
 U^{\mathrm{value}}(\phi(x),\phi(y))
   =W^{\mathrm{value}}(\psi(x),\psi(y))
 \quad\text{for almost every }(x,y).
$$
`MeasurePreserving` requires measurability and equality of the pushforward
probability measure to normalized interval volume. `unitSquareMeasure` is
product volume. `Graphon` is an $L^1$ equivalence class under almost-everywhere
equality, not a quotient by cut distance zero. Its canonical `value` first
symmetrizes a representative and then clips it to $[0,1]$. It is measurable,
pointwise symmetric, bounded, and almost everywhere equal to the original
representative (`value_ae_eq`).

**Translation/adaptation argument.** Apply the published implication
(a)$\Rightarrow$(d) to `U.value` and `W.value`. Their pointwise properties
meet all source hypotheses. Their ordinary homomorphism densities are
exactly the integrals used in Lean: the same unordered edge products,
with the same independent coordinates. Thus the Lean hypothesis supplies
(a) for every finite graph; finite relabeling identifies an arbitrary
finite graph with one on `Fin f`. Rename the two maps, and if necessary
exchange sides of the equality, to obtain the displayed orientation.

For completeness, the source permits Lebesgue-completed measurability,
whereas the project's interval carries its standard Borel measurable
structure and volume. A Lebesgue-measurable interval-valued map has a
Borel version equal almost everywhere: approximate its real coordinates
by measurable simple functions and replace each completed-measurable
level set by a Borel set modulo a null set. Clip the resulting version
to $[0,1]$. Such a change preserves all pushforward probabilities of Borel
sets and hence measure preservation. Changing either map on a null set
changes its two-coordinate pullback only on a subset of
$(N\times[0,1])\cup([0,1]\times N)$, also null. This supplies the exact
Lean measurability without assuming invertibility. Changing a graphon
representative is likewise harmless: the product of a measure-preserving
map with itself preserves product measure and pulls back null sets to
null sets. In fact applying the theorem directly to `value` already avoids
that latter replacement in the conclusion.

These source/convention adaptations are included in the axiom's trust
boundary. `PriorInstances.commonPullbackInput` merely packages this assumed
statement; it does not prove the published theorem. The local
`commonPullback_of_cutDist_eq_zero` first obtains equality of densities
using A09 and then invokes this input.

**Interface classification:** SPECIALIZATION / WEAKENING (the
$[0,1]$-valued case and only one implication of the published equivalence).

**Audit finding:** VERIFIED AS WEAKER SPECIALIZATION.

**No-stronger checklist.** Hypotheses PASS; conclusion PASS; quantifier order
PASS; constants/factors PASS; normalizations PASS; labeling PASS;
strict/non-strict PASS; measure-theoretic equivalence PASS. In particular,
neither pointwise equality everywhere nor bijectivity is asserted.

# Hatami--Janson--Szegedy (2018)

## A11. Labeled-family entropy upper bound

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.hatamiJansonSzegedyLabeledEntropyUpperBound`, in [InducedStars/PriorLiterature.lean:463](../../InducedStars/PriorLiterature.lean#L463). The exact declaration is reproduced in the declaration appendix; this is a direct proposition, not a structure-valued axiom.

**Published authority.** Hamed Hatami, Svante Janson, and Balázs Szegedy, *Graph properties, graph limits, and entropy*, Journal of Graph Theory **87** (2018), 208–229, DOI [10.1002/jgt.22152](https://doi.org/10.1002/jgt.22152). Theorem 1, equation (5), and Remark 1, equation (6), printed p. 211, PDF p. 4. Relevant definitions are on printed pp. 209–210 (PDF pp. 2–3); cut convergence is explained on pp. 217–218 (PDF pp. 10–11). Theorem 1 is proved on pp. 224–225 (PDF pp. 17–18), using Lemma 9 on pp. 223–224.

### Published statement and conventions

A graph class \(\mathcal R\) is a set of isomorphism classes of finite simple graphs; no hereditary hypothesis is imposed by Theorem 1. Let \(\mathcal R_n\) be its unlabeled graphs of order \(n\), and let \(\widehat{\mathcal R}\) be its graph limits along orders tending to infinity. The theorem states

\[
 \limsup_{n\to\infty}
 \frac{\log_2|\mathcal R_n|}{\binom n2}
 \le \max_{\Gamma\in\widehat{\mathcal R}}\operatorname{Ent}(\Gamma).
\]

Remark 1 gives \(|\mathcal R_n|\le |\mathcal R_n^L|\le n!|\mathcal R_n|\), where \(\mathcal R_n^L\) comprises *all* labeled realizations on \([n]\), and explicitly allows replacing the unlabeled count by the labeled count in the theorem. The source uses base-two entropy

\[
 h_2(p)=-p\log_2p-(1-p)\log_2(1-p),\qquad
 \operatorname{Ent}(W)=\int_{[0,1]^2}h_2(W(x,y))\,dx\,dy.
\]

The two zero-log products are defined by continuity. In the source's finite-class case both sides of the theorem are interpreted as \(-\infty\). That case is excluded by Lean's eventual-nonemptiness hypothesis, so no extended-real convention is silently imported into the real-valued Lean statement.

### Definitions and exact Lean meaning

For each natural \(n\), `Q n` is an arbitrary finite set of graphs on `Fin n`; it is **not** assumed closed under relabeling. `completeEdgeCount n` is exactly \(\binom n2\). `normalizedLogGraphCount n (Q n).card` is \(\log_2|Q_n|/\binom n2\), not division by \(n^2\). Lean's `log2 0` is totalized to zero, which is why the eventual nonemptiness condition matters.

`Graphon` is a symmetric, almost-everywhere \([0,1]\)-valued \(L^1\) class on the unit square. It is quotiented by a.e. equality, **not** already by cut distance zero. `Graphon.value` is a measurable pointwise symmetric \([0,1]\)-valued representative equal a.e. to that class. `graphonEntropy` integrates `Real.binEntropy / Real.log 2` evaluated at this representative. It is exactly the source's bit entropy.

`graphGraphon G` is the equal-cell adjacency graphon, with zero diagonal cells. `cutNorm` is the supremum of the absolute kernel integral over measurable rectangles. `cutDist` is the infimum of that cut norm over measure-preserving measurable bijections of the interval. This is the ordinary graphon cut pseudometric: the equivalent bijection formulation is also independently printed in Janson's published monograph, Theorem 6.9(v), pp. 17–18. Thus there is no replacement of cut distance by labeled cut norm and no change by a hidden factor four.

`labeledGraphFamilyLimitSet Q` consists exactly of graphons \(W\) for which there are strictly increasing orders \(\sigma(j)\), choices \(G_j\in Q_{\sigma(j)}\), and
\(\delta_\square(W_{G_j},W)\to0\). Its image under entropy is a nonempty bounded real set when \(Q_n\) is eventually nonempty: compactness supplies a subsequential limit, and every entropy lies in \([0,1]\). Its `sSup` is therefore an ordinary finite supremum, not the arbitrary value of a supremum of the empty set.

The assumed conclusion is: for every \(\varepsilon>0\), eventually
\[
 \frac{\log_2|Q_n|}{\binom n2}
 \le \sup_{W\in\operatorname{Lim}(Q)}\operatorname{Ent}(W)+\varepsilon.
\]

### Classification and complete implication

**Classification: DERIVED CONSEQUENCE. Status: VERIFIED AS DERIVED CONSEQUENCE.** The arbitrary-labeled-family interface is not literally the published theorem.

1. Define the relabeling closure
   \(\overline Q_n=\{\pi G:G\in Q_n,\ \pi\in S_n\}\), and let \(\mathcal R\) be the graph class consisting of their isomorphism classes, across all orders. Then \(\mathcal R_n^L=\overline Q_n\). No monotonicity or heredity is needed; the union across orders is a graph class in precisely the source's sense.
2. The action map \(Q_n\times S_n\to\overline Q_n\) is surjective. Consequently
   \[
      |Q_n|\le |\overline Q_n|\le n!|Q_n|.
   \]
   Also every unlabeled class has between one and \(n!\) labeled realizations, giving the source's Remark 1 bounds. This handles automorphisms without incorrectly treating every orbit as having exactly \(n!\) elements.
3. For \(n\ge2\),
   \[
     0\le\frac{\log_2(n!)}{\binom n2}
       \le\frac{n\log_2 n}{n(n-1)/2}
       =\frac{2\log_2 n}{n-1}\longrightarrow0.
   \]
   Thus relabeling closure, and then passage between labeled and unlabeled class counts, changes normalized logarithms by a vanishing amount. For an upper bound alone, \(|Q_n|\le|\overline Q_n|\) already suffices after the source's labeled version is used.
4. The representative-level limit sets are equal. The inclusion from \(Q\) to \(\overline Q\) is immediate. Conversely, if \(H_j\in\overline Q_{\sigma(j)}\) converges to \(W\), choose \(G_j\in Q_{\sigma(j)}\) isomorphic to \(H_j\). Their adjacency graphons have cut distance zero; the triangle inequality in both directions gives identical distance to \(W\). Hence \(G_j\to W\) too. Locally proved supporting facts are `cutDist_graphGraphon_eq_zero_of_iso`, `cutDist_graphGraphon_comap_perm_eq_zero`, and `mem_labeledGraphFamilyLimitSet_iff_of_cutDist_eq_zero`.
5. HJS defines graph limits by convergent finite-graph sequences with orders tending to infinity and identifies this with cut convergence. A divergent order sequence has a strictly increasing subsequence; a strictly increasing natural sequence tends to infinity. Therefore its quotient limit set is exactly the cut-zero quotient of Lean's representative-level set. Entropy is invariant under this equivalence, as the source states on p. 211; the local theorem `graphonEntropy_eq_of_cutDist_eq_zero` also establishes the corresponding invariant from the project's separately recorded graphon-equivalence inputs. Hence the published maximum equals Lean's supremum. Every graph limit has a graphon representative, and the maximum is attained in the source, so neither direction of this identification loses an extremizer.
6. Apply Theorem 1 and Remark 1 to \(\mathcal R\), and use the preceding identifications to obtain a limsup at most \(S:=\sup\operatorname{Ent}(\operatorname{Lim}(Q))\). On the eventual nonempty tail, the normalized count is a real number in \([0,1]\). If for a fixed \(\varepsilon>0\) it exceeded \(S+\varepsilon\) infinitely often, an increasing subsequence of such indices would force the limsup to be at least \(S+\varepsilon\), a contradiction. Thus it is eventually strictly less than \(S+\varepsilon\), which implies the required non-strict inequality. The threshold may depend on \(Q\) and \(\varepsilon\); no uniform threshold is assumed.

**Trust-boundary location.** The full relabeling-closure, count comparison, quotient-limit identification, and limsup-to-eventual adaptation is accepted as part of this external axiom. The cited permutation and cut-zero lemmas are locally proved support, but there is no separate Lean proof of the complete published-to-interface adapter. This guide preserves its ordinary mathematical justification; the derivation is not kernel-checked.

### No-stronger-than-source checks

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | Arbitrary labeled families become a graph class by relabeling closure; eventual nonemptiness avoids the source's finite-class convention. |
| Conclusion | PASS | It is an epsilon-eventual upper bound deduced from the published limsup inequality. |
| Quantifier order | PASS | Each fixed family and positive epsilon has its own eventual threshold. |
| Constants/factors | PASS | The \(n!\) discrepancy has vanishing normalized logarithm. |
| Normalizations | PASS | Both use bits and \(\binom n2\); entropy is the whole-square integral. |
| Labeling | PASS | Explicit orbit closure and orbit-cardinality inequalities handle arbitrary labels. |
| Inequalities | PASS | Eventual strict upper bounds imply Lean's non-strict bound. |
| Measure/equivalence | PASS | a.e. graphons, cut-zero quotient limits, and invariant entropy are distinguished explicitly. |

## A12. Graphon entropy upper semicontinuity

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.hatamiJansonSzegedyEntropyUpperSemicontinuous`, in [InducedStars/PriorLiterature.lean:485](../../InducedStars/PriorLiterature.lean#L485). Exact declaration: see the declaration appendix.

**Published authority.** Hatami–Janson–Szegedy, *Graph properties, graph limits, and entropy*, Journal of Graph Theory **87** (2018), 208–229, DOI [10.1002/jgt.22152](https://doi.org/10.1002/jgt.22152), **Lemma 3(ii)**, printed p. 218 (PDF p. 11), proof pp. 218–219 (PDF pp. 11–12). The publication is the same as A11.

**Locator and terminology finding.** The published PDF numbers this **Lemma 3(ii)**, not Lemma 3.3(ii). It calls the property “lower semicontinuous” while printing
\[
 \limsup_{m\to\infty}\operatorname{Ent}(W_m)\le\operatorname{Ent}(W)
 \quad\text{when }W_m\to W.
\]
That inequality is standard **upper** semicontinuity. No alternative order convention is declared there. The existing Lean docstring's explanation “under its order convention” is unsupported by the inspected passage; the inequality assumed in Lean is nevertheless exactly in the correct direction. This is a source/docstring terminology issue, not an axiom-strength mismatch.

### Definitions and published statement

The graphons, bit-valued entropy, a.e. representatives, whole-square measure, and bijection cut-distance convention are as detailed in A11. HJS pp. 217–218 identify convergence in its graphon/graph-limit topology with cut-distance convergence. Lemma 3(ii) applies to every graphon sequence converging to a graphon in that topology, with no fixed density, forbidden-subgraph restriction, or pointwise convergence assumption.

Lean assumes that for every `Wseq : ℕ → Graphon`, every graphon `W`, and every proof that \(\delta_\square(W_n,W)\to0\), for each \(\varepsilon>0\) eventually
\[
 \operatorname{Ent}(W_n)\le\operatorname{Ent}(W)+\varepsilon.
\]

`PriorInstances.entropySemicontinuityInput` packages precisely that proposition into `DenseGraph.EntropySemicontinuityInput.eventually_le`; the record adds no additional hypothesis or conclusion. Its theorem-valued field is the same universal sequence/limit/positive-epsilon implication. This instance is a proved record assembly, not a fifteenth external assumption.

### Classification and complete implication

**Classification: SPECIALIZATION / WEAKENING. Status: VERIFIED AS WEAKER SPECIALIZATION.** This selects the sequential epsilon-eventual form of the published lemma. For real bounded entropy sequences it is equivalent to the displayed limsup formulation; the classification reflects the narrower interface, not a reversal of semicontinuity.

1. Use the exact standard cut-distance convention explained in A11, so the Lean convergence hypothesis is convergence in HJS's graphon topology.
2. Apply the printed inequality of Lemma 3(ii). Both entropy definitions use base two; there is no extra factor of \(\log 2\) at this step. Each entropy lies in \([0,1]\), ensuring a finite real limsup.
3. Fix \(\varepsilon>0\). If the desired eventual upper bound failed, infinitely many terms would be greater than \(\operatorname{Ent}(W)+\varepsilon\). Their subsequence would force the limsup to be at least that value, contradicting Lemma 3(ii). This proves the exact order \(\forall W_n,W,\ h_{\rm cut}\Rightarrow\forall\varepsilon>0,\ \exists N,\ \forall n\ge N\).
4. Replacing any graphon by its canonical a.e.-equal `Graphon.value` changes neither entropy nor cut distance. Thus the source's representatives and Lean's \(L^1\)-classes define the same assertion.

The printed proof additionally corroborates the direction: averaging over a measurable partition increases entropy by Jensen's inequality; cut convergence controls the finite block averages; refinement then recovers the limit entropy by dominated convergence. That is an upper bound on the sequence's limsup, not a lower bound on its liminf.

**Trust-boundary location.** The limsup-to-epsilon conversion is inside the external proposition. `PriorInstances.entropySemicontinuityInput` and `graphonEntropy_eventually_le_of_cutDist_tendsto_zero` are local wrappers. Relative-entropy lower semicontinuity is proved locally in `graphonRelativeEntropy_eventually_ge_of_cutDist_tendsto_zero_withInput`, using the entropy input and cut-continuity of edge density; it is not an extra published assumption.

### No-stronger-than-source checks

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | Exactly an arbitrary cut-convergent graphon sequence. |
| Conclusion | PASS | The printed limsup inequality implies the displayed eventual inequality. |
| Quantifier order | PASS | The threshold may depend on the sequence, limit, and epsilon. |
| Constants/factors | PASS | No numerical change. |
| Normalizations | PASS | Identical bit entropy and whole-square integral. |
| Labeling | PASS | No finite-graph labeling occurs in either statement. |
| Inequalities | PASS | The mathematical displayed inequality, not the erroneous adjective, determines the direction. |
| Measure/equivalence | PASS | Canonical representatives agree a.e.; the cut topology is the same. |

# Janson (2013)

## A13. Entropy of the sampled labeled graph

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity.** `InducedStars.PriorLiterature.jansonWRandomGraphEntropyAsymptotic`, in [InducedStars/PriorLiterature.lean:552](../../InducedStars/PriorLiterature.lean#L552). Exact declaration: see the declaration appendix.

**Published authority.** Svante Janson, *Graphons, cut norm and distance, couplings and rearrangements*, New York Journal of Mathematics Monographs **4** (2013), 1–76. Theorem D.5, equation (D.1), printed and PDF p. 61; proof pp. 61–62. The labeled sampling law is defined on p. 58; the entropy and binary-entropy definitions are on p. 60. [Published monograph](https://nyjm.albany.edu/m/2013/4.htm). No DOI is asserted here.

### Published statement and exact sampling semantics

For every graphon \(W\) on a probability space \((\Omega,\mu)\), Janson proves
\[
 \frac{\mathsf H(G(n,W))}{\binom n2}
 \longrightarrow \int_{\Omega^2}h(W(x,y))\,d\mu(x)\,d\mu(y).
\]
Here \(G(n,W)\) is a **labeled** graph on \([n]\). Sample independent \(X_1,\ldots,X_n\) with law \(\mu\); conditional on these latent variables, draw every unordered pair \(i<j\) independently with success probability \(W(X_i,X_j)\). There are \(2^{\binom n2}\) outcomes. The entropy is that of this entire marginal random graph, not its conditional entropy given the latent points and not the entropy of its isomorphism class.

On p. 60 the source defines \(\mathsf H(Z)=-\sum p_i\log p_i\) and \(h(p)=-p\log p-(1-p)\log(1-p)\), with \(h(0)=h(1)=0\). It uses unqualified `log`, conventionally the natural logarithm; the passage does not explicitly declare a logarithm base. The theorem is unchanged under using any one logarithm base consistently on both sides. This audit makes the conversion to natural units and then to bits explicitly, rather than relying on an unprinted base declaration.

### Definitions and exact Lean meaning

Specialize \(\Omega\) to the unit interval with its probability volume measure. The graphon carrier and canonical `Graphon.value` are as in A11. For a graph \(G\) on `Fin n`,
\[
 \mu_W(G)=\int_{[0,1]^n}
   \prod_{\{i,j\}\in E(G)}W^{\mathrm{value}}(x_i,x_j)
   \prod_{\substack{i<j\\\{i,j\}\notin E(G)}}
       (1-W^{\mathrm{value}}(x_i,x_j))\,dx.
\]
This is `wRandomGraphMass W G`; each unordered, nonloop edge occurs once. `wRandomConditionalWeight` is the displayed integrand, expressed through `graphonInducedIntegrand`. Local `sum_wRandomConditionalWeight` proves its finite conditional normalization; `sum_wRandomGraphMass` (also `wRandomGraphMass_sum`) proves \(\sum_G\mu_W(G)=1\). `wRandomGraphEventProbability W A` is \(\sum_{G\in A}\mu_W(G)\).

`finiteShannonEntropy μ` is \(-\sum_G\mu(G)\log_2\mu(G)\), and `wRandomGraphEntropy W n` applies it to \(\mu_W\). The zero-mass term contributes zero, as it should: Lean's totalized logarithm is multiplied by zero. `graphonEntropy` is \(\int h_{\rm nat}(W^{\rm value})/\ln2\). `completeEdgeCount n` is exactly \(\binom n2\). There is no graphon-density normalization \(2e/n^2\) in this entropy assertion.

### Classification and complete implication

**Classification: SPECIALIZATION / WEAKENING. Status: VERIFIED AS WEAKER SPECIALIZATION.** The source allows general probability spaces; Lean needs only the unit interval, followed by an exact change of entropy units.

1. A Lean graphon has a measurable pointwise bounded symmetric representative `Graphon.value`, so it satisfies the graphon hypotheses of Theorem D.5 on \([0,1]\). Replacing an a.e. version by this representative changes no displayed integral. In the sampling formula each pair of independent latent coordinates has product-volume law; the preimage of a graphon null set is null. The union over the finitely many unordered pairs is still null. Thus this replacement also leaves every finite graph mass unchanged.
2. Conditional independence of the edges gives exactly the product in \(\mu_W(G)\); integrating out the latent variables gives exactly the Lean marginal. The bijection \([n]\leftrightarrow\mathrm{Fin}\ n\) merely relabels the finite outcome set and preserves every mass and Shannon entropy. In particular, no \(n!\) correction is needed here: both laws are labeled.
3. Use Theorem D.5 in natural-log units. If the source's unqualified logarithm were instead understood as any fixed base \(b>1\), multiply both sides by \(\ln b\) first; the same natural-log theorem results. Write \(H_{\rm nat}(n)\) and \(E_{\rm nat}(W)\) for its two entropies. Then
   \[
   \begin{aligned}
   \operatorname{wRandomGraphEntropy}(W,n)
       &=H_{\rm nat}(n)/\ln2,\\
   \operatorname{graphonEntropy}(W)&=E_{\rm nat}(W)/\ln2.
   \end{aligned}
   \]
   The first identity is explicitly supported by local `finiteShannonEntropy_eq_negMulLog`; the second follows by linearity of the integral from `binaryEntropy = Real.binEntropy / Real.log 2`. The denominator \(\ln2\) is strictly positive.
4. Divide the published convergent sequence and its limit by \(\ln2\), obtaining
   \[
    \frac{\operatorname{wRandomGraphEntropy}(W,n)}{\binom n2}
        \longrightarrow\operatorname{graphonEntropy}(W),
   \]
   which is the Lean proposition. The source takes positive graph orders and the proof's ratio starts at \(n\ge2\); Lean starts at zero. Changing the finitely many values at \(n=0,1\), including its totalized zero denominators, has no effect on an `atTop` limit.

**Trust-boundary location.** Finite sampling masses, their normalization, and the finite Shannon formula are locally defined/proved. The asymptotic theorem, specialization to this law, and change-of-units limit are assumed together in this declaration, not re-proved in Lean. The source's finite lower bound \(\mathsf H(G(n,W))\ge\binom n2\int h(W)\), obtained on p. 61 by conditioning on latent points, independently checks the sign and the absence of a factor two; its upper proof contributes only a vanishing \(n\log m/\binom n2\) term before refining the step approximation.

### No-stronger-than-source checks

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | A unit-interval graphon is a special case of the source's probability-space graphon. |
| Conclusion | PASS | The same entropy convergence, in rescaled units. |
| Quantifier order | PASS | For each fixed graphon the limit is asserted; no rate uniform in graphons is added. |
| Constants/factors | PASS | One factor \(1/\ln2\) multiplies both entropies; no factor two is introduced. |
| Normalizations | PASS | Both divide by exactly \(\binom n2\). The first two indices are irrelevant. |
| Labeling | PASS | Both are the Shannon entropy of the full labeled graph law. |
| Inequalities | PASS | Both are equal-limit statements; no finite inequality is strengthened. |
| Measure/equivalence | PASS | Canonical a.e. representatives give the identical finite marginal by the finite-null-union argument. |

# Riordan--Warnke (2015)

## A14. Riordan--Warnke principal-event Janson input

**Unresolved source-to-axiom issue:** none recorded in the inherited dossier; independent human certification is not claimed.

**Lean identity:** `InducedStars.PriorLiterature.riordanWarnkePrincipalJanson`, [InducedStars/PriorLiterature.lean:438](../../InducedStars/PriorLiterature.lean#L438).

**Verdict:** VERIFIED AS WEAKER SPECIALIZATION. **Interface classification:** SPECIALIZATION / WEAKENING. It specializes the general up-set theorem to finite product principal success events and weakens the dependency denominator by an overlap overcount. The zero-expectation totalized case is an elementary extension.

### Published source and locator

Oliver Riordan and Lutz Warnke, *The Janson Inequalities for General Up-Sets*, Random Structures & Algorithms **46** (2015), 391--395; DOI [10.1002/rsa.20506](https://doi.org/10.1002/rsa.20506). The journal PDF records online publication in 2013; the volume publication year is 2015. Theorem 1, equation (4), and the ordered-dependency convention are on printed p. 392, PDF page 2. Conditions (1)--(2), including positive association and closure under intersections and unions, are on printed p. 391, PDF page 1. The proof occupies pp. 392--394, PDF pages 2--4.

### Published theorem, including its hypotheses

Let a collection of events in a probability space be positively associated pairwise and closed under finite intersections and unions. For events `A_1,...,A_m` in that collection let `X=sum_i 1_(A_i)`, `mu=EX`, and

\[
\Delta_{\mathrm{source}}=\sum_i\sum_{j\sim i}\mathbb P(A_i\cap A_j),
\]

where `i~j` means **distinct** indices with dependent events. The sum is explicitly over ordered pairs. For `0<=t<=mu`, the first inequality in equation (4) is

\[
\mathbb P(X\leq\mu-t)\leq
\exp\left(-\frac{\varphi(-t/\mu)\mu^2}{\mu+\Delta_{\mathrm{source}}}\right),
\]

where `phi(x)=(1+x)log(1+x)-x` and `phi(-1)=1`. The logarithm and exponential here are natural. For `mu>0`, taking `t=mu` gives

\[
\mathbb P(X=0)\leq\exp\left(-\frac{\mu^2}{\mu+\Delta_{\mathrm{source}}}\right).
\]

The same published page expressly identifies the principal-event specialization in a product space. The preceding page identifies all increasing events in a Bernoulli product as a collection satisfying the hypotheses (Harris positive association); no equality of coordinate probabilities is imposed.

### Expanded Lean proposition and definitions

Let Omega and I be arbitrary finite types, with a decidable equality on Omega and a linear order on I. A `FiniteBernoulliProduct Omega` supplies a number `p_e in [0,1]` for each coordinate e; endpoints are permitted. An outcome is a subset T of Omega and has mass

\[
w(T)=\prod_{e\in T}p_e\prod_{e\notin T}(1-p_e).
\]

`eventProbability E=sum_(T in E) w(T)`. Its normalization and nonnegativity are proved locally in `BernoulliProduct.lean`. For a family of required-coordinate sets `R_i subset Omega`, define

\[
A_i=\{T:R_i\subseteq T\},\qquad
\mathrm{Avoid}=\{T:\forall i,\ R_i\nsubseteq T\},
\]
\[
\mu=\sum_i\mathbb P(A_i)=\sum_i\prod_{e\in R_i}p_e,
\]
\[
\Delta=\sum_{\substack{i<j\\R_i\cap R_j\ne\varnothing}}\mathbb P(A_i\cap A_j)
=\sum_{\substack{i<j\\R_i\cap R_j\ne\varnothing}}\prod_{e\in R_i\cup R_j}p_e.
\]

The single field `DenseGraph.PrincipalJansonInput.avoidance_le` asserts, for **every** such finite product and required-set family,

\[
\mathbb P(\mathrm{Avoid})\leq\exp\left(-\frac{\mu^2}{\mu+2\Delta}\right).
\]

This expands the full proposition of the structure-valued axiom. There are no hidden graph hypotheses, fixed-cardinality conclusions, Harris/FKG capability fields, or density thresholds. The required set can be empty, I can be empty, and deterministic coordinates can have success probability zero or one. The order on I chooses one orientation for each unordered pair; it is not a probability assumption.

### End-to-end implication

1. Use the finite cube with the displayed product masses as the published probability space. All principal events `R_i subset T` are increasing in T. The collection of all increasing events is closed under intersection and union, and has Harris positive association, exactly the product-space case stated in the publication. The finite Bernoulli law permits inhomogeneous parameters; no further source hypothesis restricts them.
2. The Lean avoidance event is exactly `X=0`. Its mu is exactly `EX`. The identity `A_i intersect A_j=A_(R_i union R_j)` and the principal-event product formula are proved locally as `principalSuccessEvent_inter` and `eventProbability_principalSuccessEvent`.
3. If `R_i` and `R_j` are disjoint, the events depend on disjoint sets of independent coordinates and are independent. The equality of their intersection probability with the product of their probabilities is locally proved by `eventProbability_principalSuccessEvent_inter_eq_mul_of_disjoint`. Hence every genuinely dependent distinct pair is among the overlapping required-set pairs. The converse is **not** assumed: deterministic or null events may overlap without being dependent.
4. Every unordered overlapping pair contributes once to Delta and twice to the corresponding ordered sum. Union is symmetric, so both orientations have the same intersection probability. The exact conversion is locally proved as `principalJansonOrderedDelta_eq_two_mul`. Nonnegative probabilities give `Delta_source<=2 Delta`.
5. If `mu>0`, both denominators are positive, and therefore

   \[
   \exp\left(-\frac{\mu^2}{\mu+\Delta_{\mathrm{source}}}\right)
   \leq\exp\left(-\frac{\mu^2}{\mu+2\Delta}\right).
   \]

   The overcount thus weakens the bound in the safe direction. The first inequality of source equation (4), at `t=mu`, supplies precisely the needed constant, with **no extra factor 2 in front of the whole denominator**. Using its weaker second inequality instead would not justify the stated axiom; the audit explicitly uses its first inequality and `phi(-1)=1`.
6. If `mu=0`, the nonnegative event probabilities are all zero; their finite union has probability zero, and `P(Avoid)=1`. The right-hand side is also one: real division in Lean makes `0/(mu+2 Delta)=0`, including `0/0=0`. Thus the otherwise singular endpoint is justified by the trivial probability bound, not by substituting undefined source arithmetic.
7. If some `R_i` is empty, that principal event is certain, so `P(Avoid)=0`; the right side is positive and the claimed inequality is immediate. If I is empty, `mu=Delta=0`, the avoidance event is the whole space, and the assertion is equality `1=exp(0)`.
8. Probabilities `p_e=0` or `p_e=1` cause no problem. One can remove deterministic coordinates: fix the certain coordinates, discard impossible events and delete fixed-success requirements. If a resulting required set is empty the avoidance probability is zero. Otherwise the remaining events are the same principal events on a smaller ordinary product. Equivalently, Harris and product-event identities already include these degenerate product measures. Any additional overlaps from deterministic coordinates only enlarge Lean's nonnegative Delta and therefore remain safe.
9. If `Delta=0` and `mu>0`, the exact denominator form becomes `exp(-mu)`; there is no division by Delta. The local theorem `principalJanson_avoidance_le_exp_neg_of_delta_eq_zero` makes this explicit. The alternative minimum bound `exp(-min(mu/2,mu^2/(4 Delta)))` is proved locally only for `mu>0, Delta>0`. No invalid positive-Delta specialization is silently used at zero overlap.

Steps 1 and the published lower-tail assertion are supplied by the external axiom. Steps 2--4 have the cited local identities; the full published-to-interface deduction has not itself been reconstructed as a Lean theorem and is part of this audited specialization. Subsequent minimum-form and zero-overlap corollaries are actual local Lean proofs.

### No-stronger-than-source checklist

| Check | Result | Reason |
|---|---|---|
| Hypotheses | PASS | Finite product satisfies the published up-set assumptions; degenerate and empty cases handled. |
| Conclusion | PASS | Only zero-event probability; weaker overlap denominator, not an added graph penalty. |
| Quantifier order | PASS | Arbitrary finite product and required-set family; no unproved uniform constant. |
| Constants/factors | PASS | Ordered source Delta bounded by twice unordered Lean Delta; equation (4)'s first bound used. |
| Normalization | PASS | Actual probability; natural exponential; no logarithm-base conversion. |
| Label convention | PASS | Relabeling finite coordinates/events has no mathematical effect. |
| Strictness | PASS | Non-strict probability bound; exact separation of positive and zero denominators. |
| Measure equivalence | PASS | Finite product measure, no graphon representative or null-set quotient issue. |

# Exact Lean declarations

The declarations below have namespace `InducedStars.PriorLiterature`; imports and opened namespaces are as in the linked source. Their exact texts and all displayed record definitions retain the historical dossier's source checks and agree with the corresponding declarations in this release.

## `InducedStars.PriorLiterature.btwHomogeneousSubpartition`

Source: [InducedStars/PriorLiterature.lean:86](../../InducedStars/PriorLiterature.lean#L86).

```lean
axiom btwHomogeneousSubpartition :
    ∀ (q : ℕ) (ε : ℝ), 0 < ε →
      ∃ μ : ℝ, 0 < μ ∧
        ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
            μ⁻¹ ≤ (Fintype.card V : ℝ) →
              ∃ S : Regularity.HomogeneousSubpartition
                  G Finset.univ μ ε q,
                S.IsSparse ∨ S.IsDense
```

## `InducedStars.PriorLiterature.furediCliqueFreePartiteSubgraph`

Source: [InducedStars/PriorLiterature.lean:139](../../InducedStars/PriorLiterature.lean#L139).

```lean
axiom furediCliqueFreePartiteSubgraph :
    ∀ (n r t : ℕ), 0 < n → 0 < r →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (r + 1) →
        G.edgeFinset.card + t = SimpleGraph.turanNumber n r →
        ∃ S : G.Subgraph, ∃ _ : S.coe.Coloring (Fin r),
          G.edgeFinset.card - t ≤ S.coe.edgeFinset.card
```

## `InducedStars.PriorLiterature.bclsvFiniteWeightedAlignment`

Source: [InducedStars/PriorLiterature.lean:414](../../InducedStars/PriorLiterature.lean#L414).

```lean
axiom bclsvFiniteWeightedAlignment :
    DenseGraph.FiniteWeightedAlignmentInput
```

## `InducedStars.PriorLiterature.riordanWarnkePrincipalJanson`

Source: [InducedStars/PriorLiterature.lean:438](../../InducedStars/PriorLiterature.lean#L438).

```lean
axiom riordanWarnkePrincipalJanson : DenseGraph.PrincipalJansonInput
```

## `InducedStars.PriorLiterature.hatamiJansonSzegedyLabeledEntropyUpperBound`

Source: [InducedStars/PriorLiterature.lean:463](../../InducedStars/PriorLiterature.lean#L463).

```lean
axiom hatamiJansonSzegedyLabeledEntropyUpperBound
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (hne : ∀ᶠ n in atTop, (Q n).Nonempty) :
    ∀ ε > 0,
      ∀ᶠ n in atTop,
        normalizedLogGraphCount n (Q n).card ≤
          sSup (graphonEntropy '' labeledGraphFamilyLimitSet Q) + ε
```

## `InducedStars.PriorLiterature.hatamiJansonSzegedyEntropyUpperSemicontinuous`

Source: [InducedStars/PriorLiterature.lean:485](../../InducedStars/PriorLiterature.lean#L485).

```lean
axiom hatamiJansonSzegedyEntropyUpperSemicontinuous
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut :
      Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0)) :
    ∀ ε > 0,
      ∀ᶠ n in atTop,
        graphonEntropy (Wseq n) ≤ graphonEntropy W + ε
```

## `InducedStars.PriorLiterature.bclsvWRandomGraphCutConvergenceInProbability`

Source: [InducedStars/PriorLiterature.lean:510](../../InducedStars/PriorLiterature.lean#L510).

```lean
axiom bclsvWRandomGraphCutConvergenceInProbability
    (W : Graphon) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          ε ≤ cutDist (graphGraphon G) W})
      atTop (nhds 0)
```

## `InducedStars.PriorLiterature.bclsvGraphonSequentialCompactness`

Source: [InducedStars/PriorLiterature.lean:533](../../InducedStars/PriorLiterature.lean#L533).

```lean
axiom bclsvGraphonSequentialCompactness (W : ℕ → Graphon) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ U : Graphon,
        Tendsto (fun n ↦ cutDist (W (σ n)) U) atTop (nhds 0)
```

## `InducedStars.PriorLiterature.jansonWRandomGraphEntropyAsymptotic`

Source: [InducedStars/PriorLiterature.lean:552](../../InducedStars/PriorLiterature.lean#L552).

```lean
axiom jansonWRandomGraphEntropyAsymptotic (W : Graphon) :
    Tendsto
      (fun n ↦ wRandomGraphEntropy W n / (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W))
```

## `InducedStars.PriorLiterature.lovaszSzegedyNestedMatrixLimit`

Source: [InducedStars/PriorLiterature.lean:571](../../InducedStars/PriorLiterature.lean#L571).

```lean
axiom lovaszSzegedyNestedMatrixLimit (Q : Graphon.NestedDensityMatrices) :
    ∃ W : Graphon,
      (∀ᵐ z ∂unitSquareMeasure,
        Tendsto (fun n ↦ nestedMatrixGraphon Q n z) atTop (𝓝 (W z))) ∧
      ∀ (n : ℕ) (i j : Fin (Q.size n)),
        Q.matrix n i j =
          (Q.size n : ℝ) ^ 2 *
            ∫ z in equalCell i ×ˢ equalCell j, W z ∂unitSquareMeasure
```

## `InducedStars.PriorLiterature.existsInducedFreeApproximatingGraphSequence`

Source: [InducedStars/PriorLiterature.lean:604](../../InducedStars/PriorLiterature.lean#L604).

```lean
axiom existsInducedFreeApproximatingGraphSequence
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (hfree : graphonInducedDensity F W = 0) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin (n + 1)),
      (∀ n, ¬ Regularity.InducedEmbeds F (G n)) ∧
      ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
        Tendsto (fun n ↦ graphHomDensity H (G n)) atTop
          (𝓝 (graphonHomDensity H W))
```

## `InducedStars.PriorLiterature.bclsvCutConvergence_of_homDensityConvergence`

Source: [InducedStars/PriorLiterature.lean:622](../../InducedStars/PriorLiterature.lean#L622).

```lean
axiom bclsvCutConvergence_of_homDensityConvergence
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hhom : ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
      Tendsto (fun n ↦ graphonHomDensity H (Wseq n)) atTop
        (𝓝 (graphonHomDensity H W))) :
    Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (𝓝 0)
```

## `InducedStars.PriorLiterature.bclsvHomDensity_eq_of_cutDist_eq_zero`

Source: [InducedStars/PriorLiterature.lean:645](../../InducedStars/PriorLiterature.lean#L645).

```lean
axiom bclsvHomDensity_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
      graphonHomDensity F U = graphonHomDensity F W
```

## `InducedStars.PriorLiterature.borgsChayesLovaszCommonPullback_of_homDensity_eq`

Source: [InducedStars/PriorLiterature.lean:664](../../InducedStars/PriorLiterature.lean#L664).

```lean
axiom borgsChayesLovaszCommonPullback_of_homDensity_eq
    (U W : Graphon)
    (hhom : ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
      graphonHomDensity F U = graphonHomDensity F W) :
    ∃ φ ψ : UnitInterval → UnitInterval,
      MeasurePreserving φ volume volume ∧
      MeasurePreserving ψ volume volume ∧
      ∀ᵐ z ∂unitSquareMeasure,
        U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2)
```

# Appendix: expanded theorem-valued interfaces

The seven records below are propositions containing theorem fields, not additional axioms. `PriorInstances.lean` constructs their values from the fourteen assumptions. Only alignment and principal Janson are themselves record-valued axiom declarations.

## `DenseGraph.PrincipalJansonInput`

Source: [DenseGraph/FiniteModels/Janson.lean:109](../../DenseGraph/FiniteModels/Janson.lean#L109).

```lean
structure PrincipalJansonInput : Prop where
  avoidance_le :
    ∀ {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
      [Fintype I] [LinearOrder I]
      (P : FiniteBernoulliProduct Ω) (required : I → Finset Ω),
      P.eventProbability
          (FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
        Real.exp
          (-((P.principalJansonMu required) ^ 2 /
            (P.principalJansonMu required +
              2 * P.principalJansonDelta required)))
```

## `DenseGraph.FiniteWeightedAlignmentInput`

Source: [DenseGraph/Graphon/Inputs.lean:62](../../DenseGraph/Graphon/Inputs.lean#L62).

```lean
structure FiniteWeightedAlignmentInput : Prop where
  align :
    ∀ η : ℝ, 0 < η →
      ∃ τ : ℝ, 0 < τ ∧
        ∀ {n : ℕ}
          (A B : FiniteWeightedGraph (Fin n)),
            InducedStars.cutDist A.toGraphon B.toGraphon < τ →
              ∃ π : Equiv.Perm (Fin n),
                FiniteWeightedGraph.finiteLabeledCutDist
                    A (B.permute π) < η
```

## `DenseGraph.CutZeroHomDensityInput`

Source: [DenseGraph/Graphon/Inputs.lean:19](../../DenseGraph/Graphon/Inputs.lean#L19).

```lean
structure CutZeroHomDensityInput : Prop where
  homDensity_eq :
    ∀ (U W : InducedStars.Graphon), InducedStars.cutDist U W = 0 →
      ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
        InducedStars.graphonHomDensity F U =
          InducedStars.graphonHomDensity F W
```

## `DenseGraph.CommonPullbackInput`

Source: [DenseGraph/Graphon/Inputs.lean:27](../../DenseGraph/Graphon/Inputs.lean#L27).

```lean
structure CommonPullbackInput : Prop where
  commonPullback :
    ∀ (U W : InducedStars.Graphon),
      (∀ (f : ℕ) (F : SimpleGraph (Fin f)),
        InducedStars.graphonHomDensity F U =
          InducedStars.graphonHomDensity F W) →
      ∃ φ ψ : InducedStars.UnitInterval → InducedStars.UnitInterval,
        MeasurePreserving φ volume volume ∧
        MeasurePreserving ψ volume volume ∧
        ∀ᵐ z ∂InducedStars.unitSquareMeasure,
          U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2)
```

## `DenseGraph.EntropySemicontinuityInput`

Source: [DenseGraph/Graphon/Inputs.lean:40](../../DenseGraph/Graphon/Inputs.lean#L40).

```lean
structure EntropySemicontinuityInput : Prop where
  eventually_le :
    ∀ (Wseq : ℕ → InducedStars.Graphon) (W : InducedStars.Graphon),
      Tendsto (fun n ↦ InducedStars.cutDist (Wseq n) W) atTop (nhds 0) →
      ∀ ε > 0,
        ∀ᶠ n in atTop,
          InducedStars.graphonEntropy (Wseq n) ≤
            InducedStars.graphonEntropy W + ε
```

## `DenseGraph.SequentialCompactnessInput`

Source: [DenseGraph/Graphon/Inputs.lean:50](../../DenseGraph/Graphon/Inputs.lean#L50).

```lean
structure SequentialCompactnessInput : Prop where
  compact_subsequence :
    ∀ W : ℕ → InducedStars.Graphon,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ U : InducedStars.Graphon,
          Tendsto (fun n ↦ InducedStars.cutDist (W (σ n)) U)
            atTop (nhds 0)
```

## `DenseGraph.HomogeneousSubpartitionInput`

Source: [DenseGraph/Regularity/Inputs.lean:26](../../DenseGraph/Regularity/Inputs.lean#L26).

```lean
structure HomogeneousSubpartitionInput : Prop where
  homogeneousSubpartition :
    ∀ (q : ℕ) (ε : ℝ), 0 < ε →
      ∃ μ : ℝ, 0 < μ ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
            μ⁻¹ ≤ (Fintype.card V : ℝ) →
              ∃ S : HomogeneousSubpartition G Finset.univ μ ε q,
                S.IsSparse ∨ S.IsDense
```

## `InducedStars.Graphon.NestedDensityMatrices`

Source: [InducedStars/Graphon/LimitInputs.lean:90](../../InducedStars/Graphon/LimitInputs.lean#L90). This is input data, not another axiom.

```lean
structure NestedDensityMatrices where
  size : ℕ → ℕ
  size_pos : ∀ n, 0 < size n
  matrix : (n : ℕ) → Matrix (Fin (size n)) (Fin (size n)) ℝ
  matrix_symmetric : ∀ n, (matrix n).IsSymm
  matrix_mem_Icc : ∀ n i j, matrix n i j ∈ Icc (0 : ℝ) 1
  dvd_of_le : ∀ {m n}, m ≤ n → size m ∣ size n
  blockAverage : ∀ {m n} (h : m ≤ n) (i : Fin (size m)) (j : Fin (size m)),
    matrix m i j = matrixBlockAverage (dvd_of_le h) (matrix n) i j
```
