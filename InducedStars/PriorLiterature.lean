import DenseGraph.FiniteModels.Janson
import DenseGraph.FiniteModels.ColorPartition
import DenseGraph.FiniteModels.TuranRounding
import DenseGraph.Graphon.Inputs
import InducedStars.Basic
import InducedStars.FiniteModels.GraphonLimits
import InducedStars.FiniteModels.Shannon
import InducedStars.Graphon.Densities
import InducedStars.Graphon.LimitInputs
import InducedStars.Graphon.Metric
import InducedStars.Regularity.Basic
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
import Mathlib.Data.Real.Basic

/-!
# Inputs from prior literature

This module is the sole location for project-specific assumptions imported
from prior mathematical literature.  Each interface below is reduced to the
weakest exact statement needed by a local proof.

Planned external-interface audit:

* **Erdős--Simonovits stability.**  Locally derived from Füredi (2015),
  Theorem 2, published p. 68 (proof p. 69), whose sole external interface
  retains a clique-free graph's large properly colored subgraph. The
  internal-edge and balance conclusions are proved locally, including the
  finite Turán rounding term. Used in the colored core-extraction recursion;
  both thresholds may depend on the fixed Turán parameter.
* **General-up-set Janson inequality.**  Source: Riordan--Warnke (2015).
  Used by the supercritical, subcritical, and induced-`C₄` defect penalties.
* **Induced regularity/type machinery.**  Source:
  Böttcher--Taraz--Würfl (2012), Lemma 2.5.  This is the only BTW assumption
  needed for the local selected-image proof of their Lemma 2.9; the
  operational cluster-family embedding lemma is proved locally.  Their Lemma
  2.7, and the prescribed-initial-partition and uniform-refinement enhancements
  in the present paper's type lemma, remain local obligations.
* **Nested graph-limit machinery.**  Sources: Lovász--Szegedy (2006),
  Lemmas 4.2, 5.1, 5.2 and Corollary 2.6; Lovász (2012), §9.1.2; and
  Borgs--Chayes--Lovász--Sós--Vesztergombi (2008), Theorem 3.8.  These inputs
  support the local graphon-sequence lemma; that lemma itself is not external.
* **Graphon compactness and entropy semicontinuity.**  Sources: Borgs et al.
  (2008), Proposition 3.6, and Chatterjee--Varadhan (2011), Lemma 2.1.  Used
  only to justify optimizer existence where the local candidate construction
  does not already suffice.  Borgs et al. (2008), Theorem 3.7 instead gives
  the comparison estimates between homomorphism densities and cut distance.
* **Fixed-density enumeration.**  Proposition 2.11 of the unpublished
  manuscript *The typical structure of dense claw-free graphs* is a local
  proof obligation, not prior literature.  Its proof may use only the narrow
  published HJS, BCLSV, and Janson interfaces recorded here; the repaired
  exact-edge transfer is proved in Lean.  The manuscript's `G(n,p)` transfer
  and rough-structure arguments are likewise local obligations for later
  goals and are not assumptions in this module.
* **Finite/graphon metric and weighted counting bridges.**  Sources: Lovász
  (2012), Lemma 8.9; Borgs et al. (2008), Theorems 2.3 and 2.7 and the
  p. 1831 remark.  Used in the supercritical and subcritical deterministic
  bridge lemmas.
* **Induced-`C₄` appendix transfers.**  Source: Perkins--van der Poel (2025),
  Lemma A.1(i)--(iii), Lemma A.3, and Lemma A.4.  Used only by the appendix's
  fixed-count comparisons and matching extraction.

An interface may be added here only after checking that Mathlib does not
already provide it and that it is genuinely external to the present paper.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace InducedStars.PriorLiterature

open InducedStars.Regularity

/-! ## Böttcher--Taraz--Würfl induced-embedding inputs -/

/-- **Published external input: Böttcher--Taraz--Würfl, Lemma 2.5.**

Source: J. Böttcher, A. Taraz, and A. Würfl, *Perfect graphs of fixed
density: counting and homogeneous sets*, Combinatorics, Probability and
Computing 21 (2012), Lemma 2.5, journal p. 668.

This is the printed global-vertex-set statement: every sufficiently large
finite graph has a sparse or dense `(μ, ε, q)`-subpartition.  Passing to an
induced parent cluster is deliberately not part of this axiom and is proved
as a local transport adapter.  This declaration is consumed by the local
selected-image theorem in `InducedStars.Regularity.Type`. -/
axiom btwHomogeneousSubpartition :
    ∀ (q : ℕ) (ε : ℝ), 0 < ε →
      ∃ μ : ℝ, 0 < μ ∧
        ∀ {V : Type*} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
            μ⁻¹ ≤ (Fintype.card V : ℝ) →
              ∃ S : Regularity.HomogeneousSubpartition
                  G Finset.univ μ ε q,
                S.IsSparse ∨ S.IsDense

/-- Apply the exact global BTW Lemma 2.5 input to the graph induced by a
finite parent set and transport its subpartition back to the ambient graph.
This is a proved subtype adapter, not an additional assumption. -/
theorem btwHomogeneousSubpartitionInside
    (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ {V : Type*} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (parent : Finset V),
          μ⁻¹ ≤ (parent.card : ℝ) →
            ∃ S : Regularity.HomogeneousSubpartition G parent μ ε q,
              S.IsSparse ∨ S.IsDense := by
  obtain ⟨μ, hμ, hglobal⟩ := btwHomogeneousSubpartition q ε hε
  refine ⟨μ, hμ, ?_⟩
  intro V _ _ G _ parent hparent
  have hcard : Fintype.card ↥(↑parent : Set V) = parent.card := by
    change Fintype.card ↥parent = parent.card
    exact Fintype.card_coe parent
  obtain ⟨S, hS⟩ := hglobal (G.induce (↑parent : Set V)) (by
    rw [hcard]
    exact hparent)
  refine ⟨Regularity.liftHomogeneousSubpartition G parent S, ?_⟩
  rcases hS with hS | hS
  · exact Or.inl ((Regularity.liftHomogeneousSubpartition_isSparse_iff
      G parent S).mpr hS)
  · exact Or.inr ((Regularity.liftHomogeneousSubpartition_isDense_iff
      G parent S).mpr hS)

open Classical in
/-- **Published external input: Füredi, Theorem 2.**

Source: Zoltán Füredi, *A proof of the stability of extremal graphs,
Simonovits' stability from Szemerédi's regularity*, Journal of Combinatorial
Theory, Series B 115 (2015), 66--71, Theorem 2 on printed p. 68;
proof on printed p. 69. DOI: 10.1016/j.jctb.2015.05.001.
Verified against `references/Furedi-2015-Stability/published.pdf`
(PDF pages 3--4), not an arXiv version.

For a clique-free graph with exact nonnegative deficit `t` from the Turán
number, retain an actual subgraph and a proper coloring using at most `r`
colors, losing at most `t` edges. The additive natural equality expresses
the published exact deficit without truncated-subtraction ambiguity.
No spanning or balance conclusion is assumed: isolated vertices are added
locally below, and all balance estimates are locally proved. -/
axiom furediCliqueFreePartiteSubgraph :
    ∀ (n r t : ℕ), 0 < n → 0 < r →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (r + 1) →
        G.edgeFinset.card + t = SimpleGraph.turanNumber n r →
        ∃ S : G.Subgraph, ∃ _ : S.coe.Coloring (Fin r),
          G.edgeFinset.card - t ≤ S.coe.edgeFinset.card

/-- Extend a proper subgraph coloring by assigning color zero to the added
isolated vertices. This is local bookkeeping, not part of the published input. -/
private noncomputable def furediSpanningColoring {n r : ℕ}
    (hr : 0 < r) {G : SimpleGraph (Fin n)}
    (S : G.Subgraph) (C : S.coe.Coloring (Fin r)) :
    S.spanningCoe.Coloring (Fin r) := by
  classical
  refine SimpleGraph.Coloring.mk
    (fun v ↦ if h : v ∈ S.verts then C ⟨v, h⟩ else ⟨0, hr⟩) ?_
  intro v w hvw
  have hv : v ∈ S.verts := S.edge_vert hvw
  have hw : w ∈ S.verts := S.edge_vert hvw.symm
  simpa only [dif_pos hv, dif_pos hw] using
    C.valid (v := ⟨v, hv⟩) (w := ⟨w, hw⟩) hvw

open Classical in
/-- Adding isolated vertices preserves the exact number of subgraph edges. -/
private theorem furediSpanning_edgeFinset_card {n : ℕ}
    {G : SimpleGraph (Fin n)} (S : G.Subgraph) :
    S.spanningCoe.edgeFinset.card = S.coe.edgeFinset.card := by
  rw [← SimpleGraph.Subgraph.spanningCoe_coe]
  convert! SimpleGraph.card_edgeFinset_map (Function.Embedding.subtype _) S.coe

/-- Locally proved Erdős--Simonovits stability in the exact finite form used
by the colored core-extraction recursion.

For `r ≥ 2`, an `(r + 1)`-clique-free graph whose edge count is within
`δ * n ^ 2` of `SimpleGraph.turanNumber n r` has an indexed partition into
`r` parts with at most `ε * n ^ 2` internal edges in total, and every part
has size within `ε * n` of `n / r`. The pairwise-disjointness and union fields
encode a genuine partition; no canonical partition or stronger edit-distance
conclusion is assumed.

The only external input is `furediCliqueFreePartiteSubgraph`: Füredi (2015),
Theorem 2 on published p. 68, with proof on p. 69, verified against the
published journal PDF. Let `t = turanNumber n r - e(G)`; Mathlib's Turán
bound proves the exact deficit identity. Extend the supplied subgraph by
isolated vertices and take all `r` proper color classes, including empty
ones. They have at most `t` internal ambient edges and squared size
deviations totaling at most `4*t + r/4`.

The rounding term is proved locally from the exact quotient/remainder
formula, not assumed from the unnumbered balancing sentence following
Corollary 3 on p. 68. That sentence omits rounding when `r` does not divide
`n` (already visible when `t=0`). Choose
`δ = min (ε/2) (ε^2/16)` and `n₀ = ceil(r/ε^2) + 1`.
This preserves the original declaration's exact type and every downstream
finite-type adapter. It partitions the red neighborhood at a seed stage in the
proof of the paper's `lemma:kth-order-recursion` in
`InducedStars/EdgeColoring/CoreExtraction.lean`.
No balance conclusion or paper-local result is an external assumption. -/
theorem erdosSimonovitsStability :
    ∀ (r : ℕ), 2 ≤ r → ∀ (ε : ℝ), 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
        ∀ (n : ℕ), n₀ ≤ n →
          ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
            G.CliqueFree (r + 1) →
            (SimpleGraph.turanNumber n r : ℝ) - δ * (n : ℝ) ^ 2 ≤
              (G.edgeFinset.card : ℝ) →
            ∃ parts : Fin r → Finset (Fin n),
              Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts ∧
              (Finset.univ : Finset (Fin r)).biUnion parts = Finset.univ ∧
              (∑ i : Fin r,
                  ((G.edgeFinset ∩ (parts i).sym2).card : ℝ)) ≤
                ε * (n : ℝ) ^ 2 ∧
              ∀ i : Fin r,
                |((parts i).card : ℝ) - (n : ℝ) / (r : ℝ)| ≤
                  ε * (n : ℝ) := by
  classical
  intro r hr ε hε
  let δ : ℝ := min (ε / 2) (ε ^ 2 / 16)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  let n₀ : ℕ := Nat.ceil ((r : ℝ) / ε ^ 2) + 1
  refine ⟨δ, hδ, n₀, ?_⟩
  intro n hn G _ hclique hedge
  have hrpos : 0 < r := by omega
  have hnpos : 0 < n := by dsimp [n₀] at hn; omega
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hround : (r : ℝ) ≤ ε ^ 2 * (n : ℝ) ^ 2 := by
    have hceil : Nat.ceil ((r : ℝ) / ε ^ 2) ≤ n := by dsimp [n₀] at hn; omega
    have hdiv : (r : ℝ) / ε ^ 2 ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    have hlin : (r : ℝ) ≤ (n : ℝ) * ε ^ 2 := (div_le_iff₀ hεsq).mp hdiv
    have hnsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hnsq hεsq.le]
  have hTuran : G.edgeFinset.card ≤ SimpleGraph.turanNumber n r := by
    simpa only [Fintype.card_fin] using hclique.card_edgeFinset_le
  let t : ℕ := SimpleGraph.turanNumber n r - G.edgeFinset.card
  have hdeficit : G.edgeFinset.card + t = SimpleGraph.turanNumber n r :=
    Nat.add_sub_of_le hTuran
  have hdeficitR : (G.edgeFinset.card : ℝ) + (t : ℝ) =
      (SimpleGraph.turanNumber n r : ℝ) := by exact_mod_cast hdeficit
  have ht : (t : ℝ) ≤ δ * (n : ℝ) ^ 2 := by linarith
  obtain ⟨S, C, hS⟩ := furediCliqueFreePartiteSubgraph n r t hnpos hrpos G
    hclique hdeficit
  let H := S.spanningCoe
  let coloring : H.Coloring (Fin r) := furediSpanningColoring hrpos S C
  have hH : G.edgeFinset.card - t ≤ H.edgeFinset.card := by
    simpa only [H, furediSpanning_edgeFinset_card] using hS
  have hHG : H ≤ G := S.spanningCoe_le
  let parts := DenseGraph.coloringParts coloring
  have hsum : ∑ i, (parts i).card = n := DenseGraph.sum_card_coloringParts coloring
  have hinternal := DenseGraph.sum_internal_edges_coloringParts_le coloring hHG t hH
  have hcapNat := DenseGraph.card_edgeFinset_le_multipartiteCrossCapacity_coloringParts coloring
  have hHreal : (G.edgeFinset.card : ℝ) - t ≤ (H.edgeFinset.card : ℝ) := by
    have hnat : G.edgeFinset.card ≤ H.edgeFinset.card + t := by omega
    have hreal : (G.edgeFinset.card : ℝ) ≤ (H.edgeFinset.card : ℝ) + t := by
      exact_mod_cast hnat
    linarith
  have hcap : (SimpleGraph.turanNumber n r : ℝ) - 2 * (t : ℝ) ≤
      (DenseGraph.multipartiteCrossCapacity (fun i ↦ (parts i).card) : ℝ) := by
    have hcapR : (H.edgeFinset.card : ℝ) ≤
        (DenseGraph.multipartiteCrossCapacity (fun i ↦ (parts i).card) : ℝ) := by
      exact_mod_cast hcapNat
    linarith
  have hvariance := DenseGraph.sum_sq_sub_average_le_of_turan_deficit
    hrpos (fun i ↦ (parts i).card) hsum t hcap
  refine ⟨parts, DenseGraph.coloringParts_pairwiseDisjoint coloring,
    DenseGraph.coloringParts_biUnion coloring, ?_, ?_⟩
  · have hδε : δ ≤ ε / 2 := min_le_left _ _
    have hδbound : δ ≤ ε := by linarith
    exact hinternal.trans (ht.trans (mul_le_mul_of_nonneg_right hδbound (sq_nonneg _)))
  · intro i
    have hi : (((parts i).card : ℝ) - (n : ℝ) / r) ^ 2 ≤
        ∑ j, (((parts j).card : ℝ) - (n : ℝ) / r) ^ 2 :=
      Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (((parts j).card : ℝ) - (n : ℝ) / r)) (Finset.mem_univ i)
    have hδsq : δ ≤ ε ^ 2 / 16 := min_le_right _ _
    have htSq : (t : ℝ) ≤ ε ^ 2 / 16 * (n : ℝ) ^ 2 :=
      ht.trans (mul_le_mul_of_nonneg_right hδsq (sq_nonneg _))
    apply abs_le_of_sq_le_sq _ (mul_nonneg hε.le hnNonneg)
    nlinarith

universe u

/-- Transport a fixed `Fin n` Erdős--Simonovits witness to an arbitrary
finite vertex type.  Keeping `δ` and `n₀` as explicit inputs is useful when a
downstream parameter hierarchy has already selected the exact `Fin`-indexed
witness by `Classical.choose`. -/
theorem erdosSimonovitsStabilityFiniteOfFin
    (r : ℕ) (ε δ : ℝ) (n₀ : ℕ)
    (hES : ∀ (n : ℕ), n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.CliqueFree (r + 1) →
        (SimpleGraph.turanNumber n r : ℝ) - δ * (n : ℝ) ^ 2 ≤
            (G.edgeFinset.card : ℝ) →
          ∃ parts : Fin r → Finset (Fin n),
            Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts ∧
            (Finset.univ : Finset (Fin r)).biUnion parts = Finset.univ ∧
            (∑ i : Fin r,
                ((G.edgeFinset ∩ (parts i).sym2).card : ℝ)) ≤
              ε * (n : ℝ) ^ 2 ∧
            ∀ i : Fin r,
              |((parts i).card : ℝ) - (n : ℝ) / (r : ℝ)| ≤
                ε * (n : ℝ)) :
    ∀ {V : Type u} [Fintype V] [DecidableEq V],
      n₀ ≤ Fintype.card V →
        ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
          G.CliqueFree (r + 1) →
          (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) -
                δ * (Fintype.card V : ℝ) ^ 2 ≤
              (G.edgeFinset.card : ℝ) →
          ∃ parts : Fin r → Finset V,
            Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts ∧
            (Finset.univ : Finset (Fin r)).biUnion parts = Finset.univ ∧
            (∑ i : Fin r,
                ((G.edgeFinset ∩ (parts i).sym2).card : ℝ)) ≤
              ε * (Fintype.card V : ℝ) ^ 2 ∧
            ∀ i : Fin r,
              |((parts i).card : ℝ) -
                  (Fintype.card V : ℝ) / (r : ℝ)| ≤
                ε * (Fintype.card V : ℝ) := by
  classical
  intro V _ _ hn G _ hclique hedge
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let H : SimpleGraph (Fin (Fintype.card V)) := G.map e.toEmbedding
  have hHclique : H.CliqueFree (r + 1) := by
    rw [SimpleGraph.cliqueFree_iff_free_top_fin] at hclique ⊢
    exact (SimpleGraph.free_congr_right (SimpleGraph.Iso.map e G)).mp hclique
  have hHcard : H.edgeFinset.card = G.edgeFinset.card := by
    exact SimpleGraph.card_edgeFinset_map e.toEmbedding G
  have hHedge :
      (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) -
          δ * (Fintype.card V : ℝ) ^ 2 ≤
        (H.edgeFinset.card : ℝ) := by
    simpa [hHcard] using hedge
  obtain ⟨partsFin, hdisjFin, hcoverFin, hinternalFin, hbalanceFin⟩ :=
    hES (Fintype.card V) hn H hHclique hHedge
  let parts : Fin r → Finset V := fun i ↦
    (partsFin i).map e.symm.toEmbedding
  refine ⟨parts, ?_, ?_, ?_, ?_⟩
  · intro i _ j _ hij
    exact (Finset.disjoint_map e.symm.toEmbedding).2
      (hdisjFin (Set.mem_univ i) (Set.mem_univ j) hij)
  · ext v
    have hmem := Finset.ext_iff.mp hcoverFin (e v)
    simpa [parts] using hmem
  · have hinter (i : Fin r) :
        (G.edgeFinset ∩ (parts i).sym2).card =
          (H.edgeFinset ∩ (partsFin i).sym2).card := by
      rw [show H.edgeFinset = G.edgeFinset.map e.toEmbedding.sym2Map by
        exact SimpleGraph.edgeFinset_map e.toEmbedding G]
      rw [show (partsFin i).sym2 =
          (parts i).sym2.map e.toEmbedding.sym2Map by
        have hp : (parts i).map e.toEmbedding = partsFin i := by
          dsimp [parts]
          rw [Finset.map_map]
          ext x
          simp
        rw [← Finset.sym2_map, hp]]
      rw [← Finset.map_inter]
      exact (Finset.card_map _).symm
    simpa only [hinter] using hinternalFin
  · intro i
    simpa [parts] using hbalanceFin i

/-- Isomorphism-invariant finite-type form of `erdosSimonovitsStability`.

This is a proved adapter, not an additional external assumption. It transports
the graph and the resulting partition along `Fintype.equivFin V`, preserving
clique-freeness, edge counts, internal-edge counts, covering,
pairwise-disjointness, and part cardinalities. -/
theorem erdosSimonovitsStabilityFinite
    (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ,
      ∀ {V : Type*} [Fintype V] [DecidableEq V],
        n₀ ≤ Fintype.card V →
          ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
            G.CliqueFree (r + 1) →
            (SimpleGraph.turanNumber (Fintype.card V) r : ℝ) -
                δ * (Fintype.card V : ℝ) ^ 2 ≤
              (G.edgeFinset.card : ℝ) →
            ∃ parts : Fin r → Finset V,
              Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts ∧
              (Finset.univ : Finset (Fin r)).biUnion parts = Finset.univ ∧
              (∑ i : Fin r,
                  ((G.edgeFinset ∩ (parts i).sym2).card : ℝ)) ≤
                ε * (Fintype.card V : ℝ) ^ 2 ∧
              ∀ i : Fin r,
                |((parts i).card : ℝ) -
                    (Fintype.card V : ℝ) / (r : ℝ)| ≤
                  ε * (Fintype.card V : ℝ) := by
  obtain ⟨δ, hδ, n₀, hES⟩ := erdosSimonovitsStability r hr ε hε
  exact ⟨δ, hδ, n₀,
    erdosSimonovitsStabilityFiniteOfFin r ε δ n₀ hES⟩

/-! ## Published graph-limit inputs -/

/-- **Published external input: BCLSV finite weighted alignment.**

Source: C. Borgs, J. Chayes, L. Lovász, V. T. Sós, and K. Vesztergombi,
*Convergent sequences of dense graphs I: Subgraph frequencies, metric
properties and testing*, Advances in Mathematics 219 (2008), 1801--1851.
Equation (3.13), on published p. 1815, identifies the fractional cut distance
of weighted graphs with the cut distance of their associated step graphons.
Theorem 2.3, on published p. 1807, compares fractional alignment with
permutation alignment; its proof appears on published pp. 1831--1832.

The Lean interface is restricted to weighted graphs on the same finite vertex
set `Fin n`, hence equal vertex sets with unit node weights, and its edge
weights lie in `[0,1]` by `DenseGraph.FiniteWeightedGraph`.  It is a strictly
weaker qualitative consequence of the published quantitative result: for a
requested same-label cut error it supplies only a positive graphon-cut radius,
an aligning permutation, and the resulting cut-discrepancy bound.  It assumes
no finite-graph or partition-structure conclusion. -/
axiom bclsvFiniteWeightedAlignment :
    DenseGraph.FiniteWeightedAlignmentInput

/-! ## Published finite-probability inputs -/

/-- **Published external input: Riordan--Warnke, Theorem 1.**

Source: Oliver Riordan and Lutz Warnke, *The Janson Inequalities for General
Up-Sets*, Random Structures & Algorithms 46 (2015), 391--395, Theorem 1 on
published p. 392 (proof on pp. 392--394).

The published theorem writes
`Δ = ∑ i, ∑ j ∼ i, P(A i ∩ A j)` and explicitly declares this to be a sum
over **ordered** distinct dependent pairs.  At `t = μ`, its first lower-tail
bound is `exp (-μ² / (μ + Δ))`.  The reusable Lean interface specializes to
principal up-sets in a finite independent Bernoulli product.  Disjoint
required-coordinate sets give independent events, so actual dependent pairs
are contained among overlapping pairs.  The Lean `principalJansonDelta` sums
each overlapping pair once; replacing the published ordered sum by twice
this unordered overcount gives the weaker denominator `μ + 2 * Δ`.

This axiom supplies only `DenseGraph.PrincipalJansonInput`: it contains no
graph terminology, Harris/FKG interface, fixed-cardinality comparison, or
medium-degree conclusion. -/
axiom riordanWarnkePrincipalJanson : DenseGraph.PrincipalJansonInput

/-! ### Published inputs for fixed-density enumeration -/

/-- **Published external input: Hatami--Janson--Szegedy, Theorem 1 and
Remark 1, labeled-family specialization.**

Source: H. Hatami, S. Janson, and B. Szegedy, *Graph properties, graph
limits, and entropy*, Journal of Graph Theory 87 (2018), 208--229,
Theorem 1 and Remark 1 on published p. 211; the supporting neighborhood-count
argument and proof appear on published pp. 223--225.

The published theorem is stated for an isomorphism-closed graph class.  For
an arbitrary labeled family `Q`, close each `Q n` under relabeling.  This can
increase its cardinality by at most `n!`, whose base-two logarithm is
`o(n²)`, while finite relabeling changes the associated adjacency graphon by
cut distance zero.  Thus the closure has the same representative-level limit
set, using the cut-zero invariance of `labeledGraphFamilyLimitSet`, and the
published labeled/unlabeled remark yields this weaker eventual form.

Our `normalizedLogGraphCount` is exactly `log₂ |Q n| / n.choose 2`, with
`completeEdgeCount n = n.choose 2`.  Our `graphonEntropy` divides the natural
binary-entropy integrand by `Real.log 2`, so it is the same bit-valued entropy
used with the paper's base-two counting normalization.  Eventual nonemptiness
keeps the totalized value `log2 0` out of the asymptotic regime. -/
axiom hatamiJansonSzegedyLabeledEntropyUpperBound
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (hne : ∀ᶠ n in atTop, (Q n).Nonempty) :
    ∀ ε > 0,
      ∀ᶠ n in atTop,
        normalizedLogGraphCount n (Q n).card ≤
          sSup (graphonEntropy '' labeledGraphFamilyLimitSet Q) + ε

/-- **Published external input: Hatami--Janson--Szegedy, entropy
semicontinuity.**

Source: H. Hatami, S. Janson, and B. Szegedy, *Graph properties, graph
limits, and entropy*, Journal of Graph Theory 87 (2018), 208--229,
Lemma 3(ii) in Section 3 (the locator also cited as Lemma 3.3(ii)),
published pp. 218--219.

The published lemma states that if graphons `W_m` converge to `W` in cut
distance, then `limsup Ent(W_m) ≤ Ent(W)`.  (The paper calls this lower
semicontinuity under its order convention.)  The statement below is the
weaker epsilon-eventual sequential form used by the local compactness-gap
arguments.  It records exactly the printed inequality and includes no
feasibility, optimizer, relative-entropy, or finite-graph conclusion. -/
axiom hatamiJansonSzegedyEntropyUpperSemicontinuous
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hcut :
      Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (nhds 0)) :
    ∀ ε > 0,
      ∀ᶠ n in atTop,
        graphonEntropy (Wseq n) ≤ graphonEntropy W + ε

/-- **Published external input: BCLSV Theorem 4.5(b), convergence in
probability specialization.**

Source: C. Borgs, J. Chayes, L. Lovász, V. T. Sós, and K. Vesztergombi,
*Convergent sequences of dense graphs I: Subgraph frequencies, metric
properties and testing*, Advances in Mathematics 219 (2008), 1801--1851,
Theorem 4.5(b), published p. 1821.

The published theorem says that the standard sampled graph `G(n,W)` converges
to `W` almost surely.  The law in `wRandomGraphEventProbability` is the same
law: latent vertices are independent uniform points and, conditional on
them, unordered edges are independent Bernoulli variables with parameters
`W(Xᵢ,Xⱼ)`.  Almost-sure cut convergence implies the weaker tail-probability
convergence recorded here.  The event uses `ε ≤ cutDist`, so it is precisely
the complement of the open `ε`-ball needed by convergence in probability;
each unordered edge is sampled once, and `graphGraphon` uses the equal-cell
adjacency graphon normalization. -/
axiom bclsvWRandomGraphCutConvergenceInProbability
    (W : Graphon) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          ε ≤ cutDist (graphGraphon G) W})
      atTop (nhds 0)

/-- **Published external input: BCLSV Proposition 3.6, sequential
compactness consequence.**

Source: C. Borgs, J. Chayes, L. Lovász, V. T. Sós, and K. Vesztergombi,
*Convergent sequences of dense graphs I: Subgraph frequencies, metric
properties and testing*, Advances in Mathematics 219 (2008), 1801--1851,
Proposition 3.6 on published p. 1816.

The published proposition says that graphons valued in a fixed finite
interval form a compact metric space after graphons at cut distance zero are
identified.  Applied to the interval `[0,1]`, sequential compactness of this
quotient gives a cut-convergent subsequence.  The statement below is only the
representative-level selection consequence: it chooses one graphon
representing the quotient limit.  It includes no entropy, edge-density,
induced-freeness, or optimizer conclusion. -/
axiom bclsvGraphonSequentialCompactness (W : ℕ → Graphon) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ U : Graphon,
        Tendsto (fun n ↦ cutDist (W (σ n)) U) atTop (nhds 0)

/-- **Published external input: Janson, Theorem D.5.**

Source: S. Janson, *Graphons, cut norm and distance, couplings and
rearrangements*, New York Journal of Mathematics Monographs 4 (2013),
Theorem D.5 and its proof, published pp. 61--62.

Janson proves that the Shannon entropy of the labeled sampled graph
`G(n,W)`, divided by `n.choose 2`, converges to the integral of the pointwise
binary entropy of `W`.  The printed theorem uses natural logarithms.  Both
`wRandomGraphEntropy` and `graphonEntropy` divide the corresponding natural
entropy by `Real.log 2`, so converting both sides gives exactly this base-two
statement.  The denominator `completeEdgeCount n` is definitionally
`n.choose 2`; its zero values at the first two indices are harmless for the
`atTop` limit. -/
axiom jansonWRandomGraphEntropyAsymptotic (W : Graphon) :
    Tendsto
      (fun n ↦ wRandomGraphEntropy W n / (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W))

/-- The step graphon belonging to one level of a nested density-matrix tower. -/
noncomputable def nestedMatrixGraphon (Q : Graphon.NestedDensityMatrices) (n : ℕ) : Graphon :=
  matrixGraphon (Q.matrix n) (Q.matrix_symmetric n)
    (Q.matrix_nonneg n) (Q.matrix_le_one n)

/-- **Published external input: Lovász--Szegedy, Lemma 5.2.**

Source: L. Lovász and B. Szegedy, *Limits of dense graph sequences*,
Journal of Combinatorial Theory, Series B 96 (2006), Lemma 5.2,
published pp. 949--951.

The input is exactly a locally defined `NestedDensityMatrices` tower.  The
conclusion exposes only the published a.e. convergence and exact block-average
identity.  In particular, `L¹` convergence is not assumed here. -/
axiom lovaszSzegedyNestedMatrixLimit (Q : Graphon.NestedDensityMatrices) :
    ∃ W : Graphon,
      (∀ᵐ z ∂unitSquareMeasure,
        Tendsto (fun n ↦ nestedMatrixGraphon Q n z) atTop (𝓝 (W z))) ∧
      ∀ (n : ℕ) (i j : Fin (Q.size n)),
        Q.matrix n i j =
          (Q.size n : ℝ) ^ 2 *
            ∫ z in equalCell i ×ˢ equalCell j, W z ∂unitSquareMeasure

/-- Local dominated-convergence consequence of published LS Lemma 5.2. -/
theorem lovaszSzegedyNestedMatrixLimit_l1 (Q : Graphon.NestedDensityMatrices) :
    ∃ W : Graphon,
      Tendsto (fun n ↦ graphonL1Dist (nestedMatrixGraphon Q n) W)
        atTop (𝓝 0) ∧
      ∀ (n : ℕ) (i j : Fin (Q.size n)),
        Q.matrix n i j =
          (Q.size n : ℝ) ^ 2 *
            ∫ z in equalCell i ×ˢ equalCell j, W z ∂unitSquareMeasure := by
  obtain ⟨W, hae, hblocks⟩ := lovaszSzegedyNestedMatrixLimit Q
  exact ⟨W, graphonL1Dist_tendsto_zero_of_ae _ W hae, hblocks⟩

/-- **Published external input: deterministic consequence of
Lovász--Szegedy §2.6 and Corollary 2.6.**

Source: L. Lovász and B. Szegedy, *Limits of dense graph sequences*,
Journal of Combinatorial Theory, Series B 96 (2006), §2.6 and Corollary
2.6, published pp. 941--942.

This is deliberately weaker than the published almost-sure random-graph
statement.  For fixed `F` and `W`, zero induced density makes every fixed
induced-`F` embedding event null; choosing one outcome in the probability-one
hom-density convergence event gives the deterministic sequence below.  Cut
convergence is not bundled into this interface. -/
axiom existsInducedFreeApproximatingGraphSequence
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (hfree : graphonInducedDensity F W = 0) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin (n + 1)),
      (∀ n, ¬ Regularity.InducedEmbeds F (G n)) ∧
      ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
        Tendsto (fun n ↦ graphHomDensity H (G n)) atTop
          (𝓝 (graphonHomDensity H W))

/-- **Published external input: BCLSV Theorem 3.8, needed direction.**

Source: C. Borgs, J. Chayes, L. Lovász, V. T. Sós, and K. Vesztergombi,
*Convergent sequences of dense graphs I: Subgraph frequencies, metric
properties and testing*, Advances in Mathematics 219 (2008), Theorem 3.8,
published p. 1817.

The published theorem is an equivalence.  This interface exposes only its
homomorphism-density-convergence to cut-distance-convergence direction. -/
axiom bclsvCutConvergence_of_homDensityConvergence
    (Wseq : ℕ → Graphon) (W : Graphon)
    (hhom : ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
      Tendsto (fun n ↦ graphonHomDensity H (Wseq n)) atTop
        (𝓝 (graphonHomDensity H W))) :
    Tendsto (fun n ↦ cutDist (Wseq n) W) atTop (𝓝 0)

/-- **Published external input: BCLSV Theorem 3.8, constant-sequence
specialization of the reverse direction.**

Source: C. Borgs, J. Chayes, L. Lovász, V. T. Sós, and K. Vesztergombi,
*Convergent sequences of dense graphs I: Subgraph frequencies, metric
properties and testing*, Advances in Mathematics 219 (2008), Theorem 3.8,
published p. 1817, DOI 10.1016/j.aim.2008.07.008.

The published theorem says, for graphons on a fixed finite interval, that
convergence in cut distance is equivalent to convergence of every finite
simple-graph homomorphism density. Applying its cut-to-density direction to
the constant sequence `U, U, …` and a graphon `W` at cut distance zero gives
exactly this interface, a strictly weaker consequence than the published
equivalence.  Its direct local consumers are
`InducedStars.commonPullback_of_cutDist_eq_zero` and
`InducedStars.graphonInducedDensity_eq_of_cutDist_eq_zero`. -/
axiom bclsvHomDensity_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
      graphonHomDensity F U = graphonHomDensity F W

/-- **Published external input: Borgs--Chayes--Lovász Corollary 2.2(d).**

Source: C. Borgs, J. Chayes, and L. Lovász, *Moments of Two-Variable
Functions and the Uniqueness of Graph Limits*, Geometric and Functional
Analysis 19 (2010), Corollary 2.2(d), published p. 1601,
DOI 10.1007/s00039-010-0044-0.

For graphons on `[0,1]`, the printed conclusion gives two measure-preserving
maps from a common copy of `[0,1]` whose two pullbacks agree almost everywhere.
The hypothesis here is item (a) of that corollary, equality of every finite
simple-graph homomorphism density. We apply the published statement to the
canonical measurable representatives `Graphon.value`; this changes neither
graphon nor any homomorphism density.  Its sole direct local consumer is
`InducedStars.commonPullback_of_cutDist_eq_zero`. -/
axiom borgsChayesLovaszCommonPullback_of_homDensity_eq
    (U W : Graphon)
    (hhom : ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
      graphonHomDensity F U = graphonHomDensity F W) :
    ∃ φ ψ : UnitInterval → UnitInterval,
      MeasurePreserving φ volume volume ∧
      MeasurePreserving ψ volume volume ∧
      ∀ᵐ z ∂unitSquareMeasure,
        U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2)

/-- Local finite-graph adapter for the needed direction of BCLSV Theorem 3.8.

The only graph-limit input in this proof is
`bclsvCutConvergence_of_homDensityConvergence`; the passage from a finite
graph to its adjacency graphon is the exact counting identity proved in
`Graphon.Densities`. -/
theorem bclsvCutConvergence_of_graphHomDensityConvergence
    (size : ℕ → ℕ) (hsize : ∀ n, 0 < size n)
    (G : (n : ℕ) → SimpleGraph (Fin (size n))) (W : Graphon)
    (hhom : ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
      Tendsto (fun n ↦ graphHomDensity H (G n)) atTop
        (𝓝 (graphonHomDensity H W))) :
    Tendsto (fun n ↦ cutDist (graphGraphon (G n)) W) atTop (𝓝 0) := by
  classical
  apply bclsvCutConvergence_of_homDensityConvergence
  intro h H
  simpa only [graphonHomDensity_graphGraphon (hsize _)] using hhom h H

/-- The sampling consequence followed by the local BCLSV adapter.  Cut
convergence is deliberately derived here rather than included in the
sampling axiom. -/
theorem existsInducedFreeApproximatingGraphSequence_cut
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon)
    (hfree : graphonInducedDensity F W = 0) :
    ∃ G : (n : ℕ) → SimpleGraph (Fin (n + 1)),
      (∀ n, ¬ Regularity.InducedEmbeds F (G n)) ∧
      (∀ (h : ℕ) (H : SimpleGraph (Fin h)),
        Tendsto (fun n ↦ graphHomDensity H (G n)) atTop
          (𝓝 (graphonHomDensity H W))) ∧
      Tendsto (fun n ↦ cutDist (graphGraphon (G n)) W) atTop (𝓝 0) := by
  obtain ⟨G, hGfree, hhom⟩ :=
    existsInducedFreeApproximatingGraphSequence F W hfree
  refine ⟨G, hGfree, hhom, ?_⟩
  exact bclsvCutConvergence_of_graphHomDensityConvergence
    (fun n ↦ n + 1) (fun n ↦ Nat.zero_lt_succ n) G W hhom

end InducedStars.PriorLiterature
