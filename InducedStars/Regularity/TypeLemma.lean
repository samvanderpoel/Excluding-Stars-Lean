import InducedStars.Regularity.Type
import InducedStars.Regularity.Refinement

/-!
# The enhanced Type Lemma

This file combines the purely regularity-theoretic uniform-refinement theorem
with the uniform vertex-decoration theorem from `Regularity.Type`.  The
result exposes the indexed refinement data needed by the later graphon bridge.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u

/-- The complete paper-facing output of the enhanced Type Lemma.

The parent blocks form a partition of the final nonexceptional cluster
indices.  Every block has the same positive cardinality, and its clusters
partition the corresponding initial part after removal of the exceptional
vertices. -/
structure TypeLemmaResult
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (η δ : ℝ) (ℓ : ℕ) {s : ℕ} (initial : EquitableInitialPartition V s)
    (L U : ℕ) where
  childCount : ℕ
  childCount_pos : 0 < childCount
  regularityType : RegularityType G η δ ℓ
  lower_clusterCount : L ≤ regularityType.partition.clusterCount
  upper_clusterCount : regularityType.partition.clusterCount ≤ U
  clusterCount_eq : regularityType.partition.clusterCount = s * childCount
  parentBlocks : Fin s → Finset (Fin regularityType.partition.clusterCount)
  parentBlocks_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parentBlocks
  parentBlocks_cover :
    Finset.univ.biUnion parentBlocks =
      (Finset.univ : Finset (Fin regularityType.partition.clusterCount))
  parentBlock_card : ∀ i, (parentBlocks i).card = childCount
  cluster_subset_initial :
    ∀ i j, j ∈ parentBlocks i →
      regularityType.partition.clusters j ⊆ initial.parts i
  parent_sdiff_exception_eq_biUnion :
    ∀ i, initial.parts i \ regularityType.partition.exceptional =
      (parentBlocks i).biUnion regularityType.partition.clusters

/-- Paper: Lemma `lemma:type-lemma`, with density threshold in `(0, 1/2)`.

The witness `εStar` is selected solely from `(δ, ℓ)` and is capped at `1/2`
before `L`, `t`, and `η` are quantified.  The cluster-count bound is then
selected before the ambient vertex type, graph, actual parent count, and
initial partition. -/
theorem typeLemma
    (δ : ℝ) (ℓ : ℕ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (_hℓ : 0 < ℓ) :
    ∃ εStar : ℝ, 0 < εStar ∧ εStar ≤ 1 / 2 ∧
      ∀ L t : ℕ, 0 < L → 0 < t →
        ∀ η : ℝ, 0 < η → η < εStar →
          ∃ U n₀ : ℕ,
            ∀ {V : Type u} [Fintype V] [DecidableEq V]
              (G : SimpleGraph V) [DecidableRel G.Adj]
              {s : ℕ} (_hs : 0 < s) (_hst : s ≤ t)
              (initial : EquitableInitialPartition V s),
                n₀ ≤ Fintype.card V →
                  Nonempty (TypeLemmaResult G η δ ℓ initial L U) := by
  obtain ⟨εDecoration, hεDecoration, clusterSizeThreshold, hdecorate⟩ :=
    existsTypeVertexColors_of_largeRegularPartition δ ℓ hδ hδhalf
  let εStar : ℝ := min εDecoration (1 / 2)
  have hεStar : 0 < εStar := by
    simp only [εStar, lt_min_iff]
    exact ⟨hεDecoration, by norm_num⟩
  have hεStarHalf : εStar ≤ 1 / 2 := by
    exact min_le_right _ _
  refine ⟨εStar, hεStar, hεStarHalf, ?_⟩
  intro L t hL ht η hη hηStar
  change η < min εDecoration (1 / 2) at hηStar
  have hηDecoration : η < εDecoration :=
    hηStar.trans_le (min_le_left _ _)
  have hηHalf : η < 1 / 2 :=
    hηStar.trans_le (min_le_right _ _)
  obtain ⟨U, hU⟩ :=
    exists_uniformRefiningRegularPartition_with_minClusterSize
      η hη L t hL ht
  obtain ⟨n₀, hn₀⟩ := hU clusterSizeThreshold
  refine ⟨U, n₀, ?_⟩
  intro V _ _ G _ s hs hst initial hn
  obtain ⟨R⟩ := hn₀ G hs hst initial hn
  obtain ⟨vertexColor, hinduced⟩ :=
    hdecorate η hη hηDecoration G R.partition R.min_clusterSize
  let T : RegularityType G η δ ℓ :=
    { epsilon_pos := hη
      epsilon_lt_half := hηHalf
      delta_pos := hδ
      delta_lt_half := hδhalf
      partition := R.partition
      vertexColor := vertexColor
      inducedEmbedding := hinduced }
  refine ⟨?_⟩
  refine
    { childCount := R.childCount
      childCount_pos := R.childCount_pos
      regularityType := T
      lower_clusterCount := ?_
      upper_clusterCount := ?_
      clusterCount_eq := ?_
      parentBlocks := R.parentBlocks
      parentBlocks_pairwiseDisjoint := ?_
      parentBlocks_cover := ?_
      parentBlock_card := ?_
      cluster_subset_initial := ?_
      parent_sdiff_exception_eq_biUnion := ?_ }
  · simpa only [T] using R.lower_clusterCount
  · simpa only [T] using R.upper_clusterCount
  · simpa only [T] using R.clusterCount_eq
  · simpa only [T] using R.parentBlocks_pairwiseDisjoint
  · simpa only [T] using R.parentBlocks_cover
  · simpa only [T] using R.parentBlock_card
  · simpa only [T] using R.cluster_subset_parent
  · simpa only [T] using R.parent_sdiff_exception_eq_biUnion

end InducedStars.Regularity
