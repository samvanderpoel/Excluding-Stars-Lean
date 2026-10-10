import InducedStars.Regularity.TypeLemma
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-!
# Reindexing regularity partitions and Types

The enhanced Type Lemma records the children of each prescribed parent as an
abstract finite block of cluster indices.  This file supplies the finite
reindexing layer which turns those blocks into consecutive blocks.  The
orientation convention is that a reindexing equivalence sends a new index to
the corresponding old index.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u v w

section PairCounting

variable {I : Type*} [Fintype I] [LinearOrder I]

/-- The increasing ordered representatives of the edges of a finite simple
graph have the same cardinality as its edge finset. -/
private theorem card_increasingAdjPairs_eq_card_edgeFinset
    (H : SimpleGraph I) [DecidableRel H.Adj] :
    ((Finset.univ.offDiag.filter fun ij : I × I =>
        ij.1 < ij.2 ∧ H.Adj ij.1 ij.2).card) = H.edgeFinset.card := by
  classical
  let increasing : Finset (I × I) :=
    Finset.univ.offDiag.filter fun ij : I × I =>
      ij.1 < ij.2 ∧ H.Adj ij.1 ij.2
  let ordered : Finset (I × I) :=
    Finset.univ.filter fun ij : I × I => H.Adj ij.1 ij.2
  let swap : I × I ↪ I × I := (Equiv.prodComm I I).toEmbedding
  have hordered : ordered = increasing ∪ increasing.map swap := by
    ext ij
    constructor
    · intro hij
      have hadj : H.Adj ij.1 ij.2 :=
        (Finset.mem_filter.mp hij).2
      rcases lt_or_gt_of_ne hadj.ne with hlt | hgt
      · exact Finset.mem_union_left _ <|
          Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
            ⟨Finset.mem_univ _, Finset.mem_univ _, hadj.ne⟩, hlt, hadj⟩
      · apply Finset.mem_union_right
        refine Finset.mem_map.mpr ⟨(ij.2, ij.1), ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr
            ⟨Finset.mem_univ _, Finset.mem_univ _, hadj.ne.symm⟩,
              hgt, H.adj_symm hadj⟩
        · rfl
    · intro hij
      rcases Finset.mem_union.mp hij with hij | hij
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hij).2.2⟩
      · obtain ⟨ji, hji, hji_eq⟩ := Finset.mem_map.mp hij
        have hadj : H.Adj ji.1 ji.2 := (Finset.mem_filter.mp hji).2.2
        rw [← hji_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.adj_symm hadj⟩
  have hdisjoint : Disjoint increasing (increasing.map swap) := by
    rw [Finset.disjoint_left]
    intro ij hij hswap
    rcases ij with ⟨i, j⟩
    have hijlt : i < j := by
      change (i, j) ∈
        (Finset.univ.offDiag.filter fun ij : I × I =>
          ij.1 < ij.2 ∧ H.Adj ij.1 ij.2) at hij
      exact (Finset.mem_filter.mp hij).2.1
    obtain ⟨ji, hji, hji_eq⟩ := Finset.mem_map.mp hswap
    rcases ji with ⟨j', i'⟩
    have hjilt : j' < i' := by
      change (j', i') ∈
        (Finset.univ.offDiag.filter fun ij : I × I =>
          ij.1 < ij.2 ∧ H.Adj ij.1 ij.2) at hji
      exact (Finset.mem_filter.mp hji).2.1
    simp only [swap, Equiv.coe_toEmbedding, Equiv.prodComm_apply] at hji_eq
    rcases hji_eq with ⟨rfl, rfl⟩
    exact (lt_asymm hijlt hjilt).elim
  have horderedCard : ordered.card = 2 * increasing.card := by
    rw [hordered, Finset.card_union_of_disjoint hdisjoint, Finset.card_map]
    omega
  have hedge : 2 * H.edgeFinset.card = ordered.card := by
    simpa only [ordered] using H.two_mul_card_edgeFinset
  change increasing.card = H.edgeFinset.card
  omega

/-- The simple graph whose edges are precisely the distinct pairs on which a
given cluster family is not regular. -/
private noncomputable def irregularPairGraph
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon : ℝ)
    {q : ℕ} (clusters : Fin q → Finset V) : SimpleGraph (Fin q) :=
  SimpleGraph.fromRel fun i j =>
    ¬ IsRegularPair G epsilon (clusters i) (clusters j)

noncomputable local instance irregularPairGraphDecidableRel
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon : ℝ)
    {q : ℕ} (clusters : Fin q → Finset V) :
    DecidableRel (irregularPairGraph G epsilon clusters).Adj :=
  Classical.decRel _

private theorem irregularPairGraph_adj
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon : ℝ)
    {q : ℕ} (clusters : Fin q → Finset V) (i j : Fin q) :
    (irregularPairGraph G epsilon clusters).Adj i j ↔
      i ≠ j ∧ ¬ IsRegularPair G epsilon (clusters i) (clusters j) := by
  rw [irregularPairGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, fun hreg => h (IsRegularPair.symm G hreg)⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

private theorem irregularPairs_card_eq_edgeFinset
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon : ℝ)
    {q : ℕ} (clusters : Fin q → Finset V) :
    (irregularPairs G epsilon clusters).card =
      (irregularPairGraph G epsilon clusters).edgeFinset.card := by
  classical
  rw [← card_increasingAdjPairs_eq_card_edgeFinset
    (irregularPairGraph G epsilon clusters)]
  congr 1
  ext ij
  rcases ij with ⟨i, j⟩
  simp [irregularPairs, irregularPairGraph_adj]
  all_goals tauto

end PairCounting

section PartitionReindex

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {epsilon : ℝ}

/-- Reindex the nonexceptional classes of a regular partition.  The
equivalence maps each new index to the old index carrying the same class. -/
noncomputable def RegularPartition.reindexClusters {q : ℕ}
    (P : RegularPartition G epsilon) (e : Fin q ≃ Fin P.clusterCount) :
    RegularPartition G epsilon where
  clusterCount := q
  exceptional := P.exceptional
  clusters i := P.clusters (e i)
  clusters_pairwiseDisjoint := by
    intro i _ j _ hij
    exact P.clusters_disjoint (fun h => hij (e.injective h))
  exceptional_disjoint := fun i => P.exceptional_disjoint (e i)
  cover := by
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      have hv : v ∈ P.exceptional ∪ Finset.univ.biUnion P.clusters := by
        rw [P.cover]
        exact Finset.mem_univ v
      rcases Finset.mem_union.mp hv with hvE | hvC
      · exact Finset.mem_union_left _ hvE
      · obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hvC
        exact Finset.mem_union_right _ <|
          Finset.mem_biUnion.mpr ⟨e.symm j, Finset.mem_univ _, by simpa⟩
  equal_card := fun i j => P.equal_card (e i) (e j)
  exceptional_card_le := P.exceptional_card_le
  irregular_pair_card_le := by
    classical
    let Hnew := irregularPairGraph G epsilon (fun i : Fin q => P.clusters (e i))
    let Hold := irregularPairGraph G epsilon P.clusters
    let iso : Hnew ≃g Hold :=
      { toEquiv := e
        map_rel_iff' := by
          intro i j
          simp only [Hnew, Hold, irregularPairGraph_adj]
          exact and_congr e.injective.eq_iff.not (Iff.rfl) }
    have hcard :
        (irregularPairs G epsilon (fun i : Fin q => P.clusters (e i))).card =
          (irregularPairs G epsilon P.clusters).card := by
      calc
        _ = Hnew.edgeFinset.card :=
          irregularPairs_card_eq_edgeFinset G epsilon _
        _ = Hold.edgeFinset.card := iso.card_edgeFinset_eq
        _ = _ := (irregularPairs_card_eq_edgeFinset G epsilon _).symm
    rw [hcard]
    have hecard : q = P.clusterCount := by
      simpa only [Fintype.card_fin] using Fintype.card_congr e
    simpa only [hecard] using P.irregular_pair_card_le

namespace RegularPartition

variable {q : ℕ} (P : RegularPartition G epsilon)
  (e : Fin q ≃ Fin P.clusterCount)

@[simp] theorem reindexClusters_clusterCount :
    (P.reindexClusters e).clusterCount = q :=
  rfl

@[simp] theorem reindexClusters_exceptional :
    (P.reindexClusters e).exceptional = P.exceptional :=
  rfl

@[simp] theorem reindexClusters_clusters (i : Fin q) :
    (P.reindexClusters e).clusters i = P.clusters (e i) :=
  rfl

@[simp] theorem reindexClusters_clusterSize :
    (P.reindexClusters e).clusterSize = P.clusterSize := by
  by_cases hq : 0 < q
  · have hk : 0 < P.clusterCount := Nat.pos_of_ne_zero fun hk => by
      have hecard : q = P.clusterCount := by
        simpa only [Fintype.card_fin] using Fintype.card_congr e
      omega
    let i : Fin q := ⟨0, hq⟩
    rw [← P.cluster_card_eq (e i), ← (P.reindexClusters e).cluster_card_eq i]
    rfl
  · have hk : P.clusterCount = 0 := by
      have hecard : q = P.clusterCount := by
        simpa only [Fintype.card_fin] using Fintype.card_congr e
      omega
    simp [RegularPartition.clusterSize, Nat.eq_zero_of_not_pos hq, hk]

@[simp] theorem graphDensity_reindexClusters (i j : Fin q) :
    graphDensity G ((P.reindexClusters e).clusters i)
        ((P.reindexClusters e).clusters j) =
      graphDensity G (P.clusters (e i)) (P.clusters (e j)) :=
  rfl

/-- Reindexing clusters induces the expected isomorphism of regular-pair
graphs. -/
noncomputable def regularPairGraphReindexIso :
    (P.reindexClusters e).regularPairGraph ≃g P.regularPairGraph where
  toEquiv := e
  map_rel_iff' := by
    intro i j
    simp only [regularPairGraph_adj]
    exact and_congr e.injective.eq_iff.not (Iff.rfl)

@[simp] theorem regularPairGraphReindexIso_apply (i : Fin q) :
    P.regularPairGraphReindexIso e i = e i :=
  rfl

end RegularPartition

end PartitionReindex

section TypeReindex

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {epsilon delta : ℝ} {ℓ : ℕ}

/-- Fully polymorphic target-isomorphism transport for colored
homomorphisms.  The earlier `map_iso` API uses the same type parameter for
the source graph and the new target; reindexing a Type requires these to be
independent. -/
theorem RegularityColoredGraph.IsColoredHom.map_iso_target
    {A : Type u} {B : Type v} {X : Type w}
    {J : RegularityColoredGraph A} {J' : RegularityColoredGraph B}
    {H : SimpleGraph X} {φ : X → A}
    (hφ : RegularityColoredGraph.IsColoredHom H J φ)
    (e : RegularityColoredGraph.Iso J J') :
    RegularityColoredGraph.IsColoredHom H J' (e.graphIso ∘ φ) := by
  intro x y hxy
  constructor
  · intro hadj
    rcases hφ.map_edge hadj with hcollapse | ⟨himage, hcolor⟩
    · left
      constructor
      · exact congrArg e.graphIso hcollapse.1
      · change J'.vertexColor (e.graphIso (φ x)) = .blue
        exact (e.map_vertexColor (φ x)).trans hcollapse.2
    · right
      let himage' : J'.graph.Adj (e.graphIso (φ x)) (e.graphIso (φ y)) :=
        e.graphIso.map_rel_iff.mpr himage
      refine ⟨himage', ?_⟩
      have htransport := e.map_edgeColor (φ x) (φ y) himage
      rcases hcolor with hred | hblue
      · left
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
          himage' = .red
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
            himage' = J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hred
      · right
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
          himage' = .blue
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
            himage' = J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hblue
  · intro hnonedge
    rcases hφ.map_nonedge hxy hnonedge with hcollapse | ⟨himage, hcolor⟩
    · left
      constructor
      · exact congrArg e.graphIso hcollapse.1
      · change J'.vertexColor (e.graphIso (φ x)) = .green
        exact (e.map_vertexColor (φ x)).trans hcollapse.2
    · right
      let himage' : J'.graph.Adj (e.graphIso (φ x)) (e.graphIso (φ y)) :=
        e.graphIso.map_rel_iff.mpr himage
      refine ⟨himage', ?_⟩
      have htransport := e.map_edgeColor (φ x) (φ y) himage
      rcases hcolor with hred | hgreen
      · left
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
          himage' = .red
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
            himage' = J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hred
      · right
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
          himage' = .green
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y))
            himage' = J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hgreen

/-- The reduced colored graph of a reindexed partition is isomorphic to the
original reduced colored graph. -/
noncomputable def reducedColoredGraphReindexIso
    {q : ℕ} (P : RegularPartition G epsilon)
    (e : Fin q ≃ Fin P.clusterCount)
    (vertexColor : Fin P.clusterCount → TypeVertexColor) :
    RegularityColoredGraph.Iso
      (reducedColoredGraph (P.reindexClusters e) delta
        (fun i => vertexColor (e i)))
      (reducedColoredGraph P delta vertexColor) where
  graphIso := P.regularPairGraphReindexIso e
  map_vertexColor := fun _ => rfl
  map_edgeColor := by
    intro i j h
    rfl

namespace RegularityType

/-- Reindex the nonexceptional clusters and vertex colors of a Type.  Its
colored-homomorphism semantics are transported through the induced colored
graph isomorphism. -/
noncomputable def reindexClusters {q : ℕ}
    (T : RegularityType G epsilon delta ℓ)
    (e : Fin q ≃ Fin T.partition.clusterCount) :
    RegularityType G epsilon delta ℓ where
  epsilon_pos := T.epsilon_pos
  epsilon_lt_half := T.epsilon_lt_half
  delta_pos := T.delta_pos
  delta_lt_half := T.delta_lt_half
  partition := T.partition.reindexClusters e
  vertexColor i := T.vertexColor (e i)
  inducedEmbedding := by
    intro f hf H hhom
    change RegularityColoredGraph.ColoredHomExists H
      (reducedColoredGraph (T.partition.reindexClusters e) delta
        (fun i => T.vertexColor (e i))) at hhom
    obtain ⟨φ, hφ⟩ := hhom
    apply T.inducedEmbedding f hf H
    let iso : RegularityColoredGraph.Iso
        (reducedColoredGraph (T.partition.reindexClusters e) delta
          (fun i => T.vertexColor (e i)))
        (reducedColoredGraph T.partition delta T.vertexColor) :=
      reducedColoredGraphReindexIso (delta := delta)
        T.partition e T.vertexColor
    have hφtyped : RegularityColoredGraph.IsColoredHom H
        (reducedColoredGraph (T.partition.reindexClusters e) delta
          (fun i => T.vertexColor (e i))) φ := hφ
    have hφold : RegularityColoredGraph.IsColoredHom H
        (reducedColoredGraph T.partition delta T.vertexColor)
        (iso.graphIso ∘ φ) :=
      RegularityColoredGraph.IsColoredHom.map_iso_target
        (H := H) (φ := φ)
        (J := reducedColoredGraph (T.partition.reindexClusters e) delta
          (fun i => T.vertexColor (e i)))
        (J' := reducedColoredGraph T.partition delta T.vertexColor)
        hφtyped iso
    exact ⟨iso.graphIso ∘ φ, hφold⟩

variable {q : ℕ} (T : RegularityType G epsilon delta ℓ)
  (e : Fin q ≃ Fin T.partition.clusterCount)

@[simp] theorem reindexClusters_partition :
    (T.reindexClusters e).partition = T.partition.reindexClusters e :=
  rfl

@[simp] theorem reindexClusters_vertexColor (i : Fin q) :
    (T.reindexClusters e).vertexColor i = T.vertexColor (e i) :=
  rfl

@[simp] theorem reindexClusters_clusterCount :
    (T.reindexClusters e).partition.clusterCount = q :=
  rfl

@[simp] theorem reindexClusters_clusters (i : Fin q) :
    (T.reindexClusters e).partition.clusters i =
      T.partition.clusters (e i) :=
  rfl

end RegularityType

end TypeReindex

section CanonicalTypeLemmaIndexing

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {eta delta : ℝ} {ℓ s L U : ℕ}
  {initial : EquitableInitialPartition V s}

namespace TypeLemmaResult

variable (R : TypeLemmaResult G eta delta ℓ initial L U)

/-- Enumerate the abstract child block below a prescribed parent. -/
noncomputable def childEquiv (i : Fin s) :
    Fin R.childCount ≃ {j // j ∈ R.parentBlocks i} :=
  (finCongr (R.parentBlock_card i).symm).trans
    (R.parentBlocks i).equivFin.symm

@[simp] theorem childEquiv_mem_parentBlock (i : Fin s)
    (a : Fin R.childCount) :
    (R.childEquiv i a : Fin R.regularityType.partition.clusterCount) ∈
      R.parentBlocks i :=
  (R.childEquiv i a).property

/-- The old cluster index selected by a parent/child coordinate. -/
noncomputable def canonicalChildMap
    (ia : Fin s × Fin R.childCount) :
    Fin R.regularityType.partition.clusterCount :=
  (R.childEquiv ia.1 ia.2).1

private theorem canonicalChildMap_bijective :
    Function.Bijective R.canonicalChildMap := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hiMem : R.canonicalChildMap (i, a) ∈ R.parentBlocks i :=
      (R.childEquiv i a).property
    have hjMem : R.canonicalChildMap (j, b) ∈ R.parentBlocks j :=
      (R.childEquiv j b).property
    have hij : i = j := by
      by_contra hne
      exact Finset.disjoint_left.mp
        (R.parentBlocks_pairwiseDisjoint (Set.mem_univ i)
          (Set.mem_univ j) hne) hiMem (h ▸ hjMem)
    subst j
    have hab : a = b := by
      apply (R.childEquiv i).injective
      apply Subtype.ext
      exact h
    subst b
    rfl
  · intro j
    have hjcover : j ∈ Finset.univ.biUnion R.parentBlocks := by
      rw [R.parentBlocks_cover]
      exact Finset.mem_univ j
    obtain ⟨i, _, hji⟩ := Finset.mem_biUnion.mp hjcover
    obtain ⟨a, ha⟩ := (R.childEquiv i).surjective ⟨j, hji⟩
    refine ⟨(i, a), ?_⟩
    exact congrArg Subtype.val ha

/-- Send the consecutive index `i * childCount + a` to the corresponding old
abstract child in the block below parent `i`. -/
noncomputable def canonicalClusterEquiv :
    Fin (s * R.childCount) ≃
      Fin R.regularityType.partition.clusterCount :=
  finProdFinEquiv.symm.trans
    (Equiv.ofBijective R.canonicalChildMap R.canonicalChildMap_bijective)

@[simp] theorem canonicalClusterEquiv_finProdFinEquiv
    (i : Fin s) (a : Fin R.childCount) :
    R.canonicalClusterEquiv (finProdFinEquiv (i, a)) =
      (R.childEquiv i a).1 := by
  simp [canonicalClusterEquiv, canonicalChildMap]

/-- Consecutive canonical children land in exactly their prescribed parent
block. -/
@[simp] theorem canonicalClusterEquiv_mem_parentBlock
    (i : Fin s) (a : Fin R.childCount) :
    R.canonicalClusterEquiv (finProdFinEquiv (i, a)) ∈
      R.parentBlocks i := by
  rw [R.canonicalClusterEquiv_finProdFinEquiv]
  exact (R.childEquiv i a).property

/-- Membership in an abstract parent block is characterized by the first
coordinate of the canonical consecutive index. -/
theorem canonicalClusterEquiv_mem_parentBlock_iff
    (x : Fin (s * R.childCount)) (i : Fin s) :
    R.canonicalClusterEquiv x ∈ R.parentBlocks i ↔
      (finProdFinEquiv.symm x).1 = i := by
  let ix := (finProdFinEquiv.symm x).1
  let ax := (finProdFinEquiv.symm x).2
  have hx : finProdFinEquiv (ix, ax) = x := by
    exact finProdFinEquiv.apply_symm_apply x
  constructor
  · intro hmem
    by_contra hne
    exact Finset.disjoint_left.mp
      (R.parentBlocks_pairwiseDisjoint (Set.mem_univ ix)
        (Set.mem_univ i) hne)
      (by simpa only [hx] using
        R.canonicalClusterEquiv_mem_parentBlock ix ax) hmem
  · intro h
    subst i
    simpa only [hx] using
      R.canonicalClusterEquiv_mem_parentBlock ix ax

/-- The Type Lemma output reindexed so that the children of parent `i` have
the consecutive indices `i * childCount + a`. -/
noncomputable def canonicalType : RegularityType G eta delta ℓ :=
  R.regularityType.reindexClusters R.canonicalClusterEquiv

@[simp] theorem canonicalType_clusterCount :
    R.canonicalType.partition.clusterCount = s * R.childCount :=
  rfl

@[simp] theorem canonicalType_clusters
    (x : Fin (s * R.childCount)) :
    R.canonicalType.partition.clusters x =
      R.regularityType.partition.clusters (R.canonicalClusterEquiv x) :=
  rfl

@[simp] theorem canonicalType_cluster_finProdFinEquiv
    (i : Fin s) (a : Fin R.childCount) :
    R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) =
      R.regularityType.partition.clusters (R.childEquiv i a) := by
  rw [R.canonicalType_clusters,
    R.canonicalClusterEquiv_finProdFinEquiv]

theorem canonicalType_cluster_subset_initial
    (i : Fin s) (a : Fin R.childCount) :
    R.canonicalType.partition.clusters (finProdFinEquiv (i, a)) ⊆
      initial.parts i := by
  rw [R.canonicalType_cluster_finProdFinEquiv]
  exact R.cluster_subset_initial i (R.childEquiv i a)
    (R.childEquiv i a).property

end TypeLemmaResult

end CanonicalTypeLemmaIndexing

end InducedStars.Regularity
