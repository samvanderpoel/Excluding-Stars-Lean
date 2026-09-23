import InducedStars.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.Density
import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Real.Basic

/-!
# Finite graph regularity in the paper's normalization

This file supplies the part of the regularity language that is independent of
external results.  Mathlib's `SimpleGraph.edgeDensity` has exactly the desired
once-oriented cross-edge normalization, so `graphDensity` is only its real
cast.  The paper uses a non-strict error bound, while Mathlib's
`SimpleGraph.IsUniform` uses a strict one; `IsRegularPair` therefore records
the paper's predicate explicitly.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u v

variable {V : Type u} {W : Type v}

section Density

variable [Fintype V] [DecidableEq V]

/-- The paper's cross-density `e_G(A,B) / (|A||B|)`, valued in `ℝ`.

`SimpleGraph.edgeDensity` uses the once-oriented set of cross edges and is
valued in `ℚ`; this definition is its canonical real cast. -/
noncomputable def graphDensity (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : ℝ :=
  (G.edgeDensity A B : ℝ)

@[simp]
theorem graphDensity_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    graphDensity G A B =
      (G.interedges A B).card / ((A.card : ℝ) * (B.card : ℝ)) := by
  simp [graphDensity, SimpleGraph.edgeDensity_def, div_eq_mul_inv]

theorem graphDensity_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    graphDensity G A B = graphDensity G B A := by
  simp only [graphDensity, G.edgeDensity_comm A B]

theorem graphDensity_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    0 ≤ graphDensity G A B := by
  simpa only [graphDensity, Rat.cast_nonneg] using G.edgeDensity_nonneg A B

theorem graphDensity_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    graphDensity G A B ≤ 1 := by
  rw [graphDensity]
  exact_mod_cast G.edgeDensity_le_one A B

/-- The paper's non-strict definition of an `ε`-regular pair. -/
def IsRegularPair (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (A B : Finset V) : Prop :=
  ∀ ⦃A' : Finset V⦄, A' ⊆ A →
    ∀ ⦃B' : Finset V⦄, B' ⊆ B →
      ε * (A.card : ℝ) ≤ A'.card →
      ε * (B.card : ℝ) ≤ B'.card →
        |graphDensity G A' B' - graphDensity G A B| ≤ ε

/-- Mathlib's strict regularity predicate implies the paper's non-strict one. -/
theorem IsRegularPair.of_isUniform (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} {A B : Finset V} (h : G.IsUniform ε A B) :
    IsRegularPair G ε A B := by
  intro A' hA' B' hB' hAcard hBcard
  exact (h hA' hB' (by simpa [mul_comm] using hAcard)
    (by simpa [mul_comm] using hBcard)).le

/-- Regularity is symmetric in its two vertex sets. -/
theorem IsRegularPair.symm (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε : ℝ} {A B : Finset V} (h : IsRegularPair G ε A B) :
    IsRegularPair G ε B A := by
  intro B' hB' A' hA' hBcard hAcard
  rw [graphDensity_comm G B' A', graphDensity_comm G B A]
  exact h hA' hB' hAcard hBcard

theorem isRegularPair_comm (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (A B : Finset V) :
    IsRegularPair G ε A B ↔ IsRegularPair G ε B A :=
  ⟨IsRegularPair.symm G, IsRegularPair.symm G⟩

/-- Increasing the tolerance weakens the regular-pair predicate. -/
theorem IsRegularPair.mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {ε ε' : ℝ} {A B : Finset V} (hε : ε ≤ ε')
    (hreg : IsRegularPair G ε A B) : IsRegularPair G ε' A B := by
  intro A' hA' B' hB' hAcard hBcard
  exact (hreg hA' hB'
    (le_trans (by gcongr) hAcard)
    (le_trans (by gcongr) hBcard)).trans hε

/-- A large subpair has density close to its regular parent pair. -/
theorem IsRegularPair.density_subsets (G : SimpleGraph V) [DecidableRel G.Adj]
    {η μ : ℝ} {A B A' B' : Finset V}
    (hreg : IsRegularPair G η A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hμA : μ * (A.card : ℝ) ≤ A'.card)
    (hμB : μ * (B.card : ℝ) ≤ B'.card)
    (hημ : η ≤ μ) :
    |graphDensity G A' B' - graphDensity G A B| ≤ η := by
  apply hreg hA hB
  · calc
      η * (A.card : ℝ) ≤ μ * (A.card : ℝ) := by
        gcongr
      _ ≤ A'.card := hμA
  · calc
      η * (B.card : ℝ) ≤ μ * (B.card : ℝ) := by
        gcongr
      _ ≤ B'.card := hμB

/-- The non-strict slicing lemma in the form used by the BTW adapter.

The hypotheses expose both losses: `η ≤ μ * ε'` makes subsets that are
`ε'`-large inside the children still `η`-large inside the parents, and
`2η ≤ ε'` pays for the two density comparisons through the parent pair. -/
theorem IsRegularPair.slice (G : SimpleGraph V) [DecidableRel G.Adj]
    {η μ ε' : ℝ} {A B A' B' : Finset V}
    (hreg : IsRegularPair G η A B)
    (hA : A' ⊆ A) (hB : B' ⊆ B)
    (hμA : μ * (A.card : ℝ) ≤ A'.card)
    (hμB : μ * (B.card : ℝ) ≤ B'.card)
    (hμ : 0 ≤ μ) (hε' : 0 ≤ ε')
    (hημε' : η ≤ μ * ε') (h2η : 2 * η ≤ ε') :
    IsRegularPair G ε' A' B' := by
  intro A'' hA'' B'' hB'' hAcard hBcard
  have hA''A : A'' ⊆ A := hA''.trans hA
  have hB''B : B'' ⊆ B := hB''.trans hB
  have hηA : η * (A.card : ℝ) ≤ A''.card := by
    calc
      η * (A.card : ℝ) ≤ (μ * ε') * (A.card : ℝ) := by gcongr
      _ = ε' * (μ * (A.card : ℝ)) := by ring
      _ ≤ ε' * (A'.card : ℝ) := by gcongr
      _ ≤ A''.card := hAcard
  have hηB : η * (B.card : ℝ) ≤ B''.card := by
    calc
      η * (B.card : ℝ) ≤ (μ * ε') * (B.card : ℝ) := by gcongr
      _ = ε' * (μ * (B.card : ℝ)) := by ring
      _ ≤ ε' * (B'.card : ℝ) := by gcongr
      _ ≤ B''.card := hBcard
  have hbig := hreg hA''A hB''B hηA hηB
  have hchild : |graphDensity G A' B' - graphDensity G A B| ≤ η := by
    apply hreg hA hB
    · exact hηA.trans (Nat.cast_le.2 (card_le_card hA''))
    · exact hηB.trans (Nat.cast_le.2 (card_le_card hB''))
  calc
    |graphDensity G A'' B'' - graphDensity G A' B'| =
        |(graphDensity G A'' B'' - graphDensity G A B) -
          (graphDensity G A' B' - graphDensity G A B)| := by ring_nf
    _ ≤ |graphDensity G A'' B'' - graphDensity G A B| +
          |graphDensity G A' B' - graphDensity G A B| := abs_sub _ _
    _ ≤ η + η := add_le_add hbig hchild
    _ = 2 * η := by ring
    _ ≤ ε' := h2η

end Density

section Partition

variable [Fintype V] [DecidableEq V]

/-- The unordered irregular cluster pairs, represented uniquely by `i < j`. -/
noncomputable def irregularPairs (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) {k : ℕ} (clusters : Fin k → Finset V) : Finset (Fin k × Fin k) := by
  classical
  exact Finset.univ.offDiag.filter fun ij =>
    ij.1 < ij.2 ∧ ¬IsRegularPair G ε (clusters ij.1) (clusters ij.2)

/-- The paper's regular partition, including its exceptional class.

The nonexceptional classes are indexed by `Fin clusterCount`; their exact
equality of sizes is stronger than Mathlib's general equipartition convention
and is therefore recorded explicitly. -/
structure RegularPartition (G : SimpleGraph V) [DecidableRel G.Adj] (ε : ℝ) where
  clusterCount : ℕ
  exceptional : Finset V
  clusters : Fin clusterCount → Finset V
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  exceptional_disjoint : ∀ i, Disjoint exceptional (clusters i)
  cover : exceptional ∪ Finset.univ.biUnion clusters = Finset.univ
  equal_card : ∀ i j, (clusters i).card = (clusters j).card
  exceptional_card_le :
    (exceptional.card : ℝ) ≤ ε * (Fintype.card V : ℝ)
  irregular_pair_card_le :
    ((irregularPairs G ε clusters).card : ℝ) ≤
      ε * (Nat.choose clusterCount 2 : ℝ)

namespace RegularPartition

variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

/-- The graph on cluster indices whose edges are exactly regular pairs. -/
noncomputable def regularPairGraph (P : RegularPartition G ε) :
    SimpleGraph (Fin P.clusterCount) :=
  SimpleGraph.fromRel fun i j => IsRegularPair G ε (P.clusters i) (P.clusters j)

@[simp]
theorem regularPairGraph_adj (P : RegularPartition G ε) (i j : Fin P.clusterCount) :
    P.regularPairGraph.Adj i j ↔
      i ≠ j ∧ IsRegularPair G ε (P.clusters i) (P.clusters j) := by
  rw [regularPairGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, h | h⟩
    · exact ⟨hij, h⟩
    · exact ⟨hij, IsRegularPair.symm G h⟩
  · rintro ⟨hij, h⟩
    exact ⟨hij, Or.inl h⟩

theorem clusters_disjoint (P : RegularPartition G ε) {i j : Fin P.clusterCount}
    (hij : i ≠ j) : Disjoint (P.clusters i) (P.clusters j) := by
  exact P.clusters_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij

/-- The common cardinality of the nonexceptional classes. -/
def clusterSize (P : RegularPartition G ε) : ℕ :=
  if h : 0 < P.clusterCount then (P.clusters ⟨0, h⟩).card else 0

theorem cluster_card_eq (P : RegularPartition G ε) (i : Fin P.clusterCount) :
    (P.clusters i).card = P.clusterSize := by
  simp only [clusterSize]
  split_ifs with h
  · exact P.equal_card i ⟨0, h⟩
  · exact (h (Nat.zero_lt_of_lt i.isLt)).elim

/-- Increasing the tolerance turns a regular partition into a regular
partition with the same classes. -/
noncomputable def mono (P : RegularPartition G ε) {ε' : ℝ} (hε : ε ≤ ε') :
    RegularPartition G ε' where
  clusterCount := P.clusterCount
  exceptional := P.exceptional
  clusters := P.clusters
  clusters_pairwiseDisjoint := P.clusters_pairwiseDisjoint
  exceptional_disjoint := P.exceptional_disjoint
  cover := P.cover
  equal_card := P.equal_card
  exceptional_card_le := by
    calc
      (P.exceptional.card : ℝ) ≤ ε * (Fintype.card V : ℝ) := P.exceptional_card_le
      _ ≤ ε' * (Fintype.card V : ℝ) := by gcongr
  irregular_pair_card_le := by
    classical
    have hsub : irregularPairs G ε' P.clusters ⊆ irregularPairs G ε P.clusters := by
      intro ij hij
      rw [irregularPairs, mem_filter] at hij ⊢
      refine ⟨hij.1, hij.2.1, ?_⟩
      exact fun hreg => hij.2.2 (hreg.mono G hε)
    calc
      ((irregularPairs G ε' P.clusters).card : ℝ) ≤
          (irregularPairs G ε P.clusters).card := by
            exact_mod_cast card_le_card hsub
      _ ≤ ε * (Nat.choose P.clusterCount 2 : ℝ) := P.irregular_pair_card_le
      _ ≤ ε' * (Nat.choose P.clusterCount 2 : ℝ) := by gcongr

end RegularPartition

end Partition

section GraphRelabeling

variable {V : Type u} {W : Type v}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {G' : SimpleGraph W}
  [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-- Image of a finite vertex set under a graph isomorphism. -/
def relabelFinset (e : G ≃g G') (A : Finset V) : Finset W :=
  A.map e.toEquiv.toEmbedding

@[simp]
theorem mem_relabelFinset (e : G ≃g G') (A : Finset V) (x : W) :
    x ∈ relabelFinset e A ↔ e.symm x ∈ A := by
  simp only [relabelFinset, Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (RelIso.symm_apply_apply e a).symm ▸ ha
  · intro hx
    refine ⟨e.symm x, hx, ?_⟩
    exact RelIso.apply_symm_apply e x

@[simp]
theorem card_relabelFinset (e : G ≃g G') (A : Finset V) :
    (relabelFinset e A).card = A.card := by
  simp [relabelFinset]

/-- Cross-density is invariant under a graph isomorphism. -/
theorem graphDensity_relabel (e : G ≃g G') (A B : Finset V) :
    graphDensity G' (relabelFinset e A) (relabelFinset e B) =
      graphDensity G A B := by
  have hcard :
      (G'.interedges (relabelFinset e A) (relabelFinset e B)).card =
        (G.interedges A B).card := by
    rw [← Finset.card_map
      (e.toEquiv.toEmbedding.prodMap e.toEquiv.toEmbedding)]
    congr 1
    ext xy
    rcases xy with ⟨x, y⟩
    simp [SimpleGraph.interedges, Rel.interedges, relabelFinset,
      ← e.symm.map_rel_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hadj⟩
      exact ⟨e.symm x, e.symm y, ⟨⟨hx, hy⟩, hadj⟩, by simp, by simp⟩
    · rintro ⟨a, b, ⟨⟨ha, hb⟩, hadj⟩, rfl, rfl⟩
      constructor
      · constructor
        · exact (RelIso.symm_apply_apply e a).symm ▸ ha
        · exact (RelIso.symm_apply_apply e b).symm ▸ hb
      · simpa only [RelIso.symm_apply_apply] using hadj
  rw [graphDensity_eq, graphDensity_eq, hcard]
  simp [relabelFinset]

/-- A regular pair remains regular after relabeling by a graph isomorphism. -/
theorem IsRegularPair.relabel {ε : ℝ} {A B : Finset V}
    (h : IsRegularPair G ε A B) (e : G ≃g G') :
    IsRegularPair G' ε (relabelFinset e A) (relabelFinset e B) := by
  intro A' hA' B' hB' hAcard hBcard
  obtain ⟨a, ha, rfl⟩ := Finset.subset_map_iff.mp hA'
  obtain ⟨b, hb, rfl⟩ := Finset.subset_map_iff.mp hB'
  change
    |graphDensity G' (relabelFinset e a) (relabelFinset e b) -
      graphDensity G' (relabelFinset e A) (relabelFinset e B)| ≤ ε
  rw [graphDensity_relabel e a b, graphDensity_relabel e A B]
  apply h ha hb
  · simpa [relabelFinset] using hAcard
  · simpa [relabelFinset] using hBcard

/-- Regular-pair status is invariant under graph isomorphism. -/
theorem isRegularPair_relabel_iff (e : G ≃g G') (ε : ℝ) (A B : Finset V) :
    IsRegularPair G' ε (relabelFinset e A) (relabelFinset e B) ↔
      IsRegularPair G ε A B := by
  constructor
  · intro h a ha b hb hacard hbcard
    have hma : relabelFinset e a ⊆ relabelFinset e A := by
      simpa only [relabelFinset, Finset.map_subset_map] using ha
    have hmb : relabelFinset e b ⊆ relabelFinset e B := by
      simpa only [relabelFinset, Finset.map_subset_map] using hb
    have h' := h hma hmb
      (by simpa [relabelFinset] using hacard)
      (by simpa [relabelFinset] using hbcard)
    simpa only [graphDensity_relabel e a b, graphDensity_relabel e A B] using h'
  · exact fun h => h.relabel e

namespace RegularPartition

/-- Relabel every class of a regular partition along a graph isomorphism. -/
noncomputable def relabel {ε : ℝ} (P : RegularPartition G ε) (e : G ≃g G') :
    RegularPartition G' ε where
  clusterCount := P.clusterCount
  exceptional := relabelFinset e P.exceptional
  clusters i := relabelFinset e (P.clusters i)
  clusters_pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint
      ((P.clusters i).map e.toEquiv.toEmbedding)
      ((P.clusters j).map e.toEquiv.toEmbedding)
    rw [Finset.disjoint_map]
    exact P.clusters_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
  exceptional_disjoint := by
    intro i
    change Disjoint
      (P.exceptional.map e.toEquiv.toEmbedding)
      ((P.clusters i).map e.toEquiv.toEmbedding)
    rw [Finset.disjoint_map]
    exact P.exceptional_disjoint i
  cover := by
    have hmap := congrArg (Finset.map e.toEquiv.toEmbedding) P.cover
    ext x
    have hx := Finset.ext_iff.mp hmap x
    simpa [relabelFinset] using hx
  equal_card := by
    intro i j
    simpa [relabelFinset] using P.equal_card i j
  exceptional_card_le := by
    have hcard : Fintype.card V = Fintype.card W := e.card_eq
    simpa [relabelFinset, ← hcard] using P.exceptional_card_le
  irregular_pair_card_le := by
    have hirregular :
        irregularPairs G' ε (fun i => relabelFinset e (P.clusters i)) =
          irregularPairs G ε P.clusters := by
      ext ij
      simp only [irregularPairs, Finset.mem_filter, Finset.mem_offDiag,
        Finset.mem_univ, true_and]
      rw [isRegularPair_relabel_iff]
    rw [hirregular]
    exact P.irregular_pair_card_le

@[simp]
theorem relabel_clusterCount {ε : ℝ} (P : RegularPartition G ε) (e : G ≃g G') :
    (P.relabel e).clusterCount = P.clusterCount :=
  rfl

@[simp]
theorem relabel_exceptional {ε : ℝ} (P : RegularPartition G ε) (e : G ≃g G') :
    (P.relabel e).exceptional = relabelFinset e P.exceptional :=
  rfl

@[simp]
theorem relabel_clusters {ε : ℝ} (P : RegularPartition G ε) (e : G ≃g G')
    (i : Fin P.clusterCount) :
    (P.relabel e).clusters i = relabelFinset e (P.clusters i) :=
  rfl

end RegularPartition

end GraphRelabeling

section BTWConfigurations

variable [Fintype V] [DecidableEq V]

/-- A `(μ, ε, q)`-subpartition inside a specified parent set.

This is the invariant ambient-set form of BTW's Definition preceding Lemma
2.5.  Taking `parent = univ` gives its printed formulation; taking another
parent is the same definition for the induced graph on that parent. -/
structure HomogeneousSubpartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (parent : Finset V) (μ ε : ℝ) (q : ℕ) where
  parts : Fin q → Finset V
  parts_subset : ∀ i, parts i ⊆ parent
  parts_pairwiseDisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) parts
  card_lower : ∀ i, μ * (parent.card : ℝ) ≤ (parts i).card
  regular : ∀ {i j}, i ≠ j → IsRegularPair G ε (parts i) (parts j)

namespace HomogeneousSubpartition

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {parent : Finset V} {μ ε : ℝ} {q : ℕ}

/-- Every child pair has density strictly below `1/2`. -/
def IsSparse (S : HomogeneousSubpartition G parent μ ε q) : Prop :=
  ∀ {i j}, i ≠ j → graphDensity G (S.parts i) (S.parts j) < 1 / 2

/-- Every child pair has density at least `1/2`. -/
def IsDense (S : HomogeneousSubpartition G parent μ ε q) : Prop :=
  ∀ {i j}, i ≠ j → 1 / 2 ≤ graphDensity G (S.parts i) (S.parts j)

theorem parts_disjoint (S : HomogeneousSubpartition G parent μ ε q)
    {i j : Fin q} (hij : i ≠ j) : Disjoint (S.parts i) (S.parts j) :=
  S.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij

theorem parts_nonempty (S : HomogeneousSubpartition G parent μ ε q)
    (hμ : 0 < μ) (hparent : μ⁻¹ ≤ (parent.card : ℝ)) (i : Fin q) :
    (S.parts i).Nonempty := by
  have hone : (1 : ℝ) ≤ μ * (parent.card : ℝ) := by
    calc
      (1 : ℝ) = μ * μ⁻¹ := (mul_inv_cancel₀ hμ.ne').symm
      _ ≤ μ * (parent.card : ℝ) := by gcongr
  have hcard : (1 : ℝ) ≤ (S.parts i).card := hone.trans (S.card_lower i)
  exact Finset.card_pos.mp (by exact_mod_cast hcard)

end HomogeneousSubpartition

/-! ### Transport from an induced parent graph -/

/-- Inclusion of the subtype belonging to a finite parent set. -/
def parentEmbedding (parent : Finset V) : {x // x ∈ parent} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

/-- View a finset of vertices of an induced parent graph in the ambient type. -/
def liftFinset (parent : Finset V) (s : Finset {x // x ∈ parent}) : Finset V :=
  s.map (parentEmbedding parent)

@[simp]
theorem card_liftFinset (parent : Finset V) (s : Finset {x // x ∈ parent}) :
    (liftFinset parent s).card = s.card := by
  simp [liftFinset]

@[simp]
theorem mem_liftFinset {parent : Finset V} {s : Finset {x // x ∈ parent}} {x : V} :
    x ∈ liftFinset parent s ↔
      ∃ hx : x ∈ parent, (⟨x, hx⟩ : {x // x ∈ parent}) ∈ s := by
  simp [liftFinset, parentEmbedding]

/-- Cross-density is unchanged when sets in an induced parent graph are
viewed in the ambient graph. -/
theorem graphDensity_induce_lift (G : SimpleGraph V) [DecidableRel G.Adj]
    (parent : Finset V) (s t : Finset {x // x ∈ parent}) :
    graphDensity (G.induce (↑parent : Set V)) s t =
      graphDensity G (liftFinset parent s) (liftFinset parent t) := by
  have hcard :
      ((G.induce (↑parent : Set V)).interedges s t).card =
        (G.interedges (liftFinset parent s) (liftFinset parent t)).card := by
    rw [← Finset.card_map ((parentEmbedding parent).prodMap (parentEmbedding parent))]
    congr 1
    simp only [SimpleGraph.interedges, Rel.interedges, liftFinset]
    rw [← Finset.prodMap_map_product, Finset.filter_map]
    rfl
  rw [graphDensity_eq, graphDensity_eq, hcard, card_liftFinset, card_liftFinset]

/-- Exact regular-pair transport between an induced parent graph and the
ambient graph. -/
theorem isRegularPair_induce_lift_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (parent : Finset V) (ε : ℝ) (s t : Finset {x // x ∈ parent}) :
    IsRegularPair (G.induce (↑parent : Set V)) ε s t ↔
      IsRegularPair G ε (liftFinset parent s) (liftFinset parent t) := by
  constructor
  · intro h A hA B hB hAcard hBcard
    obtain ⟨a, ha, rfl⟩ := Finset.subset_map_iff.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.subset_map_iff.mp hB
    change
      |graphDensity G (liftFinset parent a) (liftFinset parent b) -
          graphDensity G (liftFinset parent s) (liftFinset parent t)| ≤ ε
    rw [← graphDensity_induce_lift G parent a b,
      ← graphDensity_induce_lift G parent s t]
    exact h ha hb (by simpa only [card_liftFinset, Finset.card_map] using hAcard)
      (by simpa only [card_liftFinset, Finset.card_map] using hBcard)
  · intro h a ha b hb hacard hbcard
    have hla : liftFinset parent a ⊆ liftFinset parent s := by
      simpa only [liftFinset, Finset.map_subset_map] using ha
    have hlb : liftFinset parent b ⊆ liftFinset parent t := by
      simpa only [liftFinset, Finset.map_subset_map] using hb
    simpa only [← graphDensity_induce_lift] using
      h hla hlb (by simpa only [card_liftFinset] using hacard)
        (by simpa only [card_liftFinset] using hbcard)

/-- Lift a homogeneous subpartition of an induced parent graph into the
ambient vertex type. -/
noncomputable def liftHomogeneousSubpartition (G : SimpleGraph V)
    [DecidableRel G.Adj] (parent : Finset V) {μ ε : ℝ} {q : ℕ}
    (S : HomogeneousSubpartition (G.induce (↑parent : Set V))
      Finset.univ μ ε q) :
    HomogeneousSubpartition G parent μ ε q where
  parts i := liftFinset parent (S.parts i)
  parts_subset i := by
    intro x hx
    rw [mem_liftFinset] at hx
    exact hx.choose
  parts_pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint
      ((S.parts i).map (parentEmbedding parent))
      ((S.parts j).map (parentEmbedding parent))
    rw [Finset.disjoint_map]
    exact S.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
  card_lower i := by
    have hcard : Fintype.card ↥(↑parent : Set V) = parent.card := by
      change Fintype.card ↥parent = parent.card
      exact Fintype.card_coe parent
    simpa only [card_liftFinset, Finset.card_univ, hcard] using S.card_lower i
  regular hij :=
    (isRegularPair_induce_lift_iff G parent ε (S.parts _) (S.parts _)).mp
      (S.regular hij)

theorem liftHomogeneousSubpartition_isSparse_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] (parent : Finset V) {μ ε : ℝ} {q : ℕ}
    (S : HomogeneousSubpartition (G.induce (↑parent : Set V))
      Finset.univ μ ε q) :
    (liftHomogeneousSubpartition G parent S).IsSparse ↔ S.IsSparse := by
  constructor <;> intro h i j hij
  · change graphDensity (G.induce (↑parent : Set V)) (S.parts i) (S.parts j) < 1 / 2
    rw [graphDensity_induce_lift]
    exact h hij
  · change graphDensity G (liftFinset parent (S.parts i))
      (liftFinset parent (S.parts j)) < 1 / 2
    rw [← graphDensity_induce_lift]
    exact h hij

theorem liftHomogeneousSubpartition_isDense_iff (G : SimpleGraph V)
    [DecidableRel G.Adj] (parent : Finset V) {μ ε : ℝ} {q : ℕ}
    (S : HomogeneousSubpartition (G.induce (↑parent : Set V))
      Finset.univ μ ε q) :
    (liftHomogeneousSubpartition G parent S).IsDense ↔ S.IsDense := by
  constructor <;> intro h i j hij
  · change 1 / 2 ≤ graphDensity (G.induce (↑parent : Set V)) (S.parts i) (S.parts j)
    rw [graphDensity_induce_lift]
    exact h hij
  · change 1 / 2 ≤ graphDensity G (liftFinset parent (S.parts i))
      (liftFinset parent (S.parts j))
    rw [← graphDensity_induce_lift]
    exact h hij

/-- The operational cluster-family hypotheses checked in the published proof
of BTW Lemma 2.9 (journal p. 671).

The printed statement of BTW Lemma 2.4 phrases its candidate sets as actual
clusters of one regular partition.  Since the Lemma 2.5 children used on
p. 671 need not be equal-sized partition classes, this project proves the
family embedding theorem locally instead of strengthening the external
Lemma 2.4 interface. This is the selected-image construction used in the
paper's proof of `lemma:type-lemma`. -/
structure InducedEmbeddingConfiguration (G : SimpleGraph V) [DecidableRel G.Adj]
    {f : ℕ} (H : SimpleGraph (Fin f)) (ε d : ℝ) where
  parts : Fin f → Finset V
  parts_pairwiseDisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin f)) parts
  parts_nonempty : ∀ i, (parts i).Nonempty
  regular : ∀ {i j}, i ≠ j → IsRegularPair G ε (parts i) (parts j)
  edge_density : ∀ {i j}, H.Adj i j → d ≤ graphDensity G (parts i) (parts j)
  nonedge_density : ∀ {i j}, i ≠ j → ¬H.Adj i j →
    graphDensity G (parts i) (parts j) ≤ 1 - d

namespace InducedEmbeddingConfiguration

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {f : ℕ} {H : SimpleGraph (Fin f)} {ε ε' d : ℝ}

/-- Increase only the regularity tolerance of an embedding configuration. -/
def mono (C : InducedEmbeddingConfiguration G H ε d) (hε : ε ≤ ε') :
    InducedEmbeddingConfiguration G H ε' d where
  parts := C.parts
  parts_pairwiseDisjoint := C.parts_pairwiseDisjoint
  parts_nonempty := C.parts_nonempty
  regular hij := (C.regular hij).mono G hε
  edge_density := C.edge_density
  nonedge_density := C.nonedge_density

end InducedEmbeddingConfiguration

end BTWConfigurations

/-- The project's induced-embedding predicate is Mathlib's strong graph
embedding / induced containment, not ordinary subgraph containment. -/
abbrev InducedEmbeds (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  H ⊴ G

theorem inducedEmbeds_iff_nonempty_embedding (H : SimpleGraph V) (G : SimpleGraph W) :
    InducedEmbeds H G ↔ Nonempty (H ↪g G) :=
  Iff.rfl

end InducedStars.Regularity
