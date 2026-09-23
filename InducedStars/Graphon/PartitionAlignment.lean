import InducedStars.Regularity.Basic
import Mathlib.Tactic

/-!
# Alignment of a regular partition with equal graphon cells

This file constructs the finite relabeling used to compare a graph on `Fin n`
with a `k`-cell type graphon.  Taking `k` copies of every vertex makes each
nonexceptional cluster contribute equally to its own target cell, while the
exceptional copies are distributed one per target cell.
-/

noncomputable section

open Finset

namespace InducedStars
namespace Regularity

/-- The exceptional class and the equal nonexceptional classes account for
all vertices of a regular partition. -/
theorem RegularPartition.exceptional_card_add_mul_clusterSize
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) :
    P.exceptional.card + P.clusterCount * P.clusterSize = Fintype.card V := by
  classical
  let U : Finset V := Finset.univ.biUnion P.clusters
  have hdisj : Disjoint P.exceptional U := by
    rw [Finset.disjoint_left]
    intro v hvE hvU
    obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvU
    exact (Finset.disjoint_left.mp (P.exceptional_disjoint i)) hvE hvi
  have hUcard : U.card = P.clusterCount * P.clusterSize := by
    dsimp only [U]
    rw [Finset.card_biUnion (by simpa using P.clusters_pairwiseDisjoint)]
    simp [P.cluster_card_eq]
  have hcover : P.exceptional ∪ U = (Finset.univ : Finset V) := by
    exact P.cover
  rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisj, hUcard]

/-- `Fin n` specialization of the partition cardinality identity. -/
theorem RegularPartition.exceptional_card_add_mul_clusterSize_eq
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) :
    P.exceptional.card + P.clusterCount * P.clusterSize = n := by
  simpa using P.exceptional_card_add_mul_clusterSize

/-- Every nonexceptional vertex lies in a unique cluster. -/
theorem RegularPartition.existsUnique_cluster_of_not_mem_exceptional
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : V} (hv : v ∉ P.exceptional) :
    ∃! i : Fin P.clusterCount, v ∈ P.clusters i := by
  classical
  have hvCover : v ∈ P.exceptional ∪ Finset.univ.biUnion P.clusters := by
    rw [P.cover]
    exact Finset.mem_univ v
  have hvUnion : v ∈ Finset.univ.biUnion P.clusters :=
    (Finset.mem_union.mp hvCover).resolve_left hv
  obtain ⟨i, _, hvi⟩ := Finset.mem_biUnion.mp hvUnion
  refine ⟨i, hvi, ?_⟩
  intro j hvj
  by_contra hij
  exact (Finset.disjoint_left.mp (P.clusters_disjoint hij)) hvj hvi

/-- Target cell assigned to a copied vertex.  Exceptional vertices use their
copy index; nonexceptional vertices use their unique cluster index. -/
noncomputable def RegularPartition.alignmentLabel
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (x : Fin n × Fin P.clusterCount) :
    Fin P.clusterCount :=
  if hx : x.1 ∈ P.exceptional then x.2
  else Classical.choose (P.existsUnique_cluster_of_not_mem_exceptional hx)

@[simp]
theorem RegularPartition.alignmentLabel_of_mem_exceptional
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : Fin n} (hv : v ∈ P.exceptional)
    (b : Fin P.clusterCount) :
    P.alignmentLabel (v, b) = b := by
  simp [RegularPartition.alignmentLabel, hv]

@[simp]
theorem RegularPartition.alignmentLabel_of_mem_cluster
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : Fin n} (i : Fin P.clusterCount)
    (hv : v ∈ P.clusters i) (b : Fin P.clusterCount) :
    P.alignmentLabel (v, b) = i := by
  classical
  have hvE : v ∉ P.exceptional := by
    intro hv'
    exact (Finset.disjoint_left.mp (P.exceptional_disjoint i)) hv' hv
  rw [RegularPartition.alignmentLabel, dite_eq_right hvE]
  let j := Classical.choose (P.existsUnique_cluster_of_not_mem_exceptional hvE)
  have hj : v ∈ P.clusters j :=
    (Classical.choose_spec (P.existsUnique_cluster_of_not_mem_exceptional hvE)).1
  change j = i
  by_contra hji
  exact (Finset.disjoint_left.mp (P.clusters_disjoint hji)) hj hv

/-- A nonexceptional copied vertex belongs to the cluster selected by its
alignment label. -/
theorem RegularPartition.mem_cluster_alignmentLabel
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : Fin n} (hv : v ∉ P.exceptional)
    (b : Fin P.clusterCount) :
    v ∈ P.clusters (P.alignmentLabel (v, b)) := by
  classical
  rw [RegularPartition.alignmentLabel, dite_eq_right hv]
  exact (Classical.choose_spec
    (P.existsUnique_cluster_of_not_mem_exceptional hv)).1

/-- The source fiber over target cell `i` consists of one copy of every
exceptional vertex and all `k` copies of every vertex of cluster `i`. -/
noncomputable def RegularPartition.alignmentFiberEquiv
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (i : Fin P.clusterCount) :
    {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} ≃
      {v : Fin n // v ∈ P.exceptional} ⊕
        ({v : Fin n // v ∈ P.clusters i} × Fin P.clusterCount) := by
  classical
  let toF : {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} →
      {v : Fin n // v ∈ P.exceptional} ⊕
        ({v : Fin n // v ∈ P.clusters i} × Fin P.clusterCount) :=
    fun x ↦ if hv : x.1.1 ∈ P.exceptional then
      Sum.inl ⟨x.1.1, hv⟩
    else
      Sum.inr (⟨x.1.1, by
        simpa only [x.2] using
          P.mem_cluster_alignmentLabel hv x.1.2⟩, x.1.2)
  let invF : {v : Fin n // v ∈ P.exceptional} ⊕
      ({v : Fin n // v ∈ P.clusters i} × Fin P.clusterCount) →
      {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} :=
    fun y ↦ match y with
      | Sum.inl v => ⟨(v.1, i), P.alignmentLabel_of_mem_exceptional v.2 i⟩
      | Sum.inr vb => ⟨(vb.1.1, vb.2),
          P.alignmentLabel_of_mem_cluster i vb.1.2 vb.2⟩
  refine ⟨toF, invF, ?_, ?_⟩
  · intro x
    rcases x with ⟨⟨v, b⟩, hx⟩
    apply Subtype.ext
    by_cases hv : v ∈ P.exceptional
    · have hb : b = i := by
        simpa using (P.alignmentLabel_of_mem_exceptional hv b).symm.trans hx
      simp only [toF, invF, dite_eq_left hv]
      exact Prod.ext rfl hb.symm
    · simp only [toF, invF, dite_eq_right hv]
  · intro y
    rcases y with v | vb
    · simp only [toF, invF, dite_eq_left v.2]
    · have hvE : vb.1.1 ∉ P.exceptional := by
        intro hv
        exact (Finset.disjoint_left.mp (P.exceptional_disjoint i)) hv vb.1.2
      simp only [toF, invF, dite_eq_right hvE]

/-- The source fiber assigned to each target cell has exactly `n` elements. -/
theorem RegularPartition.card_alignmentLabel_fiber
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (i : Fin P.clusterCount) :
    Fintype.card {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} = n := by
  calc
    Fintype.card {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} =
        Fintype.card ({v : Fin n // v ∈ P.exceptional} ⊕
          ({v : Fin n // v ∈ P.clusters i} × Fin P.clusterCount)) :=
      Fintype.card_congr (P.alignmentFiberEquiv i)
    _ = P.exceptional.card + (P.clusters i).card * P.clusterCount := by simp
    _ = n := by
      rw [P.cluster_card_eq]
      simpa [Nat.mul_comm] using P.exceptional_card_add_mul_clusterSize

/-- The fiber of `Prod.fst` over a fixed first coordinate is equivalent to
the unrestricted second coordinate. -/
def fstFiberEquiv {α β : Type*} (a : α) :
    {x : α × β // x.1 = a} ≃ β where
  toFun x := x.1.2
  invFun b := ⟨(a, b), rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.2.symm rfl
  right_inv _ := rfl

/-- Fiberwise equivalence between copied vertices assigned to `i` and the
target pairs whose first coordinate is `i`. -/
noncomputable def RegularPartition.alignmentFiberTargetEquiv
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (i : Fin P.clusterCount) :
    {x : Fin n × Fin P.clusterCount // P.alignmentLabel x = i} ≃
      {y : Fin P.clusterCount × Fin n // y.1 = i} :=
  Fintype.equivOfCardEq <| (P.card_alignmentLabel_fiber i).trans <| by
    simpa using
      (Fintype.card_congr (fstFiberEquiv (β := Fin n) i)).symm

/-- An alignment of `k` copied graph vertices with `k` equal target cells.
The first target coordinate is exactly `alignmentLabel`. -/
noncomputable def RegularPartition.alignmentEquiv
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) :
    (Fin n × Fin P.clusterCount) ≃ (Fin P.clusterCount × Fin n) :=
  Equiv.ofFiberEquiv fun i ↦ P.alignmentFiberTargetEquiv i

theorem RegularPartition.alignmentEquiv_fst
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (x : Fin n × Fin P.clusterCount) :
    (P.alignmentEquiv x).1 = P.alignmentLabel x := by
  exact Equiv.ofFiberEquiv_map (fun i ↦ P.alignmentFiberTargetEquiv i) x

/-- Every copy of an exceptional vertex is sent to the cell indexed by its
copy coordinate. -/
theorem RegularPartition.alignmentEquiv_fst_of_mem_exceptional
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : Fin n} (hv : v ∈ P.exceptional)
    (b : Fin P.clusterCount) :
    (P.alignmentEquiv (v, b)).1 = b := by
  rw [P.alignmentEquiv_fst, P.alignmentLabel_of_mem_exceptional hv b]

/-- Every copy of a vertex in cluster `i` is sent to target cell `i`. -/
theorem RegularPartition.alignmentEquiv_fst_of_mem_cluster
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) {v : Fin n} (i : Fin P.clusterCount)
    (hv : v ∈ P.clusters i) (b : Fin P.clusterCount) :
    (P.alignmentEquiv (v, b)).1 = i := by
  rw [P.alignmentEquiv_fst, P.alignmentLabel_of_mem_cluster i hv b]

/-- Bundled existence statement for the partition-alignment equivalence. -/
theorem RegularPartition.exists_alignmentEquiv
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {ε : ℝ}
    (P : RegularPartition G ε) (_hk : 0 < P.clusterCount) :
    ∃ e : (Fin n × Fin P.clusterCount) ≃ (Fin P.clusterCount × Fin n),
      (∀ v ∈ P.exceptional, ∀ b, (e (v, b)).1 = b) ∧
      (∀ i, ∀ v ∈ P.clusters i, ∀ b, (e (v, b)).1 = i) := by
  refine ⟨P.alignmentEquiv, ?_, ?_⟩
  · intro v hv b
    exact P.alignmentEquiv_fst_of_mem_exceptional hv b
  · intro i v hv b
    exact P.alignmentEquiv_fst_of_mem_cluster i hv b

end Regularity
end InducedStars
