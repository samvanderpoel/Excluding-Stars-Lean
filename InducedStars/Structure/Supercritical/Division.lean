import DenseGraph.FiniteModels.WeightedGraph
import DenseGraph.FiniteModels.Multipartite
import InducedStars.FiniteModels.GraphonLimits
import Mathlib.Order.WellFounded
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

/-!
# Supercritical divisions and defect graphs

This file contains the finite, deterministic bookkeeping used in the
supercritical structural argument.  A division consists of nonempty,
pairwise-disjoint main parts; vertices outside their union form the sparse
set.  The defect graph records missing edges inside a main part and present
edges between the main support and the sparse set.  The combined defect graph
also retains the graph induced by the sparse set.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V W : Type*}

/-! ## Divisions -/

/-- A supercritical division has `k - 1` nonempty, pairwise-disjoint main
parts.  The main parts need not cover the ambient finite vertex set. -/
structure SupercriticalDivision (k : ℕ) (V : Type*) [Fintype V]
    [DecidableEq V] where
  parts : Fin (k - 1) → Finset V
  parts_nonempty : ∀ i, (parts i).Nonempty
  parts_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (k - 1))) parts

namespace SupercriticalDivision

variable [Fintype V] [DecidableEq V]

/-- The union of the main parts of a division. -/
def support (D : SupercriticalDivision k V) : Finset V :=
  Finset.univ.biUnion D.parts

/-- Vertices not belonging to a main part. -/
def sparse (D : SupercriticalDivision k V) : Finset V :=
  Finset.univ \ D.support

@[simp] theorem mem_support {D : SupercriticalDivision k V} {v : V} :
    v ∈ D.support ↔ ∃ i, v ∈ D.parts i := by
  simp [support]

@[simp] theorem mem_sparse {D : SupercriticalDivision k V} {v : V} :
    v ∈ D.sparse ↔ v ∉ D.support := by
  simp [sparse]

theorem part_subset_support (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) : D.parts i ⊆ D.support := by
  intro v hv
  exact mem_support.mpr ⟨i, hv⟩

theorem sparse_disjoint_part (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) : Disjoint D.sparse (D.parts i) := by
  rw [Finset.disjoint_left]
  intro v hvs hvp
  exact (mem_sparse.mp hvs) (part_subset_support D i hvp)

theorem part_disjoint_sparse (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) : Disjoint (D.parts i) D.sparse :=
  (D.sparse_disjoint_part i).symm

@[simp] theorem support_union_sparse (D : SupercriticalDivision k V) :
    D.support ∪ D.sparse = Finset.univ := by
  ext v
  by_cases hv : v ∈ D.support <;> simp [hv]

@[simp] theorem support_inter_sparse (D : SupercriticalDivision k V) :
    D.support ∩ D.sparse = ∅ := by
  ext v
  simp

theorem card_support_add_card_sparse (D : SupercriticalDivision k V) :
    D.support.card + D.sparse.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint]
  · simp
  · exact Finset.disjoint_left.mpr fun v hv hs ↦ (mem_sparse.mp hs) hv

theorem card_support (D : SupercriticalDivision k V) :
    D.support.card = ∑ i, (D.parts i).card := by
  rw [support, Finset.card_biUnion]
  simpa using D.parts_pairwiseDisjoint

theorem card_parts_add_card_sparse (D : SupercriticalDivision k V) :
    (∑ i, (D.parts i).card) + D.sparse.card = Fintype.card V := by
  rw [← D.card_support]
  exact D.card_support_add_card_sparse

theorem mem_part_unique (D : SupercriticalDivision k V) {v : V}
    {i j : Fin (k - 1)} (hvi : v ∈ D.parts i)
    (hvj : v ∈ D.parts j) : i = j := by
  by_contra hij
  exact (Finset.disjoint_left.mp
    (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hvi hvj

/-- Every vertex is either sparse or belongs to one unique main part. -/
theorem sparse_or_existsUnique_part (D : SupercriticalDivision k V)
    (v : V) : v ∈ D.sparse ∨ ∃! i, v ∈ D.parts i := by
  by_cases hs : v ∈ D.sparse
  · exact Or.inl hs
  · right
    have hv : v ∈ D.support := by simpa using hs
    obtain ⟨i, hi⟩ := mem_support.mp hv
    exact ⟨i, hi, fun j hj ↦ D.mem_part_unique hj hi⟩

/-- Transport a division across a vertex equivalence. -/
def relabel [Fintype W] [DecidableEq W] (D : SupercriticalDivision k V)
    (e : V ≃ W) : SupercriticalDivision k W where
  parts i := (D.parts i).map e.toEmbedding
  parts_nonempty i := by
    obtain ⟨v, hv⟩ := D.parts_nonempty i
    exact ⟨e v, by simp [hv]⟩
  parts_pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint ((D.parts i).map e.toEmbedding)
      ((D.parts j).map e.toEmbedding)
    rw [Finset.disjoint_left]
    intro w hwi hwj
    simp only [Finset.mem_map] at hwi hwj
    obtain ⟨vi, hvi, rfl⟩ := hwi
    obtain ⟨vj, hvj, hvij⟩ := hwj
    have : vi = vj := e.injective hvij.symm
    subst vj
    exact (Finset.disjoint_left.mp
      (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hvi hvj

@[simp] theorem mem_relabel_part [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W)
    (i : Fin (k - 1)) (w : W) :
    w ∈ (D.relabel e).parts i ↔ e.symm w ∈ D.parts i := by
  simp [relabel]

@[simp] theorem mem_relabel_support [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W) (w : W) :
    w ∈ (D.relabel e).support ↔ e.symm w ∈ D.support := by
  simp

@[simp] theorem mem_relabel_sparse [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W) (w : W) :
    w ∈ (D.relabel e).sparse ↔ e.symm w ∈ D.sparse := by
  simp

/-- A finite vertex set admits a division as soon as it has at least one
vertex for each main part. -/
theorem exists_of_sub_one_le_card (hcard : k - 1 ≤ Fintype.card V) :
    Nonempty (SupercriticalDivision k V) := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let seed : Fin (k - 1) → V := fun i ↦
    e.symm ⟨i.1, i.2.trans_le hcard⟩
  have hseed : Function.Injective seed := by
    intro i j hij
    dsimp [seed] at hij
    have hf := e.symm.injective hij
    apply Fin.ext
    exact congrArg (fun z : Fin (Fintype.card V) ↦ z.1) hf
  exact ⟨{
    parts := fun i ↦ {seed i}
    parts_nonempty := fun i ↦ Finset.singleton_nonempty _
    parts_pairwiseDisjoint := by
      intro i _ j _ hij
      change Disjoint ({seed i} : Finset V) {seed j}
      rw [Finset.disjoint_singleton]
      exact fun h ↦ hij (hseed h)
  }⟩

end SupercriticalDivision

/-! ## Location relations and defect graphs -/

section DefectGraphs

variable [Fintype V] [DecidableEq V]

/-- Two vertices belong to the same main part. -/
def SupercriticalDivision.SameMainPart (D : SupercriticalDivision k V)
    (x y : V) : Prop :=
  ∃ i, x ∈ D.parts i ∧ y ∈ D.parts i

instance (D : SupercriticalDivision k V) (x y : V) :
    Decidable (D.SameMainPart x y) := Classical.propDecidable _

theorem SupercriticalDivision.sameMainPart_comm
    (D : SupercriticalDivision k V) (x y : V) :
    D.SameMainPart x y ↔ D.SameMainPart y x := by
  constructor <;> rintro ⟨i, hx, hy⟩ <;> exact ⟨i, hy, hx⟩

theorem SupercriticalDivision.sameMainPart_imp_support
    {D : SupercriticalDivision k V} {x y : V}
    (h : D.SameMainPart x y) : x ∈ D.support ∧ y ∈ D.support := by
  obtain ⟨i, hx, hy⟩ := h
  exact ⟨D.part_subset_support i hx, D.part_subset_support i hy⟩

theorem SupercriticalDivision.not_sameMainPart_of_mem_distinct
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)} (hij : i ≠ j)
    {x y : V} (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    ¬ D.SameMainPart x y := by
  rintro ⟨a, hxa, hya⟩
  have hai : a = i := D.mem_part_unique hxa hx
  have haj : a = j := D.mem_part_unique hya hy
  exact hij (hai.symm.trans haj)

/-- A support--sparse unordered location pair. -/
def SupercriticalDivision.IsSupportSparsePair
    (D : SupercriticalDivision k V) (x y : V) : Prop :=
  (x ∈ D.support ∧ y ∈ D.sparse) ∨
    (y ∈ D.support ∧ x ∈ D.sparse)

theorem SupercriticalDivision.isSupportSparsePair_comm
    (D : SupercriticalDivision k V) (x y : V) :
    D.IsSupportSparsePair x y ↔ D.IsSupportSparsePair y x := by
  simp only [IsSupportSparsePair]
  tauto

private def supercriticalDefectCondition (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) : Prop :=
  (D.SameMainPart x y ∧ ¬ G.Adj x y) ∨
    (D.IsSupportSparsePair x y ∧ G.Adj x y)

private theorem supercriticalDefectCondition_comm (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) :
    supercriticalDefectCondition G D x y ↔
      supercriticalDefectCondition G D y x := by
  simp only [supercriticalDefectCondition, D.sameMainPart_comm x y,
    D.isSupportSparsePair_comm x y, G.adj_comm]

/-- Missing edges inside main parts together with present edges between the
main support and the sparse set. -/
def supercriticalDefectGraph (G : SimpleGraph V)
    (D : SupercriticalDivision k V) : SimpleGraph V :=
  SimpleGraph.fromRel (supercriticalDefectCondition G D)

@[simp] theorem supercriticalDefectGraph_adj (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) :
    (supercriticalDefectGraph G D).Adj x y ↔
      x ≠ y ∧ supercriticalDefectCondition G D x y := by
  rw [supercriticalDefectGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, h⟩
    · exact ⟨hxy, (supercriticalDefectCondition_comm G D y x).mp h⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

theorem supercriticalDefectGraph_adj_of_mem_same_part
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) {x y : V} (hx : x ∈ D.parts i)
    (hy : y ∈ D.parts i) :
    (supercriticalDefectGraph G D).Adj x y ↔ x ≠ y ∧ ¬ G.Adj x y := by
  rw [supercriticalDefectGraph_adj]
  have hsame : D.SameMainPart x y := ⟨i, hx, hy⟩
  have hxs : x ∈ D.support := D.part_subset_support i hx
  have hys : y ∈ D.support := D.part_subset_support i hy
  have hxns : x ∉ D.sparse := by simpa using hxs
  have hyns : y ∉ D.sparse := by simpa using hys
  simp [supercriticalDefectCondition, hsame,
    SupercriticalDivision.IsSupportSparsePair, hxs, hys, hxns, hyns]

theorem supercriticalDefectGraph_not_adj_of_mem_distinct_parts
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {i j : Fin (k - 1)} (hij : i ≠ j) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    ¬ (supercriticalDefectGraph G D).Adj x y := by
  rw [supercriticalDefectGraph_adj]
  have hsame := D.not_sameMainPart_of_mem_distinct hij hx hy
  have hxs := D.part_subset_support i hx
  have hys := D.part_subset_support j hy
  have hxns : x ∉ D.sparse := by simpa using hxs
  have hyns : y ∉ D.sparse := by simpa using hys
  simp [supercriticalDefectCondition, hsame,
    SupercriticalDivision.IsSupportSparsePair, hxs, hys, hxns, hyns]

theorem supercriticalDefectGraph_adj_support_sparse
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    (supercriticalDefectGraph G D).Adj x y ↔ G.Adj x y := by
  rw [supercriticalDefectGraph_adj]
  have hxy : x ≠ y := fun h ↦ (SupercriticalDivision.mem_sparse.mp hy) (h ▸ hx)
  have hnSame : ¬ D.SameMainPart x y := fun h ↦
    (SupercriticalDivision.mem_sparse.mp hy)
      (SupercriticalDivision.sameMainPart_imp_support h).2
  simp [supercriticalDefectCondition, hnSame,
    SupercriticalDivision.IsSupportSparsePair, hx, hy, hxy]

theorem supercriticalDefectGraph_not_adj_of_mem_sparse
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    ¬ (supercriticalDefectGraph G D).Adj x y := by
  rw [supercriticalDefectGraph_adj]
  have hxns := SupercriticalDivision.mem_sparse.mp hx
  have hyns := SupercriticalDivision.mem_sparse.mp hy
  have hnSame : ¬ D.SameMainPart x y := fun h ↦ hxns
    (SupercriticalDivision.sameMainPart_imp_support h).1
  simp [supercriticalDefectCondition, hnSame,
    SupercriticalDivision.IsSupportSparsePair, hx, hy, hxns, hyns]

private def sparseInducedCondition (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) : Prop :=
  x ∈ D.sparse ∧ y ∈ D.sparse ∧ G.Adj x y

/-- The ambient graph whose edges are exactly the edges induced by the sparse
set. -/
def sparseInducedGraph (G : SimpleGraph V)
    (D : SupercriticalDivision k V) : SimpleGraph V :=
  SimpleGraph.fromRel (sparseInducedCondition G D)

@[simp] theorem sparseInducedGraph_adj (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) :
    (sparseInducedGraph G D).Adj x y ↔
      x ∈ D.sparse ∧ y ∈ D.sparse ∧ G.Adj x y := by
  rw [sparseInducedGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.2.1, h.1, (G.adj_comm y x).mp h.2.2⟩
  · intro h
    exact ⟨G.ne_of_adj h.2.2, Or.inl h⟩

/-- The defect graph used in the degree trichotomy. -/
def combinedSupercriticalDefectGraph (G : SimpleGraph V)
    (D : SupercriticalDivision k V) : SimpleGraph V :=
  supercriticalDefectGraph G D ⊔ sparseInducedGraph G D

@[simp] theorem combinedSupercriticalDefectGraph_adj (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) :
    (combinedSupercriticalDefectGraph G D).Adj x y ↔
      (supercriticalDefectGraph G D).Adj x y ∨
        (x ∈ D.sparse ∧ y ∈ D.sparse ∧ G.Adj x y) := by
  simp [combinedSupercriticalDefectGraph]

theorem combinedSupercriticalDefectGraph_adj_of_mem_same_part
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) {x y : V} (hx : x ∈ D.parts i)
    (hy : y ∈ D.parts i) :
    (combinedSupercriticalDefectGraph G D).Adj x y ↔
      x ≠ y ∧ ¬ G.Adj x y := by
  rw [combinedSupercriticalDefectGraph_adj,
    supercriticalDefectGraph_adj_of_mem_same_part G D i hx hy]
  have hxns : x ∉ D.sparse := by
    simpa using D.part_subset_support i hx
  simp [hxns]

theorem combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {i j : Fin (k - 1)} (hij : i ≠ j) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    ¬ (combinedSupercriticalDefectGraph G D).Adj x y := by
  intro h
  rw [combinedSupercriticalDefectGraph_adj] at h
  rcases h with h | h
  · exact supercriticalDefectGraph_not_adj_of_mem_distinct_parts G D hij hx hy h
  have hxns : x ∉ D.sparse := by simpa using D.part_subset_support i hx
  exact hxns h.1

theorem combinedSupercriticalDefectGraph_adj_support_sparse
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    (combinedSupercriticalDefectGraph G D).Adj x y ↔ G.Adj x y := by
  rw [combinedSupercriticalDefectGraph_adj,
    supercriticalDefectGraph_adj_support_sparse G D hx hy]
  have hxns : x ∉ D.sparse := by simpa using hx
  simp [hxns]

theorem combinedSupercriticalDefectGraph_adj_of_mem_sparse
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    (combinedSupercriticalDefectGraph G D).Adj x y ↔ G.Adj x y := by
  constructor
  · intro h
    rw [combinedSupercriticalDefectGraph_adj] at h
    rcases h with h | h
    · exact False.elim (supercriticalDefectGraph_not_adj_of_mem_sparse G D hx hy h)
    · exact h.2.2
  · intro h
    rw [combinedSupercriticalDefectGraph_adj]
    exact Or.inr ⟨hx, hy, h⟩

/-! ## Cost and model graph -/

/-- The number of missing internal main-part edges plus the number of present
edges incident with the sparse set. -/
def supercriticalDefectCost (G : SimpleGraph V)
    (D : SupercriticalDivision k V) : ℕ :=
  (finiteGraphEdges (supercriticalDefectGraph G D)).card +
    (finiteGraphEdges (sparseInducedGraph G D)).card

/-- Toggle exactly the combined defect edges.  Equivalently, this completes
each main part, preserves edges between distinct main parts, and isolates the
sparse set. -/
def supercriticalDivisionModelGraph (G : SimpleGraph V)
    (D : SupercriticalDivision k V) : SimpleGraph V :=
  (G \ combinedSupercriticalDefectGraph G D) ⊔
    (combinedSupercriticalDefectGraph G D \ G)

private theorem prop_xor_xor_cancel (A B : Prop) :
    (A ∧ ¬ ((A ∧ ¬ B) ∨ (B ∧ ¬ A))) ∨
        (((A ∧ ¬ B) ∨ (B ∧ ¬ A)) ∧ ¬ A) ↔ B := by
  tauto

@[simp] theorem supercriticalDivisionModelGraph_adj (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (x y : V) :
    (supercriticalDivisionModelGraph G D).Adj x y ↔
      (G.Adj x y ∧ ¬ (combinedSupercriticalDefectGraph G D).Adj x y) ∨
        ((combinedSupercriticalDefectGraph G D).Adj x y ∧ ¬ G.Adj x y) := by
  simp [supercriticalDivisionModelGraph]

theorem supercriticalDivisionModelGraph_adj_of_mem_same_part
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) {x y : V} (hx : x ∈ D.parts i)
    (hy : y ∈ D.parts i) :
    (supercriticalDivisionModelGraph G D).Adj x y ↔ x ≠ y := by
  rw [supercriticalDivisionModelGraph_adj,
    combinedSupercriticalDefectGraph_adj_of_mem_same_part G D i hx hy]
  constructor
  · intro h
    by_contra hxy
    subst y
    simp at h
  · intro hxy
    by_cases hG : G.Adj x y <;> simp [hxy, hG]

theorem supercriticalDivisionModelGraph_adj_of_mem_distinct_parts
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {i j : Fin (k - 1)} (hij : i ≠ j) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    (supercriticalDivisionModelGraph G D).Adj x y ↔ G.Adj x y := by
  rw [supercriticalDivisionModelGraph_adj]
  have hc : ¬ (combinedSupercriticalDefectGraph G D).Adj x y :=
    combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
      G D hij hx hy
  constructor
  · rintro (⟨hG, -⟩ | ⟨hC, -⟩)
    · exact hG
    · exact False.elim (hc hC)
  · intro hG
    exact Or.inl ⟨hG, hc⟩

theorem supercriticalDivisionModelGraph_not_adj_of_mem_sparse_left
    (G : SimpleGraph V) (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.sparse) :
    ¬ (supercriticalDivisionModelGraph G D).Adj x y := by
  rw [supercriticalDivisionModelGraph_adj]
  by_cases hy : y ∈ D.sparse
  · have hc := combinedSupercriticalDefectGraph_adj_of_mem_sparse G D hx hy
    tauto
  · have hys : y ∈ D.support := by simpa using hy
    have hc : (combinedSupercriticalDefectGraph G D).Adj x y ↔ G.Adj x y := by
      rw [(combinedSupercriticalDefectGraph G D).adj_comm, G.adj_comm]
      exact combinedSupercriticalDefectGraph_adj_support_sparse G D hys hx
    tauto

theorem finiteGraphEdges_defect_disjoint_sparseInduced
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    Disjoint (finiteGraphEdges (supercriticalDefectGraph G D))
      (finiteGraphEdges (sparseInducedGraph G D)) := by
  rw [Finset.disjoint_left]
  intro e heD heS
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet] at heD heS
      rw [sparseInducedGraph_adj] at heS
      exact supercriticalDefectGraph_not_adj_of_mem_sparse G D heS.1 heS.2.1 heD

theorem card_finiteGraphEdges_combinedSupercriticalDefectGraph
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (finiteGraphEdges (combinedSupercriticalDefectGraph G D)).card =
      supercriticalDefectCost G D := by
  classical
  have hfin : finiteGraphEdges (combinedSupercriticalDefectGraph G D) =
      finiteGraphEdges (supercriticalDefectGraph G D) ∪
        finiteGraphEdges (sparseInducedGraph G D) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y => simp [combinedSupercriticalDefectGraph]
  rw [hfin, Finset.card_union_of_disjoint
    (finiteGraphEdges_defect_disjoint_sparseInduced G D)]
  rfl

theorem graphEditFinset_model_eq_combinedDefect {n : ℕ}
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n)) :
    graphEditFinset G (supercriticalDivisionModelGraph G D) =
      finiteGraphEdges (combinedSupercriticalDefectGraph G D) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mem_graphEditFinset, mem_finiteGraphEdges]
      simp only [SimpleGraph.mem_edgeSet]
      rw [supercriticalDivisionModelGraph_adj]
      exact prop_xor_xor_cancel _ _

theorem simpleGraphEditFinset_model_eq_combinedDefect
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    DenseGraph.simpleGraphEditFinset G (supercriticalDivisionModelGraph G D) =
      finiteGraphEdges (combinedSupercriticalDefectGraph G D) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [DenseGraph.mem_simpleGraphEditFinset, mem_finiteGraphEdges]
      simp only [SimpleGraph.mem_edgeSet]
      rw [supercriticalDivisionModelGraph_adj]
      exact prop_xor_xor_cancel _ _

theorem simpleGraphEditDistance_divisionModel
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    DenseGraph.simpleGraphEditDistance G (supercriticalDivisionModelGraph G D) =
      supercriticalDefectCost G D := by
  rw [DenseGraph.simpleGraphEditDistance,
    simpleGraphEditFinset_model_eq_combinedDefect,
    card_finiteGraphEdges_combinedSupercriticalDefectGraph]

/-- Exact unordered edit cost of the division model. -/
theorem graphEditDistance_divisionModel {n : ℕ}
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n)) :
    graphEditDistance G (supercriticalDivisionModelGraph G D) =
      supercriticalDefectCost G D := by
  rw [graphEditDistance, graphEditFinset_model_eq_combinedDefect,
    card_finiteGraphEdges_combinedSupercriticalDefectGraph]

/-- Same-label finite cut discrepancy from the division model, with the
ordered/unordered factor two explicit. -/
theorem finiteLabeledCutDist_divisionModel_le {n : ℕ}
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n)) :
    DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (supercriticalDivisionModelGraph G D)) ≤
      2 * (supercriticalDefectCost G D : ℝ) / (n : ℝ) ^ 2 := by
  simpa only [DenseGraph.simpleGraphEditDistance_eq_graphEditDistance,
    graphEditDistance_divisionModel, Fintype.card_fin] using
    (DenseGraph.finiteLabeledCutDist_ofSimpleGraph_le_simpleGraphEdit
      G (supercriticalDivisionModelGraph G D))

end DefectGraphs

/-! ## Canonical minimizing divisions -/

section Canonical

variable [Fintype V] [DecidableEq V]

/-- A fixed division minimizing defect cost.  The size proof is an explicit
argument so the definition remains honest on vertex sets too small to admit a
division. -/
def canonicalSupercriticalDivision (G : SimpleGraph V)
    (hcard : k - 1 ≤ Fintype.card V) : SupercriticalDivision k V :=
  Function.argminOn (supercriticalDefectCost G)
    (Set.univ : Set (SupercriticalDivision k V))
    ⟨Classical.choice (SupercriticalDivision.exists_of_sub_one_le_card hcard),
      Set.mem_univ _⟩

theorem canonicalSupercriticalDivision_minimal (G : SimpleGraph V)
    (hcard : k - 1 ≤ Fintype.card V) (D : SupercriticalDivision k V) :
    supercriticalDefectCost G (canonicalSupercriticalDivision G hcard) ≤
      supercriticalDefectCost G D := by
  exact Function.argminOn_le _ _ (Set.mem_univ D)

theorem canonicalSupercriticalDivision_proof_irrel (G : SimpleGraph V)
    (hcard hcard' : k - 1 ≤ Fintype.card V) :
    canonicalSupercriticalDivision G hcard =
      canonicalSupercriticalDivision G hcard' := by
  congr

def canonicalSupercriticalDefectGraph (G : SimpleGraph V)
    (hcard : k - 1 ≤ Fintype.card V) : SimpleGraph V :=
  supercriticalDefectGraph G (canonicalSupercriticalDivision G hcard)

def canonicalCombinedDefectGraph (G : SimpleGraph V)
    (hcard : k - 1 ≤ Fintype.card V) : SimpleGraph V :=
  combinedSupercriticalDefectGraph G (canonicalSupercriticalDivision G hcard)

@[simp] theorem canonicalSupercriticalDefectGraph_proof_irrel
    (G : SimpleGraph V) (hcard hcard' : k - 1 ≤ Fintype.card V) :
    canonicalSupercriticalDefectGraph G hcard =
      canonicalSupercriticalDefectGraph G hcard' := by
  simp only [canonicalSupercriticalDefectGraph,
    canonicalSupercriticalDivision_proof_irrel G hcard hcard']

@[simp] theorem canonicalCombinedDefectGraph_proof_irrel
    (G : SimpleGraph V) (hcard hcard' : k - 1 ≤ Fintype.card V) :
    canonicalCombinedDefectGraph G hcard =
      canonicalCombinedDefectGraph G hcard' := by
  simp only [canonicalCombinedDefectGraph,
    canonicalSupercriticalDivision_proof_irrel G hcard hcard']

def canonicalSupercriticalDefectCost (G : SimpleGraph V)
    (hcard : k - 1 ≤ Fintype.card V) : ℕ :=
  supercriticalDefectCost G (canonicalSupercriticalDivision G hcard)

@[simp] theorem canonicalSupercriticalDefectCost_proof_irrel
    (G : SimpleGraph V) (hcard hcard' : k - 1 ≤ Fintype.card V) :
    canonicalSupercriticalDefectCost G hcard =
      canonicalSupercriticalDefectCost G hcard' := by
  simp only [canonicalSupercriticalDefectCost,
    canonicalSupercriticalDivision_proof_irrel G hcard hcard']

/-- A co-multipartite witness with nonempty parts is, after forgetting the
clique proofs and the cover, a supercritical division. -/
def SupercriticalDivision.ofCoMultipartiteWitness
    {G : SimpleGraph V}
    (C : DenseGraph.CoMultipartiteWitness G (k - 1))
    (hnonempty : ∀ i, (C.parts i).Nonempty) :
    SupercriticalDivision k V where
  parts := C.parts
  parts_nonempty := hnonempty
  parts_pairwiseDisjoint := C.pairwiseDisjoint

@[simp] theorem SupercriticalDivision.support_ofCoMultipartiteWitness
    {G : SimpleGraph V}
    (C : DenseGraph.CoMultipartiteWitness G (k - 1))
    (hnonempty : ∀ i, (C.parts i).Nonempty) :
    (SupercriticalDivision.ofCoMultipartiteWitness C hnonempty).support =
      Finset.univ := by
  simpa [SupercriticalDivision.support,
    SupercriticalDivision.ofCoMultipartiteWitness] using C.cover

@[simp] theorem SupercriticalDivision.sparse_ofCoMultipartiteWitness
    {G : SimpleGraph V}
    (C : DenseGraph.CoMultipartiteWitness G (k - 1))
    (hnonempty : ∀ i, (C.parts i).Nonempty) :
    (SupercriticalDivision.ofCoMultipartiteWitness C hnonempty).sparse = ∅ := by
  simp [SupercriticalDivision.sparse]

theorem divisionModel_ofCoMultipartiteWitness_eq_completeWithinParts
    (G H : SimpleGraph V)
    (C : DenseGraph.CoMultipartiteWitness H (k - 1))
    (hnonempty : ∀ i, (C.parts i).Nonempty) :
    supercriticalDivisionModelGraph G
        (SupercriticalDivision.ofCoMultipartiteWitness C hnonempty) =
      DenseGraph.completeWithinParts G C.parts := by
  let D := SupercriticalDivision.ofCoMultipartiteWitness C hnonempty
  have hmem (z : V) : ∃ i, z ∈ D.parts i := by
    simpa [D, SupercriticalDivision.ofCoMultipartiteWitness] using C.exists_mem_part z
  have hunique {z : V} {a b : Fin (k - 1)}
      (hza : z ∈ D.parts a) (hzb : z ∈ D.parts b) : a = b :=
    D.mem_part_unique hza hzb
  ext x y
  obtain ⟨i, hxi⟩ := hmem x
  obtain ⟨j, hyj⟩ := hmem y
  by_cases hij : i = j
  · subst j
    rw [supercriticalDivisionModelGraph_adj_of_mem_same_part G D i hxi hyj,
      DenseGraph.completeWithinParts_adj]
    constructor
    · intro hxy
      exact Or.inr ⟨hxy, i, hxi, hyj⟩
    · rintro (hG | ⟨hxy, -⟩)
      · exact G.ne_of_adj hG
      · exact hxy
  · rw [supercriticalDivisionModelGraph_adj_of_mem_distinct_parts
      G D hij hxi hyj, DenseGraph.completeWithinParts_adj]
    have hncommon : ¬ ∃ a, x ∈ C.parts a ∧ y ∈ C.parts a := by
      rintro ⟨a, hxa, hya⟩
      have hai : a = i := hunique (by simpa [D,
        SupercriticalDivision.ofCoMultipartiteWitness] using hxa) hxi
      have haj : a = j := hunique (by simpa [D,
        SupercriticalDivision.ofCoMultipartiteWitness] using hya) hyj
      exact hij (hai.symm.trans haj)
    simp [hncommon]

/-- Canonical minimality against a prescribed covering nonempty partition. -/
theorem canonicalSupercriticalDefectCost_le_completeWithinParts
    (G : SimpleGraph V) (hcard : k - 1 ≤ Fintype.card V)
    (parts : Fin (k - 1) → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint
      (Set.univ : Set (Fin (k - 1))) parts) :
    canonicalSupercriticalDefectCost G hcard ≤
      DenseGraph.simpleGraphEditDistance G
        (DenseGraph.completeWithinParts G parts) := by
  let H := DenseGraph.completeWithinParts G parts
  let C : DenseGraph.CoMultipartiteWitness H (k - 1) :=
    DenseGraph.completeWithinPartsWitness G parts hcover hdisjoint
  have hCnonempty : ∀ i, (C.parts i).Nonempty := by
    intro i
    change (parts i).Nonempty
    exact hnonempty i
  let D : SupercriticalDivision k V :=
    SupercriticalDivision.ofCoMultipartiteWitness C hCnonempty
  have hCparts : C.parts = parts := by rfl
  have hmin := canonicalSupercriticalDivision_minimal G hcard D
  have hmodel : supercriticalDivisionModelGraph G D = H := by
    rw [show D = SupercriticalDivision.ofCoMultipartiteWitness C hCnonempty by rfl,
      divisionModel_ofCoMultipartiteWitness_eq_completeWithinParts G H C hCnonempty,
      hCparts]
  rw [canonicalSupercriticalDefectCost]
  calc
    supercriticalDefectCost G (canonicalSupercriticalDivision G hcard) ≤
        supercriticalDefectCost G D := hmin
    _ = DenseGraph.simpleGraphEditDistance G
        (supercriticalDivisionModelGraph G D) :=
      (simpleGraphEditDistance_divisionModel G D).symm
    _ = DenseGraph.simpleGraphEditDistance G H := by rw [hmodel]
    _ = _ := rfl

/-- Canonical defect cost is bounded by edit distance to any co-multipartite
approximation whose displayed witness has nonempty parts. -/
theorem canonicalSupercriticalDefectCost_le_of_coMultipartiteWitness
    (G H : SimpleGraph V) (hcard : k - 1 ≤ Fintype.card V)
    (C : DenseGraph.CoMultipartiteWitness H (k - 1))
    (hnonempty : ∀ i, (C.parts i).Nonempty) :
    canonicalSupercriticalDefectCost G hcard ≤
      DenseGraph.simpleGraphEditDistance G H := by
  apply le_trans (canonicalSupercriticalDefectCost_le_completeWithinParts
    G hcard C.parts hnonempty C.cover C.pairwiseDisjoint)
  unfold DenseGraph.simpleGraphEditDistance
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [DenseGraph.mem_simpleGraphEditFinset] at he ⊢
      simp only [SimpleGraph.mem_edgeSet] at he ⊢
      rcases he with ⟨hG, hncomplete⟩ | ⟨hcomplete, hnG⟩
      · exact False.elim (hncomplete
          ((DenseGraph.completeWithinParts_adj G C.parts x y).mpr (Or.inl hG)))
      · rw [DenseGraph.completeWithinParts_adj] at hcomplete
        rcases hcomplete with hG | ⟨hxy, i, hxi, hyi⟩
        · exact False.elim (hnG hG)
        · exact Or.inr ⟨C.isClique i hxi hyi hxy, hnG⟩

/-- Canonical defect cost is bounded by edit distance to every co-`(k - 1)`-
partite approximation.  Unlike the explicit-witness version, this public
bridge imposes no nonemptiness condition on the witness supplied by the
caller: empty displayed parts are eliminated by refining its clique
partition into exactly `k - 1` nonempty parts. -/
theorem canonicalSupercriticalDefectCost_le_of_isCoMultipartite
    (G H : SimpleGraph V) (hcard : k - 1 ≤ Fintype.card V)
    (hH : DenseGraph.IsCoMultipartite H (k - 1)) :
    canonicalSupercriticalDefectCost G hcard ≤
      DenseGraph.simpleGraphEditDistance G H := by
  obtain ⟨C⟩ := hH
  obtain ⟨C', hnonempty⟩ := C.exists_nonempty_refinement hcard
  exact canonicalSupercriticalDefectCost_le_of_coMultipartiteWitness
    G H hcard C' hnonempty

end Canonical

/-! ## Degrees into a finite set -/

section DegreePredicates

variable [Fintype V] [DecidableEq V]

/-- The number of neighbors of `v` in `S`. -/
def degreeInFinset (G : SimpleGraph V) (v : V) (S : Finset V) : ℕ :=
  by
    classical
    exact (S.filter fun w ↦ G.Adj v w).card

/-- The number of nonneighbors other than `v` in `S`.  This is the degree
into `S` in the loopless complement graph. -/
def complementDegreeInFinset (G : SimpleGraph V) (v : V)
    (S : Finset V) : ℕ :=
  by
    classical
    exact (S.filter fun w ↦ w ≠ v ∧ ¬ G.Adj v w).card

@[simp] theorem degreeInFinset_empty (G : SimpleGraph V) (v : V) :
    degreeInFinset G v ∅ = 0 := by simp [degreeInFinset]

@[simp] theorem complementDegreeInFinset_empty (G : SimpleGraph V) (v : V) :
    complementDegreeInFinset G v ∅ = 0 := by simp [complementDegreeInFinset]

theorem degreeInFinset_add_complementDegreeInFinset
    (G : SimpleGraph V) (v : V) (S : Finset V) :
    degreeInFinset G v S + complementDegreeInFinset G v S =
      (S.erase v).card := by
  classical
  let A := S.filter fun w ↦ G.Adj v w
  let B := S.filter fun w ↦ w ≠ v ∧ ¬ G.Adj v w
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro w hwA hwB
    exact (Finset.mem_filter.mp hwB).2.2 (Finset.mem_filter.mp hwA).2
  have hunion : A ∪ B = S.erase v := by
    ext w
    by_cases hwv : w = v
    · subst w
      simp [A, B]
    · by_cases hG : G.Adj v w <;> simp [A, B, hwv, hG]
  rw [degreeInFinset, complementDegreeInFinset, ← hunion,
    Finset.card_union_of_disjoint hdisj]

theorem degreeInFinset_union (G : SimpleGraph V) (v : V)
    {S T : Finset V} (hST : Disjoint S T) :
    degreeInFinset G v (S ∪ T) =
      degreeInFinset G v S + degreeInFinset G v T := by
  classical
  unfold degreeInFinset
  have hfilter : (S ∪ T).filter (G.Adj v) =
      S.filter (G.Adj v) ∪ T.filter (G.Adj v) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hfilter, Finset.card_union_of_disjoint]
  exact hST.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem degreeInFinset_mono (G : SimpleGraph V) (v : V)
    {S T : Finset V} (hST : S ⊆ T) :
    degreeInFinset G v S ≤ degreeInFinset G v T := by
  classical
  unfold degreeInFinset
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hST hx.1, hx.2⟩

@[simp] theorem degreeInFinset_erase_self (G : SimpleGraph V) (v : V)
    (S : Finset V) :
    degreeInFinset G v (S.erase v) = degreeInFinset G v S := by
  classical
  unfold degreeInFinset
  congr 1
  ext x
  by_cases hx : x = v
  · subst x
    simp
  · simp [hx]

@[simp] theorem complementDegreeInFinset_erase_self
    (G : SimpleGraph V) (v : V) (S : Finset V) :
    complementDegreeInFinset G v (S.erase v) =
      complementDegreeInFinset G v S := by
  classical
  unfold complementDegreeInFinset
  congr 1
  ext x
  by_cases hx : x = v <;> simp [hx]

@[simp] theorem degreeInFinset_insert_self (G : SimpleGraph V) (v : V)
    (S : Finset V) :
    degreeInFinset G v (insert v S) = degreeInFinset G v S := by
  classical
  unfold degreeInFinset
  congr 1
  ext x
  by_cases hx : x = v <;> simp [hx]

@[simp] theorem complementDegreeInFinset_insert_self
    (G : SimpleGraph V) (v : V) (S : Finset V) :
    complementDegreeInFinset G v (insert v S) =
      complementDegreeInFinset G v S := by
  classical
  unfold complementDegreeInFinset
  congr 1
  ext x
  by_cases hx : x = v <;> simp [hx]

theorem card_finiteGraphEdges_eq_deleteIncidence_add_degree
    (G : SimpleGraph V) (v : V) :
    (finiteGraphEdges G).card =
      (finiteGraphEdges (G.deleteIncidenceSet v)).card +
        degreeInFinset G v Finset.univ := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hdegree : G.degree v = degreeInFinset G v Finset.univ := by
    rw [← G.card_neighborFinset_eq_degree]
    unfold degreeInFinset
    congr 1
    ext w
    simp [SimpleGraph.neighborFinset]
  have hG : finiteGraphEdges G = G.edgeFinset := by
    ext e
    simp [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hdel : finiteGraphEdges (G.deleteIncidenceSet v) =
      (G.deleteIncidenceSet v).edgeFinset := by
    ext e
    simp [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hle : G.degree v ≤ G.edgeFinset.card := by
    rw [← G.card_incidenceFinset_eq_degree v]
    exact Finset.card_le_card (G.incidenceFinset_subset v)
  have hcard := G.card_edgeFinset_deleteIncidenceSet v
  calc
    (finiteGraphEdges G).card = G.edgeFinset.card := by rw [hG]
    _ = (G.deleteIncidenceSet v).edgeFinset.card + G.degree v := by
      rw [hcard]
      exact (Nat.sub_add_cancel hle).symm
    _ = (finiteGraphEdges (G.deleteIncidenceSet v)).card + G.degree v := by
      rw [hdel]
    _ = (finiteGraphEdges (G.deleteIncidenceSet v)).card +
        degreeInFinset G v Finset.univ := by rw [hdegree]

theorem degreeInFinset_support_add_sparse (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (v : V) :
    degreeInFinset G v D.support + degreeInFinset G v D.sparse =
      degreeInFinset G v Finset.univ := by
  rw [← degreeInFinset_union G v]
  · rw [D.support_union_sparse]
  · exact Finset.disjoint_left.mpr fun x hx hs ↦
      (SupercriticalDivision.mem_sparse.mp hs) hx

/-- Restricted degree into the support is the sum of the restricted degrees
into its pairwise-disjoint main parts. -/
theorem degreeInFinset_support_eq_sum (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (v : V) :
    degreeInFinset G v D.support =
      ∑ i : Fin (k - 1), degreeInFinset G v (D.parts i) := by
  classical
  unfold degreeInFinset SupercriticalDivision.support
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi j hj hij
  exact (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Restricted complement-degree into the support is the sum of the restricted
complement-degrees into its pairwise-disjoint main parts. -/
theorem complementDegreeInFinset_support_eq_sum (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (v : V) :
    complementDegreeInFinset G v D.support =
      ∑ i : Fin (k - 1), complementDegreeInFinset G v (D.parts i) := by
  classical
  unfold complementDegreeInFinset SupercriticalDivision.support
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro i hi j hj hij
  exact (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- At a main-part vertex, combined-defect degree is the missing degree in
its own part plus the present degree into the sparse set. -/
theorem degreeInFinset_combinedDefect_of_mem_part (G : SimpleGraph V)
    (D : SupercriticalDivision k V) {v : V} (i : Fin (k - 1))
    (hv : v ∈ D.parts i) :
    degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ =
      complementDegreeInFinset G v (D.parts i) +
        degreeInFinset G v D.sparse := by
  classical
  let A := (D.parts i).filter fun x ↦ x ≠ v ∧ ¬ G.Adj v x
  let B := D.sparse.filter fun x ↦ G.Adj v x
  have hdisj : Disjoint A B := by
    exact (D.part_disjoint_sparse i).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have heq : Finset.univ.filter
      ((combinedSupercriticalDefectGraph G D).Adj v) = A ∪ B := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, A, B]
    constructor
    · intro hx
      rcases D.sparse_or_existsUnique_part x with hs | ⟨j, hxj, -⟩
      · right
        exact ⟨hs, (combinedSupercriticalDefectGraph_adj_support_sparse G D
          (D.part_subset_support i hv) hs).mp hx⟩
      · by_cases hji : j = i
        · subst j
          left
          have h := (combinedSupercriticalDefectGraph_adj_of_mem_same_part
            G D i hv hxj).mp hx
          exact ⟨hxj, h.1.symm, h.2⟩
        · exact False.elim
            (combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
              G D (Ne.symm hji) hv hxj hx)
    · rintro (h | h)
      · exact (combinedSupercriticalDefectGraph_adj_of_mem_same_part
          G D i hv h.1).mpr ⟨h.2.1.symm, h.2.2⟩
      · exact (combinedSupercriticalDefectGraph_adj_support_sparse G D
          (D.part_subset_support i hv) h.1).mpr h.2
  unfold degreeInFinset complementDegreeInFinset
  rw [heq, Finset.card_union_of_disjoint hdisj]

/-- At a sparse vertex, every combined-defect edge is exactly an edge of the
original graph. -/
theorem degreeInFinset_combinedDefect_of_mem_sparse (G : SimpleGraph V)
    (D : SupercriticalDivision k V) {v : V} (hv : v ∈ D.sparse) :
    degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ =
      degreeInFinset G v Finset.univ := by
  classical
  unfold degreeInFinset
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases D.sparse_or_existsUnique_part x with hs | ⟨i, hxi, -⟩
  · exact combinedSupercriticalDefectGraph_adj_of_mem_sparse G D hv hs
  · rw [(combinedSupercriticalDefectGraph G D).adj_comm, G.adj_comm]
    exact combinedSupercriticalDefectGraph_adj_support_sparse G D
      (D.part_subset_support i hxi) hv

theorem degreeInFinset_combinedDefect_part_of_mem_same
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {v : V} (i : Fin (k - 1)) (hv : v ∈ D.parts i) :
    degreeInFinset (combinedSupercriticalDefectGraph G D) v (D.parts i) =
      complementDegreeInFinset G v (D.parts i) := by
  classical
  unfold degreeInFinset complementDegreeInFinset
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxi, hx⟩
    have hx' := (combinedSupercriticalDefectGraph_adj_of_mem_same_part
      G D i hv hxi).mp hx
    exact ⟨hxi, hx'.1.symm, hx'.2⟩
  · rintro ⟨hxi, hxne, hx⟩
    exact ⟨hxi, (combinedSupercriticalDefectGraph_adj_of_mem_same_part
      G D i hv hxi).mpr ⟨hxne.symm, hx⟩⟩

theorem degreeInFinset_combinedDefect_part_of_mem_distinct
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {v : V} {i j : Fin (k - 1)} (hij : i ≠ j)
    (hv : v ∈ D.parts j) :
    degreeInFinset (combinedSupercriticalDefectGraph G D) v (D.parts i) = 0 := by
  classical
  unfold degreeInFinset
  rw [Finset.card_eq_zero]
  ext x
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hxi, hx⟩
  exact combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
    G D hij.symm hv hxi hx

theorem degreeInFinset_combinedDefect_part_of_mem_sparse
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {v : V} (hv : v ∈ D.sparse) (i : Fin (k - 1)) :
    degreeInFinset (combinedSupercriticalDefectGraph G D) v (D.parts i) =
      degreeInFinset G v (D.parts i) := by
  classical
  unfold degreeInFinset
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hxi, hx⟩
    have hx' : (combinedSupercriticalDefectGraph G D).Adj x v :=
      ((combinedSupercriticalDefectGraph G D).adj_comm v x).mp hx
    have hg' : G.Adj x v :=
      (combinedSupercriticalDefectGraph_adj_support_sparse G D
        (D.part_subset_support i hxi) hv).mp hx'
    exact ⟨hxi, (G.adj_comm v x).mpr hg'⟩
  · rintro ⟨hxi, hx⟩
    have hg' : G.Adj x v := (G.adj_comm v x).mp hx
    have hx' : (combinedSupercriticalDefectGraph G D).Adj x v :=
      (combinedSupercriticalDefectGraph_adj_support_sparse G D
        (D.part_subset_support i hxi) hv).mpr hg'
    exact ⟨hxi, ((combinedSupercriticalDefectGraph G D).adj_comm v x).mpr hx'⟩

/-- Low defect degree into a main part. -/
def HasLowDegreeInPart (G : SimpleGraph V) (α : ℝ)
    (D : SupercriticalDivision k V) (v : V) (i : Fin (k - 1)) : Prop :=
  (degreeInFinset G v (D.parts i) : ℝ) < α * (D.parts i).card

/-- Medium defect degree into a main part. -/
def HasMediumDegreeInPart (G : SimpleGraph V) (α : ℝ)
    (D : SupercriticalDivision k V) (v : V) (i : Fin (k - 1)) : Prop :=
  α * (D.parts i).card ≤ (degreeInFinset G v (D.parts i) : ℝ) ∧
    (degreeInFinset G v (D.parts i) : ℝ) ≤
      (1 - α) * (D.parts i).card

/-- High defect degree into a main part. -/
def HasHighDegreeInPart (G : SimpleGraph V) (α : ℝ)
    (D : SupercriticalDivision k V) (v : V) (i : Fin (k - 1)) : Prop :=
  (1 - α) * (D.parts i).card <
    (degreeInFinset G v (D.parts i) : ℝ)

def HasMediumDegreeSomePart (G : SimpleGraph V) (α : ℝ)
    (D : SupercriticalDivision k V) (v : V) : Prop :=
  ∃ i, HasMediumDegreeInPart G α D v i

theorem low_or_medium_or_high_degree_in_part (G : SimpleGraph V) (α : ℝ)
    (D : SupercriticalDivision k V) (v : V) (i : Fin (k - 1)) :
    HasLowDegreeInPart G α D v i ∨
      HasMediumDegreeInPart G α D v i ∨
        HasHighDegreeInPart G α D v i := by
  unfold HasLowDegreeInPart HasMediumDegreeInPart HasHighDegreeInPart
  by_cases hlo : (degreeInFinset G v (D.parts i) : ℝ) <
      α * (D.parts i).card
  · exact Or.inl hlo
  · right
    by_cases hhi : (1 - α) * (D.parts i).card <
        (degreeInFinset G v (D.parts i) : ℝ)
    · exact Or.inr hhi
    · exact Or.inl ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩

theorem not_low_and_high_degree_in_part (G : SimpleGraph V) {α : ℝ}
    (hα : α ≤ 1 / 2) (D : SupercriticalDivision k V) (v : V)
    (i : Fin (k - 1)) :
    ¬ (HasLowDegreeInPart G α D v i ∧
      HasHighDegreeInPart G α D v i) := by
  rintro ⟨hlo, hhi⟩
  unfold HasLowDegreeInPart at hlo
  unfold HasHighDegreeInPart at hhi
  have hcard : (0 : ℝ) ≤ (D.parts i).card := by positivity
  have hcoef : α ≤ 1 - α := by linarith
  have := mul_le_mul_of_nonneg_right hcoef hcard
  linarith

end DegreePredicates

/-! ## Elementary moves of a division -/

namespace SupercriticalDivision

variable [Fintype V] [DecidableEq V]

/-- Move a vertex from one main part to another.  The explicit remainder
hypothesis is exactly what is needed to keep the source part nonempty. -/
def moveMainToMain (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (v : V) (hi : v ∈ D.parts i) (hij : i ≠ j)
    (hremain : (D.parts i).erase v |>.Nonempty) :
    SupercriticalDivision k V where
  parts a := if a = i then (D.parts i).erase v
    else if a = j then insert v (D.parts j) else D.parts a
  parts_nonempty a := by
    by_cases hai : a = i
    · subst a
      simpa using hremain
    · by_cases haj : a = j
      · subst a
        simp [Ne.symm hij]
      · simpa [hai, haj] using D.parts_nonempty a
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint
      (if a = i then (D.parts i).erase v
        else if a = j then insert v (D.parts j) else D.parts a)
      (if b = i then (D.parts i).erase v
        else if b = j then insert v (D.parts j) else D.parts b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    have hmem : ∀ (c : Fin (k - 1)) {z : V},
        z ∈ (if c = i then (D.parts i).erase v
          else if c = j then insert v (D.parts j) else D.parts c) →
        z ≠ v → z ∈ D.parts c := by
      intro c z hz hzv
      by_cases hci : c = i
      · subst c
        simpa [hzv] using hz
      · by_cases hcj : c = j
        · subst c
          simpa [Ne.symm hij, hzv] using hz
        · simpa [hci, hcj] using hz
    have hvloc : ∀ (c : Fin (k - 1)),
        v ∈ (if c = i then (D.parts i).erase v
          else if c = j then insert v (D.parts j) else D.parts c) →
        c = j := by
      intro c hc
      by_contra hcj
      by_cases hci : c = i
      · subst c
        simp at hc
      · have hvc : v ∈ D.parts c := by simpa [hci, hcj] using hc
        have hic : i ≠ c := fun h ↦ hci h.symm
        exact (Finset.disjoint_left.mp
          (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ c) hic)) hi hvc
    by_cases hxv : x = v
    · subst x
      exact hab ((hvloc a hxa).trans (hvloc b hxb).symm)
    · exact (Finset.disjoint_left.mp
        (D.parts_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab))
          (hmem a hxa hxv) (hmem b hxb hxv)

/-- Move a main-part vertex into the sparse set. -/
def moveMainToSparse (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (_hi : v ∈ D.parts i)
    (hremain : ((D.parts i).erase v).Nonempty) :
    SupercriticalDivision k V where
  parts a := if a = i then (D.parts i).erase v else D.parts a
  parts_nonempty a := by
    by_cases hai : a = i
    · subst a
      simpa using hremain
    · simpa [hai] using D.parts_nonempty a
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint
      (if a = i then (D.parts i).erase v else D.parts a)
      (if b = i then (D.parts i).erase v else D.parts b)
    by_cases hai : a = i <;> by_cases hbi : b = i
    · exact False.elim (hab (hai.trans hbi.symm))
    · subst a
      simpa [hbi] using
        (Finset.disjoint_of_subset_left (Finset.erase_subset _ _)
          (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ b) hab))
    · subst b
      simpa [hai] using
        (Finset.disjoint_of_subset_right (Finset.erase_subset _ _)
          (D.parts_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ i) hab))
    · simpa [hai, hbi] using
        (D.parts_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab)

/-- Move a sparse vertex into a main part. -/
def moveSparseToMain (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (hv : v ∈ D.sparse) : SupercriticalDivision k V where
  parts a := if a = i then insert v (D.parts i) else D.parts a
  parts_nonempty a := by
    by_cases hai : a = i
    · subst a
      simp
    · simpa [hai] using D.parts_nonempty a
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint
      (if a = i then insert v (D.parts i) else D.parts a)
      (if b = i then insert v (D.parts i) else D.parts b)
    rw [Finset.disjoint_left]
    intro x hxa hxb
    by_cases hai : a = i <;> by_cases hbi : b = i
    · exact hab (hai.trans hbi.symm)
    · subst a
      simp only [if_true, hbi, if_false, Finset.mem_insert] at hxa hxb
      rcases hxa with rfl | hxa
      · exact (mem_sparse.mp hv) (D.part_subset_support b hxb)
      · exact (Finset.disjoint_left.mp
          (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ b) hab)) hxa hxb
    · subst b
      simp only [hai, if_false, if_true, Finset.mem_insert] at hxa hxb
      rcases hxb with rfl | hxb
      · exact (mem_sparse.mp hv) (D.part_subset_support a hxa)
      · exact (Finset.disjoint_left.mp
          (D.parts_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ i) hab)) hxa hxb
    · simp only [hai, hbi, if_false] at hxa hxb
      exact (Finset.disjoint_left.mp
        (D.parts_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab)) hxa hxb

theorem mem_moveMainToMain_part_of_ne
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (v x : V) (hi : v ∈ D.parts i) (hij : i ≠ j)
    (hremain : ((D.parts i).erase v).Nonempty) (hxv : x ≠ v)
    (a : Fin (k - 1)) :
    x ∈ (D.moveMainToMain v hi hij hremain).parts a ↔
      x ∈ D.parts a := by
  by_cases hai : a = i
  · subst a
    simp [moveMainToMain, hxv]
  · by_cases haj : a = j
    · subst a
      simp [moveMainToMain, Ne.symm hij, hxv]
    · simp [moveMainToMain, hai, haj]

theorem mem_moveMainToSparse_part_of_ne
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v x : V) (hi : v ∈ D.parts i)
    (hremain : ((D.parts i).erase v).Nonempty) (hxv : x ≠ v)
    (a : Fin (k - 1)) :
    x ∈ (D.moveMainToSparse i v hi hremain).parts a ↔
      x ∈ D.parts a := by
  by_cases hai : a = i
  · subst a
    simp [moveMainToSparse, hxv]
  · simp [moveMainToSparse, hai]

theorem mem_moveSparseToMain_part_of_ne
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v x : V) (hv : v ∈ D.sparse) (hxv : x ≠ v)
    (a : Fin (k - 1)) :
    x ∈ (D.moveSparseToMain i v hv).parts a ↔ x ∈ D.parts a := by
  by_cases hai : a = i
  · subst a
    simp [moveSparseToMain, hxv]
  · simp [moveSparseToMain, hai]

@[simp] theorem mem_moveMainToMain_target
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (v : V) (hi : v ∈ D.parts i) (hij : i ≠ j)
    (hremain : ((D.parts i).erase v).Nonempty) :
    v ∈ (D.moveMainToMain v hi hij hremain).parts j := by
  simp [moveMainToMain, Ne.symm hij]

@[simp] theorem mem_moveMainToSparse_sparse
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (hi : v ∈ D.parts i)
    (hremain : ((D.parts i).erase v).Nonempty) :
    v ∈ (D.moveMainToSparse i v hi hremain).sparse := by
  rw [mem_sparse]
  simp only [mem_support]
  push_neg
  intro a
  by_cases hai : a = i
  · subst a
    simp [moveMainToSparse]
  · have hia : i ≠ a := fun h ↦ hai h.symm
    have hnmem : v ∉ D.parts a := fun hva ↦
      (Finset.disjoint_left.mp
        (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ a) hia)) hi hva
    simpa [moveMainToSparse, hai] using hnmem

@[simp] theorem mem_moveSparseToMain_part
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (hv : v ∈ D.sparse) :
    v ∈ (D.moveSparseToMain i v hv).parts i := by
  simp [moveSparseToMain]

theorem sparse_moveMainToMain
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (v : V) (hi : v ∈ D.parts i) (hij : i ≠ j)
    (hremain : ((D.parts i).erase v).Nonempty) :
    (D.moveMainToMain v hi hij hremain).sparse = D.sparse := by
  ext x
  by_cases hxv : x = v
  · subst x
    have hvOld : v ∉ D.sparse := by
      intro hs
      exact (mem_sparse.mp hs) (D.part_subset_support i hi)
    have hvNew : v ∉ (D.moveMainToMain v hi hij hremain).sparse := by
      intro hs
      exact (mem_sparse.mp hs)
        ((D.moveMainToMain v hi hij hremain).part_subset_support j
          (mem_moveMainToMain_target D v hi hij hremain))
    simp [hvOld, hvNew]
  · simp only [mem_sparse]
    exact not_congr (by
      simp only [mem_support]
      exact exists_congr fun a ↦ mem_moveMainToMain_part_of_ne
        D v x hi hij hremain hxv a)

theorem sparse_moveMainToSparse
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (hi : v ∈ D.parts i)
    (hremain : ((D.parts i).erase v).Nonempty) :
    (D.moveMainToSparse i v hi hremain).sparse = insert v D.sparse := by
  ext x
  by_cases hxv : x = v
  · subst x
    simp only [mem_moveMainToSparse_sparse, Finset.mem_insert, true_or]
  · rw [Finset.mem_insert]
    simp only [hxv, false_or, mem_sparse]
    exact not_congr (by
      simp only [mem_support]
      exact exists_congr fun a ↦ mem_moveMainToSparse_part_of_ne
        D i v x hi hremain hxv a)

theorem sparse_moveSparseToMain
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (v : V) (hv : v ∈ D.sparse) :
    (D.moveSparseToMain i v hv).sparse = D.sparse.erase v := by
  ext x
  by_cases hxv : x = v
  · subst x
    have hvNew : v ∉ (D.moveSparseToMain i v hv).sparse := by
      intro hs
      exact (mem_sparse.mp hs)
        ((D.moveSparseToMain i v hv).part_subset_support i
          (mem_moveSparseToMain_part D i v hv))
    simp [hvNew]
  · rw [Finset.mem_erase]
    rw [mem_sparse, mem_sparse]
    have hsupp : x ∈ (D.moveSparseToMain i v hv).support ↔
        x ∈ D.support := by
      simp only [mem_support]
      exact exists_congr fun a ↦ mem_moveSparseToMain_part_of_ne
        D i v x hv hxv a
    constructor
    · intro hn
      exact ⟨hxv, fun ho ↦ hn (hsupp.mpr ho)⟩
    · rintro ⟨_, ho⟩ hn
      exact ho (hsupp.mp hn)

private theorem combinedDefectGraph_adj_congr_of_parts_off_vertex
    (G : SimpleGraph V) (D E : SupercriticalDivision k V) (v : V)
    (hparts : ∀ (a : Fin (k - 1)) (x : V), x ≠ v →
      (x ∈ E.parts a ↔ x ∈ D.parts a))
    {x y : V} (hxv : x ≠ v) (hyv : y ≠ v) :
    (combinedSupercriticalDefectGraph G E).Adj x y ↔
      (combinedSupercriticalDefectGraph G D).Adj x y := by
  have hsupp (z : V) (hzv : z ≠ v) : z ∈ E.support ↔ z ∈ D.support := by
    simp only [SupercriticalDivision.mem_support]
    exact exists_congr fun a ↦ hparts a z hzv
  have hsparse (z : V) (hzv : z ≠ v) : z ∈ E.sparse ↔ z ∈ D.sparse := by
    rw [SupercriticalDivision.mem_sparse, SupercriticalDivision.mem_sparse]
    exact not_congr (hsupp z hzv)
  have hsame : E.SameMainPart x y ↔ D.SameMainPart x y := by
    simp only [SupercriticalDivision.SameMainPart]
    exact exists_congr fun a ↦ and_congr (hparts a x hxv) (hparts a y hyv)
  rw [combinedSupercriticalDefectGraph_adj,
    combinedSupercriticalDefectGraph_adj,
    supercriticalDefectGraph_adj, supercriticalDefectGraph_adj]
  simp only [supercriticalDefectCondition,
    SupercriticalDivision.IsSupportSparsePair]
  rw [hsame, hsupp x hxv, hsupp y hyv, hsparse x hxv, hsparse y hyv]

private theorem deleteIncidenceSet_combinedDefectGraph_eq_of_parts_off_vertex
    (G : SimpleGraph V) (D E : SupercriticalDivision k V) (v : V)
    (hparts : ∀ (a : Fin (k - 1)) (x : V), x ≠ v →
      (x ∈ E.parts a ↔ x ∈ D.parts a)) :
    (combinedSupercriticalDefectGraph G E).deleteIncidenceSet v =
      (combinedSupercriticalDefectGraph G D).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj]
  constructor
  · rintro ⟨hxy, hxv, hyv⟩
    exact ⟨(combinedDefectGraph_adj_congr_of_parts_off_vertex
      G D E v hparts hxv hyv).mp hxy, hxv, hyv⟩
  · rintro ⟨hxy, hxv, hyv⟩
    exact ⟨(combinedDefectGraph_adj_congr_of_parts_off_vertex
      G D E v hparts hxv hyv).mpr hxy, hxv, hyv⟩

private theorem defectCost_add_degree_eq_of_parts_off_vertex
    (G : SimpleGraph V) (D E : SupercriticalDivision k V) (v : V)
    (hparts : ∀ (a : Fin (k - 1)) (x : V), x ≠ v →
      (x ∈ E.parts a ↔ x ∈ D.parts a)) :
    supercriticalDefectCost G E +
        degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ =
      supercriticalDefectCost G D +
        degreeInFinset (combinedSupercriticalDefectGraph G E) v Finset.univ := by
  let CE := combinedSupercriticalDefectGraph G E
  let CD := combinedSupercriticalDefectGraph G D
  have hE := card_finiteGraphEdges_eq_deleteIncidence_add_degree CE v
  have hD := card_finiteGraphEdges_eq_deleteIncidence_add_degree CD v
  have hdel : CE.deleteIncidenceSet v = CD.deleteIncidenceSet v :=
    deleteIncidenceSet_combinedDefectGraph_eq_of_parts_off_vertex
      G D E v hparts
  have hdelCard : (finiteGraphEdges (CE.deleteIncidenceSet v)).card =
      (finiteGraphEdges (CD.deleteIncidenceSet v)).card := by rw [hdel]
  have hcostE : (finiteGraphEdges CE).card = supercriticalDefectCost G E := by
    exact card_finiteGraphEdges_combinedSupercriticalDefectGraph G E
  have hcostD : (finiteGraphEdges CD).card = supercriticalDefectCost G D := by
    exact card_finiteGraphEdges_combinedSupercriticalDefectGraph G D
  dsimp [CE, CD] at hE hD hcostE hcostD hdelCard
  calc
    supercriticalDefectCost G E +
        degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ =
      (finiteGraphEdges (combinedSupercriticalDefectGraph G E)).card +
        degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ := by
          rw [hcostE]
    _ = (finiteGraphEdges
          ((combinedSupercriticalDefectGraph G E).deleteIncidenceSet v)).card +
        degreeInFinset (combinedSupercriticalDefectGraph G E) v Finset.univ +
        degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ := by
          rw [hE]
    _ = (finiteGraphEdges
          ((combinedSupercriticalDefectGraph G D).deleteIncidenceSet v)).card +
        degreeInFinset (combinedSupercriticalDefectGraph G D) v Finset.univ +
        degreeInFinset (combinedSupercriticalDefectGraph G E) v Finset.univ := by
          rw [hdelCard]
          omega
    _ = (finiteGraphEdges (combinedSupercriticalDefectGraph G D)).card +
        degreeInFinset (combinedSupercriticalDefectGraph G E) v Finset.univ := by
          rw [hD]
    _ = supercriticalDefectCost G D +
        degreeInFinset (combinedSupercriticalDefectGraph G E) v Finset.univ := by
          rw [hcostD]

@[simp] theorem moveMainToMain_parts_target
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (v : V) (hi : v ∈ D.parts i) (hij : i ≠ j)
    (hremain : ((D.parts i).erase v).Nonempty) :
    (D.moveMainToMain v hi hij hremain).parts j = insert v (D.parts j) := by
  simp [moveMainToMain, Ne.symm hij]

/-- Exact main-to-main cost identity used in `lemma:SuperCloseStructureK1k`. -/
theorem supercriticalDefectCost_moveMainToMain_add
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    {i j : Fin (k - 1)} (v : V) (hi : v ∈ D.parts i)
    (hij : i ≠ j) (hremain : ((D.parts i).erase v).Nonempty) :
    supercriticalDefectCost G (D.moveMainToMain v hi hij hremain) +
        complementDegreeInFinset G v (D.parts i) =
      supercriticalDefectCost G D +
        complementDegreeInFinset G v (D.parts j) := by
  let E := D.moveMainToMain v hi hij hremain
  have hbase := defectCost_add_degree_eq_of_parts_off_vertex G D E v
    (fun a x hxv ↦ mem_moveMainToMain_part_of_ne
      D v x hi hij hremain hxv a)
  have hold := degreeInFinset_combinedDefect_of_mem_part G D i hi
  have hvE : v ∈ E.parts j := by
    exact mem_moveMainToMain_target D v hi hij hremain
  have hnew := degreeInFinset_combinedDefect_of_mem_part G E j hvE
  have hsparse : E.sparse = D.sparse := sparse_moveMainToMain D v hi hij hremain
  have hpart : E.parts j = insert v (D.parts j) :=
    moveMainToMain_parts_target D v hi hij hremain
  dsimp [E] at hbase
  rw [hold, hnew, hsparse, hpart,
    complementDegreeInFinset_insert_self] at hbase
  omega

/-- Exact main-to-sparse cost identity: the degree term is
the degree into the old main support, not the total graph degree. -/
theorem supercriticalDefectCost_moveMainToSparse_add
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) (v : V) (hi : v ∈ D.parts i)
    (hremain : ((D.parts i).erase v).Nonempty) :
    supercriticalDefectCost G (D.moveMainToSparse i v hi hremain) +
        complementDegreeInFinset G v (D.parts i) =
      supercriticalDefectCost G D + degreeInFinset G v D.support := by
  let E := D.moveMainToSparse i v hi hremain
  have hbase := defectCost_add_degree_eq_of_parts_off_vertex G D E v
    (fun a x hxv ↦ mem_moveMainToSparse_part_of_ne
      D i v x hi hremain hxv a)
  have hold := degreeInFinset_combinedDefect_of_mem_part G D i hi
  have hvE : v ∈ E.sparse := mem_moveMainToSparse_sparse D i v hi hremain
  have hnew := degreeInFinset_combinedDefect_of_mem_sparse G E hvE
  have hsplit := degreeInFinset_support_add_sparse G D v
  dsimp [E] at hbase
  rw [hold, hnew] at hbase
  omega

/-- Exact sparse-to-main cost identity used in `lemma:SuperCloseStructureK1k`. -/
theorem supercriticalDefectCost_moveSparseToMain_add
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) (v : V) (hv : v ∈ D.sparse) :
    supercriticalDefectCost G (D.moveSparseToMain i v hv) +
        degreeInFinset G v D.support =
      supercriticalDefectCost G D +
        complementDegreeInFinset G v (D.parts i) := by
  let E := D.moveSparseToMain i v hv
  have hbase := defectCost_add_degree_eq_of_parts_off_vertex G D E v
    (fun a x hxv ↦ mem_moveSparseToMain_part_of_ne D i v x hv hxv a)
  have hold := degreeInFinset_combinedDefect_of_mem_sparse G D hv
  have hvE : v ∈ E.parts i := mem_moveSparseToMain_part D i v hv
  have hnew := degreeInFinset_combinedDefect_of_mem_part G E i hvE
  have hsparse : E.sparse = D.sparse.erase v := sparse_moveSparseToMain D i v hv
  have hpart : E.parts i = insert v (D.parts i) := by
    simp [E, moveSparseToMain]
  have hsplit := degreeInFinset_support_add_sparse G D v
  dsimp [E] at hbase
  rw [hold, hnew, hsparse, hpart,
    degreeInFinset_erase_self, complementDegreeInFinset_insert_self] at hbase
  omega

@[simp] theorem moveMainToSparse_parts_same
    (D : SupercriticalDivision k V) (i : Fin (k - 1)) (v : V)
    (hi : v ∈ D.parts i) (hremain : ((D.parts i).erase v).Nonempty) :
    (D.moveMainToSparse i v hi hremain).parts i = (D.parts i).erase v := by
  simp [moveMainToSparse]

@[simp] theorem moveSparseToMain_parts_same
    (D : SupercriticalDivision k V) (i : Fin (k - 1)) (v : V)
    (hv : v ∈ D.sparse) :
    (D.moveSparseToMain i v hv).parts i = insert v (D.parts i) := by
  simp [moveSparseToMain]

end SupercriticalDivision

/-! ## Canonical minimality excludes high defect degree -/

/-- If every canonical main part is large enough that
`|V| < k(1-α)|Pᵢ|`, then the combined canonical defect graph has no high
degree into a main part.  In the main-part case, the `k` contributions are the
`k - 1` complement-degrees forced by main-to-main minimality together with the
support-degree forced by the main-to-sparse identity. -/
theorem canonicalCombinedDefectGraph_no_high_degree_of_card_lt
    [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V)
    {α : ℝ} (hα : α < 1 / 2)
    (hlarge : ∀ i : Fin (k - 1),
      (Fintype.card V : ℝ) <
        (k : ℝ) * (1 - α) *
          ((canonicalSupercriticalDivision G hcard).parts i).card)
    (v : V) (i : Fin (k - 1)) :
    ¬ HasHighDegreeInPart (canonicalCombinedDefectGraph G hcard) α
      (canonicalSupercriticalDivision G hcard) v i := by
  let D := canonicalSupercriticalDivision G hcard
  let T := combinedSupercriticalDefectGraph G D
  have hmin (E : SupercriticalDivision k V) :
      supercriticalDefectCost G D ≤ supercriticalDefectCost G E := by
    exact canonicalSupercriticalDivision_minimal G hcard E
  intro hhigh
  change (1 - α) * ((D.parts i).card : ℝ) <
    (degreeInFinset T v (D.parts i) : ℝ) at hhigh
  rcases D.sparse_or_existsUnique_part v with hvSparse | ⟨j, hvj, -⟩
  · have hdeg := degreeInFinset_combinedDefect_part_of_mem_sparse G D hvSparse i
    change degreeInFinset T v (D.parts i) = degreeInFinset G v (D.parts i) at hdeg
    rw [hdeg] at hhigh
    have hvnot : v ∉ D.parts i := fun hvi ↦
      (SupercriticalDivision.mem_sparse.mp hvSparse) (D.part_subset_support i hvi)
    have hsum := degreeInFinset_add_complementDegreeInFinset G v (D.parts i)
    rw [Finset.erase_eq_self.mpr hvnot] at hsum
    have hmono := degreeInFinset_mono G v (D.part_subset_support i)
    have hmove := SupercriticalDivision.supercriticalDefectCost_moveSparseToMain_add
      G D i v hvSparse
    have hminimal := hmin (D.moveSparseToMain i v hvSparse)
    have hsupport_le_comp : degreeInFinset G v D.support ≤
        complementDegreeInFinset G v (D.parts i) := by omega
    have htwice : 2 * degreeInFinset G v (D.parts i) ≤ (D.parts i).card := by
      omega
    have htwiceReal :
        2 * (degreeInFinset G v (D.parts i) : ℝ) ≤
          ((D.parts i).card : ℝ) := by exact_mod_cast htwice
    have hcardNonneg : (0 : ℝ) ≤ ((D.parts i).card : ℝ) := by positivity
    nlinarith
  · by_cases hji : j = i
    · subst j
      have hdeg := degreeInFinset_combinedDefect_part_of_mem_same G D i hvj
      change degreeInFinset T v (D.parts i) =
        complementDegreeInFinset G v (D.parts i) at hdeg
      rw [hdeg] at hhigh
      have hpartPos : (0 : ℝ) < ((D.parts i).card : ℝ) := by
        exact_mod_cast (Finset.card_pos.mpr (D.parts_nonempty i))
      have hthresholdPos : 0 < (1 - α) * ((D.parts i).card : ℝ) := by
        have : 0 < 1 - α := by linarith
        positivity
      have hcompPosReal :
          0 < (complementDegreeInFinset G v (D.parts i) : ℝ) :=
        hthresholdPos.trans hhigh
      have hcompPos : 0 < complementDegreeInFinset G v (D.parts i) := by
        exact_mod_cast hcompPosReal
      have hsumI := degreeInFinset_add_complementDegreeInFinset G v (D.parts i)
      have hremain : ((D.parts i).erase v).Nonempty := by
        rw [← Finset.card_pos]
        omega
      have hcomp_le_all : ∀ a : Fin (k - 1),
          complementDegreeInFinset G v (D.parts i) ≤
            complementDegreeInFinset G v (D.parts a) := by
        intro a
        by_cases hai : a = i
        · subst a
          exact le_rfl
        · have hmove :=
            SupercriticalDivision.supercriticalDefectCost_moveMainToMain_add
              G D v hvj (Ne.symm hai) hremain
          have hminimal := hmin (D.moveMainToMain v hvj (Ne.symm hai) hremain)
          omega
      have hsumComp :
          (k - 1) * complementDegreeInFinset G v (D.parts i) ≤
            ∑ a : Fin (k - 1),
              complementDegreeInFinset G v (D.parts a) := by
        calc
          (k - 1) * complementDegreeInFinset G v (D.parts i) =
              ∑ _a : Fin (k - 1),
                complementDegreeInFinset G v (D.parts i) := by simp
          _ ≤ ∑ a : Fin (k - 1),
              complementDegreeInFinset G v (D.parts a) :=
            Finset.sum_le_sum fun a _ ↦ hcomp_le_all a
      have hmoveSparse :=
        SupercriticalDivision.supercriticalDefectCost_moveMainToSparse_add
          G D i v hvj hremain
      have hminimalSparse := hmin (D.moveMainToSparse i v hvj hremain)
      have hcomp_le_supportDegree :
          complementDegreeInFinset G v (D.parts i) ≤
            degreeInFinset G v D.support := by omega
      have hdegreeSum := degreeInFinset_support_eq_sum G D v
      have hcompSum := complementDegreeInFinset_support_eq_sum G D v
      have hsupportPartition :=
        degreeInFinset_add_complementDegreeInFinset G v D.support
      have heraseSupportLe : (D.support.erase v).card ≤ Fintype.card V :=
        Finset.card_le_card (Finset.subset_univ _)
      have hkcomp :
          k * complementDegreeInFinset G v (D.parts i) ≤ Fintype.card V := by
        have hkEq : (k - 1) + 1 = k := by omega
        calc
          k * complementDegreeInFinset G v (D.parts i) =
              ((k - 1) + 1) * complementDegreeInFinset G v (D.parts i) :=
            (congrArg (fun n : ℕ ↦
              n * complementDegreeInFinset G v (D.parts i)) hkEq).symm
          _ =
              complementDegreeInFinset G v (D.parts i) +
                (k - 1) * complementDegreeInFinset G v (D.parts i) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          _ ≤ degreeInFinset G v D.support +
                ∑ a : Fin (k - 1),
                  complementDegreeInFinset G v (D.parts a) :=
            Nat.add_le_add hcomp_le_supportDegree hsumComp
          _ = degreeInFinset G v D.support +
                complementDegreeInFinset G v D.support := by rw [hcompSum]
          _ = (D.support.erase v).card := hsupportPartition
          _ ≤ Fintype.card V := heraseSupportLe
      have hkcompReal :
          (k : ℝ) * (complementDegreeInFinset G v (D.parts i) : ℝ) ≤
            (Fintype.card V : ℝ) := by exact_mod_cast hkcomp
      have hkPos : (0 : ℝ) < k := by positivity
      nlinarith [hlarge i]
    · have hdeg := degreeInFinset_combinedDefect_part_of_mem_distinct
          (i := i) (j := j) G D (Ne.symm hji) hvj
      change degreeInFinset T v (D.parts i) = 0 at hdeg
      rw [hdeg] at hhigh
      have hnonneg : 0 ≤ (1 - α) * ((D.parts i).card : ℝ) := by
        have : 0 ≤ 1 - α := by linarith
        positivity
      exact (not_lt_of_ge hnonneg) (by simpa using hhigh)

end InducedStars
