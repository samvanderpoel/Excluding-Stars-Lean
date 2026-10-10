import DenseGraph.FiniteModels.GraphEdit
import InducedStars.Structure.Subcritical.Division
import InducedStars.Regularity.Basic

/-!
# Subcritical defect graphs and canonical repair

This file formalizes the edit bookkeeping in Definition `dfn:D-reg-blowup`.
An active pair is deliberately unconstrained: the repaired graph retains the
edges of the input graph there, and an active bipartite graph may be empty.
-/

noncomputable section

open Finset Set

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance graphEdgeSetFintype (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite G.edgeSet

/-! ## The fixed-division model and its defects -/

/-- Repair relative to `D`: complete every part, retain the input graph on
active pairs, and delete every other edge. -/
def subcriticalDivisionModelGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    D.SamePart x y ∨ (D.ActivePair x y ∧ G.Adj x y)

@[simp] theorem subcriticalDivisionModelGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (x y : V) :
    (subcriticalDivisionModelGraph G D).Adj x y ↔
      x ≠ y ∧ (D.SamePart x y ∨ (D.ActivePair x y ∧ G.Adj x y)) := by
  rw [subcriticalDivisionModelGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hxy, h | h⟩
    · exact ⟨hxy, h⟩
    · exact ⟨hxy, Or.elim h
        (fun hs ↦ Or.inl ((D.samePart_comm _ _).mpr hs))
        (fun ha ↦ Or.inr ⟨(D.activePair_comm _ _).mpr ha.1, ha.2.symm⟩)⟩
  · rintro ⟨hxy, h⟩
    exact ⟨hxy, Or.inl h⟩

/-- The combined defect graph is exactly the unordered adjacency disagreement
between `G` and its fixed-division repair. It includes sparse--sparse edges. -/
def subcriticalCombinedDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    G.Adj x y ≠ (subcriticalDivisionModelGraph G D).Adj x y

@[simp] theorem subcriticalCombinedDefectGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (x y : V) :
    (subcriticalCombinedDefectGraph G D).Adj x y ↔
      G.Adj x y ≠ (subcriticalDivisionModelGraph G D).Adj x y := by
  rw [subcriticalCombinedDefectGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · simpa only [G.adj_comm y x,
        (subcriticalDivisionModelGraph G D).adj_comm y x] using h
  · intro h
    refine ⟨?_, Or.inl h⟩
    intro hxy
    subst y
    exact h (by simp)

/-- The paper's ordinary defect graph, obtained by omitting precisely the
defects whose two endpoints are in the sparse remainder. -/
def subcriticalDefectGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    (subcriticalCombinedDefectGraph G D).Adj x y ∧
      ¬ (x ∈ D.sparse ∧ y ∈ D.sparse)

@[simp] theorem subcriticalDefectGraph_adj
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (x y : V) :
    (subcriticalDefectGraph G D).Adj x y ↔
      (subcriticalCombinedDefectGraph G D).Adj x y ∧
        ¬ (x ∈ D.sparse ∧ y ∈ D.sparse) := by
  rw [subcriticalDefectGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, fun hs ↦ h.2 ⟨hs.2, hs.1⟩⟩
  · intro h
    exact ⟨h.1.ne, Or.inl h⟩

theorem subcriticalCombinedDefectGraph_adj_iff
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {x y : V} :
    (subcriticalCombinedDefectGraph G D).Adj x y ↔
      x ≠ y ∧ ((D.SamePart x y ∧ ¬ G.Adj x y) ∨
        (¬ D.SamePart x y ∧ ¬ D.ActivePair x y ∧ G.Adj x y)) := by
  rw [subcriticalCombinedDefectGraph_adj, subcriticalDivisionModelGraph_adj]
  have hloop : G.Adj x y → x ≠ y := SimpleGraph.Adj.ne
  have hdisj : D.SamePart x y → ¬ D.ActivePair x y :=
    D.not_activePair_of_samePart
  tauto

theorem subcriticalDefectGraph_adj_iff
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {x y : V} :
    (subcriticalDefectGraph G D).Adj x y ↔
      (x ≠ y ∧ ((D.SamePart x y ∧ ¬ G.Adj x y) ∨
        (¬ D.SamePart x y ∧ ¬ D.ActivePair x y ∧ G.Adj x y))) ∧
      ¬ (x ∈ D.sparse ∧ y ∈ D.sparse) := by
  rw [subcriticalDefectGraph_adj, subcriticalCombinedDefectGraph_adj_iff]

/-- The paper's `b(G,D)`, in unordered-edge normalization. -/
def subcriticalDefectCost (G : SimpleGraph V)
    (D : SubcriticalDivision k V) : ℕ :=
  (finiteGraphEdges (subcriticalCombinedDefectGraph G D)).card

theorem subcriticalDefectCost_eq_card_edgeFinset
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    subcriticalDefectCost G D =
      (subcriticalCombinedDefectGraph G D).edgeFinset.card := by
  classical
  rfl

theorem subcriticalDefectGraph_no_sparse_sparse
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {x y : V} (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    ¬ (subcriticalDefectGraph G D).Adj x y := by
  simp [hx, hy]

theorem subcriticalCombinedDefectGraph_of_sparse
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {x y : V} (hx : x ∈ D.sparse) (hy : y ∈ D.sparse) :
    (subcriticalCombinedDefectGraph G D).Adj x y ↔ G.Adj x y := by
  rw [subcriticalCombinedDefectGraph_adj_iff]
  have hs : ¬ D.SamePart x y := fun h ↦
    (D.mem_sparse.mp hx) (SubcriticalDivision.samePart_imp_support h).1
  have ha : ¬ D.ActivePair x y := fun h ↦
    (D.mem_sparse.mp hx) (SubcriticalDivision.activePair_imp_support h).1
  constructor
  · rintro ⟨_, hmissing | hpresent⟩
    · exact False.elim (hs hmissing.1)
    · exact hpresent.2.2
  · intro hG
    exact ⟨hG.ne, Or.inr ⟨hs, ha, hG⟩⟩

/-! ## Regular blow-ups -/

/-- A simple graph is a regular blow-up respecting this particular division.
The second field only forbids non-active pairs; it does not require active
pairs to be nonempty. -/
structure IsSubcriticalRegularBlowupFor
    (D : SubcriticalDivision k V) (H : SimpleGraph V) : Prop where
  part_complete : ∀ (a : D.PartIndex) {x y : V},
    x ∈ D.part a → y ∈ D.part a → x ≠ y → H.Adj x y
  edge_allowed : ∀ {x y : V}, H.Adj x y →
    D.SamePart x y ∨ D.ActivePair x y

/-- The finite simple-graph interpretation of Definition
`dfn:D-reg-blowup`. -/
def IsSubcriticalRegularBlowup (k : ℕ) (H : SimpleGraph V) : Prop :=
  ∃ D : SubcriticalDivision k V, IsSubcriticalRegularBlowupFor D H

namespace SubcriticalDivision

/-- The canonical injection of the vertices of one component core into the
global part-index type. -/
def componentPartEmbedding (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) : Fin (D.core i).order ↪ D.PartIndex where
  toFun j := ⟨i, j⟩
  inj' := by
    intro a b h
    simpa using h

/-- The part of `a` and the core-neighboring parts. These are exactly the
possible parts of vertices adjacent to a vertex in `a` in a regular blow-up. -/
def closedPartIndices (D : SubcriticalDivision k V) (a : D.PartIndex) :
    Finset D.PartIndex := by
  classical
  exact (Finset.univ.filter fun v ↦
    v = a.2 ∨ (D.core a.1).graph.Adj a.2 v).map
      (D.componentPartEmbedding a.1)

theorem card_closedPartIndices (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (a : D.PartIndex) : (D.closedPartIndices a).card = k - 1 := by
  classical
  letI : (D.core a.1).graph.LocallyFinite := fun _ ↦ Fintype.ofFinite _
  rw [closedPartIndices, Finset.card_map]
  have heq : (Finset.univ.filter fun v ↦
      v = a.2 ∨ (D.core a.1).graph.Adj a.2 v) =
      insert a.2 (SimpleGraph.neighborFinset
        (G := (D.core a.1).graph) a.2) := by
    ext v
    simp [eq_comm]
  rw [heq, Finset.card_insert_of_notMem]
  · have hdegree := (D.core a.1).degree_eq a.2
    rw [← (D.core a.1).graph.card_neighborSet_eq_degree] at hdegree
    have hncard : ((D.core a.1).graph.neighborSet a.2).ncard = k - 2 := by
      simpa only [Set.fintypeCard_eq_ncard] using hdegree
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset, hncard]
    omega
  · simp

theorem self_mem_closedPartIndices (D : SubcriticalDivision k V)
    (a : D.PartIndex) : a ∈ D.closedPartIndices a := by
  classical
  rcases a with ⟨i, u⟩
  rw [closedPartIndices, Finset.mem_map]
  exact ⟨u, by simp, rfl⟩

theorem mem_closedPartIndices_of_activePart (D : SubcriticalDivision k V)
    {a b : D.PartIndex} (h : D.ActivePart a b) :
    b ∈ D.closedPartIndices a := by
  classical
  obtain ⟨i, u, v, rfl, rfl, huv⟩ := h
  rw [closedPartIndices, Finset.mem_map]
  exact ⟨v, by simp [huv], rfl⟩

end SubcriticalDivision

theorem subcriticalDivisionModelGraph_isRegularBlowupFor
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    IsSubcriticalRegularBlowupFor D (subcriticalDivisionModelGraph G D) := by
  constructor
  · intro a x y hx hy hxy
    exact (subcriticalDivisionModelGraph_adj G D x y).mpr
      ⟨hxy, Or.inl ⟨a, hx, hy⟩⟩
  · intro x y hxy
    rcases (subcriticalDivisionModelGraph_adj G D x y).mp hxy with ⟨_, h | h⟩
    · exact Or.inl h
    · exact Or.inr h.1

theorem subcriticalDivisionModelGraph_isRegularBlowup
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    IsSubcriticalRegularBlowup k (subcriticalDivisionModelGraph G D) :=
  ⟨D, subcriticalDivisionModelGraph_isRegularBlowupFor G D⟩

/-- Every regular-core blow-up is induced-`K_{1,k}`-free.  The `k` leaves
would have to occupy distinct parts in the closed neighborhood of the
center's core vertex, but that closed neighborhood has only `k-1` parts. -/
theorem isSubcriticalRegularBlowupFor_not_inducedEmbeds_inducedStar
    (hk : 3 ≤ k) (D : SubcriticalDivision k V) (H : SimpleGraph V)
    (hH : IsSubcriticalRegularBlowupFor D H) :
    ¬ Regularity.InducedEmbeds (inducedStar k) H := by
  rintro ⟨f⟩
  let firstLeaf : Fin k := ⟨0, by omega⟩
  have hcenterEdge : H.Adj (f 0) (f firstLeaf.succ) :=
    f.map_rel_iff.mpr (inducedStar_center_adj_leaf firstLeaf)
  have hcenterSupport : f 0 ∈ D.support := by
    rcases hH.edge_allowed hcenterEdge with hs | ha
    · exact (SubcriticalDivision.samePart_imp_support hs).1
    · exact (SubcriticalDivision.activePair_imp_support ha).1
  obtain ⟨centerPart, hcenterPart⟩ := D.mem_support.mp hcenterSupport
  have hleafSupport (i : Fin k) : f i.succ ∈ D.support := by
    have hi : H.Adj (f 0) (f i.succ) :=
      f.map_rel_iff.mpr (inducedStar_center_adj_leaf i)
    rcases hH.edge_allowed hi with hs | ha
    · exact (SubcriticalDivision.samePart_imp_support hs).2
    · exact (SubcriticalDivision.activePair_imp_support ha).2
  let leafPart : Fin k → D.PartIndex := fun i ↦
    Classical.choose (D.mem_support.mp (hleafSupport i))
  have hleafPart (i : Fin k) : f i.succ ∈ D.part (leafPart i) :=
    Classical.choose_spec (D.mem_support.mp (hleafSupport i))
  have hleafClosed (i : Fin k) :
      leafPart i ∈ D.closedPartIndices centerPart := by
    have hi : H.Adj (f 0) (f i.succ) :=
      f.map_rel_iff.mpr (inducedStar_center_adj_leaf i)
    rcases hH.edge_allowed hi with hs | ha
    · have heq : centerPart = leafPart i :=
        (D.samePart_iff_of_mem_parts hcenterPart (hleafPart i)).mp hs
      rw [← heq]
      exact D.self_mem_closedPartIndices centerPart
    · exact D.mem_closedPartIndices_of_activePart
        ((D.activePair_iff_of_mem_parts hcenterPart (hleafPart i)).mp ha)
  have hleafInjective : Function.Injective leafPart := by
    intro i j hij
    by_contra hne
    have himages : f i.succ ≠ f j.succ := by
      exact f.injective.ne ((Fin.succ_injective k).ne hne)
    have hadj : H.Adj (f i.succ) (f j.succ) := by
      apply hH.part_complete (leafPart i) (hleafPart i)
      · simpa [hij] using hleafPart j
      · exact himages
    exact inducedStar_leaf_nonadj_leaf i j (f.map_rel_iff.mp hadj)
  let leafEmbedding : Fin k ↪ {a // a ∈ D.closedPartIndices centerPart} := {
    toFun := fun i ↦ ⟨leafPart i, hleafClosed i⟩
    inj' := fun i j h ↦ hleafInjective (congrArg Subtype.val h)
  }
  have hcard := Fintype.card_le_of_injective leafEmbedding leafEmbedding.injective
  have : k ≤ k - 1 := by
    simpa only [Fintype.card_fin, Fintype.card_coe,
      D.card_closedPartIndices hk centerPart] using hcard
  omega

theorem isSubcriticalRegularBlowup_not_inducedEmbeds_inducedStar
    (hk : 3 ≤ k) (H : SimpleGraph V)
    (hH : IsSubcriticalRegularBlowup k H) :
    ¬ Regularity.InducedEmbeds (inducedStar k) H := by
  obtain ⟨D, hD⟩ := hH
  exact isSubcriticalRegularBlowupFor_not_inducedEmbeds_inducedStar hk D H hD

theorem subcriticalDivisionModelGraph_eq_of_isRegularBlowupFor
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hG : IsSubcriticalRegularBlowupFor D G) :
    subcriticalDivisionModelGraph G D = G := by
  ext x y
  rw [subcriticalDivisionModelGraph_adj]
  constructor
  · rintro ⟨_, hs | ha⟩
    · obtain ⟨a, hx, hy⟩ := hs
      exact hG.part_complete a hx hy (fun h ↦ by subst y; simp at *)
    · exact ha.2
  · intro hxy
    exact ⟨hxy.ne, hG.edge_allowed hxy |>.elim Or.inl (fun ha ↦ Or.inr ⟨ha, hxy⟩)⟩

/-! ## Exact edit distance and fixed-division minimality -/

theorem subcriticalCombinedDefectGraph_edgeFinset_eq_editFinset
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    finiteGraphEdges (subcriticalCombinedDefectGraph G D) =
      DenseGraph.simpleGraphEditFinset G (subcriticalDivisionModelGraph G D) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet,
        DenseGraph.mem_simpleGraphEditFinset,
        subcriticalCombinedDefectGraph_adj]
      tauto

theorem simpleGraphEditDistance_subcriticalDivisionModelGraph
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    DenseGraph.simpleGraphEditDistance G (subcriticalDivisionModelGraph G D) =
      subcriticalDefectCost G D := by
  rw [DenseGraph.simpleGraphEditDistance, subcriticalDefectCost,
    ← subcriticalCombinedDefectGraph_edgeFinset_eq_editFinset]

theorem subcriticalDivisionModelGraph_minimal
    (G H : SimpleGraph V) (D : SubcriticalDivision k V)
    (hH : IsSubcriticalRegularBlowupFor D H) :
    subcriticalDefectCost G D ≤ DenseGraph.simpleGraphEditDistance G H := by
  classical
  rw [← simpleGraphEditDistance_subcriticalDivisionModelGraph,
    DenseGraph.simpleGraphEditDistance, DenseGraph.simpleGraphEditDistance]
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [DenseGraph.mem_simpleGraphEditFinset] at he ⊢
      rcases he with ⟨hG, hnR⟩ | ⟨hR, hnG⟩
      · left
        refine ⟨hG, ?_⟩
        intro hHxy
        rcases hH.edge_allowed hHxy with hs | ha
        · exact hnR ((subcriticalDivisionModelGraph_adj G D x y).mpr
            ⟨hHxy.ne, Or.inl hs⟩)
        · exact hnR ((subcriticalDivisionModelGraph_adj G D x y).mpr
            ⟨hHxy.ne, Or.inr ⟨ha, hG⟩⟩)
      · right
        refine ⟨?_, hnG⟩
        rcases (subcriticalDivisionModelGraph_adj G D x y).mp hR with ⟨hxy, hs | ha⟩
        · obtain ⟨a, hx, hy⟩ := hs
          exact hH.part_complete a hx hy hxy
        · exact False.elim (hnG ha.2)

/-- Exact factor-two finite cut bound for the repaired simple graph. -/
theorem finiteLabeledCutDist_subcriticalDivisionModelGraph_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) :
    DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph G)
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (subcriticalDivisionModelGraph G D)) ≤
      2 * (subcriticalDefectCost G D : ℝ) /
        (Fintype.card V : ℝ) ^ 2 := by
  simpa [simpleGraphEditDistance_subcriticalDivisionModelGraph] using
    DenseGraph.finiteLabeledCutDist_ofSimpleGraph_le_simpleGraphEdit G
      (subcriticalDivisionModelGraph G D)

/-! ## Reindexing -/

@[simp] theorem subcriticalDivisionModelGraph_reindex
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) :
    subcriticalDivisionModelGraph G (D.reindex e) =
      subcriticalDivisionModelGraph G D := by
  ext x y
  simp [subcriticalDivisionModelGraph_adj]

@[simp] theorem subcriticalCombinedDefectGraph_reindex
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) :
    subcriticalCombinedDefectGraph G (D.reindex e) =
      subcriticalCombinedDefectGraph G D := by
  ext x y
  simp

@[simp] theorem subcriticalDefectGraph_reindex
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) :
    subcriticalDefectGraph G (D.reindex e) = subcriticalDefectGraph G D := by
  ext x y
  simp

@[simp] theorem subcriticalDefectCost_reindex
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) :
    subcriticalDefectCost G (D.reindex e) = subcriticalDefectCost G D := by
  simp [subcriticalDefectCost]

/-! ## Relabeling -/

theorem subcritical_map_equiv_adj_iff
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) (x y : W) :
    (G.map e.toEmbedding).Adj x y ↔ G.Adj (e.symm x) (e.symm y) := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    have ha : a = e.symm x := by
      apply e.injective
      simpa using hax
    have hb : b = e.symm y := by
      apply e.injective
      simpa using hby
    simpa [ha, hb] using hab
  · intro h
    exact ⟨e.symm x, e.symm y, h, e.apply_symm_apply x, e.apply_symm_apply y⟩

@[simp] theorem subcriticalDivisionModelGraph_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (e : V ≃ W) :
    subcriticalDivisionModelGraph (G.map e.toEmbedding) (D.relabel e) =
      (subcriticalDivisionModelGraph G D).map e.toEmbedding := by
  ext x y
  rw [subcriticalDivisionModelGraph_adj,
    subcritical_map_equiv_adj_iff (subcriticalDivisionModelGraph G D) e x y,
    subcriticalDivisionModelGraph_adj]
  simp only [D.relabel_samePart, D.relabel_activePair,
    subcritical_map_equiv_adj_iff]
  exact and_congr (e.symm.injective.eq_iff.not.symm) Iff.rfl

@[simp] theorem subcriticalCombinedDefectGraph_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (e : V ≃ W) :
    subcriticalCombinedDefectGraph (G.map e.toEmbedding) (D.relabel e) =
      (subcriticalCombinedDefectGraph G D).map e.toEmbedding := by
  ext x y
  rw [subcriticalCombinedDefectGraph_adj,
    subcritical_map_equiv_adj_iff (subcriticalCombinedDefectGraph G D) e x y,
    subcriticalCombinedDefectGraph_adj]
  simp only [subcriticalDivisionModelGraph_relabel, subcritical_map_equiv_adj_iff]

theorem subcriticalDefectCost_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (e : V ≃ W) :
    subcriticalDefectCost (G.map e.toEmbedding) (D.relabel e) =
      subcriticalDefectCost G D := by
  rw [← simpleGraphEditDistance_subcriticalDivisionModelGraph,
    ← simpleGraphEditDistance_subcriticalDivisionModelGraph,
    subcriticalDivisionModelGraph_relabel]
  exact DenseGraph.simpleGraphEditDistance_eq_of_pair_iso
    (SimpleGraph.Iso.map e G).symm
    (SimpleGraph.Iso.map e (subcriticalDivisionModelGraph G D)).symm rfl

/-! ## Canonical minimization -/

/-- Divisions satisfying the paper's ordering convention at `R₀`. -/
def orderedSubcriticalDivisions (k : ℕ) (V : Type*) [Fintype V]
    [DecidableEq V] (R₀ : ℕ) : Set (SubcriticalDivision k V) :=
  {D | D.IsOrderedByCutoff R₀}

theorem orderedSubcriticalDivisions_nonempty (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) (R₀ : ℕ) :
    (orderedSubcriticalDivisions k V R₀).Nonempty := by
  obtain ⟨D, hD⟩ := SubcriticalDivision.exists_ordered_of_sub_one_le_card hk hcard R₀
  exact ⟨D, hD⟩

/-- A stable choice of an ordered division minimizing the exact defect cost. -/
def canonicalSubcriticalDivision (G : SimpleGraph V) (R₀ : ℕ)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V) :
    SubcriticalDivision k V :=
  Function.argminOn (subcriticalDefectCost G)
    (orderedSubcriticalDivisions k V R₀)
    (orderedSubcriticalDivisions_nonempty hk hcard R₀)

theorem canonicalSubcriticalDivision_isOrdered
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    (canonicalSubcriticalDivision G R₀ hk hcard).IsOrderedByCutoff R₀ := by
  show canonicalSubcriticalDivision G R₀ hk hcard ∈
    orderedSubcriticalDivisions k V R₀
  exact Function.argminOn_mem _ _ _

theorem canonicalSubcriticalDivision_minimal_ordered
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V)
    (D : SubcriticalDivision k V) (hD : D.IsOrderedByCutoff R₀) :
    subcriticalDefectCost G (canonicalSubcriticalDivision G R₀ hk hcard) ≤
      subcriticalDefectCost G D :=
  Function.argminOn_le _ _ hD

theorem canonicalSubcriticalDivision_minimal
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V)
    (D : SubcriticalDivision k V) :
    subcriticalDefectCost G (canonicalSubcriticalDivision G R₀ hk hcard) ≤
      subcriticalDefectCost G D := by
  let e := D.orderingPermutation R₀
  calc
    _ ≤ subcriticalDefectCost G (D.reindex e) :=
      canonicalSubcriticalDivision_minimal_ordered G R₀ hk hcard _
        (D.reindex_orderingPermutation_isOrdered R₀)
    _ = _ := subcriticalDefectCost_reindex G D e

/-- Although the selected minimizer may depend on the ordering cutoff, its
minimum cost does not. -/
theorem canonicalSubcriticalDefectCost_independent_of_cutoff
    (G : SimpleGraph V) (R₀ R₁ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    subcriticalDefectCost G (canonicalSubcriticalDivision G R₀ hk hcard) =
      subcriticalDefectCost G (canonicalSubcriticalDivision G R₁ hk hcard) := by
  apply Nat.le_antisymm
  · exact canonicalSubcriticalDivision_minimal G R₀ hk hcard _
  · exact canonicalSubcriticalDivision_minimal G R₁ hk hcard _

/-- The ordinary canonical defect graph `T(G)`. -/
def canonicalSubcriticalDefectGraph (G : SimpleGraph V) (R₀ : ℕ)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V) : SimpleGraph V :=
  subcriticalDefectGraph G (canonicalSubcriticalDivision G R₀ hk hcard)

/-- The canonical combined defect graph, including the sparse-induced graph. -/
def canonicalSubcriticalCombinedDefectGraph (G : SimpleGraph V) (R₀ : ℕ)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V) : SimpleGraph V :=
  subcriticalCombinedDefectGraph G (canonicalSubcriticalDivision G R₀ hk hcard)

/-- The exact canonical minimum defect cost `b(G)`. -/
def canonicalSubcriticalDefectCost (G : SimpleGraph V) (R₀ : ℕ)
    (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V) : ℕ :=
  subcriticalDefectCost G (canonicalSubcriticalDivision G R₀ hk hcard)

/-- The canonical minimum defect cost is invariant under a relabeling of the
vertex set.  No equivariance claim is made about the chosen argmin itself. -/
theorem canonicalSubcriticalDefectCost_relabel
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcardV : k - 1 ≤ Fintype.card V)
    (hcardW : k - 1 ≤ Fintype.card W) :
    canonicalSubcriticalDefectCost (G.map e.toEmbedding) R₀ hk hcardW =
      canonicalSubcriticalDefectCost G R₀ hk hcardV := by
  apply Nat.le_antisymm
  · calc
      canonicalSubcriticalDefectCost (G.map e.toEmbedding) R₀ hk hcardW ≤
          subcriticalDefectCost (G.map e.toEmbedding)
            ((canonicalSubcriticalDivision G R₀ hk hcardV).relabel e) :=
        canonicalSubcriticalDivision_minimal
          (G.map e.toEmbedding) R₀ hk hcardW _
      _ = canonicalSubcriticalDefectCost G R₀ hk hcardV :=
        subcriticalDefectCost_relabel G
          (canonicalSubcriticalDivision G R₀ hk hcardV) e
  · let D := canonicalSubcriticalDivision
        (G.map e.toEmbedding) R₀ hk hcardW
    have hdouble : (G.map e.toEmbedding).map e.symm.toEmbedding = G := by
      ext x y
      simp only [subcritical_map_equiv_adj_iff]
      simp
    have hcost := subcriticalDefectCost_relabel
      (G.map e.toEmbedding) D e.symm
    calc
      canonicalSubcriticalDefectCost G R₀ hk hcardV ≤
          subcriticalDefectCost G (D.relabel e.symm) :=
        canonicalSubcriticalDivision_minimal G R₀ hk hcardV _
      _ = subcriticalDefectCost (G.map e.toEmbedding) D := by
        simpa only [hdouble] using hcost
      _ = canonicalSubcriticalDefectCost
          (G.map e.toEmbedding) R₀ hk hcardW := rfl

theorem canonicalSubcriticalRepair_attains
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    DenseGraph.simpleGraphEditDistance G
        (subcriticalDivisionModelGraph G
          (canonicalSubcriticalDivision G R₀ hk hcard)) =
      canonicalSubcriticalDefectCost G R₀ hk hcard := by
  exact simpleGraphEditDistance_subcriticalDivisionModelGraph _ _

theorem canonicalSubcriticalDefectCost_le_regularBlowup
    (G H : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V)
    (hH : IsSubcriticalRegularBlowup k H) :
    canonicalSubcriticalDefectCost G R₀ hk hcard ≤
      DenseGraph.simpleGraphEditDistance G H := by
  obtain ⟨D, hD⟩ := hH
  exact (canonicalSubcriticalDivision_minimal G R₀ hk hcard D).trans
    (subcriticalDivisionModelGraph_minimal G H D hD)

/-- The canonical repair simultaneously realizes the defect cost and the
minimum edit distance from `G` to the entire regular-blow-up family. -/
theorem canonicalSubcriticalMinimumEditCharacterization
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    IsSubcriticalRegularBlowup k
        (subcriticalDivisionModelGraph G
          (canonicalSubcriticalDivision G R₀ hk hcard)) ∧
      DenseGraph.simpleGraphEditDistance G
          (subcriticalDivisionModelGraph G
            (canonicalSubcriticalDivision G R₀ hk hcard)) =
        canonicalSubcriticalDefectCost G R₀ hk hcard ∧
      ∀ H : SimpleGraph V, IsSubcriticalRegularBlowup k H →
        canonicalSubcriticalDefectCost G R₀ hk hcard ≤
          DenseGraph.simpleGraphEditDistance G H := by
  exact ⟨subcriticalDivisionModelGraph_isRegularBlowup _ _,
    canonicalSubcriticalRepair_attains G R₀ hk hcard,
    fun H hH ↦ canonicalSubcriticalDefectCost_le_regularBlowup
      G H R₀ hk hcard hH⟩

theorem canonicalSubcriticalDefectCost_eq_zero_iff
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    canonicalSubcriticalDefectCost G R₀ hk hcard = 0 ↔
      IsSubcriticalRegularBlowup k G := by
  constructor
  · intro hzero
    let D := canonicalSubcriticalDivision G R₀ hk hcard
    have hedit := canonicalSubcriticalRepair_attains G R₀ hk hcard
    rw [hzero] at hedit
    have heq := DenseGraph.simpleGraphEditDistance_eq_zero_iff.mp hedit
    rw [heq]
    exact subcriticalDivisionModelGraph_isRegularBlowup G D
  · rintro ⟨D, hD⟩
    have hrepair : subcriticalDivisionModelGraph G D = G :=
      subcriticalDivisionModelGraph_eq_of_isRegularBlowupFor G D hD
    have hcost : subcriticalDefectCost G D = 0 := by
      rw [← simpleGraphEditDistance_subcriticalDivisionModelGraph, hrepair]
      simp
    exact Nat.eq_zero_of_le_zero <|
      (canonicalSubcriticalDivision_minimal G R₀ hk hcard D).trans_eq hcost

/-- With singleton division parts the repair only deletes input edges, so its
cost is at most the number of input edges. -/
theorem subcriticalDefectCost_le_card_edges_of_singleton_parts
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hparts : ∀ a : D.PartIndex, (D.part a).card = 1) :
    subcriticalDefectCost G D ≤ (finiteGraphEdges G).card := by
  classical
  rw [subcriticalDefectCost]
  apply Finset.card_le_card
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      have he' : (subcriticalCombinedDefectGraph G D).Adj x y := by
        simpa only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet] using he
      simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet]
      rw [subcriticalCombinedDefectGraph_adj_iff] at he'
      rcases he'.2 with hmissing | hpresent
      · obtain ⟨a, hx, hy⟩ := hmissing.1
        have hxy : x = y := by
          exact Finset.card_le_one.mp (hparts a).le x hx y hy
        exact False.elim (he'.1 hxy)
      · exact hpresent.2.2

theorem canonicalSubcriticalDefectCost_le_card_edges
    (G : SimpleGraph V) (R₀ : ℕ) (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) :
    canonicalSubcriticalDefectCost G R₀ hk hcard ≤ (finiteGraphEdges G).card := by
  obtain ⟨D, hDord, hparts⟩ :=
    SubcriticalDivision.exists_ordered_singleton_parts hk hcard R₀
  exact (canonicalSubcriticalDivision_minimal_ordered G R₀ hk hcard D hDord).trans
    (subcriticalDefectCost_le_card_edges_of_singleton_parts G D hparts)

end InducedStars
