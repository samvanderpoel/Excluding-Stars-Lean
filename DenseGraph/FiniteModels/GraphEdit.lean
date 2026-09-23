import DenseGraph.FiniteModels.WeightedGraph
import InducedStars.FiniteModels.GraphonLimits
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

/-!
# Edit distance for finite simple graphs

This file gives the vertex-type-generic version of the labeled simple-graph
edit distance.  An edit is an unordered edge toggle.  The historical
`InducedStars.graphEditDistance` on `Fin n` is recovered exactly, so the
existing sharp graphon estimate can be reused without a change of
normalization.
-/

noncomputable section

open scoped symmDiff

namespace DenseGraph

universe u v

variable {V : Type u} [Fintype V]

/-- The unordered pairs on which two finite simple graphs disagree. -/
def simpleGraphEditFinset (G H : SimpleGraph V) : Finset (Sym2 V) :=
  (Set.toFinite (G.edgeSet ∆ H.edgeSet)).toFinset

@[simp] theorem mem_simpleGraphEditFinset {G H : SimpleGraph V} {e : Sym2 V} :
    e ∈ simpleGraphEditFinset G H ↔
      (e ∈ G.edgeSet ∧ e ∉ H.edgeSet) ∨
        (e ∈ H.edgeSet ∧ e ∉ G.edgeSet) := by
  classical
  simp [simpleGraphEditFinset, Finset.mem_symmDiff]

/-- The number of unordered edge toggles between two labeled finite graphs. -/
def simpleGraphEditDistance (G H : SimpleGraph V) : ℕ :=
  (simpleGraphEditFinset G H).card

/-- The ordered vertex pairs on which two finite graphs disagree. -/
def simpleGraphOrderedEditFinset (G H : SimpleGraph V) : Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p ↦ G.Adj p.1 p.2 ≠ H.Adj p.1 p.2

@[simp] theorem mem_simpleGraphOrderedEditFinset
    {G H : SimpleGraph V} {p : V × V} :
    p ∈ simpleGraphOrderedEditFinset G H ↔
      G.Adj p.1 p.2 ≠ H.Adj p.1 p.2 := by
  classical
  simp [simpleGraphOrderedEditFinset]

/-- Each changed unordered edge has exactly two ordered orientations. -/
theorem card_simpleGraphOrderedEditFinset (G H : SimpleGraph V) :
    (simpleGraphOrderedEditFinset G H).card =
      2 * simpleGraphEditDistance G H := by
  classical
  let D : SimpleGraph V := (G \ H) ⊔ (H \ G)
  letI : DecidableRel D.Adj := Classical.decRel _
  letI : Fintype D.edgeSet := D.fintypeEdgeSet
  have hedge : D.edgeFinset = simpleGraphEditFinset G H := by
    ext e
    induction e using Sym2.inductionOn with
    | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset,
          mem_simpleGraphEditFinset]
        change
          ((G.Adj u v ∧ ¬H.Adj u v) ∨
              (H.Adj u v ∧ ¬G.Adj u v)) ↔ _
        tauto
  have hpairs :
      simpleGraphOrderedEditFinset G H =
        Finset.univ.filter fun p : V × V ↦ D.Adj p.1 p.2 := by
    ext p
    simp only [mem_simpleGraphOrderedEditFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (G.Adj p.1 p.2 ≠ H.Adj p.1 p.2) ↔
      ((G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2) ∨
        (H.Adj p.1 p.2 ∧ ¬G.Adj p.1 p.2))
    tauto
  calc
    (simpleGraphOrderedEditFinset G H).card =
        (Finset.univ.filter fun p : V × V ↦ D.Adj p.1 p.2).card := by
      rw [hpairs]
    _ = 2 * D.edgeFinset.card := by
      simpa only [] using D.two_mul_card_edgeFinset.symm
    _ = 2 * simpleGraphEditDistance G H := by
      rw [hedge]
      rfl

@[simp] theorem simpleGraphEditFinset_self (G : SimpleGraph V) :
    simpleGraphEditFinset G G = ∅ := by
  classical
  simp [simpleGraphEditFinset]

@[simp] theorem simpleGraphEditDistance_self (G : SimpleGraph V) :
    simpleGraphEditDistance G G = 0 := by
  simp [simpleGraphEditDistance]

theorem simpleGraphEditFinset_comm (G H : SimpleGraph V) :
    simpleGraphEditFinset G H = simpleGraphEditFinset H G := by
  classical
  ext e
  simp only [mem_simpleGraphEditFinset]
  tauto

theorem simpleGraphEditDistance_comm (G H : SimpleGraph V) :
    simpleGraphEditDistance G H = simpleGraphEditDistance H G := by
  rw [simpleGraphEditDistance, simpleGraphEditDistance,
    simpleGraphEditFinset_comm]

/-- Edge disagreements obey the set-theoretic triangle inclusion. -/
theorem simpleGraphEditFinset_triangle_subset [DecidableEq V]
    (G H K : SimpleGraph V) :
    simpleGraphEditFinset G K ⊆
      simpleGraphEditFinset G H ∪ simpleGraphEditFinset H K := by
  classical
  intro e he
  simp only [mem_simpleGraphEditFinset, Finset.mem_union] at he ⊢
  tauto

/-- Triangle inequality for unordered-edge edit distance. -/
theorem simpleGraphEditDistance_triangle (G H K : SimpleGraph V) :
    simpleGraphEditDistance G K ≤
      simpleGraphEditDistance G H + simpleGraphEditDistance H K := by
  classical
  calc
    simpleGraphEditDistance G K ≤
        (simpleGraphEditFinset G H ∪ simpleGraphEditFinset H K).card :=
      Finset.card_le_card (simpleGraphEditFinset_triangle_subset G H K)
    _ ≤ (simpleGraphEditFinset G H).card +
        (simpleGraphEditFinset H K).card := Finset.card_union_le _ _
    _ = _ := rfl

/-- Zero edit distance characterizes equality of finite simple graphs. -/
@[simp] theorem simpleGraphEditDistance_eq_zero_iff {G H : SimpleGraph V} :
    simpleGraphEditDistance G H = 0 ↔ G = H := by
  classical
  constructor
  · intro h
    have hD : simpleGraphEditFinset G H = ∅ :=
      Finset.card_eq_zero.mp h
    apply SimpleGraph.edgeSet_injective
    ext e
    have he := Finset.ext_iff.mp hD e
    simp only [mem_simpleGraphEditFinset, Finset.notMem_empty,
      iff_false] at he
    tauto
  · rintro rfl
    exact simpleGraphEditDistance_self G

/-- Exact decomposition into deleted and added unordered edges. -/
theorem simpleGraphEditDistance_eq_deleted_add_added [DecidableEq V]
    (G H : SimpleGraph V) :
    simpleGraphEditDistance G H =
      (InducedStars.finiteGraphEdges G \
        InducedStars.finiteGraphEdges H).card +
      (InducedStars.finiteGraphEdges H \
        InducedStars.finiteGraphEdges G).card := by
  classical
  have hfin : simpleGraphEditFinset G H =
      InducedStars.finiteGraphEdges G ∆
        InducedStars.finiteGraphEdges H := by
    ext e
    simp [mem_simpleGraphEditFinset, Finset.mem_symmDiff]
  rw [simpleGraphEditDistance, hfin, Finset.symmDiff_def,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_of_subset_right Finset.sdiff_subset Finset.sdiff_disjoint

/-- If the target edge family is obtained by deleting a subfamily `D` and
adding a disjoint subfamily `A`, then the edit distance is exactly
`|D| + |A|`.  This is the convenient counting interface for graph repairs. -/
theorem simpleGraphEditDistance_eq_card_delete_add
    [DecidableEq V] (G H : SimpleGraph V) (D A : Finset (Sym2 V))
    (hD : D ⊆ InducedStars.finiteGraphEdges G)
    (hA : Disjoint A (InducedStars.finiteGraphEdges G))
    (hH : InducedStars.finiteGraphEdges H =
      (InducedStars.finiteGraphEdges G \ D) ∪ A) :
    simpleGraphEditDistance G H = D.card + A.card := by
  classical
  rw [simpleGraphEditDistance_eq_deleted_add_added, hH]
  have hdelete : InducedStars.finiteGraphEdges G \
      ((InducedStars.finiteGraphEdges G \ D) ∪ A) = D := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨heG, hnot⟩
      have heD : e ∈ D := by
        by_contra heD
        exact hnot (Or.inl ⟨heG, heD⟩)
      exact heD
    · intro heD
      refine ⟨hD heD, ?_⟩
      intro hbad
      rcases hbad with hremain | heA
      · exact hremain.2 heD
      · exact (Finset.disjoint_left.mp hA heA (hD heD))
  have hadd : ((InducedStars.finiteGraphEdges G \ D) ∪ A) \
      InducedStars.finiteGraphEdges G = A := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hremain | heA, hnotG⟩
      · exact False.elim (hnotG hremain.1)
      · exact heA
    · intro heA
      exact ⟨Or.inr heA, fun heG ↦
        Finset.disjoint_left.mp hA heA heG⟩
  rw [hdelete, hadd]

/-! ## Finite labeled cut distance -/

private theorem abs_ofSimpleGraph_weight_sub
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (i j : V) :
    |(FiniteWeightedGraph.ofSimpleGraph G).weight i j -
        (FiniteWeightedGraph.ofSimpleGraph H).weight i j| =
      if G.Adj i j ≠ H.Adj i j then 1 else 0 := by
  rw [FiniteWeightedGraph.ofSimpleGraph_weight,
    FiniteWeightedGraph.ofSimpleGraph_weight]
  by_cases hG : G.Adj i j <;> by_cases hH : H.Adj i j <;>
    simp [hG, hH]

/-- Every rectangle discrepancy between two adjacency matrices is bounded
by the total number of ordered adjacency disagreements. -/
theorem abs_rectangleDiscrepancy_ofSimpleGraph_le_edit
    [DecidableEq V] (G H : SimpleGraph V) (S T : Finset V) :
    |FiniteWeightedGraph.rectangleDiscrepancy
        (FiniteWeightedGraph.ofSimpleGraph G)
        (FiniteWeightedGraph.ofSimpleGraph H) S T| ≤
      2 * (simpleGraphEditDistance G H : ℝ) := by
  classical
  simp only [FiniteWeightedGraph.rectangleDiscrepancy]
  rw [← Finset.sum_product']
  calc
    |∑ p ∈ S ×ˢ T,
        ((FiniteWeightedGraph.ofSimpleGraph G).weight p.1 p.2 -
          (FiniteWeightedGraph.ofSimpleGraph H).weight p.1 p.2)| ≤
        ∑ p ∈ S ×ˢ T,
          |(FiniteWeightedGraph.ofSimpleGraph G).weight p.1 p.2 -
            (FiniteWeightedGraph.ofSimpleGraph H).weight p.1 p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (Finset.univ : Finset (V × V)),
          |(FiniteWeightedGraph.ofSimpleGraph G).weight p.1 p.2 -
            (FiniteWeightedGraph.ofSimpleGraph H).weight p.1 p.2| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro p _hp _hnot
        exact abs_nonneg _
    _ = ((simpleGraphOrderedEditFinset G H).card : ℝ) := by
      rw [show
        (∑ p ∈ (Finset.univ : Finset (V × V)),
            |(FiniteWeightedGraph.ofSimpleGraph G).weight p.1 p.2 -
              (FiniteWeightedGraph.ofSimpleGraph H).weight p.1 p.2|) =
          ∑ p ∈ (Finset.univ : Finset (V × V)),
            if G.Adj p.1 p.2 ≠ H.Adj p.1 p.2 then 1 else 0 by
        apply Finset.sum_congr rfl
        intro p _hp
        exact abs_ofSimpleGraph_weight_sub G H p.1 p.2]
      rw [simpleGraphOrderedEditFinset]
      exact (Finset.natCast_card_filter
        (R := ℝ) (fun p : V × V ↦
          G.Adj p.1 p.2 ≠ H.Adj p.1 p.2) Finset.univ).symm
    _ = 2 * (simpleGraphEditDistance G H : ℝ) := by
      exact_mod_cast card_simpleGraphOrderedEditFinset G H

/-- The unnormalized finite cut discrepancy of two simple graphs is at most
twice their unordered edit distance. -/
theorem finiteLabeledCutRaw_ofSimpleGraph_le_edit
    [DecidableEq V] (G H : SimpleGraph V) :
    FiniteWeightedGraph.finiteLabeledCutRaw
        (FiniteWeightedGraph.ofSimpleGraph G)
        (FiniteWeightedGraph.ofSimpleGraph H) ≤
      2 * (simpleGraphEditDistance G H : ℝ) := by
  obtain ⟨S, T, hST⟩ :=
    FiniteWeightedGraph.exists_rectangleDiscrepancy_eq_raw
      (FiniteWeightedGraph.ofSimpleGraph G)
      (FiniteWeightedGraph.ofSimpleGraph H)
  rw [← hST]
  exact abs_rectangleDiscrepancy_ofSimpleGraph_le_edit G H S T

/-- Same-label finite cut distance is controlled by simple-graph edit
distance, with the sharp ordered/unordered factor two. -/
theorem finiteLabeledCutDist_ofSimpleGraph_le_simpleGraphEdit
    [DecidableEq V] (G H : SimpleGraph V) :
    FiniteWeightedGraph.finiteLabeledCutDist
        (FiniteWeightedGraph.ofSimpleGraph G)
        (FiniteWeightedGraph.ofSimpleGraph H) ≤
      2 * (simpleGraphEditDistance G H : ℝ) /
        (Fintype.card V : ℝ) ^ 2 := by
  rw [FiniteWeightedGraph.finiteLabeledCutDist]
  exact div_le_div_of_nonneg_right
    (finiteLabeledCutRaw_ofSimpleGraph_le_edit G H) (sq_nonneg _)

section Relabeling

variable {W : Type v} [Fintype W]

/-- A vertex equivalence acts equivalently on unordered vertex pairs. -/
def sym2Equiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by
    rw [Sym2.map_map]
    have hfun : e.symm ∘ e = id := by
      funext a
      exact e.symm_apply_apply a
    rw [hfun, Sym2.map_id]
    rfl
  right_inv x := by
    rw [Sym2.map_map]
    have hfun : e ∘ e.symm = id := by
      funext a
      exact e.apply_symm_apply a
    rw [hfun, Sym2.map_id]
    rfl

/-- Relabeling both graphs by the same vertex equivalence preserves the
edit finset, after transporting its unordered pairs. -/
theorem simpleGraphEditFinset_comap_equiv
    [DecidableEq V] (e : V ≃ W) (G H : SimpleGraph W) :
    simpleGraphEditFinset (G.comap e) (H.comap e) =
      (simpleGraphEditFinset G H).map (sym2Equiv e).symm.toEmbedding := by
  classical
  ext x
  rw [Finset.mem_map_equiv]
  induction x using Sym2.inductionOn with
  | _ a b =>
      simp [mem_simpleGraphEditFinset, sym2Equiv,
        SimpleGraph.mem_edgeSet]

/-- Edit distance is invariant under a simultaneous change of vertex labels. -/
theorem simpleGraphEditDistance_comap_equiv
    (e : V ≃ W) (G H : SimpleGraph W) :
    simpleGraphEditDistance (G.comap e) (H.comap e) =
      simpleGraphEditDistance G H := by
  classical
  rw [simpleGraphEditDistance, simpleGraphEditDistance,
    simpleGraphEditFinset_comap_equiv, Finset.card_map]

/-- Isomorphisms of two graph pairs preserve their edit distance when they
have the same underlying vertex equivalence. -/
theorem simpleGraphEditDistance_eq_of_pair_iso
    {G H : SimpleGraph V} {G' H' : SimpleGraph W}
    (eG : G ≃g G') (eH : H ≃g H')
    (he : eG.toEquiv = eH.toEquiv) :
    simpleGraphEditDistance G H = simpleGraphEditDistance G' H' := by
  have hG : G = G'.comap eG.toEquiv := by
    ext i j
    exact eG.map_rel_iff.symm
  have hH0 : H = H'.comap eH.toEquiv := by
    ext i j
    exact eH.map_rel_iff.symm
  have hH : H = H'.comap eG.toEquiv := by
    rw [he]
    exact hH0
  rw [hG, hH, simpleGraphEditDistance_comap_equiv]

end Relabeling

/-! ## Compatibility with the historical `Fin n` API -/

@[simp] theorem simpleGraphEditFinset_eq_graphEditFinset {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    simpleGraphEditFinset G H = InducedStars.graphEditFinset G H := by
  classical
  ext e
  simp only [mem_simpleGraphEditFinset,
    InducedStars.mem_graphEditFinset]

@[simp] theorem simpleGraphEditDistance_eq_graphEditDistance {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    simpleGraphEditDistance G H = InducedStars.graphEditDistance G H := by
  rw [simpleGraphEditDistance, InducedStars.graphEditDistance,
    simpleGraphEditFinset_eq_graphEditFinset]

/-- The sharp identity-alignment graphon estimate, now stated using the
generic edit distance.  It is valid also at order zero. -/
theorem cutDist_graphGraphon_le_simpleGraphEdit {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    InducedStars.cutDist (InducedStars.graphGraphon G)
        (InducedStars.graphGraphon H) ≤
      2 * (simpleGraphEditDistance G H : ℝ) / (n : ℝ) ^ 2 := by
  by_cases hn : 0 < n
  · simpa only [simpleGraphEditDistance_eq_graphEditDistance] using
      InducedStars.cutDist_graphGraphon_le_edit hn G H
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hGH : G = H := by
      ext i
      exact Fin.elim0 i
    subst H
    simp

end DenseGraph
