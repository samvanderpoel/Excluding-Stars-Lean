import DenseGraph.FiniteModels.BalancedAssignments

/-!
# Partitions obtained from a proper coloring of a spanning subgraph

The color fibers retain empty classes.  Internal edges of the ambient graph
are among the edges omitted by its properly colored spanning subgraph.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

variable {n r : ℕ} {G H : SimpleGraph (Fin n)}

/-- The indexed color classes of a proper coloring, including empty classes. -/
def coloringParts (C : H.Coloring (Fin r)) (i : Fin r) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ C v = i

@[simp] theorem mem_coloringParts (C : H.Coloring (Fin r)) (i : Fin r) (v : Fin n) :
    v ∈ coloringParts C i ↔ C v = i := by
  simp [coloringParts]

theorem coloringParts_pairwiseDisjoint (C : H.Coloring (Fin r)) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin r)) (coloringParts C) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact hij ((mem_coloringParts C i v).mp hvi |>.symm.trans
    ((mem_coloringParts C j v).mp hvj))

@[simp] theorem coloringParts_biUnion (C : H.Coloring (Fin r)) :
    (Finset.univ : Finset (Fin r)).biUnion (coloringParts C) = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  exact ⟨C v, by simp⟩

@[simp] theorem sum_card_coloringParts (C : H.Coloring (Fin r)) :
    ∑ i : Fin r, (coloringParts C i).card = n := by
  rw [← Finset.card_biUnion]
  · simp
  · simpa using coloringParts_pairwiseDisjoint C

private theorem internalEdges_coloringParts_pairwiseDisjoint
    [DecidableRel G.Adj] (C : H.Coloring (Fin r)) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin r))
      (fun i ↦ G.edgeFinset ∩ (coloringParts C i).sym2) := by
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro e hei hej
  induction e using Sym2.inductionOn with
  | hf a b =>
      have hai := (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hei).2).1
      have haj := (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hej).2).1
      exact Finset.disjoint_left.mp
        (coloringParts_pairwiseDisjoint C (Set.mem_univ i) (Set.mem_univ j) hij) hai haj

/-- Internal ambient edges lie among the edges deleted from the properly
colored spanning subgraph. -/
theorem sum_internal_edges_coloringParts_le
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (C : H.Coloring (Fin r)) (hHG : H ≤ G) (t : ℕ)
    (hcard : G.edgeFinset.card - t ≤ H.edgeFinset.card) :
    (∑ i : Fin r, ((G.edgeFinset ∩ (coloringParts C i).sym2).card : ℝ)) ≤
      (t : ℝ) := by
  have hsum :
      (∑ i : Fin r, (G.edgeFinset ∩ (coloringParts C i).sym2).card) ≤ t := by
    rw [← Finset.card_biUnion
      (by simpa using internalEdges_coloringParts_pairwiseDisjoint (G := G) C)]
    have hsub :
        (Finset.univ : Finset (Fin r)).biUnion
          (fun i ↦ G.edgeFinset ∩ (coloringParts C i).sym2) ⊆
            G.edgeFinset \ H.edgeFinset := by
      intro e he
      obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp he
      refine Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp hei).1, ?_⟩
      induction e using Sym2.inductionOn with
      | hf a b =>
          intro heH
          have hab : H.Adj a b := by simpa using heH
          obtain ⟨hai, hbi⟩ := Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp hei).2
          exact C.valid hab (((mem_coloringParts C i a).mp hai).trans
            ((mem_coloringParts C i b).mp hbi).symm)
    have hcount := Finset.card_le_card hsub
    have hHsub : H.edgeFinset ⊆ G.edgeFinset :=
      SimpleGraph.edgeFinset_mono hHG
    rw [Finset.card_sdiff_of_subset hHsub] at hcount
    omega
  exact_mod_cast hsum

/-- A properly colored graph has at most the complete multipartite capacity
of its actual color-class sizes. -/
theorem card_edgeFinset_le_multipartiteCrossCapacity_coloringParts
    [DecidableRel H.Adj] (C : H.Coloring (Fin r)) :
    H.edgeFinset.card ≤ multipartiteCrossCapacity
      (fun i ↦ (coloringParts C i).card) := by
  let P : SimpleGraph (Fin n) := (⊤ : SimpleGraph (Fin r)).comap C
  have hHP : H ≤ P := fun _ _ hab ↦ C.valid hab
  let e : Fin n ≃ (Σ i : Fin r, Fin (coloringParts C i).card) :=
    (Equiv.sigmaFiberEquiv (fun v : Fin n ↦ C v)).symm.trans
      (Equiv.sigmaCongrRight fun i ↦
        Fintype.equivFinOfCardEq (by simp [coloringParts, Fintype.card_subtype]))
  let f : P ≃g SimpleGraph.completeMultipartiteGraph
      (fun i : Fin r ↦ Fin (coloringParts C i).card) :=
    { e with
      map_rel_iff' := by
        intro a b
        simp [e, P, SimpleGraph.completeMultipartiteGraph,
          SimpleGraph.comap_adj, SimpleGraph.top_adj,
          Equiv.sigmaFiberEquiv, Equiv.sigmaCongrRight] }
  calc
    H.edgeFinset.card ≤ P.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hHP)
    _ = multipartiteCrossCapacity (fun i ↦ (coloringParts C i).card) :=
      f.card_edgeFinset_eq

end DenseGraph
