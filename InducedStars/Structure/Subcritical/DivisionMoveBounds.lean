import InducedStars.Structure.Subcritical.DivisionMoves
import InducedStars.Structure.Subcritical.ModelEdgeBounds
import InducedStars.Structure.Subcritical.SingletonComponents

/-!
# Quantitative finite bounds for canonical division moves

These lemmas use actual minimizing divisions and exact integer bookkeeping.
They supply the elementary comparison steps in the sparse-row budget proof.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem degreeInFinset_univ_eq_degree (G : SimpleGraph V) (v : V) :
    degreeInFinset G v Finset.univ = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degreeInFinset
  congr 1
  ext y
  simp [degreeInFinset]

theorem subcriticalGraph_degree_le_defect_add_model
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V) :
    G.degree v ≤ (subcriticalCombinedDefectGraph G D).degree v +
      (subcriticalDivisionModelGraph G D).degree v := by
  have hsub : G.neighborFinset v ⊆
      (subcriticalCombinedDefectGraph G D).neighborFinset v ∪
        (subcriticalDivisionModelGraph G D).neighborFinset v := by
    intro y hy
    have hG : G.Adj v y := by simpa using hy
    by_cases hM : (subcriticalDivisionModelGraph G D).Adj v y
    · exact Finset.mem_union_right _ (by simpa using hM)
    · apply Finset.mem_union_left
      simp only [SimpleGraph.mem_neighborFinset, subcriticalCombinedDefectGraph_adj]
      exact fun h ↦ hM (h ▸ hG)
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem subcriticalMove_target_cost_bound
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (target : D.PartIndex)
    (hvalid : ∀ a, some target ≠ some a → ((D.part a).erase v).Nonempty) :
    subcriticalDefectCost G (D.moveVertex v (some target) hvalid) +
        2 * degreeInFinset G v (D.part target) ≤
      subcriticalDefectCost G D + (D.part target).card +
        (subcriticalDivisionModelGraph G D).degree v := by
  have hcost := subcriticalDefectCost_moveVertex G D v (some target) hvalid
  have hnew := subcriticalMoveVertexToPart_degree_bound G D v target hvalid
  have hcover := subcriticalGraph_degree_le_defect_add_model G D v
  omega

theorem subcriticalDefectCost_le_add_modelEdit
    (G : SimpleGraph V) (D E : SubcriticalDivision k V) :
    subcriticalDefectCost G E ≤ subcriticalDefectCost G D +
      DenseGraph.simpleGraphEditDistance
        (subcriticalDivisionModelGraph G D) (subcriticalDivisionModelGraph G E) := by
  simpa only [simpleGraphEditDistance_subcriticalDivisionModelGraph] using
    DenseGraph.simpleGraphEditDistance_triangle G
      (subcriticalDivisionModelGraph G D) (subcriticalDivisionModelGraph G E)

/-- A swap inside one component costs at most four closed-neighborhood
row budgets. It remains a valid division even when the source is singleton. -/
theorem subcriticalSwap_cost_le
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (j l : Fin (D.core i).order)
    (v w : V) (hv : v ∈ D.parts i j) (hw : w ∈ D.parts i l) (hvw : v ≠ w)
    (B : ℝ) (hparts : ∀ t, ((D.parts i t).card : ℝ) ≤ B) :
    (subcriticalDefectCost G (D.relabel (Equiv.swap v w)) : ℝ) ≤
      subcriticalDefectCost G D + 4 * ((k - 1 : ℕ) : ℝ) * B := by
  let E := D.relabel (Equiv.swap v w)
  let M := subcriticalDivisionModelGraph G D
  let N := subcriticalDivisionModelGraph G E
  have haway : ∀ x y, x ∉ ({v, w} : Finset V) → y ∉ ({v, w} : Finset V) →
      (M.Adj x y ↔ N.Adj x y) := by
    intro x y hx hy
    have hx' : x ≠ v ∧ x ≠ w := by simpa using hx
    have hy' : y ≠ v ∧ y ≠ w := by simpa using hy
    simp [M, N, E, subcriticalDivisionModelGraph_adj,
      Equiv.swap_apply_of_ne_of_ne hx'.1 hx'.2,
      Equiv.swap_apply_of_ne_of_ne hy'.1 hy'.2]
  have hedit := DenseGraph.edit_distance_le_local_degree_sum M N {v, w} haway
  simp only [Finset.sum_insert (by simpa using hvw : v ∉ ({w} : Finset V)),
    Finset.sum_singleton] at hedit
  have hvE : v ∈ E.parts i l := by simpa [E] using hw
  have hwE : w ∈ E.parts i j := by simpa [E] using hv
  have hpartsE : ∀ t, ((E.parts i t).card : ℝ) ≤ B := by
    intro t
    simpa [E, SubcriticalDivision.relabel] using hparts t
  have hMv := subcriticalModel_degree_le_of_part_bound hk G D ⟨i, j⟩ hv Finset.univ B hparts
  have hMw := subcriticalModel_degree_le_of_part_bound hk G D ⟨i, l⟩ hw Finset.univ B hparts
  have hNv := subcriticalModel_degree_le_of_part_bound hk G E ⟨i, l⟩ hvE Finset.univ B hpartsE
  have hNw := subcriticalModel_degree_le_of_part_bound hk G E ⟨i, j⟩ hwE Finset.univ B hpartsE
  simp only [degreeInFinset_univ_eq_degree] at hMv hMw hNv hNw
  have heditR : (DenseGraph.simpleGraphEditDistance M N : ℝ) ≤
      ((M.degree v : ℝ) + M.degree w) + ((N.degree v : ℝ) + N.degree w) := by
    exact_mod_cast hedit
  have hcost := subcriticalDefectCost_le_add_modelEdit G D E
  have hcostR : (subcriticalDefectCost G E : ℝ) ≤
      subcriticalDefectCost G D + DenseGraph.simpleGraphEditDistance M N := by
    exact_mod_cast hcost
  change (subcriticalDefectCost G E : ℝ) ≤ _
  change (M.degree v : ℝ) ≤ _ at hMv
  change (M.degree w : ℝ) ≤ _ at hMw
  change (N.degree v : ℝ) ≤ _ at hNv
  change (N.degree w : ℝ) ≤ _ at hNw
  nlinarith

/-- Minimality forces a sufficiently profitable target row to be matched by
some old model adjacency at the source. The destination is arbitrary. -/
theorem subcriticalMinimal_target_gain_le_model_degree
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (target : D.PartIndex)
    (hvalid : ∀ a, some target ≠ some a → ((D.part a).erase v).Nonempty) :
    2 * degreeInFinset G v (D.part target) ≤ (D.part target).card +
      (subcriticalDivisionModelGraph G D).degree v := by
  have hcost := subcriticalDefectCost_moveVertex G D v (some target) hvalid
  have hmin := hminimal (D.moveVertex v (some target) hvalid)
  have hnew := subcriticalMoveVertexToPart_degree_bound G D v target hvalid
  have hcover := subcriticalGraph_degree_le_defect_add_model G D v
  omega

namespace SubcriticalDivision

def closedPartVertices (D : SubcriticalDivision k V) (a : D.PartIndex) : Finset V :=
  (D.closedPartIndices a).biUnion D.part

theorem mem_closedPartIndices_iff (D : SubcriticalDivision k V)
    (a b : D.PartIndex) : b ∈ D.closedPartIndices a ↔ b = a ∨ D.ActivePart a b := by
  constructor
  · intro hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases hj with hja | haj
    · exact Or.inl (by subst j; rfl)
    · exact Or.inr ⟨a.1, a.2, j, by cases a; rfl, rfl, haj⟩
  · rintro (rfl | hab)
    · exact D.self_mem_closedPartIndices _
    · exact D.mem_closedPartIndices_of_activePart hab

theorem mem_closedPartVertices_iff (D : SubcriticalDivision k V)
    {v y : V} {a : D.PartIndex} (hv : v ∈ D.part a) :
    y ∈ D.closedPartVertices a ↔ D.SamePart v y ∨ D.ActivePair v y := by
  constructor
  · rintro hy
    obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy
    rcases (D.mem_closedPartIndices_iff a b).mp hb with rfl | hab
    · exact Or.inl ⟨_, hv, hyb⟩
    · exact Or.inr ((D.activePair_iff_of_mem_parts hv hyb).mpr hab)
  · rintro (⟨b, hvb, hyb⟩ | hactive)
    · have hab := D.mem_part_unique hv hvb
      subst b
      exact Finset.mem_biUnion.mpr ⟨a, D.self_mem_closedPartIndices a, hyb⟩
    · obtain ⟨b, hyb⟩ := D.mem_support.mp (activePair_imp_support hactive).2
      exact Finset.mem_biUnion.mpr ⟨b, D.mem_closedPartIndices_of_activePart
        ((D.activePair_iff_of_mem_parts hv hyb).mp hactive), hyb⟩

theorem part_subset_closedPartVertices (D : SubcriticalDivision k V) (a : D.PartIndex) :
    D.part a ⊆ D.closedPartVertices a := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨a, D.self_mem_closedPartIndices a, hv⟩

end SubcriticalDivision

theorem degreeInFinset_closedParts_le_sum (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (v : V) (a : D.PartIndex) :
    degreeInFinset G v (D.closedPartVertices a) ≤
      ∑ b ∈ D.closedPartIndices a, degreeInFinset G v (D.part b) := by
  have hsub : (D.closedPartVertices a).filter (G.Adj v) ⊆
      (D.closedPartIndices a).biUnion (fun b ↦ (D.part b).filter (G.Adj v)) := by
    intro y hy
    obtain ⟨hy, hG⟩ := Finset.mem_filter.mp hy
    obtain ⟨b, hb, hyb⟩ := Finset.mem_biUnion.mp hy
    exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_filter.mpr ⟨hyb, hG⟩⟩
  exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

theorem subcriticalDefect_degree_add_closed_degree_ge
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {v : V} {a : D.PartIndex} (hv : v ∈ D.part a) :
    G.degree v + complementDegreeInFinset G v (D.part a) ≤
      (subcriticalCombinedDefectGraph G D).degree v +
        degreeInFinset G v (D.closedPartVertices a) := by
  let N := D.closedPartVertices a
  let C := (D.part a).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y
  have hsub : (G.neighborFinset v \ N) ∪ C ⊆
      (subcriticalCombinedDefectGraph G D).neighborFinset v := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset, subcriticalCombinedDefectGraph_adj_iff]
    rcases Finset.mem_union.mp hy with hout | hC
    · obtain ⟨hG, hn⟩ := Finset.mem_sdiff.mp hout
      have hG : G.Adj v y := by simpa using hG
      have hc : ¬ D.SamePart v y ∧ ¬ D.ActivePair v y := by
        simpa only [N, D.mem_closedPartVertices_iff hv, not_or] using hn
      exact ⟨hG.ne, Or.inr ⟨hc.1, hc.2, hG⟩⟩
    · obtain ⟨hya, hyv, hnG⟩ := Finset.mem_filter.mp hC
      exact ⟨hyv.symm, Or.inl ⟨⟨a, hv, hya⟩, hnG⟩⟩
  have hdis : Disjoint (G.neighborFinset v \ N) C := by
    apply Finset.disjoint_left.mpr
    intro y hy hC
    exact (Finset.mem_sdiff.mp hy).2
      (D.part_subset_closedPartVertices a (Finset.mem_filter.mp hC).1)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset v) N
  have hinter : (G.neighborFinset v ∩ N).card = degreeInFinset G v N := by
    congr 1
    ext y
    simp [degreeInFinset, and_comm]
  rw [hinter, SimpleGraph.card_neighborFinset_eq_degree] at hp
  change G.degree v + C.card ≤ (subcriticalCombinedDefectGraph G D).degree v +
    degreeInFinset G v N
  omega

/-- Sending a removable source vertex to sparse gives the exact local
budget required for the own-component non-low row. -/
theorem subcriticalMinimal_own_part_card_le_closed_degrees
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (a : D.PartIndex) (hv : v ∈ D.part a)
    (hsource : 2 ≤ (D.part a).card) :
    (D.part a).card ≤ degreeInFinset G v (D.part a) +
      (∑ b ∈ D.closedPartIndices a, degreeInFinset G v (D.part b)) + 1 := by
  let E := D.movePartToSparse v a hv hsource
  have hcost := subcriticalDefectCost_moveVertex G D v none
    (fun b _ ↦ D.erase_nonempty_of_source hv hsource b)
  have hmin := hminimal E
  have hvE : v ∈ E.sparse := (D.moveVertex_mem_sparse_self v none _).mpr rfl
  have hnew := subcriticalCombinedDefectGraph_degree_of_sparse G E hvE
  have hlower := subcriticalDefect_degree_add_closed_degree_ge G D hv
  have hsum := degreeInFinset_closedParts_le_sum G D v a
  have hpart := degreeInFinset_add_complementDegreeInFinset G v (D.part a)
  rw [Finset.card_erase_of_mem hv] at hpart
  change subcriticalDefectCost G E + (subcriticalCombinedDefectGraph G D).degree v =
    subcriticalDefectCost G D + (subcriticalCombinedDefectGraph G E).degree v at hcost
  omega

end InducedStars
