import InducedStars.Structure.Supercritical.CountingSetup
import InducedStars.Structure.Supercritical.Closeness
import Mathlib.Tactic

/-!
# Realization of supercritical edge profiles

This module proves that the cross-edge profile extracted from a graph has
the paper's exact integer defect shift, and places the canonical profile of
a close graph in the corresponding bounded window.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance profileRealizationDecidableRel
    {W : Type*} (G : SimpleGraph W) : DecidableRel G.Adj :=
  Classical.decRel _

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem inducedEdgeCount_eq_of_induce_eq
    (G H : SimpleGraph V) (S : Finset V)
    (h : G.induce (S : Set V) = H.induce (S : Set V)) :
    inducedEdgeCount G S = inducedEdgeCount H S := by
  unfold inducedEdgeCount
  apply congrArg Finset.card
  ext e
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  rw [h]

/-! ## Ordered support-cell bookkeeping -/

/-- Split the ordered sum over all main-part cells into its diagonal and
the two orientations of the stable unordered cross profile. -/
private theorem sum_part_cells_eq_diag_add_two_profile_realization
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts j)).card) =
      (∑ i : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts i)).card) +
        2 * profileTotal (crossEdgeProfile G D) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : Std.Symm G.Adj := G.symm
  let I := Fin (k - 1)
  let f : I → I → ℕ := fun i j ↦
    (G.interedges (D.parts i) (D.parts j)).card
  let pairs : Finset (I × I) := Finset.univ ×ˢ Finset.univ
  let ltPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 < p.2
  let gtPairs : Finset (I × I) := pairs.filter fun p ↦ p.2 < p.1
  let diagPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 = p.2
  have hsymm (i j : I) : f i j = f j i := by
    exact Rel.card_interedges_comm (r := G.Adj) _ _
  have hsplit :
      (∑ p ∈ pairs, f p.1 p.2) =
        (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le]
    · simp [heq, lt_irrefl p.2]
    · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le]
  have hdiag :
      (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) =
        ∑ i : I, f i i := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ diagPairs, f p.1 p.2) = _
    apply Finset.sum_bij (fun p _ ↦ p.1)
    · intro p hp
      simp
    · intro p hp q hq hpq
      have hpEq := (Finset.mem_filter.mp hp).2
      have hqEq := (Finset.mem_filter.mp hq).2
      apply Prod.ext hpq
      simpa [hpEq, hqEq] using hpq
    · intro i hi
      refine ⟨(i, i), ?_, rfl⟩
      simp [diagPairs, pairs]
    · intro p hp
      have hpEq := (Finset.mem_filter.mp hp).2
      simpa [hpEq]
  have hlt :
      (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) =
        profileTotal (crossEdgeProfile G D) := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ ltPairs, f p.1 p.2) = _
    unfold profileTotal
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.left hpq)
        (congrArg SupercriticalPartPair.right hpq)
    · intro e he
      refine ⟨(e.left, e.right), ?_, ?_⟩
      · simp [ltPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p hp
      rfl
  have hgt :
      (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) =
        profileTotal (crossEdgeProfile G D) := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ gtPairs, f p.1 p.2) = _
    unfold profileTotal
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.2, p.1, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.right hpq)
        (congrArg SupercriticalPartPair.left hpq)
    · intro e he
      refine ⟨(e.right, e.left), ?_, ?_⟩
      · simp [gtPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p hp
      exact hsymm p.1 p.2
  change (∑ i : I, ∑ j : I, f i j) =
    (∑ i : I, f i i) + 2 * profileTotal (crossEdgeProfile G D)
  calc
    (∑ i : I, ∑ j : I, f i j) =
        ∑ p ∈ pairs, f p.1 p.2 := by
      simpa [pairs] using
        (Fintype.sum_prod_type (fun p : I × I ↦ f p.1 p.2)).symm
    _ = (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) := hsplit
    _ = (∑ i : I, f i i) +
        2 * profileTotal (crossEdgeProfile G D) := by
      rw [hdiag, hlt, hgt]
      omega

/-! ## Internal capacity versus the combined-defect support -/

private theorem inducedEdgeCount_combined_part_add_original
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) :
    inducedEdgeCount G (D.parts i) +
        inducedEdgeCount (combinedSupercriticalDefectGraph G D) (D.parts i) =
      (D.parts i).card.choose 2 := by
  let T := combinedSupercriticalDefectGraph G D
  have hgraph :
      T.induce (D.parts i : Set V) = (Gᶜ).induce (D.parts i : Set V) := by
    ext x y
    simpa [T, SimpleGraph.induce_adj, SimpleGraph.compl_adj] using
      (combinedSupercriticalDefectGraph_adj_of_mem_same_part
        G D i x.2 y.2)
  have hinduced :
      inducedEdgeCount T (D.parts i) = inducedEdgeCount Gᶜ (D.parts i) := by
    exact inducedEdgeCount_eq_of_induce_eq T Gᶜ (D.parts i) hgraph
  rw [hinduced]
  exact inducedEdgeCount_add_compl G (D.parts i)

private theorem two_mul_divisionInternalCliqueCapacity_eq_original_diag_add_support
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    2 * divisionInternalCliqueCapacity D =
      (∑ i, (G.interedges (D.parts i) (D.parts i)).card) +
        2 * inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.support := by
  let T := combinedSupercriticalDefectGraph G D
  have hcell (i : Fin (k - 1)) :
      (G.interedges (D.parts i) (D.parts i)).card +
          (T.interedges (D.parts i) (D.parts i)).card =
        2 * (D.parts i).card.choose 2 := by
    rw [card_interedges_self_eq_two_mul_inducedEdgeCount G (D.parts i),
      card_interedges_self_eq_two_mul_inducedEdgeCount T (D.parts i),
      ← Nat.mul_add, inducedEdgeCount_combined_part_add_original]
  have hTsupport :
      2 * inducedEdgeCount T D.support =
        ∑ i, (T.interedges (D.parts i) (D.parts i)).card := by
    calc
      2 * inducedEdgeCount T D.support =
          (T.interedges D.support D.support).card :=
        (card_interedges_self_eq_two_mul_inducedEdgeCount T D.support).symm
      _ = ∑ i, ∑ j, (T.interedges (D.parts i) (D.parts j)).card :=
        card_interedges_support_support_eq_sum_part_cells T D
      _ = (∑ i, (T.interedges (D.parts i) (D.parts i)).card) +
          2 * profileTotal (crossEdgeProfile T D) :=
        sum_part_cells_eq_diag_add_two_profile_realization T D
      _ = ∑ i, (T.interedges (D.parts i) (D.parts i)).card := by
        simp [T]
  unfold divisionInternalCliqueCapacity
  calc
    2 * ∑ i, (D.parts i).card.choose 2 =
        ∑ i, 2 * (D.parts i).card.choose 2 := by rw [Finset.mul_sum]
    _ = ∑ i, ((G.interedges (D.parts i) (D.parts i)).card +
        (T.interedges (D.parts i) (D.parts i)).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hcell i).symm
    _ = (∑ i, (G.interedges (D.parts i) (D.parts i)).card) +
        ∑ i, (T.interedges (D.parts i) (D.parts i)).card := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i, (G.interedges (D.parts i) (D.parts i)).card) +
        2 * inducedEdgeCount T D.support := by rw [hTsupport]

private theorem card_interedges_combined_support_sparse_eq_original
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    ((combinedSupercriticalDefectGraph G D).interedges
        D.support D.sparse).card =
      (G.interedges D.support D.sparse).card := by
  congr 1
  ext p
  simp only [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, hT⟩
    exact ⟨hx, hy,
      (combinedSupercriticalDefectGraph_adj_support_sparse G D hx hy).mp hT⟩
  · rintro ⟨hx, hy, hG⟩
    exact ⟨hx, hy,
      (combinedSupercriticalDefectGraph_adj_support_sparse G D hx hy).mpr hG⟩

private theorem inducedEdgeCount_combined_sparse_eq_original
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.sparse =
      inducedEdgeCount G D.sparse := by
  apply inducedEdgeCount_eq_of_induce_eq
  ext x y
  simpa [SimpleGraph.induce_adj] using
    (combinedSupercriticalDefectGraph_adj_of_mem_sparse G D x.2 y.2)

/-! ## Exact realization and the canonical close window -/

/-- Exact edge-count identity with the paper's literal integer defect shift. -/
theorem supercriticalDefectShift_edgeCount_identity
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    ((finiteGraphEdges G).card : ℤ) =
      (divisionInternalCliqueCapacity D : ℤ) +
        (profileTotal (crossEdgeProfile G D) : ℤ) +
        supercriticalDefectShift
          (combinedSupercriticalDefectGraph G D) D := by
  let T := combinedSupercriticalDefectGraph G D
  have htotal :=
    two_mul_card_finiteGraphEdges_eq_support_sparse_cells G D
  have hsupport := card_interedges_support_support_eq_sum_part_cells G D
  have hsplit := sum_part_cells_eq_diag_add_two_profile_realization G D
  have hsparse := card_interedges_self_eq_two_mul_inducedEdgeCount G D.sparse
  have hcapacity :=
    two_mul_divisionInternalCliqueCapacity_eq_original_diag_add_support G D
  have hcross := card_interedges_combined_support_sparse_eq_original G D
  have hTsparse := inducedEdgeCount_combined_sparse_eq_original G D
  dsimp [T]
  rw [hsupport, hsplit, hsparse] at htotal
  rw [hcross, hTsparse]
  omega

/-- The actual canonical cross profile supplied by a close-structure result
belongs to the literal profile window with budget `⌊εn²⌋`. -/
theorem canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
    {k n : ℕ} (hk : 3 ≤ k) {gamma alpha delta epsilon : ℝ}
    (hgamma : gamma ∈ Ico (gammaK k) 1)
    (G : SimpleGraph (Fin n)) (hn : k - 1 ≤ n)
    (R : SupercriticalCloseStructureResult
      k hk gamma alpha delta epsilon hgamma G hn)
    (m : ℕ) (hedges : (finiteGraphEdges G).card = m) :
    SupercriticalProfileWindow
      (canonicalSupercriticalDivision G (by simpa using hn)) m
      (supercriticalOffDiagonal k gamma) delta
      ⌊epsilon * (n : ℝ) ^ 2⌋₊
      (crossEdgeProfile G
        (canonicalSupercriticalDivision G (by simpa using hn))) := by
  let D := canonicalSupercriticalDivision G (by simpa using hn)
  apply crossEdgeProfile_mem_window_of_edge_identity
    G D m ⌊epsilon * (n : ℝ) ^ 2⌋₊
      (supercriticalOffDiagonal k gamma) delta hedges
  · exact supercriticalDefectShift_edgeCount_identity G D
  · have hshift := supercriticalDefectShift_natAbs_le_cost G D
    have hcostReal : (supercriticalDefectCost G D : ℝ) ≤
        epsilon * (n : ℝ) ^ 2 := by
      simpa [D, canonicalSupercriticalDefectCost] using R.canonicalDefectCost_le
    have hcostFloor : supercriticalDefectCost G D ≤
        ⌊epsilon * (n : ℝ) ^ 2⌋₊ := by
      by_cases hzero : supercriticalDefectCost G D = 0
      · simp [hzero]
      · exact (Nat.le_floor_iff' hzero).2 hcostReal
    exact hshift.trans hcostFloor
  · intro e
    simpa [D] using
      R.cross_density_close e.left e.right e.left_ne_right

end InducedStars
