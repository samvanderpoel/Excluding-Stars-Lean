import InducedStars.Structure.Subcritical.RowWitnesses
import InducedStars.Structure.Supercritical.CountingSetup
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

/-!
# Finite edge bounds for subcritical regular blow-ups

The edge counts here are unordered. In particular the transfer from a
repaired graph loses one copy, not two copies, of its edit distance.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem inducedEdgeCount_eq_card_inter_sym2 (G : SimpleGraph V) (A : Finset V) :
    inducedEdgeCount G A = (G.edgeFinset ∩ A.sym2).card := by
  rw [← SimpleGraph.filter_edgeFinset_toFinset_subset,
    SimpleGraph.card_filter_edgeFinset_toFinset_subset]
  rfl

/-- Restricting the endpoints does not multiply the unordered edit error. -/
theorem inducedEdgeCount_le_add_simpleGraphEditDistance
    (G H : SimpleGraph V) (A : Finset V) :
    inducedEdgeCount G A ≤ inducedEdgeCount H A +
      DenseGraph.simpleGraphEditDistance G H := by
  rw [inducedEdgeCount_eq_card_inter_sym2, inducedEdgeCount_eq_card_inter_sym2]
  apply (Finset.card_le_card (show G.edgeFinset ∩ A.sym2 ⊆
      (H.edgeFinset ∩ A.sym2) ∪ DenseGraph.simpleGraphEditFinset G H from ?_)).trans
    (Finset.card_union_le _ _)
  intro e he
  by_cases hH : e ∈ H.edgeFinset
  · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hH, (Finset.mem_inter.mp he).2⟩)
  · apply Finset.mem_union_right
    exact DenseGraph.mem_simpleGraphEditFinset.mpr (Or.inl
      ⟨SimpleGraph.mem_edgeFinset.mp (Finset.mem_inter.mp he).1,
        fun h ↦ hH (SimpleGraph.mem_edgeFinset.mpr h)⟩)

theorem sum_degreeInFinset_eq_two_mul_inducedEdgeCount
    (G : SimpleGraph V) (A : Finset V) :
    ∑ x ∈ A, degreeInFinset G x A = 2 * inducedEdgeCount G A := by
  rw [← card_interedges_self_eq_two_mul_inducedEdgeCount]
  simpa only [degreeInFinset, SimpleGraph.interedges, Rel.interedges,
    Finset.card_filter, Finset.sum_product] using
    (show ∑ x ∈ A, (A.filter (G.Adj x)).card =
      ((A ×ˢ A).filter fun p ↦ G.Adj p.1 p.2).card by
      simp only [Finset.card_filter, Finset.sum_product])

theorem inducedEdgeCount_le_mul_of_degreeInFinset_le
    (G : SimpleGraph V) (A : Finset V) (B : ℝ)
    (hdegree : ∀ x ∈ A, (degreeInFinset G x A : ℝ) ≤ B) :
    (inducedEdgeCount G A : ℝ) ≤ B * A.card := by
  have hs : (∑ x ∈ A, (degreeInFinset G x A : ℝ)) ≤ ∑ _x ∈ A, B :=
    Finset.sum_le_sum hdegree
  have he := sum_degreeInFinset_eq_two_mul_inducedEdgeCount G A
  have heR : (∑ x ∈ A, (degreeInFinset G x A : ℝ)) =
      2 * (inducedEdgeCount G A : ℝ) := by exact_mod_cast he
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  nlinarith [show (0 : ℝ) ≤ inducedEdgeCount G A from Nat.cast_nonneg _]

theorem subcriticalModel_degree_le_closedPart_sum
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (a : D.PartIndex) {x : V} (hx : x ∈ D.part a) (A : Finset V) :
    degreeInFinset (subcriticalDivisionModelGraph G D) x A ≤
      ∑ b ∈ D.closedPartIndices a, (D.part b).card := by
  classical
  unfold degreeInFinset
  apply (Finset.card_le_card (show A.filter
      ((subcriticalDivisionModelGraph G D).Adj x) ⊆
      (D.closedPartIndices a).biUnion D.part from ?_)).trans
    (Finset.card_biUnion_le)
  intro y hy
  have hxy := (Finset.mem_filter.mp hy).2
  rcases (subcriticalDivisionModelGraph_adj G D x y).mp hxy with ⟨_, hs | ha⟩
  · obtain ⟨b, hxb, hyb⟩ := hs
    have hab := D.mem_part_unique hx hxb
    subst b
    exact Finset.mem_biUnion.mpr ⟨a, D.self_mem_closedPartIndices a, hyb⟩
  · obtain ⟨b, hyb⟩ := D.mem_support.mp
      (SubcriticalDivision.activePair_imp_support ha.1).2
    exact Finset.mem_biUnion.mpr ⟨b, D.mem_closedPartIndices_of_activePart
      ((D.activePair_iff_of_mem_parts hx hyb).mp ha.1), hyb⟩

theorem subcriticalModel_degree_le_of_part_bound
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (a : D.PartIndex) {x : V} (hx : x ∈ D.part a) (A : Finset V) (B : ℝ)
    (hparts : ∀ j : Fin (D.core a.1).order, ((D.parts a.1 j).card : ℝ) ≤ B) :
    (degreeInFinset (subcriticalDivisionModelGraph G D) x A : ℝ) ≤
      (k - 1 : ℕ) * B := by
  have hdegree := subcriticalModel_degree_le_closedPart_sum G D a hx A
  have hsum : (∑ b ∈ D.closedPartIndices a, ((D.part b).card : ℝ)) ≤
      ∑ _b ∈ D.closedPartIndices a, B := by
    apply Finset.sum_le_sum
    intro b hb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hb
    exact hparts j
  simp only [Finset.sum_const, nsmul_eq_mul, D.card_closedPartIndices hk a] at hsum
  exact (show (degreeInFinset (subcriticalDivisionModelGraph G D) x A : ℝ) ≤
    ∑ b ∈ D.closedPartIndices a, ((D.part b).card : ℝ) by exact_mod_cast hdegree).trans hsum

private theorem sum_closed_products_le_sum_sq
    {I : Type*} [Fintype I] [DecidableEq I]
    (R : I → I → Prop) [DecidableRel R] (hsymm : Symmetric R)
    (d : ℕ) (hcard : ∀ u, (Finset.univ.filter (R u)).card = d)
    (a : I → ℝ) :
    (∑ u, ∑ v ∈ Finset.univ.filter (R u), a u * a v) ≤
      (d : ℝ) * ∑ u, (a u)^2 := by
  have hleft : (∑ u, ∑ _v ∈ Finset.univ.filter (R u), (a u)^2) =
      (d : ℝ) * ∑ u, (a u)^2 := by
    simp only [Finset.sum_const, nsmul_eq_mul, hcard, Finset.mul_sum]
  have hright : (∑ u, ∑ v ∈ Finset.univ.filter (R u), (a v)^2) =
      (d : ℝ) * ∑ u, (a u)^2 := by
    calc
      _ = ∑ u, ∑ v, if R u v then (a v)^2 else 0 := by simp only [Finset.sum_filter]
      _ = ∑ v, ∑ u, if R u v then (a v)^2 else 0 := Finset.sum_comm
      _ = ∑ v, ∑ u, if R v u then (a v)^2 else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        apply Finset.sum_congr rfl
        intro u _
        simp only [show R u v ↔ R v u from ⟨fun h ↦ hsymm h, fun h ↦ hsymm h⟩]
      _ = _ := by simpa only [Finset.sum_filter] using hleft
  have h : (∑ u, ∑ v ∈ Finset.univ.filter (R u), 2 * (a u * a v)) ≤
      ∑ u, ∑ v ∈ Finset.univ.filter (R u), ((a u)^2 + (a v)^2) := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    nlinarith [sq_nonneg (a u - a v)]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at h
  rw [hleft, hright] at h
  simp only [← Finset.mul_sum]
  linarith

/-- A regular blow-up component has the sharp degree-based quadratic bound.
Both the internal clique edges and active core pairs are included; an
active pair is allowed to contain any subset of its possible edges. -/
theorem subcriticalModel_component_edges_le_sum_sq
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) :
    (inducedEdgeCount (subcriticalDivisionModelGraph G D) (D.componentSupport i) : ℝ) ≤
      ((k - 1 : ℕ) : ℝ) / 2 * ∑ u, ((D.parts i u).card : ℝ)^2 := by
  let R : Fin (D.core i).order → Fin (D.core i).order → Prop :=
    fun u v ↦ v = u ∨ (D.core i).graph.Adj u v
  have hsymm : Symmetric R := by
    intro u v h
    exact h.elim (fun hh ↦ Or.inl hh.symm) (fun hh ↦ Or.inr hh.symm)
  have hcard (u : Fin (D.core i).order) :
      (Finset.univ.filter (R u)).card = k - 1 := by
    have hh := D.card_closedPartIndices hk ⟨i, u⟩
    simpa only [SubcriticalDivision.closedPartIndices, Finset.card_map, R] using hh
  have hscalar := sum_closed_products_le_sum_sq R hsymm (k - 1) hcard
    (fun u ↦ ((D.parts i u).card : ℝ))
  have hpartition : (∑ x ∈ D.componentSupport i,
      (degreeInFinset (subcriticalDivisionModelGraph G D) x (D.componentSupport i) : ℝ)) =
      ∑ u, ∑ x ∈ D.parts i u,
        (degreeInFinset (subcriticalDivisionModelGraph G D) x (D.componentSupport i) : ℝ) := by
    rw [SubcriticalDivision.componentSupport, Finset.sum_biUnion]
    intro u _ v _ huv
    exact D.part_disjoint (a := ⟨i, u⟩) (b := ⟨i, v⟩) (by simpa using huv)
  have hbound : (∑ u, ∑ x ∈ D.parts i u,
      (degreeInFinset (subcriticalDivisionModelGraph G D) x (D.componentSupport i) : ℝ)) ≤
      ∑ u, ∑ v ∈ Finset.univ.filter (R u),
        ((D.parts i u).card : ℝ) * ((D.parts i v).card : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    calc
      _ ≤ ∑ _x ∈ D.parts i u,
          ∑ v ∈ Finset.univ.filter (R u), ((D.parts i v).card : ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        have hh := subcriticalModel_degree_le_closedPart_sum G D ⟨i, u⟩ hx
          (D.componentSupport i)
        have hhR : (degreeInFinset (subcriticalDivisionModelGraph G D) x
            (D.componentSupport i) : ℝ) ≤
            ∑ b ∈ D.closedPartIndices ⟨i, u⟩, ((D.part b).card : ℝ) := by exact_mod_cast hh
        have heq : (∑ b ∈ D.closedPartIndices ⟨i, u⟩, ((D.part b).card : ℝ)) =
            ∑ v ∈ Finset.univ.filter (R u), ((D.parts i v).card : ℝ) := by
          rw [SubcriticalDivision.closedPartIndices, Finset.sum_map]
          apply Finset.sum_congr rfl
          intro v _
          rfl
        rwa [heq] at hhR
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hdegree : (∑ x ∈ D.componentSupport i,
      (degreeInFinset (subcriticalDivisionModelGraph G D) x (D.componentSupport i) : ℝ)) =
      2 * (inducedEdgeCount (subcriticalDivisionModelGraph G D) (D.componentSupport i) : ℝ) := by
    exact_mod_cast sum_degreeInFinset_eq_two_mul_inducedEdgeCount
      (subcriticalDivisionModelGraph G D) (D.componentSupport i)
  rw [← hpartition, hdegree] at hbound
  linarith

theorem subcriticalModel_degree_eq_zero_of_sparse
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {x : V} (hx : x ∈ D.sparse) (A : Finset V) :
    degreeInFinset (subcriticalDivisionModelGraph G D) x A = 0 := by
  unfold degreeInFinset
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hxy := (subcriticalDivisionModelGraph_isRegularBlowupFor G D).edge_allowed
    (Finset.mem_filter.mp hy).2
  exact (D.mem_sparse.mp hx) (hxy.elim
    (fun h ↦ (SubcriticalDivision.samePart_imp_support h).1)
    (fun h ↦ (SubcriticalDivision.activePair_imp_support h).1))

/-- The complement of an original-graph neighborhood is `K_k`-free. -/
theorem cliqueFree_compl_induce_of_inducedStarFree
    (G : SimpleGraph V) (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (x : V) (A : Finset V) (hA : ∀ y ∈ A, G.Adj x y) :
    (Gᶜ.induce (A : Set V)).CliqueFree k := by
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  apply hfree
  apply inducedEmbeds_inducedStar_of_fixed_center G x
    (⟨fun i ↦ (f i).val, fun i j hij ↦ f.injective (Subtype.ext hij)⟩ : Fin k ↪ V)
  · intro i
    exact hA _ (f i).property
  · intro i j
    by_cases hij : i = j
    · subst j
      exact G.irrefl
    · have hf := f.map_rel_iff.mpr
        (show (SimpleGraph.completeGraph (Fin k)).Adj i j from hij)
      exact hf.2

/-- Exact finite neighborhood lower bound; no density parameter is involved. -/
theorem inducedEdgeCount_neighborhood_lower
    (hk : 3 ≤ k) (G : SimpleGraph V)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (x : V) (A : Finset V) (hA : ∀ y ∈ A, G.Adj x y) :
    (A.card : ℝ)^2 / (2 * (k - 1 : ℕ)) - (A.card : ℝ) / 2 ≤
      inducedEdgeCount G A := by
  have hcf := cliqueFree_compl_induce_of_inducedStarFree G hfree x A hA
  have hcard : inducedEdgeCount Gᶜ A ≤
      SimpleGraph.turanNumber A.card (k - 1) := by
    have hh := SimpleGraph.CliqueFree.card_edgeFinset_le
      (r := k - 1) (G := Gᶜ.induce (A : Set V))
      (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hcf)
    convert! hh using 1
    · simp only [inducedEdgeCount, SimpleGraph.edgeFinset, Set.toFinset_card,
        Fintype.card_eq_nat_card]
    · simp
  have hT := SimpleGraph.mul_turanNumber_le (n := A.card) (r := k - 1)
  have hbound : 2 * (k - 1) * inducedEdgeCount Gᶜ A ≤
      (k - 1 - 1) * A.card^2 := (Nat.mul_le_mul_left _ hcard).trans hT
  have hboundR : 2 * ((k - 1 : ℕ) : ℝ) * (inducedEdgeCount Gᶜ A : ℝ) ≤
      (((k - 1 : ℕ) : ℝ) - 1) * (A.card : ℝ)^2 := by
    have hr : 1 ≤ k - 1 := by omega
    exact_mod_cast hbound
  have hsum : (inducedEdgeCount G A : ℝ) + (inducedEdgeCount Gᶜ A : ℝ) =
      (A.card : ℝ) * ((A.card : ℝ) - 1) / 2 := by
    rw [← Nat.cast_add, inducedEdgeCount_add_compl]
    simp [Nat.cast_choose_two]
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * ((k - 1 : ℕ) : ℝ))).mpr
  nlinarith

end InducedStars
