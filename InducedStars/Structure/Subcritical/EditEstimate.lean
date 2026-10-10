import InducedStars.Structure.Subcritical.Compatibility
import InducedStars.Regularity.WeightedCut

/-!
# Finite rectangle estimates for the subcritical edit construction

These are finite counting estimates, independent of graphon alignment. The
factor two in `two_mul_card_edges_le_part_rectangles_add_sparse` records
ordered pairs versus unordered edges (the matrix factor-two convention).
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

open DenseGraph FiniteWeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance graphAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- The edge count on a rectangle is bounded by its reference weight plus
one cut discrepancy. No disjointness or zero-diagonal assumption on `R` is
needed. -/
theorem subcritical_card_interedges_le_weight_add_cut
    (G : SimpleGraph V) (R : FiniteWeightedGraph V) (S T : Finset V) :
    ((G.interedges S T).card : ℝ) ≤
      (∑ x ∈ S, ∑ y ∈ T, R.weight x y) +
        finiteLabeledCutDist (ofSimpleGraph G) R * (Fintype.card V : ℝ) ^ 2 := by
  have heq : rectangleDiscrepancy (ofSimpleGraph G) R S T =
      ((G.interedges S T).card : ℝ) - ∑ x ∈ S, ∑ y ∈ T, R.weight x y := by
    simp only [rectangleDiscrepancy, ofSimpleGraph_weight, Finset.sum_sub_distrib]
    rw [Regularity.sum_adjIndicator_eq_card_interedges]
  have h := abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
    (ofSimpleGraph G) R S T
  have h' := le_abs_self (rectangleDiscrepancy (ofSimpleGraph G) R S T)
  rw [heq] at h h'
  linarith

/-- A reference-one rectangle pays for every missing edge. The extra
diagonal contribution has the correct sign and is not discarded. -/
theorem subcritical_card_compl_interedges_le_cut_of_one
    (G : SimpleGraph V) (R : FiniteWeightedGraph V) (S T : Finset V)
    (hR : ∀ x ∈ S, ∀ y ∈ T, R.weight x y = 1) :
    (((Gᶜ).interedges S T).card : ℝ) ≤
      finiteLabeledCutDist (ofSimpleGraph G) R * (Fintype.card V : ℝ) ^ 2 := by
  let A := Rel.interedges (fun x y ↦ ¬ G.Adj x y) S T
  have hsub : (Gᶜ).interedges S T ⊆ A := by
    intro p hp
    rw [SimpleGraph.mem_interedges_iff] at hp
    exact Rel.mem_interedges_iff.mpr ⟨hp.1, hp.2.1, hp.2.2.2⟩
  have hpartition := Rel.card_interedges_add_card_interedges_compl G.Adj S T
  have hpart : ((G.interedges S T).card : ℝ) + A.card =
      (S.card : ℝ) * T.card := by exact_mod_cast hpartition
  have heq : rectangleDiscrepancy (ofSimpleGraph G) R S T =
      ((G.interedges S T).card : ℝ) - (S.card : ℝ) * T.card := by
    unfold rectangleDiscrepancy
    calc
      _ = ∑ x ∈ S, ∑ y ∈ T,
          ((if G.Adj x y then (1 : ℝ) else 0) - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [ofSimpleGraph_weight, hR x hx y hy]
      _ = _ := by simpa using Regularity.sum_centered_adjIndicator_eq G S T 1
  have hcut := abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
    (ofSimpleGraph G) R S T
  have habs := neg_le_abs (rectangleDiscrepancy (ofSimpleGraph G) R S T)
  rw [heq] at hcut habs
  have hcard : (((Gᶜ).interedges S T).card : ℝ) ≤ A.card := by
    exact_mod_cast Finset.card_le_card hsub
  linarith

/-- Cover every oriented edge by a pair of main parts or a sparse-incident
rectangle. Overlaps only improve this upper bound. -/
theorem two_mul_card_edges_le_part_rectangles_add_sparse
    {k : ℕ} (D : SubcriticalDivision k V) (Q G : SimpleGraph V)
    (hsparse : ∀ x ∈ D.sparse, ∀ y, Q.Adj x y → G.Adj x y) :
    2 * Q.edgeFinset.card ≤
      (∑ a : D.PartIndex, ∑ b : D.PartIndex,
        (Q.interedges (D.part a) (D.part b)).card) +
          2 * (G.interedges D.sparse Finset.univ).card := by
  let C := (Finset.univ : Finset (D.PartIndex × D.PartIndex)).biUnion
    fun ab ↦ Q.interedges (D.part ab.1) (D.part ab.2)
  have hsub : Q.interedges Finset.univ Finset.univ ⊆
      C ∪ (G.interedges D.sparse Finset.univ ∪ G.interedges Finset.univ D.sparse) := by
    intro p hp
    have hq := (Rel.mem_interedges_iff.mp hp).2.2
    by_cases hx : p.1 ∈ D.sparse
    · exact Finset.mem_union_right _ (Finset.mem_union_left _
        (Rel.mem_interedges_iff.mpr ⟨hx, Finset.mem_univ _, hsparse _ hx _ hq⟩))
    by_cases hy : p.2 ∈ D.sparse
    · exact Finset.mem_union_right _ (Finset.mem_union_right _
        (Rel.mem_interedges_iff.mpr
          ⟨Finset.mem_univ _, hy, (hsparse _ hy _ hq.symm).symm⟩))
    have hx' : p.1 ∈ D.support := by simpa using hx
    have hy' : p.2 ∈ D.support := by simpa using hy
    obtain ⟨a, ha⟩ := D.mem_support.mp hx'
    obtain ⟨b, hb⟩ := D.mem_support.mp hy'
    exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨(a, b), Finset.mem_univ _, Rel.mem_interedges_iff.mpr ⟨ha, hb, hq⟩⟩)
  have hC : C.card ≤ ∑ a : D.PartIndex, ∑ b : D.PartIndex,
      (Q.interedges (D.part a) (D.part b)).card := by
    simpa [C, Fintype.sum_prod_type] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset (D.PartIndex × D.PartIndex)))
        (t := fun ab ↦ Q.interedges (D.part ab.1) (D.part ab.2)))
  have hall : (Q.interedges Finset.univ Finset.univ).card = 2 * Q.edgeFinset.card := by
    simpa [SimpleGraph.interedges, Rel.interedges] using Q.two_mul_card_edgeFinset.symm
  have hcomm : (G.interedges Finset.univ D.sparse).card =
      (G.interedges D.sparse Finset.univ).card := by
    letI : Std.Symm G.Adj := G.symm
    exact Rel.card_interedges_comm (r := G.Adj) _ _
  have hcard := Finset.card_le_card hsub
  have hu := Finset.card_union_le C
    (G.interedges D.sparse Finset.univ ∪ G.interedges Finset.univ D.sparse)
  have hu' := Finset.card_union_le (G.interedges D.sparse Finset.univ)
    (G.interedges Finset.univ D.sparse)
  omega

/-- Assembly of the finite rectangle bounds. Only the number of retained
parts, not their sizes or the number of omitted components, enters the cut
error coefficient. -/
theorem subcritical_two_mul_card_edges_le_cut_and_residual
    {k : ℕ} (D : SubcriticalDivision k V) (Q G : SimpleGraph V)
    (R : FiniteWeightedGraph V) {beta : ℝ}
    (hcut : finiteLabeledCutDist (ofSimpleGraph G) R ≤ beta)
    (hcell : ∀ a b : D.PartIndex,
      ((Q.interedges (D.part a) (D.part b)).card : ℝ) ≤
        beta * (Fintype.card V : ℝ) ^ 2)
    (hsparse : ∀ x ∈ D.sparse, ∀ y, Q.Adj x y → G.Adj x y) :
    2 * (Q.edgeFinset.card : ℝ) ≤
      ((Fintype.card D.PartIndex : ℝ) ^ 2 + 2) * beta *
        (Fintype.card V : ℝ) ^ 2 +
          2 * (∑ x ∈ D.sparse, ∑ y : V, R.weight x y) := by
  have hcover : 2 * (Q.edgeFinset.card : ℝ) ≤
      (∑ a : D.PartIndex, ∑ b : D.PartIndex,
        ((Q.interedges (D.part a) (D.part b)).card : ℝ)) +
          2 * ((G.interedges D.sparse Finset.univ).card : ℝ) := by
    exact_mod_cast two_mul_card_edges_le_part_rectangles_add_sparse D Q G hsparse
  have hcells : (∑ a : D.PartIndex, ∑ b : D.PartIndex,
      ((Q.interedges (D.part a) (D.part b)).card : ℝ)) ≤
        (Fintype.card D.PartIndex : ℝ) ^ 2 * beta * (Fintype.card V : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _a : D.PartIndex, ∑ _b : D.PartIndex,
          beta * (Fintype.card V : ℝ) ^ 2 :=
        Finset.sum_le_sum fun a _ ↦ Finset.sum_le_sum fun b _ ↦ hcell a b
      _ = _ := by simp; ring
  have hs := subcritical_card_interedges_le_weight_add_cut G R D.sparse Finset.univ
  have hc := mul_le_mul_of_nonneg_right hcut (sq_nonneg (Fintype.card V : ℝ))
  nlinarith

/-- The repair-defect estimate against any full reference that agrees with
the retained division model on its support. Reference mass in the sparse
remainder is kept as an explicit term, not assumed small. -/
theorem subcritical_two_mul_defect_edges_le_cut_and_residual
    {k : ℕ} (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (Q G : SimpleGraph V) (R : FiniteWeightedGraph V) {beta : ℝ}
    (hcut : finiteLabeledCutDist (ofSimpleGraph G) R ≤ beta)
    (hQ : ∀ x y, Q.Adj x y ↔ x ≠ y ∧
      ((D.SamePart x y ∧ ¬ G.Adj x y) ∨
        (¬ D.SamePart x y ∧ ¬ D.ActivePair x y ∧ G.Adj x y)))
    (hR : ∀ x ∈ D.support, ∀ y ∈ D.support,
      R.weight x y = (subcriticalDivisionWeightedGraph hk D).weight x y) :
    2 * (Q.edgeFinset.card : ℝ) ≤
      ((Fintype.card D.PartIndex : ℝ) ^ 2 + 2) * beta *
        (Fintype.card V : ℝ) ^ 2 +
          2 * (∑ x ∈ D.sparse, ∑ y : V, R.weight x y) := by
  apply subcritical_two_mul_card_edges_le_cut_and_residual D Q G R hcut
  · intro a b
    have hRb : ∀ x ∈ D.part a, ∀ y ∈ D.part b,
        R.weight x y = if a = b then 1 else if D.ActivePart a b then pK k else 0 := by
      intro x hx y hy
      rw [hR x (D.part_subset_support a hx) y (D.part_subset_support b hy),
        subcriticalDivisionWeightedGraph_weight_of_mem_parts hk D hx hy]
    by_cases hab : a = b
    · subst b
      have hsub : Q.interedges (D.part a) (D.part a) ⊆
          (Gᶜ).interedges (D.part a) (D.part a) := by
        intro p hp
        obtain ⟨hx, hy, hq⟩ := Rel.mem_interedges_iff.mp hp
        have hs : D.SamePart p.1 p.2 := ⟨a, hx, hy⟩
        have he := (hQ _ _).mp hq
        exact Rel.mem_interedges_iff.mpr
          ⟨hx, hy, he.1, by rcases he.2 with h | h; exact h.2; exact (h.1 hs).elim⟩
      have hle := subcritical_card_compl_interedges_le_cut_of_one G R
        (D.part a) (D.part a) (fun x hx y hy ↦ by simpa using hRb x hx y hy)
      have hcard : ((Q.interedges (D.part a) (D.part a)).card : ℝ) ≤
          ((Gᶜ).interedges (D.part a) (D.part a)).card := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hle.trans (mul_le_mul_of_nonneg_right hcut (sq_nonneg _)))
    · by_cases ha : D.ActivePart a b
      · have hempty : Q.interedges (D.part a) (D.part b) = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro p hp
          obtain ⟨hx, hy, hq⟩ := Rel.mem_interedges_iff.mp hp
          have hn : ¬ D.SamePart p.1 p.2 :=
            fun h ↦ hab ((D.samePart_iff_of_mem_parts hx hy).mp h)
          have ha' : D.ActivePair p.1 p.2 := (D.activePair_iff_of_mem_parts hx hy).mpr ha
          rcases ((hQ _ _).mp hq).2 with h | h
          · exact hn h.1
          · exact h.2.1 ha'
        rw [hempty, Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg ((finiteLabeledCutDist_nonneg _ _).trans hcut) (sq_nonneg _)
      · have hsub : Q.interedges (D.part a) (D.part b) ⊆
            G.interedges (D.part a) (D.part b) := by
          intro p hp
          obtain ⟨hx, hy, hq⟩ := Rel.mem_interedges_iff.mp hp
          have hn : ¬ D.SamePart p.1 p.2 :=
            fun h ↦ hab ((D.samePart_iff_of_mem_parts hx hy).mp h)
          refine Rel.mem_interedges_iff.mpr ⟨hx, hy, ?_⟩
          rcases ((hQ _ _).mp hq).2 with h | h
          · exact (hn h.1).elim
          · exact h.2.2
        have hzero : (∑ x ∈ D.part a, ∑ y ∈ D.part b, R.weight x y) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          apply Finset.sum_eq_zero
          intro y hy
          simpa [hab, ha] using hRb x hx y hy
        have hle := subcritical_card_interedges_le_weight_add_cut G R (D.part a) (D.part b)
        rw [hzero, zero_add] at hle
        have hcard : ((Q.interedges (D.part a) (D.part b)).card : ℝ) ≤
            (G.interedges (D.part a) (D.part b)).card := by
          exact_mod_cast Finset.card_le_card hsub
        exact hcard.trans (hle.trans (mul_le_mul_of_nonneg_right hcut (sq_nonneg _)))
  · intro x hx y hq
    rcases ((hQ _ _).mp hq).2 with h | h
    · exact ((D.mem_sparse.mp hx) (SubcriticalDivision.samePart_imp_support h.1).1).elim
    · exact h.2.2

end InducedStars
