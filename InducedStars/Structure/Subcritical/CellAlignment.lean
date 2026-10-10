import InducedStars.Structure.Subcritical.Defect
import InducedStars.Structure.Subcritical.EditEstimate

/-!
# Signed rectangles and subcritical cell alignment

The original graph, its repaired simple graph, and the weighted reference
remain distinct. Every cut contradiction below uses a consistently signed
rectangle. The first overlap step uses the same bounded-degree observation
as the paper: a row meets at most `k-1` canonical parts.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

open DenseGraph FiniteWeightedGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

local instance alignmentAdjDecidable (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- A one-sided pointwise discrepancy gives a signed rectangle lower bound;
an absolute pointwise discrepancy would not suffice. -/
theorem subcritical_signed_rectangle_le_cut
    (A B : FiniteWeightedGraph V) (S T : Finset V) (g : ℝ)
    (hgap : ∀ x ∈ S, ∀ y ∈ T, g ≤ A.weight x y - B.weight x y) :
    g * S.card * T.card ≤
      finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 := by
  have hs : (∑ x ∈ S, ∑ y ∈ T, g) ≤ rectangleDiscrepancy A B S T := by
    apply Finset.sum_le_sum
    intro x hx
    exact Finset.sum_le_sum fun y hy ↦ hgap x hx y hy
  have he : (∑ x ∈ S, ∑ y ∈ T, g) = g * S.card * T.card := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [he] at hs
  exact hs.trans ((le_abs_self _).trans
    (abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq A B S T))

/-- If one side reaches the overlap threshold, a consistently discrepant
other side is smaller than that threshold. -/
theorem subcritical_card_lt_of_signed_rectangle
    (A B : FiniteWeightedGraph V) (S T : Finset V) {g m : ℝ}
    (hg : 0 < g) (hm : 0 < m) (hS : m ≤ S.card)
    (hcut : finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 < g * m ^ 2)
    (hgap : ∀ x ∈ S, ∀ y ∈ T, g ≤ A.weight x y - B.weight x y) :
    (T.card : ℝ) < m := by
  by_contra ht
  have ht' : m ≤ (T.card : ℝ) := le_of_not_gt ht
  have hh := mul_le_mul hS ht' hm.le (Nat.cast_nonneg S.card)
  have hh' := mul_le_mul_of_nonneg_left hh hg.le
  have hc := subcritical_signed_rectangle_le_cut A B S T g hgap
  nlinarith

/-- A row of a regular blow-up meets at most `k-1` parts. This weighted
cardinality estimate is the elementary bounded-degree step in the paper's
reference-cell argument; it does not count the pieces instead of vertices. -/
theorem subcritical_regularBlowup_row_sum_le
    {k : ℕ} (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (H : SimpleGraph V) (hH : IsSubcriticalRegularBlowupFor D H)
    (C : Finset V) {m : ℝ} (hm : 0 ≤ m)
    (hparts : ∀ a : D.PartIndex, ((C ∩ D.part a).card : ℝ) ≤ m)
    (x : V) :
    (∑ y ∈ C, (ofSimpleGraph H).weight x y) ≤ (k - 1 : ℕ) * m := by
  have hsum : (∑ y ∈ C, (ofSimpleGraph H).weight x y) =
      ((C.filter (H.Adj x)).card : ℝ) := by
    simp [ofSimpleGraph]
  rw [hsum]
  by_cases hx : x ∈ D.support
  · obtain ⟨a, ha⟩ := SubcriticalDivision.mem_support.mp hx
    let U := (D.closedPartIndices a).biUnion fun b ↦ C ∩ D.part b
    have hsub : C.filter (H.Adj x) ⊆ U := by
      intro y hy
      obtain ⟨hyC, hxy⟩ := Finset.mem_filter.mp hy
      rcases hH.edge_allowed hxy with hs | he
      · obtain ⟨b, hxb, hyb⟩ := hs
        have hab : b = a := D.mem_part_unique hxb ha
        subst b
        exact Finset.mem_biUnion.mpr
          ⟨a, D.self_mem_closedPartIndices a, Finset.mem_inter.mpr ⟨hyC, hyb⟩⟩
      · obtain ⟨i, u, v, huv, hxu, hyv⟩ := he
        have hau : (⟨i, u⟩ : D.PartIndex) = a := D.mem_part_unique hxu ha
        have he' : D.ActivePart a ⟨i, v⟩ := by
          rw [← hau]
          exact ⟨i, u, v, rfl, rfl, huv⟩
        exact Finset.mem_biUnion.mpr
          ⟨⟨i, v⟩, D.mem_closedPartIndices_of_activePart he',
            Finset.mem_inter.mpr ⟨hyC, hyv⟩⟩
    calc
      ((C.filter (H.Adj x)).card : ℝ) ≤ U.card := by
        exact_mod_cast Finset.card_le_card hsub
      _ ≤ ∑ b ∈ D.closedPartIndices a, ((C ∩ D.part b).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ D.closedPartIndices a, m :=
        Finset.sum_le_sum fun b _ ↦ hparts b
      _ = _ := by simp [D.card_closedPartIndices hk a, nsmul_eq_mul]
  · have hempty : C.filter (H.Adj x) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      rcases hH.edge_allowed (Finset.mem_filter.mp hy).2 with hs | he
      · exact hx (SubcriticalDivision.samePart_imp_support hs).1
      · exact hx (SubcriticalDivision.activePair_imp_support he).1
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Every sufficiently large reference-one cell overlaps a canonical part
in at least `m` vertices. Sparse vertices are handled by their zero rows. -/
theorem subcritical_exists_part_large_cell_overlap
    {k : ℕ} (hk : 3 ≤ k) (D : SubcriticalDivision k V)
    (H : SimpleGraph V) (hH : IsSubcriticalRegularBlowupFor D H)
    (R : FiniteWeightedGraph V) (C : Finset V) {m : ℝ}
    (hm : 0 < m) (hC : 2 * (k - 1 : ℕ) * m ≤ C.card)
    (hR : ∀ x ∈ C, ∀ y ∈ C, R.weight x y = 1)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < m ^ 2) :
    ∃ a : D.PartIndex, m ≤ ((C ∩ D.part a).card : ℝ) := by
  by_contra h
  have hparts : ∀ a : D.PartIndex, ((C ∩ D.part a).card : ℝ) ≤ m := by
    intro a
    exact (lt_of_not_ge (fun ha ↦ h ⟨a, ha⟩)).le
  have hrows : (∑ x ∈ C, ∑ y ∈ C, (ofSimpleGraph H).weight x y) ≤
      (C.card : ℝ) * ((k - 1 : ℕ) * m) := by
    calc
      _ ≤ ∑ _x ∈ C, (k - 1 : ℕ) * m :=
        Finset.sum_le_sum fun x _ ↦
          subcritical_regularBlowup_row_sum_le hk D H hH C hm.le hparts x
      _ = _ := by simp [nsmul_eq_mul]
  have hdisc : rectangleDiscrepancy (ofSimpleGraph H) R C C =
      (∑ x ∈ C, ∑ y ∈ C, (ofSimpleGraph H).weight x y) - (C.card : ℝ) ^ 2 := by
    unfold rectangleDiscrepancy
    simp only [Finset.sum_sub_distrib]
    congr 1
    calc
      _ = ∑ x ∈ C, ∑ y ∈ C, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_congr rfl fun y hy ↦ hR x hx y hy
      _ = _ := by simp [sq]
  have hbound := abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
    (ofSimpleGraph H) R C C
  have hlower := neg_le_abs (rectangleDiscrepancy (ofSimpleGraph H) R C C)
  rw [hdisc] at hbound hlower
  have hr : (1 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k - 1)
  have hCm : 2 * m ≤ (C.card : ℝ) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg C.card)
  nlinarith [sq_nonneg ((C.card : ℝ) - 2 * m)]

/-- Once a canonical part has a large overlap with a reference cell, its
spill outside that cell is small. The two tested sets are disjoint, so no
simple-graph diagonal is silently treated as an edge. -/
theorem subcritical_part_spill_lt_of_cell_overlap
    {k : ℕ} (D : SubcriticalDivision k V)
    (H : SimpleGraph V) (hH : IsSubcriticalRegularBlowupFor D H)
    (R : FiniteWeightedGraph V) (C : Finset V) (a : D.PartIndex)
    {g m : ℝ} (hg : 0 < g) (hm : 0 < m)
    (hoverlap : m ≤ ((C ∩ D.part a).card : ℝ))
    (hR : ∀ x ∈ C, ∀ y ∉ C, R.weight x y ≤ 1 - g)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2) :
    ((D.part a \ C).card : ℝ) < m := by
  apply subcritical_card_lt_of_signed_rectangle (ofSimpleGraph H) R
    (C ∩ D.part a) (D.part a \ C) hg hm hoverlap hcut
  intro x hx y hy
  obtain ⟨hxC, hxP⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyP, hyC⟩ := Finset.mem_sdiff.mp hy
  have hxy : x ≠ y := by rintro rfl; exact hyC hxC
  have he := hH.part_complete a hxP hyP hxy
  rw [ofSimpleGraph_weight, if_pos he]
  linarith [hR x hxC y hyC]

/-- A reference row cannot have almost unit mass on a set spread over
several cells. The alternative in `hcover` includes the unused zero region
of the sampled candidate, rather than declaring that region negligible. -/
theorem subcritical_reference_row_le_of_spread
    {ι : Type*} (R : FiniteWeightedGraph V) (cells : ι → Finset V)
    (S : Finset V) {g m : ℝ} (hg : 0 ≤ g) (hg1 : g ≤ 1)
    (hm : 0 ≤ m) (hmS : m ≤ S.card)
    (hcover : ∀ x, (∃ i, x ∈ cells i) ∨ ∀ y, R.weight x y = 0)
    (hout : ∀ i, ∀ x ∈ cells i, ∀ y ∉ cells i, R.weight x y ≤ 1 - g)
    (hspread : ∀ i, m ≤ ((S \ cells i).card : ℝ)) (x : V) :
    (∑ y ∈ S, R.weight x y) ≤ (S.card : ℝ) - g * m := by
  rcases hcover x with ⟨i, hi⟩ | hz
  · have hsplit := Finset.sum_inter_add_sum_sdiff S (cells i) (fun y ↦ R.weight x y)
    have hinside : (∑ y ∈ S ∩ cells i, R.weight x y) ≤ (S ∩ cells i).card := by
      calc
        _ ≤ ∑ _y ∈ S ∩ cells i, (1 : ℝ) :=
          Finset.sum_le_sum fun y _ ↦ R.le_one x y
        _ = _ := by simp
    have houtside : (∑ y ∈ S \ cells i, R.weight x y) ≤
        ((S \ cells i).card : ℝ) * (1 - g) := by
      calc
        _ ≤ ∑ _y ∈ S \ cells i, (1 - g) :=
          Finset.sum_le_sum fun y hy ↦ hout i x hi y (Finset.mem_sdiff.mp hy).2
        _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((S ∩ cells i).card : ℝ) + (S \ cells i).card = S.card := by
      exact_mod_cast Finset.card_inter_add_card_sdiff S (cells i)
    have hgspread := mul_le_mul_of_nonneg_left (hspread i) hg
    linarith
  · simp only [hz, Finset.sum_const_zero]
    nlinarith

/-- A sufficiently large clique of the repaired graph concentrates in one
realized reference cell. The proof sums signed row discrepancies, and
retains the exact one-vertex diagonal error of a simple graph. The family
of cells need not be finite: at each vertex only its own cell is used. -/
theorem subcritical_large_clique_concentrates_in_cell
    {ι : Type*} (H : SimpleGraph V) (R : FiniteWeightedGraph V)
    (cells : ι → Finset V) (S : Finset V) {g m : ℝ}
    (hg : 0 < g) (hg1 : g ≤ 1) (hm : 0 < m)
    (hS : 2 * m ≤ S.card) (hdiag : 2 ≤ g * m)
    (hcomplete : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → H.Adj x y)
    (hcover : ∀ x, (∃ i, x ∈ cells i) ∨ ∀ y, R.weight x y = 0)
    (hout : ∀ i, ∀ x ∈ cells i, ∀ y ∉ cells i, R.weight x y ≤ 1 - g)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H) R *
      (Fintype.card V : ℝ) ^ 2 < g * m ^ 2) :
    ∃ i, ((S \ cells i).card : ℝ) < m := by
  by_contra h
  have hspread : ∀ i, m ≤ ((S \ cells i).card : ℝ) := by
    intro i
    exact le_of_not_gt fun hi ↦ h ⟨i, hi⟩
  have hmS : m ≤ (S.card : ℝ) := by linarith
  have hRsum : (∑ x ∈ S, ∑ y ∈ S, R.weight x y) ≤
      (S.card : ℝ) * ((S.card : ℝ) - g * m) := by
    calc
      _ ≤ ∑ _x ∈ S, ((S.card : ℝ) - g * m) :=
        Finset.sum_le_sum fun x _ ↦ subcritical_reference_row_le_of_spread
          R cells S hg.le hg1 hm.le hmS hcover hout hspread x
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hHsum : (∑ x ∈ S, ∑ y ∈ S, (ofSimpleGraph H).weight x y) =
      (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hrow : ∀ x ∈ S,
        (∑ y ∈ S, (ofSimpleGraph H).weight x y) = (S.card : ℝ) - 1 := by
      intro x hx
      have he (y : V) (hy : y ∈ S) :
          (ofSimpleGraph H).weight x y = if x = y then 0 else 1 := by
        by_cases hxy : x = y
        · subst y
          simp
        · simp [ofSimpleGraph_weight, hxy, hcomplete x hx y hy hxy]
      calc
        _ = ∑ y ∈ S, if x = y then (0 : ℝ) else 1 :=
          Finset.sum_congr rfl he
        _ = _ := by
          have hf : S.filter (fun y ↦ ¬ x = y) = S.erase x := by
            ext y
            simp [eq_comm, and_comm]
          simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add,
            Finset.sum_const, nsmul_eq_mul, mul_one, hf]
          rw [Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.one_le_card.mpr ⟨x, hx⟩)]
          norm_num
    calc
      _ = ∑ _x ∈ S, ((S.card : ℝ) - 1) := Finset.sum_congr rfl hrow
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hdisc : rectangleDiscrepancy (ofSimpleGraph H) R S S =
      (S.card : ℝ) * ((S.card : ℝ) - 1) -
        ∑ x ∈ S, ∑ y ∈ S, R.weight x y := by
    simp only [rectangleDiscrepancy, Finset.sum_sub_distrib, hHsum]
  have hbound := abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
    (ofSimpleGraph H) R S S
  have hlower := le_abs_self (rectangleDiscrepancy (ofSimpleGraph H) R S S)
  rw [hdisc] at hbound hlower
  have hfactor : 0 ≤ g * m - 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_right hS hfactor
  have hprod2 := mul_le_mul_of_nonneg_right hdiag hm.le
  nlinarith

end InducedStars
