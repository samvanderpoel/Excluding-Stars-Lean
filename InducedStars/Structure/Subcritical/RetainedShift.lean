import InducedStars.Structure.Subcritical.RetainedEdges
import InducedStars.Structure.Subcritical.ModelEdgeBounds

/-!
# Exact signed retained-edge bookkeeping

Paper: the retained edge-count levels in the subcritical counting argument.
The shift is an integer, and the positive and negative errors below are
cardinalities of actual unordered edge sets. Edges wholly inside the
nonretained side are kept separate from retained-incident defects.
-/

noncomputable section

open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem retained_mem_iff_of_samePart
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) {x y : V}
    (hs : D.SamePart x y) :
    x ∈ D.retainedVertices eta R₀ ↔ y ∈ D.retainedVertices eta R₀ := by
  obtain ⟨a, hx, hy⟩ := hs
  exact (D.mem_retainedVertices_iff_of_mem_componentSupport
    (D.mem_componentSupport.mpr ⟨a.2, hx⟩)).trans
      (D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a.2, hy⟩)).symm

private theorem retained_mem_iff_of_activePair
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) {x y : V}
    (ha : D.ActivePair x y) :
    x ∈ D.retainedVertices eta R₀ ↔ y ∈ D.retainedVertices eta R₀ := by
  obtain ⟨i, u, v, _, hx, hy⟩ := ha
  exact (D.mem_retainedVertices_iff_of_mem_componentSupport
    (D.mem_componentSupport.mpr ⟨u, hx⟩)).trans
      (D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨v, hy⟩)).symm

theorem mk_mem_retainedCliquePotentialEdges_iff
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    s(x, y) ∈ retainedCliquePotentialEdges D eta R₀ ↔
      x ≠ y ∧ D.SamePart x y ∧ x ∈ D.retainedVertices eta R₀ := by
  constructor
  · intro h
    obtain ⟨a, ha, hxy⟩ := (mem_retainedCliquePotentialEdges D eta R₀ s(x, y)).mp h
    obtain ⟨u, hu, v, hv, huv, heq⟩ :=
      (mem_retainedPartCliquePotentialEdges D a s(x, y)).mp hxy
    have hh := (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp heq
    simp only [Prod.mk.injEq, Prod.swap_prod_mk] at hh
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨huv, ⟨a, hu, hv⟩, D.part_subset_retainedVertices ha hu⟩
    · exact ⟨huv.symm, ⟨a, hv, hu⟩, D.part_subset_retainedVertices ha hv⟩
  · rintro ⟨hne, ⟨a, hx, hy⟩, hret⟩
    have ha : a ∈ D.retainedPartIndices eta R₀ := by
      apply (D.mem_retainedPartIndices eta R₀ a).mpr
      exact (D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a.2, hx⟩)).mp hret
    exact (mem_retainedCliquePotentialEdges D eta R₀ s(x, y)).mpr
      ⟨a, ha, (mem_retainedPartCliquePotentialEdges D a s(x, y)).mpr
        ⟨x, hx, y, hy, hne, rfl⟩⟩

theorem mk_mem_retainedActiveEdgeUniverse_iff
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    s(x, y) ∈ retainedActiveEdgeUniverse D eta R₀ ↔
      D.ActivePair x y ∧ x ∈ D.retainedVertices eta R₀ := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := (mem_retainedActiveEdgeUniverse D eta R₀ s(x, y)).mp h
    obtain ⟨u, hu, v, hv, heq⟩ :=
      (mem_retainedActivePotentialEdges D eta R₀ e s(x, y)).mp he
    have hh := (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp heq
    simp only [Prod.mk.injEq, Prod.swap_prod_mk] at hh
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨⟨e.component, e.left, e.right, e.active, hu, hv⟩,
        D.part_subset_retainedVertices e.leftPart_mem_retained hu⟩
    · exact ⟨⟨e.component, e.right, e.left, e.active.symm, hv, hu⟩,
        D.part_subset_retainedVertices e.rightPart_mem_retained hv⟩
  · rintro ⟨⟨i, u, v, huv, hx, hy⟩, hret⟩
    have hi : i ∈ D.retainedComponentIndices eta R₀ :=
      (D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨u, hx⟩)).mp hret
    apply (mem_retainedActiveEdgeUniverse D eta R₀ s(x, y)).mpr
    rcases lt_or_gt_of_ne huv.ne with hlt | hgt
    · let e : RetainedActivePair D eta R₀ := ⟨i, hi, u, v, hlt, huv⟩
      exact ⟨e, (mem_retainedActivePotentialEdges D eta R₀ e s(x, y)).mpr
        ⟨x, hx, y, hy, rfl⟩⟩
    · let e : RetainedActivePair D eta R₀ := ⟨i, hi, v, u, hgt, huv.symm⟩
      exact ⟨e, (mem_retainedActivePotentialEdges D eta R₀ e s(x, y)).mpr
        ⟨y, hy, x, hx, Sym2.eq_swap⟩⟩

theorem mk_mem_nonretainedPotentialEdges_iff
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    s(x, y) ∈ nonretainedPotentialEdges D eta R₀ ↔
      x ∈ D.nonretainedVertices eta R₀ ∧ y ∈ D.nonretainedVertices eta R₀ ∧ x ≠ y := by
  constructor
  · intro h
    obtain ⟨u, hu, v, hv, huv, heq⟩ :=
      (mem_nonretainedPotentialEdges D eta R₀ s(x, y)).mp h
    have hh := (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp heq
    simp only [Prod.mk.injEq, Prod.swap_prod_mk] at hh
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hu, hv, huv⟩
    · exact ⟨hv, hu, huv.symm⟩
  · rintro ⟨hx, hy, hne⟩
    exact (mem_nonretainedPotentialEdges D eta R₀ s(x, y)).mpr
      ⟨x, hx, y, hy, hne, rfl⟩

/-- Missing edges within the retained clique parts, as actual unordered pairs. -/
def retainedMissingCliqueEdges (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : Finset (Sym2 V) :=
  retainedCliquePotentialEdges D eta R₀ \ finiteGraphEdges G

/-- Present edges not accounted for by retained clique edges, retained
active edges, or edges wholly within the nonretained side. The membership
theorem below identifies these exactly as retained-incident present defects. -/
def retainedPresentDefectEdges (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : Finset (Sym2 V) :=
  finiteGraphEdges G \ (retainedCliquePotentialEdges D eta R₀ ∪
    retainedActiveEdgeUniverse D eta R₀ ∪ nonretainedPotentialEdges D eta R₀)

def retainedMissingCliqueCount (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : ℕ := (retainedMissingCliqueEdges G D eta R₀).card

def retainedPresentDefectCount (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : ℕ := (retainedPresentDefectEdges G D eta R₀).card

@[simp] theorem mk_mem_retainedMissingCliqueEdges
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    s(x, y) ∈ retainedMissingCliqueEdges G D eta R₀ ↔
      x ≠ y ∧ D.SamePart x y ∧ x ∈ D.retainedVertices eta R₀ ∧ ¬ G.Adj x y := by
  simp only [retainedMissingCliqueEdges, Finset.mem_sdiff,
    mk_mem_retainedCliquePotentialEdges_iff, mk_mem_finiteGraphEdges]
  tauto

@[simp] theorem mk_mem_retainedPresentDefectEdges
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    s(x, y) ∈ retainedPresentDefectEdges G D eta R₀ ↔
      G.Adj x y ∧ ¬ D.SamePart x y ∧ ¬ D.ActivePair x y ∧
        (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) := by
  simp only [retainedPresentDefectEdges, Finset.mem_sdiff, Finset.mem_union,
    mk_mem_finiteGraphEdges, mk_mem_retainedCliquePotentialEdges_iff,
    mk_mem_retainedActiveEdgeUniverse_iff, mk_mem_nonretainedPotentialEdges_iff,
    D.mem_nonretainedVertices]
  constructor
  · rintro ⟨hG, hnot⟩
    have hret : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀ := by
      by_contra h
      exact hnot (Or.inr ⟨(not_or.mp h).1, (not_or.mp h).2, hG.ne⟩)
    refine ⟨hG, ?_, ?_, hret⟩
    · intro hs
      have hx : x ∈ D.retainedVertices eta R₀ := hret.elim id
        ((retained_mem_iff_of_samePart D eta R₀ hs).mpr)
      exact hnot (Or.inl (Or.inl ⟨hG.ne, hs, hx⟩))
    · intro ha
      have hx : x ∈ D.retainedVertices eta R₀ := hret.elim id
        ((retained_mem_iff_of_activePair D eta R₀ ha).mpr)
      exact hnot (Or.inl (Or.inr ⟨ha, hx⟩))
  · rintro ⟨hG, hs, ha, hret⟩
    refine ⟨hG, ?_⟩
    rintro ((⟨_, hs', _⟩ | ⟨ha', _⟩) | ⟨hx, hy, _⟩)
    · exact hs hs'
    · exact ha ha'
    · exact hret.elim hx hy

theorem retainedMissingCliqueEdges_subset_combinedDefect
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    retainedMissingCliqueEdges G D eta R₀ ⊆
      finiteGraphEdges (subcriticalCombinedDefectGraph G D) := by
  intro z hz
  induction z using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hne, hs, _, hG⟩ := (mk_mem_retainedMissingCliqueEdges G D eta R₀ x y).mp hz
    exact (mk_mem_finiteGraphEdges _ x y).mpr
      ((subcriticalCombinedDefectGraph_adj_iff G D).mpr ⟨hne, Or.inl ⟨hs, hG⟩⟩)

theorem retainedPresentDefectEdges_subset_combinedDefect
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    retainedPresentDefectEdges G D eta R₀ ⊆
      finiteGraphEdges (subcriticalCombinedDefectGraph G D) := by
  intro z hz
  induction z using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hG, hs, ha, _⟩ := (mk_mem_retainedPresentDefectEdges G D eta R₀ x y).mp hz
    exact (mk_mem_finiteGraphEdges _ x y).mpr
      ((subcriticalCombinedDefectGraph_adj_iff G D).mpr
        ⟨hG.ne, Or.inr ⟨hs, ha, hG⟩⟩)

theorem retainedPresentDefectEdges_disjoint_missing
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    Disjoint (retainedPresentDefectEdges G D eta R₀) (retainedMissingCliqueEdges G D eta R₀) := by
  exact Finset.disjoint_left.mpr fun _ hp hm ↦
    (Finset.mem_sdiff.mp hm).2 (Finset.mem_sdiff.mp hp).1

theorem retainedPresentDefectCount_add_missing_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    retainedPresentDefectCount G D eta R₀ + retainedMissingCliqueCount G D eta R₀ ≤
      subcriticalDefectCost G D := by
  rw [retainedPresentDefectCount, retainedMissingCliqueCount,
    ← Finset.card_union_of_disjoint (retainedPresentDefectEdges_disjoint_missing G D eta R₀)]
  exact Finset.card_le_card (Finset.union_subset
    (retainedPresentDefectEdges_subset_combinedDefect G D eta R₀)
    (retainedMissingCliqueEdges_subset_combinedDefect G D eta R₀))

theorem actualNonretainedEdges_card
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (nonretainedPotentialEdges D eta R₀ ∩ finiteGraphEdges G).card =
      inducedEdgeCount G (D.nonretainedVertices eta R₀) := by
  rw [inducedEdgeCount_eq_card_inter_sym2]
  congr 1
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [Finset.mem_inter, mk_mem_nonretainedPotentialEdges_iff,
      mk_mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Finset.mk_mem_sym2_iff]
    have hne : G.Adj x y → x ≠ y := SimpleGraph.Adj.ne
    tauto

/-- Exact integer shift of the actual retained vector. No truncated natural
subtraction enters this definition. -/
def retainedEdgeShift (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : ℤ :=
  (finiteGraphEdges G).card - (retainedCliqueCapacity D eta R₀ : ℤ) -
    (retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) : ℤ)

theorem retainedEdgeCountTotal_add_shift
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedCliqueCapacity D eta R₀ : ℤ) +
      (retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) : ℤ) +
      retainedEdgeShift G D eta R₀ = ((finiteGraphEdges G).card : ℤ) := by
  unfold retainedEdgeShift
  ring

/-- The exact signed discrepancy is the nonretained edge count plus
present retained-incident defects minus missing retained clique edges. -/
theorem retainedEdgeShift_eq_nonretained_add_present_sub_missing
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    retainedEdgeShift G D eta R₀ =
      (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℤ) +
        (retainedPresentDefectCount G D eta R₀ : ℤ) -
        (retainedMissingCliqueCount G D eta R₀ : ℤ) := by
  let E := finiteGraphEdges G
  let C := retainedCliquePotentialEdges D eta R₀
  let A := retainedActiveEdgeUniverse D eta R₀
  let S := nonretainedPotentialEdges D eta R₀
  have hCA : Disjoint (C ∩ E) (A ∩ E) :=
    (retainedCliquePotentialEdges_disjoint_active D eta R₀).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hCS : Disjoint (C ∩ E) (S ∩ E) :=
    (retainedCliquePotentialEdges_disjoint_nonretained D eta R₀).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hAS : Disjoint (A ∩ E) (S ∩ E) :=
    (retainedActiveEdgeUniverse_disjoint_nonretained D eta R₀).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hU : E ∩ (C ∪ A ∪ S) = (C ∩ E) ∪ (A ∩ E) ∪ (S ∩ E) := by
    ext z
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hpartition := Finset.card_sdiff_add_card_inter E (C ∪ A ∪ S)
  rw [hU, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hCS, hAS⟩),
    Finset.card_union_of_disjoint hCA] at hpartition
  have hmissing := Finset.card_sdiff_add_card_inter C E
  have hCcard : C.card = retainedCliqueCapacity D eta R₀ :=
    retainedCliquePotentialEdges_card D eta R₀
  have hAcard : (A ∩ E).card =
      retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) :=
    actualRetainedActiveEdgeUniverse_card G D eta R₀
  have hScard : (S ∩ E).card = inducedEdgeCount G (D.nonretainedVertices eta R₀) :=
    actualNonretainedEdges_card G D eta R₀
  rw [hAcard, hScard] at hpartition
  rw [hCcard] at hmissing
  have hpZ : (retainedPresentDefectCount G D eta R₀ : ℤ) +
      ((C ∩ E).card : ℤ) +
      (retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) : ℤ) +
      (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℤ) = (E.card : ℤ) := by
    exact_mod_cast (show (E \ (C ∪ A ∪ S)).card + (C ∩ E).card +
        retainedEdgeCountTotal (actualRetainedEdgeCountVector G D eta R₀) +
        inducedEdgeCount G (D.nonretainedVertices eta R₀) = E.card by omega)
  have hmZ : (retainedMissingCliqueCount G D eta R₀ : ℤ) + ((C ∩ E).card : ℤ) =
      (retainedCliqueCapacity D eta R₀ : ℤ) := by exact_mod_cast hmissing
  unfold retainedEdgeShift
  change (E.card : ℤ) - _ - _ = _
  omega

theorem abs_retainedEdgeShift_sub_nonretainedEdgeCount_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    |retainedEdgeShift G D eta R₀ -
      (inducedEdgeCount G (D.nonretainedVertices eta R₀) : ℤ)| ≤
        (subcriticalDefectCost G D : ℤ) := by
  rw [retainedEdgeShift_eq_nonretained_add_present_sub_missing]
  have hbound := retainedPresentDefectCount_add_missing_le G D eta R₀
  have hp : (0 : ℤ) ≤ retainedPresentDefectCount G D eta R₀ := Int.natCast_nonneg _
  have hm : (0 : ℤ) ≤ retainedMissingCliqueCount G D eta R₀ := Int.natCast_nonneg _
  rw [abs_le]
  constructor <;> omega

end InducedStars
