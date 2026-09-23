import InducedStars.Structure.Subcritical.RealizedCells
import InducedStars.Structure.Subcritical.Compatibility

/-!
# The explicit subcritical component-alignment witness

The fields retain one consistent component injection and actual core
isomorphisms, relative to a fixed candidate sequence and a single aligning
permutation. They are outputs of the finite geometric argument, not inputs
postulated for the full bridge.
-/

noncomputable section

open scoped BigOperators Classical symmDiff

namespace InducedStars

variable {k n : ℕ}

/-- Cells of one reference component, still in the original graph labels. -/
abbrev subcriticalAlignedComponentCells (L : AdmissibleBlockSequence k)
    (n : ℕ) (pi : Equiv.Perm (Fin n)) (i : ℕ)
    (v : Fin (L.core i).order) : Finset (Fin n) :=
  subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩

/-- One compact, explicitly constructed two-sided alignment. `t` can be
smaller than the paper's visible threshold so that the same assignment also
covers the bounded-order components used in compatibility and balance. -/
structure SubcriticalComponentAlignment
    (D : SubcriticalDivision k (Fin n)) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (t m : ℝ) (B : ℕ) where
  assignment : {i // i ∈ D.visibleComponentIndices t} ↪
    {j : ℕ // blockIndexActive L.count j}
  coreIso : ∀ i, (D.core i.val).graph ≃g (L.core (assignment i).val).graph
  order_le : ∀ i, (L.core (assignment i).val).order ≤ B
  cell_large : ∀ i u,
    t * n / 4 ≤ (subcriticalAlignedComponentCells L n pi
      (assignment i).val (coreIso i u)).card
  overlap : ∀ i u,
    m ≤ ((subcriticalAlignedComponentCells L n pi (assignment i).val (coreIso i u) ∩
      D.parts i.val u).card : ℝ)
  spill : ∀ i u,
    ((D.parts i.val u \ subcriticalAlignedComponentCells L n pi
      (assignment i).val (coreIso i u)).card : ℝ) < m
  symmetric_difference : ∀ i u,
    ((D.parts i.val u ∆ subcriticalAlignedComponentCells L n pi
      (assignment i).val (coreIso i u)).card : ℝ) ≤ ((B : ℝ) + 2) * m
  covers_large_blocks : ∀ j : {j : ℕ // blockIndexActive L.count j},
    (∀ v, 2 * t * n ≤ (subcriticalAlignedComponentCells L n pi j.val v).card) →
      ∃ i, assignment i = j

namespace SubcriticalComponentAlignment

variable {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {pi : Equiv.Perm (Fin n)}
  {t m : ℝ} {B : ℕ}

/-- The visible component containing a visible part. -/
def visibleComponentOfPart
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    {i : Fin D.componentCount // i ∈ D.visibleComponentIndices t} :=
  ⟨a.val.1, (D.mem_visiblePartIndices t a.val).mp a.property⟩

@[simp] theorem visibleComponentOfPart_val
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    (A.visibleComponentOfPart a).val = a.val.1 := rfl

/-- The literal aligned reference cell matched to one visible division part. -/
def matchedCellIndex
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    SubcriticalReferenceCellIndex L :=
  ⟨(A.assignment (A.visibleComponentOfPart a)).val,
    A.coreIso (A.visibleComponentOfPart a) a.val.2⟩

@[simp] theorem matchedCellIndex_fst
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    (A.matchedCellIndex a).1 =
      (A.assignment (A.visibleComponentOfPart a)).val := rfl

/-- Vertices on which a visible division part and its matched reference cell
literally agree. -/
def goodVertices
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) : Finset (Fin n) :=
  D.part a.val ∩
    subcriticalAlignedReferenceCellVertices L n pi (A.matchedCellIndex a)

@[simp] theorem mem_goodVertices
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) (x : Fin n) :
    x ∈ A.goodVertices a ↔
      x ∈ D.part a.val ∧
        x ∈ subcriticalAlignedReferenceCellVertices L n pi
          (A.matchedCellIndex a) := by
  simp [goodVertices]

theorem goodVertices_subset_part
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    A.goodVertices a ⊆ D.part a.val := Finset.inter_subset_left

theorem goodVertices_subset_matchedCell
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    A.goodVertices a ⊆
      subcriticalAlignedReferenceCellVertices L n pi
        (A.matchedCellIndex a) := Finset.inter_subset_right

/-- Every good set retains the quantitative overlap supplied by the
component-alignment witness. -/
theorem m_le_card_goodVertices
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    m ≤ (A.goodVertices a).card := by
  simpa only [goodVertices, matchedCellIndex, visibleComponentOfPart,
    SubcriticalDivision.part, subcriticalAlignedComponentCells,
    Finset.inter_comm] using
      A.overlap (A.visibleComponentOfPart a) a.val.2

/-- Fewer than `m` vertices of a visible division part are lost when it is
restricted to its good set. -/
theorem card_part_sdiff_goodVertices_lt
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    ((D.part a.val \ A.goodVertices a).card : ℝ) < m := by
  simpa only [goodVertices, matchedCellIndex, visibleComponentOfPart,
    SubcriticalDivision.part, subcriticalAlignedComponentCells,
    Finset.sdiff_inter_self_left] using
      A.spill (A.visibleComponentOfPart a) a.val.2

theorem card_part_sdiff_goodVertices_le
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    ((D.part a.val \ A.goodVertices a).card : ℝ) ≤ m :=
  (A.card_part_sdiff_goodVertices_lt a).le

/-- The original part and its matched reference cell have the two-sided
error recorded by the component-alignment witness. -/
theorem card_part_symmDiff_matchedCell_le
    (A : SubcriticalComponentAlignment D L pi t m B)
    (a : {a : D.PartIndex // a ∈ D.visiblePartIndices t}) :
    ((D.part a.val ∆ subcriticalAlignedReferenceCellVertices L n pi
      (A.matchedCellIndex a)).card : ℝ) ≤ ((B : ℝ) + 2) * m := by
  simpa only [matchedCellIndex, visibleComponentOfPart,
    SubcriticalDivision.part, subcriticalAlignedComponentCells] using
    A.symmetric_difference (A.visibleComponentOfPart a) a.val.2

/-- On the Cartesian product of any two good visible-part sets, the single
aligned full reference agrees exactly with the division palette. -/
theorem reference_weight_eq_divisionWeight_of_mem_goodVertices
    (hk : 3 ≤ k) (A : SubcriticalComponentAlignment D L pi t m B)
    (a b : {a : D.PartIndex // a ∈ D.visiblePartIndices t})
    {x y : Fin n} (hx : x ∈ A.goodVertices a)
    (hy : y ∈ A.goodVertices b) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y =
      (subcriticalDivisionWeightedGraph hk D).weight x y := by
  have hxPart : x ∈ D.part a.val := A.goodVertices_subset_part a hx
  have hyPart : y ∈ D.part b.val := A.goodVertices_subset_part b hy
  have hxCell := A.goodVertices_subset_matchedCell a hx
  have hyCell := A.goodVertices_subset_matchedCell b hy
  rcases a with ⟨⟨i, u⟩, hi⟩
  rcases b with ⟨⟨j, v⟩, hj⟩
  let ii : {i : Fin D.componentCount // i ∈ D.visibleComponentIndices t} :=
    A.visibleComponentOfPart ⟨⟨i, u⟩, hi⟩
  let jj : {i : Fin D.componentCount // i ∈ D.visibleComponentIndices t} :=
    A.visibleComponentOfPart ⟨⟨j, v⟩, hj⟩
  have hxPart' : x ∈ D.parts i u := by
    simpa [SubcriticalDivision.part] using hxPart
  have hyPart' : y ∈ D.parts j v := by
    simpa [SubcriticalDivision.part] using hyPart
  have hxCell' : x ∈ subcriticalAlignedReferenceCellVertices L n pi
      ⟨(A.assignment ii).val, A.coreIso ii u⟩ := by
    simpa only [ii, matchedCellIndex] using hxCell
  have hyCell' : y ∈ subcriticalAlignedReferenceCellVertices L n pi
      ⟨(A.assignment jj).val, A.coreIso jj v⟩ := by
    simpa only [jj, matchedCellIndex] using hyCell
  by_cases hij : i = j
  · subst j
    have hijj : jj = ii := Subtype.ext rfl
    subst jj
    by_cases huv : u = v
    · subst v
      calc
        ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 1 :=
          subcriticalReference_weight_of_mem_same_aligned_cell
            hk L pi ⟨(A.assignment ii).val, A.coreIso ii u⟩ hxCell' hyCell'
        _ = (subcriticalDivisionWeightedGraph hk D).weight x y := by
          symm
          exact subcriticalDivisionWeightedGraph_weight_of_samePart hk D
            ⟨⟨i, u⟩, hxPart', hyPart'⟩
    · by_cases hadj : (D.core i).graph.Adj u v
      · have hadj' : (L.core (A.assignment ii).val).graph.Adj
            (A.coreIso ii u) (A.coreIso ii v) :=
          (A.coreIso ii).map_adj_iff.mpr hadj
        calc
          ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = pK k :=
            subcriticalReference_weight_of_mem_active_aligned_cells
              hk L pi (A.assignment ii).val hadj' hxCell' hyCell'
          _ = (subcriticalDivisionWeightedGraph hk D).weight x y := by
            symm
            exact subcriticalDivisionWeightedGraph_weight_of_activePair hk D
              ⟨i, u, v, hadj, hxPart', hyPart'⟩
      · have huv' : A.coreIso ii u ≠ A.coreIso ii v :=
          fun h ↦ huv ((A.coreIso ii).injective h)
        have hadj' : ¬ (L.core (A.assignment ii).val).graph.Adj
            (A.coreIso ii u) (A.coreIso ii v) := by
          exact fun h ↦ hadj ((A.coreIso ii).map_adj_iff.mp h)
        calc
          ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 :=
            subcriticalReference_weight_of_mem_inactive_aligned_cells
              hk L pi (A.assignment ii).val huv' hadj' hxCell' hyCell'
          _ = (subcriticalDivisionWeightedGraph hk D).weight x y := by
            symm
            rw [subcriticalDivisionWeightedGraph_weight_of_mem_parts
              hk D hxPart hyPart]
            simp [huv, hadj]
  · have hassign : (A.assignment ii).val ≠ (A.assignment jj).val := by
      intro hval
      have heq : A.assignment ii = A.assignment jj := Subtype.ext hval
      exact hij (congrArg Subtype.val (A.assignment.injective heq))
    calc
      ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 :=
        subcriticalReference_weight_of_mem_distinct_aligned_blocks
          hk L pi hassign hxCell' hyCell'
      _ = (subcriticalDivisionWeightedGraph hk D).weight x y := by
        symm
        exact subcriticalDivisionWeightedGraph_weight_of_distinct_components
          hk D hij hxPart hyPart

end SubcriticalComponentAlignment

end InducedStars
