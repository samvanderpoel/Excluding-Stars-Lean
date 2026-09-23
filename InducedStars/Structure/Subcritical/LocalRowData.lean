import InducedStars.Structure.Subcritical.ProfileExponents

/-!
# Local row indices for the subsequent compensation arguments

Paper: notation preceding `fact:local-ent-estimates-K1k`. The sets below
retain actual division-part indices. Upper/lower labels are already exact
profile data; no tail-probability estimate or compensation claim is made here.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- Core neighbors of the retained root's own part, as global part indices. -/
def subcriticalActiveNeighborIndices (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  Finset.univ.filter fun a ↦
    D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a

def subcriticalUpperNeighborIndices (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  (subcriticalActiveNeighborIndices p v hv).filter fun a ↦ p.tails v a = some .upper

def subcriticalLowerNeighborIndices (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  (subcriticalActiveNeighborIndices p v hv).filter fun a ↦ p.tails v a = some .lower

def subcriticalMediumNeighborIndices (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  subcriticalActiveNeighborIndices p v hv \
    (subcriticalUpperNeighborIndices p v hv ∪ subcriticalLowerNeighborIndices p v hv)

@[simp] theorem mem_subcriticalActiveNeighborIndices
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalActiveNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a := by
  simp [subcriticalActiveNeighborIndices]

@[simp] theorem mem_subcriticalUpperNeighborIndices
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalUpperNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a ∧
        p.tails v a = some .upper := by
  simp [subcriticalUpperNeighborIndices]

@[simp] theorem mem_subcriticalLowerNeighborIndices
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalLowerNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a ∧
        p.tails v a = some .lower := by
  simp [subcriticalLowerNeighborIndices]

@[simp] theorem mem_subcriticalMediumNeighborIndices
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalMediumNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a ∧
        p.tails v a = none := by
  cases ht : p.tails v a with
  | none => simp [subcriticalMediumNeighborIndices, ht]
  | some t => cases t <;> simp [subcriticalMediumNeighborIndices, ht]

theorem subcriticalUpperLowerNeighborIndices_disjoint
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    Disjoint (subcriticalUpperNeighborIndices p v hv) (subcriticalLowerNeighborIndices p v hv) := by
  apply Finset.disjoint_left.mpr
  intro a hu hl
  have hu' := (mem_subcriticalUpperNeighborIndices p v hv a).mp hu
  have hl' := (mem_subcriticalLowerNeighborIndices p v hv a).mp hl
  rw [hu'.2] at hl'
  cases hl'.2

theorem subcriticalUpperLowerNeighborIndices_inter_eq_empty
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    subcriticalUpperNeighborIndices p v hv ∩ subcriticalLowerNeighborIndices p v hv = ∅ :=
  Finset.disjoint_iff_inter_eq_empty.mp (subcriticalUpperLowerNeighborIndices_disjoint p v hv)

theorem subcriticalNeighborIndices_partition
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    subcriticalUpperNeighborIndices p v hv ∪ subcriticalLowerNeighborIndices p v hv ∪
      subcriticalMediumNeighborIndices p v hv = subcriticalActiveNeighborIndices p v hv := by
  apply Finset.union_sdiff_of_subset
  exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem subcriticalNeighborIndices_card_decomposition
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalLowerNeighborIndices p v hv).card +
      (subcriticalMediumNeighborIndices p v hv).card =
        (subcriticalActiveNeighborIndices p v hv).card := by
  rw [← Finset.card_union_of_disjoint (subcriticalUpperLowerNeighborIndices_disjoint p v hv)]
  calc
    _ = (subcriticalUpperNeighborIndices p v hv ∪ subcriticalLowerNeighborIndices p v hv ∪
        subcriticalMediumNeighborIndices p v hv).card :=
      (Finset.card_union_of_disjoint disjoint_sdiff_self_right).symm
    _ = _ := congrArg Finset.card (subcriticalNeighborIndices_partition p v hv)

/-- All recorded present-row targets, including a recorded `some 0`. -/
def subcriticalProfileRowIndices (p : SubcriticalProfile D eta R₀ theta)
    (v : V) : Finset D.PartIndex := Finset.univ.filter fun a ↦ (p.rows v a).isSome

def subcriticalProfileInsideRows (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  (subcriticalProfileRowIndices p v).filter fun a ↦
    a.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1

def subcriticalProfileOutsideRows (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  subcriticalProfileRowIndices p v \ subcriticalProfileInsideRows p v hv

def subcriticalProfileHighInsideRows (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (hv : v ∈ p.retainedRoots) : Finset D.PartIndex :=
  (subcriticalProfileInsideRows p v hv).filter fun a ↦
    (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ)

@[simp] theorem mem_subcriticalProfileRowIndices
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) :
    a ∈ subcriticalProfileRowIndices p v ↔ (p.rows v a).isSome := by
  simp [subcriticalProfileRowIndices]

@[simp] theorem mem_subcriticalProfileInsideRows
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalProfileInsideRows p v hv ↔
      (p.rows v a).isSome ∧
        a.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 := by
  simp [subcriticalProfileInsideRows]

@[simp] theorem mem_subcriticalProfileOutsideRows
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalProfileOutsideRows p v hv ↔
      (p.rows v a).isSome ∧
        a.1 ≠ (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 := by
  simp [subcriticalProfileOutsideRows]
  tauto

@[simp] theorem mem_subcriticalProfileHighInsideRows
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (hv : v ∈ p.retainedRoots) (a : D.PartIndex) :
    a ∈ subcriticalProfileHighInsideRows p alpha v hv ↔
      a ∈ subcriticalProfileInsideRows p v hv ∧
        (1 - 2 * alpha) * (D.part a \ p.roots).card ≤ (p.rowCount v a : ℝ) := by
  simp only [subcriticalProfileHighInsideRows, Finset.mem_filter]

theorem subcriticalProfileInsideOutsideRows_disjoint
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    Disjoint (subcriticalProfileInsideRows p v hv) (subcriticalProfileOutsideRows p v hv) :=
  disjoint_sdiff_self_right

theorem subcriticalProfileRows_partition
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    subcriticalProfileInsideRows p v hv ∪ subcriticalProfileOutsideRows p v hv =
      subcriticalProfileRowIndices p v :=
  Finset.union_sdiff_of_subset (Finset.filter_subset _ _)

theorem subcriticalProfileRows_card_decomposition
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (subcriticalProfileInsideRows p v hv).card + (subcriticalProfileOutsideRows p v hv).card =
      (subcriticalProfileRowIndices p v).card := by
  rw [← Finset.card_union_of_disjoint (subcriticalProfileInsideOutsideRows_disjoint p v hv),
    subcriticalProfileRows_partition]

/-- For realized data, the labels recover the source's exact full-part
degree tests. This is a deterministic restatement, not a probability bound. -/
theorem RealizesSubcriticalProfile.upperNeighborIndices_iff
    {G : SimpleGraph V} {alpha : ℝ} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalUpperNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a ∧
        (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  rw [mem_subcriticalUpperNeighborIndices]
  exact and_congr_right fun ha ↦ (h.tail_labels v hv a ha).1

theorem RealizesSubcriticalProfile.lowerNeighborIndices_iff
    {G : SimpleGraph V} {alpha : ℝ} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalLowerNeighborIndices p v hv ↔
      D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a ∧
        (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card := by
  rw [mem_subcriticalLowerNeighborIndices]
  exact and_congr_right fun ha ↦ (h.tail_labels v hv a ha).2

end InducedStars
