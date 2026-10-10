import InducedStars.Structure.Supercritical.ProfileModels
import Mathlib.Tactic

/-!
# Full-profile cross-edge outcomes

This module identifies the tagged coordinates of the exact full-profile
model with unordered graph edges.  It then realizes arbitrary tagged
outcomes as graphs with a prescribed combined defect pattern and proves that
every graph having the prescribed pattern and profile is recovered from one
unique fixed-cardinality sample.
-/

noncomputable section

open Finset Set

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance profileProbabilityDecidableRel
    (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Tagged coordinates as unordered cross edges -/

/-- The unordered graph edge represented by one full-profile coordinate. -/
def supercriticalProfileCoordinateSym2
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) : Sym2 V :=
  s(c.2.1.1, c.2.1.2)

/-- Increasing part-pair orientation makes the coordinate map injective. -/
theorem supercriticalProfileCoordinateSym2_injective
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    Function.Injective (supercriticalProfileCoordinateSym2 D profile) := by
  classical
  rintro ⟨e, xy⟩ ⟨f, uv⟩ h
  have hxy : xy.1.1 ∈ D.parts e.left ∧ xy.1.2 ∈ D.parts e.right := by
    simpa using xy.2
  have huv : uv.1.1 ∈ D.parts f.left ∧ uv.1.2 ∈ D.parts f.right := by
    simpa using uv.2
  rcases Sym2.eq_iff.mp h with hstraight | hswap
  · have hx : xy.1.1 = uv.1.1 := hstraight.1
    have hy : xy.1.2 = uv.1.2 := hstraight.2
    have hleft : e.left = f.left :=
      D.mem_part_unique hxy.1 (hx ▸ huv.1)
    have hright : e.right = f.right :=
      D.mem_part_unique hxy.2 (hy ▸ huv.2)
    have hef : e = f := SupercriticalPartPair.ext hleft hright
    subst f
    have hxyuv : xy = uv := Subtype.ext (Prod.ext hx hy)
    subst uv
    rfl
  · have hx : xy.1.1 = uv.1.2 := hswap.1
    have hy : xy.1.2 = uv.1.1 := hswap.2
    have hleft : e.left = f.right :=
      D.mem_part_unique hxy.1 (hx ▸ huv.2)
    have hright : e.right = f.left :=
      D.mem_part_unique hxy.2 (hy ▸ huv.1)
    have hbad : f.right < f.left := by
      simpa [hleft, hright] using e.left_lt_right
    exact (lt_asymm f.left_lt_right hbad).elim

/-- Embedding form of the tagged-coordinate map. -/
def supercriticalProfileCoordinateEmbedding
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    (supercriticalFixedProfileBlockModel D profile).Coordinate ↪ Sym2 V :=
  ⟨supercriticalProfileCoordinateSym2 D profile,
    supercriticalProfileCoordinateSym2_injective D profile⟩

/-- A pair is a random cross coordinate precisely when its endpoints lie in
two distinct main parts. -/
def SupercriticalDivision.IsCrossPair
    (D : SupercriticalDivision k V) (x y : V) : Prop :=
  ∃ e : SupercriticalPartPair k,
    (x ∈ D.parts e.left ∧ y ∈ D.parts e.right) ∨
      (y ∈ D.parts e.left ∧ x ∈ D.parts e.right)

theorem SupercriticalDivision.isCrossPair_comm
    (D : SupercriticalDivision k V) (x y : V) :
    D.IsCrossPair x y ↔ D.IsCrossPair y x := by
  constructor
  · rintro ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  · rintro ⟨e, h | h⟩
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩

theorem SupercriticalDivision.isCrossPair_ne
    (D : SupercriticalDivision k V) {x y : V}
    (hxy : D.IsCrossPair x y) : x ≠ y := by
  rintro rfl
  obtain ⟨e, h | h⟩ := hxy
  · exact e.left_ne_right (D.mem_part_unique h.1 h.2)
  · exact e.left_ne_right (D.mem_part_unique h.1 h.2)

theorem SupercriticalDivision.isCrossPair_of_mem_distinct_parts
    (D : SupercriticalDivision k V) {i j : Fin (k - 1)}
    (hij : i ≠ j) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts j) :
    D.IsCrossPair x y := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨⟨i, j, hij⟩, Or.inl ⟨hx, hy⟩⟩
  · exact ⟨⟨j, i, hji⟩, Or.inr ⟨hy, hx⟩⟩

/-- Every cross pair has one unique tagged coordinate representing it. -/
theorem exists_unique_supercriticalProfileCoordinate_of_crossPair
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    {x y : V} (hxy : D.IsCrossPair x y) :
    ∃! c : (supercriticalFixedProfileBlockModel D profile).Coordinate,
      supercriticalProfileCoordinateSym2 D profile c = s(x, y) := by
  classical
  obtain ⟨e, h | h⟩ := hxy
  · let c : (supercriticalFixedProfileBlockModel D profile).Coordinate :=
      ⟨e, ⟨(x, y), by simpa using h⟩⟩
    have hc : supercriticalProfileCoordinateSym2 D profile c = s(x, y) := rfl
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact supercriticalProfileCoordinateSym2_injective D profile
      (hd.trans hc.symm)
  · let c : (supercriticalFixedProfileBlockModel D profile).Coordinate :=
      ⟨e, ⟨(y, x), by simpa using h⟩⟩
    have hc : supercriticalProfileCoordinateSym2 D profile c = s(x, y) := by
      simp [c, supercriticalProfileCoordinateSym2]
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact supercriticalProfileCoordinateSym2_injective D profile
      (hd.trans hc.symm)

/-- The unique coordinate represented by a cross pair. -/
def supercriticalProfileCoordinateOfCrossPair
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (x y : V) (hxy : D.IsCrossPair x y) :
    (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  Classical.choose
    (exists_unique_supercriticalProfileCoordinate_of_crossPair D profile hxy)

@[simp] theorem supercriticalProfileCoordinateOfCrossPair_spec
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (x y : V) (hxy : D.IsCrossPair x y) :
    supercriticalProfileCoordinateSym2 D profile
        (supercriticalProfileCoordinateOfCrossPair D profile x y hxy) =
      s(x, y) :=
  (Classical.choose_spec
    (exists_unique_supercriticalProfileCoordinate_of_crossPair
      D profile hxy)).1

/-- Forget the block tags in one Boolean-cube outcome. -/
def supercriticalProfileAmbientOutcome
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    Finset (Sym2 V) :=
  outcome.map (supercriticalProfileCoordinateEmbedding D profile)

@[simp] theorem mem_supercriticalProfileAmbientOutcome
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    supercriticalProfileCoordinateSym2 D profile c ∈
        supercriticalProfileAmbientOutcome D profile outcome ↔
      c ∈ outcome := by
  classical
  simp [supercriticalProfileAmbientOutcome,
    supercriticalProfileCoordinateEmbedding]

/-- Whether an arbitrary tagged outcome selects the unordered pair `xy`. -/
def supercriticalProfileIsSelectedTaggedPair
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (x y : V) : Prop :=
  s(x, y) ∈ supercriticalProfileAmbientOutcome D profile outcome

theorem supercriticalProfileIsSelectedTaggedPair_comm
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (x y : V) :
    supercriticalProfileIsSelectedTaggedPair D profile outcome x y ↔
      supercriticalProfileIsSelectedTaggedPair D profile outcome y x := by
  simp only [supercriticalProfileIsSelectedTaggedPair, Sym2.eq_swap]

theorem supercriticalProfileIsSelectedTaggedPair_isCross
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V}
    (hxy : supercriticalProfileIsSelectedTaggedPair D profile outcome x y) :
    D.IsCrossPair x y := by
  classical
  rw [supercriticalProfileIsSelectedTaggedPair,
    supercriticalProfileAmbientOutcome, Finset.mem_map] at hxy
  obtain ⟨⟨e, uv⟩, _hc, hcxy⟩ := hxy
  have huv : uv.1.1 ∈ D.parts e.left ∧
      uv.1.2 ∈ D.parts e.right := by
    simpa using uv.2
  rcases Sym2.eq_iff.mp hcxy with h | h
  · exact ⟨e, Or.inl ⟨h.1 ▸ huv.1, h.2 ▸ huv.2⟩⟩
  · exact ⟨e, Or.inr ⟨h.1 ▸ huv.1, h.2 ▸ huv.2⟩⟩

theorem supercriticalProfileIsSelectedTaggedPair_iff_coordinate_mem
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V} (hxy : D.IsCrossPair x y) :
    supercriticalProfileIsSelectedTaggedPair D profile outcome x y ↔
      supercriticalProfileCoordinateOfCrossPair D profile x y hxy ∈ outcome := by
  classical
  let c := supercriticalProfileCoordinateOfCrossPair D profile x y hxy
  have hc : supercriticalProfileCoordinateSym2 D profile c = s(x, y) := by
    simpa [c] using
      supercriticalProfileCoordinateOfCrossPair_spec D profile x y hxy
  constructor
  · intro h
    rw [supercriticalProfileIsSelectedTaggedPair,
      supercriticalProfileAmbientOutcome, Finset.mem_map] at h
    obtain ⟨d, hd, hdc⟩ := h
    have hdc' : supercriticalProfileCoordinateSym2 D profile d =
        supercriticalProfileCoordinateSym2 D profile c := hdc.trans hc.symm
    have : d = c := supercriticalProfileCoordinateSym2_injective D profile hdc'
    simpa [c, this] using hd
  · intro h
    rw [supercriticalProfileIsSelectedTaggedPair, ← hc]
    exact (mem_supercriticalProfileAmbientOutcome D profile outcome c).2
      (by simpa [c] using h)

/-! ## Graph realization -/

/-- The deterministic graph prescribed by a combined defect pattern away
from cross cells.  It has missing-pattern complements inside main parts and
copies the pattern on support--sparse and sparse--sparse pairs. -/
def supercriticalGraphFromDefectPattern
    (D : SupercriticalDivision k V) (T : SimpleGraph V) : SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    (D.SameMainPart x y ∧ ¬ T.Adj x y) ∨
      (D.IsSupportSparsePair x y ∧ T.Adj x y) ∨
        (x ∈ D.sparse ∧ y ∈ D.sparse ∧ T.Adj x y)

@[simp] theorem supercriticalGraphFromDefectPattern_adj
    (D : SupercriticalDivision k V) (T : SimpleGraph V) (x y : V) :
    (supercriticalGraphFromDefectPattern D T).Adj x y ↔
      x ≠ y ∧
        ((D.SameMainPart x y ∧ ¬ T.Adj x y) ∨
          (D.IsSupportSparsePair x y ∧ T.Adj x y) ∨
            (x ∈ D.sparse ∧ y ∈ D.sparse ∧ T.Adj x y)) := by
  rw [supercriticalGraphFromDefectPattern, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · rcases h with h | h
      · exact ⟨hne, Or.inl ⟨(D.sameMainPart_comm y x).mp h.1,
          fun hT ↦ h.2 ((T.adj_comm x y).mp hT)⟩⟩
      · rcases h with h | h
        · exact ⟨hne, Or.inr (Or.inl ⟨
            (D.isSupportSparsePair_comm y x).mp h.1,
            (T.adj_comm y x).mp h.2⟩)⟩
        · exact ⟨hne, Or.inr (Or.inr ⟨h.2.1, h.1,
            (T.adj_comm y x).mp h.2.2⟩)⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-- Realize one arbitrary cross-edge outcome while retaining exactly the
deterministic statuses prescribed by `T` outside distinct main parts. -/
def supercriticalGraphFromCrossOutcome
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    SimpleGraph V :=
  SimpleGraph.fromRel fun x y ↦
    supercriticalProfileIsSelectedTaggedPair D profile outcome x y ∨
      (¬ D.IsCrossPair x y ∧
        (supercriticalGraphFromDefectPattern D T).Adj x y)

@[simp] theorem supercriticalGraphFromCrossOutcome_adj
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (x y : V) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      supercriticalProfileIsSelectedTaggedPair D profile outcome x y ∨
        (¬ D.IsCrossPair x y ∧
          (supercriticalGraphFromDefectPattern D T).Adj x y) := by
  rw [supercriticalGraphFromCrossOutcome, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · rcases h with h | h
      · exact Or.inl
          ((supercriticalProfileIsSelectedTaggedPair_comm
            D profile outcome y x).mp h)
      · exact Or.inr ⟨
          fun hxy ↦ h.1 ((D.isCrossPair_comm x y).mp hxy),
          ((supercriticalGraphFromDefectPattern D T).adj_comm y x).mp h.2⟩
  · intro h
    have hne : x ≠ y := by
      rcases h with h | h
      · exact D.isCrossPair_ne
          (supercriticalProfileIsSelectedTaggedPair_isCross
            D profile outcome h)
      · exact (supercriticalGraphFromDefectPattern D T).ne_of_adj h.2
    exact ⟨hne, Or.inl h⟩

theorem supercriticalGraphFromCrossOutcome_adj_of_cross
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V} (hxy : D.IsCrossPair x y) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      supercriticalProfileIsSelectedTaggedPair D profile outcome x y := by
  rw [supercriticalGraphFromCrossOutcome_adj]
  simp [hxy]

theorem supercriticalGraphFromCrossOutcome_adj_of_not_cross
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V} (hxy : ¬ D.IsCrossPair x y) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      (supercriticalGraphFromDefectPattern D T).Adj x y := by
  rw [supercriticalGraphFromCrossOutcome_adj]
  constructor
  · rintro (h | h)
    · exact False.elim
        (hxy (supercriticalProfileIsSelectedTaggedPair_isCross
          D profile outcome h))
    · exact h.2
  · exact fun h ↦ Or.inr ⟨hxy, h⟩

/-! ## Exact fixed samples encoded by graphs -/

/-- The oriented cross-edge subset cut out by a graph in one full-profile
block, represented in the subtype expected by the block model. -/
def supercriticalProfileGraphBlockSelection
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (e : SupercriticalPartPair k) :
    Finset ↑((supercriticalFixedProfileBlockModel D profile).block e) :=
  Finset.univ.filter fun xy ↦ G.Adj xy.1.1 xy.1.2

theorem supercriticalProfileGraphBlockSelection_map
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (e : SupercriticalPartPair k) :
    (supercriticalProfileGraphBlockSelection D profile G e).map
        ⟨Subtype.val, Subtype.val_injective⟩ =
      G.interedges (D.parts e.left) (D.parts e.right) := by
  classical
  ext xy
  rw [SimpleGraph.mem_interedges_iff]
  constructor
  · intro hxy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hxy
    have hparts : z.1.1 ∈ D.parts e.left ∧
        z.1.2 ∈ D.parts e.right := by
      simpa using z.2
    have hadj : G.Adj z.1.1 z.1.2 := by
      unfold supercriticalProfileGraphBlockSelection at hz
      exact (Finset.mem_filter.mp hz).2
    exact ⟨hparts.1, hparts.2, hadj⟩
  · rintro ⟨hx, hy, hG⟩
    let z : ↑((supercriticalFixedProfileBlockModel D profile).block e) :=
      ⟨xy, by simpa using And.intro hx hy⟩
    apply Finset.mem_map.mpr
    refine ⟨z, ?_, rfl⟩
    unfold supercriticalProfileGraphBlockSelection
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [z] using hG⟩

@[simp] theorem card_supercriticalProfileGraphBlockSelection
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (e : SupercriticalPartPair k) :
    (supercriticalProfileGraphBlockSelection D profile G e).card =
      (G.interedges (D.parts e.left) (D.parts e.right)).card := by
  rw [← supercriticalProfileGraphBlockSelection_map D profile G e,
    Finset.card_map]

/-- Encode a graph with the prescribed full cross profile as one exact
fixed-cardinality sample. -/
def supercriticalFixedProfileSampleOfGraph
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (hprofile : crossEdgeProfile G D = profile) :
    (supercriticalFixedProfileBlockModel D profile).Sample :=
  fun e ↦ ⟨supercriticalProfileGraphBlockSelection D profile G e, by
    rw [Finset.mem_powersetCard]
    refine ⟨Finset.subset_univ _, ?_⟩
    change (supercriticalProfileGraphBlockSelection D profile G e).card =
      profile.count e
    rw [card_supercriticalProfileGraphBlockSelection]
    have h := congrArg
      (fun p : SupercriticalEdgeProfile D ↦ p.count e) hprofile
    simpa only [crossEdgeProfile_count] using h⟩

theorem supercriticalFixedProfileBlockModel_selectedInBlock_sampleOfGraph
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (hprofile : crossEdgeProfile G D = profile)
    (e : SupercriticalPartPair k) :
    (supercriticalFixedProfileBlockModel D profile).selectedInBlock
        (supercriticalFixedProfileSampleOfGraph D profile G hprofile) e =
      G.interedges (D.parts e.left) (D.parts e.right) := by
  exact supercriticalProfileGraphBlockSelection_map D profile G e

/-- A represented cross pair is selected by the graph-encoded sample exactly
when it is an edge of the graph. -/
theorem supercriticalProfileIsSelectedTaggedPair_sampleOutcome_iff
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (G : SimpleGraph V) (hprofile : crossEdgeProfile G D = profile)
    {x y : V} (hxy : D.IsCrossPair x y) :
    supercriticalProfileIsSelectedTaggedPair D profile
        ((supercriticalFixedProfileBlockModel D profile).sampleOutcome
          (supercriticalFixedProfileSampleOfGraph D profile G hprofile)) x y ↔
      G.Adj x y := by
  rw [supercriticalProfileIsSelectedTaggedPair_iff_coordinate_mem
    D profile _ hxy]
  let c := supercriticalProfileCoordinateOfCrossPair D profile x y hxy
  rw [(supercriticalFixedProfileBlockModel D profile).mem_sampleOutcome]
  change c.2 ∈
    (supercriticalProfileGraphBlockSelection D profile G c.1) ↔ G.Adj x y
  have hc := supercriticalProfileCoordinateOfCrossPair_spec
    D profile x y hxy
  change s(c.2.1.1, c.2.1.2) = s(x, y) at hc
  simp only [supercriticalProfileGraphBlockSelection, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rcases Sym2.eq_iff.mp hc with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2, G.adj_comm]

/-! ## Recovery of graphs with a prescribed combined defect pattern -/

/-- Away from distinct main-part cells, the deterministic realization of a
combined defect pattern recovers the original graph exactly. -/
theorem supercriticalGraphFromDefectPattern_adj_iff_of_not_cross
    (D : SupercriticalDivision k V) (G T : SimpleGraph V)
    (hT : combinedSupercriticalDefectGraph G D = T)
    {x y : V} (hxy : ¬ D.IsCrossPair x y) :
    (supercriticalGraphFromDefectPattern D T).Adj x y ↔ G.Adj x y := by
  subst T
  rcases D.sparse_or_existsUnique_part x with hxS | ⟨i, hxi, _hi⟩ <;>
    rcases D.sparse_or_existsUnique_part y with hyS | ⟨j, hyj, _hj⟩
  · have hxns : x ∉ D.support := by simpa using hxS
    have hyns : y ∉ D.support := by simpa using hyS
    have hsame : ¬ D.SameMainPart x y := fun h ↦
      hxns (D.sameMainPart_imp_support h).1
    have hss : ¬ D.IsSupportSparsePair x y := by
      simp [SupercriticalDivision.IsSupportSparsePair, hxns, hyns]
    rw [supercriticalGraphFromDefectPattern_adj,
      combinedSupercriticalDefectGraph_adj_of_mem_sparse G D hxS hyS]
    constructor
    · rintro ⟨_, h⟩
      rcases h with h | h | h
      · exact False.elim (hsame h.1)
      · exact False.elim (hss h.1)
      · exact h.2.2
    · intro hG
      exact ⟨G.ne_of_adj hG, Or.inr (Or.inr ⟨hxS, hyS, hG⟩)⟩
  · have hys : y ∈ D.support := D.part_subset_support j hyj
    have hxns : x ∉ D.support := by simpa using hxS
    have hynSparse : y ∉ D.sparse := by simpa using hys
    have hsame : ¬ D.SameMainPart x y := fun h ↦
      hxns (D.sameMainPart_imp_support h).1
    have hss : D.IsSupportSparsePair x y :=
      Or.inr ⟨hys, hxS⟩
    have hTadj :
        (combinedSupercriticalDefectGraph G D).Adj x y ↔ G.Adj x y := by
      rw [(combinedSupercriticalDefectGraph G D).adj_comm, G.adj_comm]
      exact combinedSupercriticalDefectGraph_adj_support_sparse G D hys hxS
    rw [supercriticalGraphFromDefectPattern_adj, hTadj]
    constructor
    · rintro ⟨_, h⟩
      rcases h with h | h | h
      · exact False.elim (hsame h.1)
      · exact h.2
      · exact False.elim (hynSparse h.2.1)
    · intro hG
      exact ⟨G.ne_of_adj hG, Or.inr (Or.inl ⟨hss, hG⟩)⟩
  · have hxs : x ∈ D.support := D.part_subset_support i hxi
    have hyns : y ∉ D.support := by simpa using hyS
    have hxnSparse : x ∉ D.sparse := by simpa using hxs
    have hsame : ¬ D.SameMainPart x y := fun h ↦
      hyns (D.sameMainPart_imp_support h).2
    have hss : D.IsSupportSparsePair x y :=
      Or.inl ⟨hxs, hyS⟩
    rw [supercriticalGraphFromDefectPattern_adj,
      combinedSupercriticalDefectGraph_adj_support_sparse G D hxs hyS]
    constructor
    · rintro ⟨_, h⟩
      rcases h with h | h | h
      · exact False.elim (hsame h.1)
      · exact h.2
      · exact False.elim (hxnSparse h.1)
    · intro hG
      exact ⟨G.ne_of_adj hG, Or.inr (Or.inl ⟨hss, hG⟩)⟩
  · have hij : i = j := by
      by_contra hij
      exact hxy (D.isCrossPair_of_mem_distinct_parts hij hxi hyj)
    subst j
    have hsame : D.SameMainPart x y := ⟨i, hxi, hyj⟩
    have hxs : x ∈ D.support := D.part_subset_support i hxi
    have hys : y ∈ D.support := D.part_subset_support i hyj
    have hxns : x ∉ D.sparse := by simpa using hxs
    have hyns : y ∉ D.sparse := by simpa using hys
    have hss : ¬ D.IsSupportSparsePair x y := by
      simp [SupercriticalDivision.IsSupportSparsePair, hxns, hyns]
    rw [supercriticalGraphFromDefectPattern_adj]
    constructor
    · rintro ⟨hne, h⟩
      rcases h with h | h | h
      · by_contra hnG
        exact h.2 ((combinedSupercriticalDefectGraph_adj_of_mem_same_part
          G D i hxi hyj).2 ⟨hne, hnG⟩)
      · exact False.elim (hss h.1)
      · exact False.elim (hxns h.1)
    · intro hG
      have hne := G.ne_of_adj hG
      refine ⟨hne, Or.inl ⟨hsame, ?_⟩⟩
      intro hdef
      exact ((combinedSupercriticalDefectGraph_adj_of_mem_same_part
        G D i hxi hyj).1 hdef).2 hG

/-- The graph encoded by its exact cross-edge sample is recovered without
loss when the fixed pattern is its combined defect graph. -/
theorem supercriticalGraphFromCrossOutcome_sampleOfGraph
    (D : SupercriticalDivision k V) (G T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (hT : combinedSupercriticalDefectGraph G D = T)
    (hprofile : crossEdgeProfile G D = profile) :
    supercriticalGraphFromCrossOutcome D T profile
        ((supercriticalFixedProfileBlockModel D profile).sampleOutcome
          (supercriticalFixedProfileSampleOfGraph D profile G hprofile)) = G := by
  ext x y
  by_cases hxy : D.IsCrossPair x y
  · rw [supercriticalGraphFromCrossOutcome_adj_of_cross D T profile _ hxy,
      supercriticalProfileIsSelectedTaggedPair_sampleOutcome_iff
        D profile G hprofile hxy]
  · rw [supercriticalGraphFromCrossOutcome_adj_of_not_cross
        D T profile _ hxy,
      supercriticalGraphFromDefectPattern_adj_iff_of_not_cross
        D G T hT hxy]

end InducedStars
