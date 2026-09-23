import InducedStars.Structure.Subcritical.Defect

/-!
# Valid one-vertex moves of subcritical divisions

The component cores and their indices are unchanged. A move is defined only
when every part left behind remains nonempty; in particular, this interface
does not silently permit removal of a singleton source part.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars
namespace SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The new part family after removing `v` from its old position and placing
it in `target`, or in the sparse remainder if `target = none`. -/
def movedPart (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (a : D.PartIndex) : Finset V :=
  if target = some a then insert v (D.part a) else (D.part a).erase v

@[simp] theorem mem_movedPart (D : SubcriticalDivision k V) (v x : V)
    (target : Option D.PartIndex) (a : D.PartIndex) :
    x ∈ D.movedPart v target a ↔
      (x = v ∧ target = some a) ∨ (x ≠ v ∧ x ∈ D.part a) := by
  by_cases ht : target = some a <;> by_cases hx : x = v <;>
    simp [movedPart, ht, hx]

theorem movedPart_pairwiseDisjoint (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) :
    Set.PairwiseDisjoint (Set.univ : Set D.PartIndex) (D.movedPart v target) := by
  intro a _ b _ hab
  change Disjoint (D.movedPart v target a) (D.movedPart v target b)
  rw [Finset.disjoint_left]
  intro x hxa hxb
  rw [mem_movedPart] at hxa hxb
  rcases hxa with ⟨rfl, ha⟩ | ⟨hxa, ha⟩
  · rcases hxb with ⟨_, hb⟩ | ⟨hxb, _⟩
    · exact hab (Option.some.inj (ha.symm.trans hb))
    · exact hxb rfl
  · rcases hxb with ⟨hxb, _⟩ | ⟨_, hb⟩
    · exact hxa hxb
    · exact Finset.disjoint_left.mp (D.part_disjoint hab) ha hb

/-- A one-vertex move, with precisely the nonemptiness obligation for
all parts other than the destination. No component core is modified. -/
def moveVertex (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex)
    (hvalid : ∀ a, target ≠ some a → ((D.part a).erase v).Nonempty) :
    SubcriticalDivision k V where
  componentCount := D.componentCount
  componentCount_pos := D.componentCount_pos
  core := D.core
  parts i j := D.movedPart v target ⟨i, j⟩
  parts_nonempty i j := by
    by_cases ht : target = some ⟨i, j⟩
    · simp [movedPart, ht]
    · simpa [movedPart, ht] using hvalid ⟨i, j⟩ ht
  parts_pairwiseDisjoint := D.movedPart_pairwiseDisjoint v target

@[simp] theorem moveVertex_part (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (hvalid) (a : D.PartIndex) :
    (D.moveVertex v target hvalid).part a = D.movedPart v target a := rfl

@[simp] theorem moveVertex_mem_part_of_ne (D : SubcriticalDivision k V)
    (v : V) (target : Option D.PartIndex) (hvalid)
    {x : V} (hx : x ≠ v) (a : D.PartIndex) :
    x ∈ (D.moveVertex v target hvalid).part a ↔ x ∈ D.part a := by
  simp [hx]

@[simp] theorem moveVertex_mem_sparse_self (D : SubcriticalDivision k V)
    (v : V) (target : Option D.PartIndex) (hvalid) :
    v ∈ (D.moveVertex v target hvalid).sparse ↔ target = none := by
  rw [mem_sparse, mem_support]
  change (¬ ∃ a : D.PartIndex, v ∈ D.movedPart v target a) ↔ target = none
  cases target <;> simp

theorem erase_nonempty_of_sparse (D : SubcriticalDivision k V) {v : V}
    (hv : v ∈ D.sparse) (a : D.PartIndex) :
    ((D.part a).erase v).Nonempty := by
  have hva : v ∉ D.part a := fun h ↦ (mem_sparse.mp hv) (D.part_subset_support a h)
  simpa [Finset.erase_eq_of_notMem hva] using D.part_nonempty a

/-- Adding a sparse vertex to any part is always a valid move. -/
def moveSparseToPart (D : SubcriticalDivision k V) (v : V)
    (hv : v ∈ D.sparse) (a : D.PartIndex) : SubcriticalDivision k V :=
  D.moveVertex v (some a) (fun b _ ↦ D.erase_nonempty_of_sparse hv b)

theorem erase_nonempty_of_source (D : SubcriticalDivision k V)
    {v : V} {source : D.PartIndex} (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) (a : D.PartIndex) :
    ((D.part a).erase v).Nonempty := by
  by_cases ha : a = source
  · subst a
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hv]
    omega
  · have hva : v ∉ D.part a := fun h ↦ ha (D.mem_part_unique h hv)
    simpa [Finset.erase_eq_of_notMem hva] using D.part_nonempty a

/-- Removing a vertex from a non-singleton part is a valid move to sparse.
The explicit lower bound cannot be dropped merely because `v` belongs to a
main part. -/
def movePartToSparse (D : SubcriticalDivision k V) (v : V)
    (source : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) : SubcriticalDivision k V :=
  D.moveVertex v none (fun a _ ↦ D.erase_nonempty_of_source hv hsource a)

/-- A valid move from a non-singleton source to a different component.
The same construction is also valid for a target in the same component. -/
def movePartToPart (D : SubcriticalDivision k V) (v : V)
    (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) : SubcriticalDivision k V :=
  D.moveVertex v (some target) (fun a _ ↦ D.erase_nonempty_of_source hv hsource a)

/-- A singleton part prevents every one-vertex move to a different part or
to sparse in an unchanged-core division. This is an exact validity statement,
not an assumption excluding the case. -/
theorem singleton_source_move_invalid (D : SubcriticalDivision k V)
    {v : V} {source : D.PartIndex} (hsource : D.part source = {v})
    (target : Option D.PartIndex) (htarget : target ≠ some source) :
    ¬ (∀ a, target ≠ some a → ((D.part a).erase v).Nonempty) := by
  intro h
  simpa [hsource] using h source htarget

theorem moveVertex_samePart_away (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (hvalid) {x y : V}
    (hx : x ≠ v) (hy : y ≠ v) :
    (D.moveVertex v target hvalid).SamePart x y ↔ D.SamePart x y := by
  change (∃ a : D.PartIndex, x ∈ D.movedPart v target a ∧
    y ∈ D.movedPart v target a) ↔ ∃ a : D.PartIndex, x ∈ D.part a ∧ y ∈ D.part a
  simp [mem_movedPart, hx, hy]

theorem moveVertex_activePair_away (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (hvalid) {x y : V}
    (hx : x ≠ v) (hy : y ≠ v) :
    (D.moveVertex v target hvalid).ActivePair x y ↔ D.ActivePair x y := by
  change (∃ i a b, (D.core i).graph.Adj a b ∧
    x ∈ D.movedPart v target ⟨i, a⟩ ∧ y ∈ D.movedPart v target ⟨i, b⟩) ↔
    ∃ i a b, (D.core i).graph.Adj a b ∧ x ∈ D.part ⟨i, a⟩ ∧ y ∈ D.part ⟨i, b⟩
  simp [mem_movedPart, hx, hy]

theorem moveVertex_samePart_self (D : SubcriticalDivision k V) (v : V)
    (target : D.PartIndex) (hvalid) {y : V} (hy : y ≠ v) :
    (D.moveVertex v (some target) hvalid).SamePart v y ↔ y ∈ D.part target := by
  change (∃ a : D.PartIndex, v ∈ D.movedPart v (some target) a ∧
    y ∈ D.movedPart v (some target) a) ↔ _
  simp [mem_movedPart, hy]

end SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

theorem subcriticalCombinedDefectGraph_move_away
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (hvalid) {x y : V}
    (hx : x ≠ v) (hy : y ≠ v) :
    (subcriticalCombinedDefectGraph G (D.moveVertex v target hvalid)).Adj x y ↔
      (subcriticalCombinedDefectGraph G D).Adj x y := by
  simp only [subcriticalCombinedDefectGraph_adj_iff,
    D.moveVertex_samePart_away v target hvalid hx hy,
    D.moveVertex_activePair_away v target hvalid hx hy]

/-- Exact unordered-edge bookkeeping when only one vertex row changes.
The addition form avoids all truncated natural subtraction. -/
theorem subcriticalMove_edge_count_of_away_agreement
    (T U : SimpleGraph V) (v : V)
    (haway : ∀ x y, x ≠ v → y ≠ v → (T.Adj x y ↔ U.Adj x y)) :
    T.edgeFinset.card + U.degree v = U.edgeFinset.card + T.degree v := by
  have hoff : T.edgeFinset.filter (fun e ↦ v ∉ e) =
      U.edgeFinset.filter (fun e ↦ v ∉ e) := by
    ext e
    induction e using Sym2.inductionOn with
    | hf x y =>
      simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        Sym2.mem_iff]
      by_cases hx : x = v
      · subst x; simp
      by_cases hy : y = v
      · subst y; simp
      simp [Ne.symm hx, Ne.symm hy, haway x y hx hy]
  have hT := Finset.card_filter_add_card_filter_not
    (s := T.edgeFinset) (fun e : Sym2 V ↦ v ∈ e)
  have hU := Finset.card_filter_add_card_filter_not
    (s := U.edgeFinset) (fun e : Sym2 V ↦ v ∈ e)
  rw [← T.incidenceFinset_eq_filter, T.card_incidenceFinset_eq_degree] at hT
  rw [← U.incidenceFinset_eq_filter, U.card_incidenceFinset_eq_degree] at hU
  rw [hoff] at hT
  omega

/-- A valid division move changes its exact canonical-repair cost by the
change of the combined-defect degree at the moved vertex. -/
theorem subcriticalDefectCost_moveVertex
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (target : Option D.PartIndex) (hvalid) :
    subcriticalDefectCost G (D.moveVertex v target hvalid) +
        (subcriticalCombinedDefectGraph G D).degree v =
      subcriticalDefectCost G D +
        (subcriticalCombinedDefectGraph G (D.moveVertex v target hvalid)).degree v := by
  exact subcriticalMove_edge_count_of_away_agreement
    (subcriticalCombinedDefectGraph G (D.moveVertex v target hvalid))
    (subcriticalCombinedDefectGraph G D) v
    (fun _ _ hx hy ↦ subcriticalCombinedDefectGraph_move_away G D v target hvalid hx hy)

/-- Sparse vertices have no exempt active or clique rows in the old
combined defect graph. -/
theorem subcriticalCombinedDefectGraph_degree_of_sparse
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {v : V}
    (hv : v ∈ D.sparse) :
    (subcriticalCombinedDefectGraph G D).degree v = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  have hs : ¬ D.SamePart v y := fun h ↦
    (D.mem_sparse.mp hv) (SubcriticalDivision.samePart_imp_support h).1
  have ha : ¬ D.ActivePair v y := fun h ↦
    (D.mem_sparse.mp hv) (SubcriticalDivision.activePair_imp_support h).1
  simp only [SimpleGraph.mem_neighborFinset, subcriticalCombinedDefectGraph_adj_iff,
    hs, ha, false_and, not_false_eq_true, true_and, false_or]
  exact and_iff_right_of_imp SimpleGraph.Adj.ne

/-- Moving a sparse vertex to a part pays at most its missing target edges
and its old neighbors outside the target; newly active edges can only improve
this upper bound. -/
theorem subcriticalMoveVertexToPart_degree_bound
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (target : D.PartIndex) (hvalid) :
    (subcriticalCombinedDefectGraph G (D.moveVertex v (some target) hvalid)).degree v +
        2 * degreeInFinset G v (D.part target) ≤
      G.degree v + (D.part target).card := by
  let A := D.part target
  let U := subcriticalCombinedDefectGraph G (D.moveVertex v (some target) hvalid)
  have hsub : U.neighborFinset v ⊆
      (G.neighborFinset v \ A) ∪ (A.filter fun y ↦ ¬ G.Adj v y) := by
    intro y hy
    have hUy : U.Adj v y := by simpa using hy
    have hyv : y ≠ v := hUy.ne.symm
    have hsame : (D.moveVertex v (some target) hvalid).SamePart v y ↔ y ∈ A :=
      D.moveVertex_samePart_self v target _ hyv
    rcases (subcriticalCombinedDefectGraph_adj_iff G
      (D.moveVertex v (some target) hvalid)).mp hUy with ⟨_, hm | hp⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hsame.mp hm.1, hm.2⟩)
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨by simpa using hp.2.2, fun ha ↦ hp.1 (hsame.mpr ha)⟩)
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hinter : (G.neighborFinset v ∩ A).card = degreeInFinset G v A := by
    congr 1
    ext y
    simp [degreeInFinset, Finset.mem_inter, and_comm]
  have hpartition := Finset.card_sdiff_add_card_inter (G.neighborFinset v) A
  rw [hinter, SimpleGraph.card_neighborFinset_eq_degree] at hpartition
  have hfilter := Finset.card_filter_add_card_filter_not (s := A) (G.Adj v)
  change degreeInFinset G v A + (A.filter fun y ↦ ¬ G.Adj v y).card = A.card at hfilter
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hcard
  change U.degree v + 2 * degreeInFinset G v A ≤ G.degree v + A.card
  omega

theorem subcriticalMoveSparseToPart_degree_bound
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {v : V}
    (hv : v ∈ D.sparse) (target : D.PartIndex) :
    (subcriticalCombinedDefectGraph G (D.moveSparseToPart v hv target)).degree v +
        2 * degreeInFinset G v (D.part target) ≤
      G.degree v + (D.part target).card :=
  subcriticalMoveVertexToPart_degree_bound G D v target _

/-- A strict majority row into any main part forbids a sparse placement in
a defect-minimizing division. This finite argument has no graphon input. -/
theorem subcritical_not_sparse_of_majority_row
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ D' : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G D')
    (v : V) (target : D.PartIndex)
    (hmajority : (D.part target).card < 2 * degreeInFinset G v (D.part target)) :
    v ∉ D.sparse := by
  intro hv
  have hcost := subcriticalDefectCost_moveVertex G D v (some target)
    (fun a _ ↦ D.erase_nonempty_of_sparse hv a)
  have hbound := subcriticalMoveSparseToPart_degree_bound G D hv target
  have hmin := hminimal (D.moveSparseToPart v hv target)
  rw [subcriticalCombinedDefectGraph_degree_of_sparse G D hv] at hcost
  change subcriticalDefectCost G (D.moveSparseToPart v hv target) + G.degree v =
    subcriticalDefectCost G D +
      (subcriticalCombinedDefectGraph G (D.moveSparseToPart v hv target)).degree v at hcost
  omega

end InducedStars
