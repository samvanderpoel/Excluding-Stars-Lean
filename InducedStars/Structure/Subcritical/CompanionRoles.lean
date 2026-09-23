import InducedStars.Structure.Subcritical.RowCounting

/-!
# The common free-vertex configuration for companion and opposite rows

There are two roles in the center's parent part and one role in each of its
`k-2` neighboring core parts. The two same-parent roles remain disjoint.
The prescribed outside vertex is not a coordinate of this pattern.
-/

noncomputable section

open Finset DenseGraph DenseGraph.FiniteWeightedGraph
open scoped BigOperators Classical

namespace InducedStars

variable {k n : ℕ}

abbrev SubcriticalCoreNeighbor (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :=
  {t : Fin (D.core i).order // (D.core i).graph.Adj j t}

abbrev SubcriticalCompanionRole (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :=
  Fin 2 ⊕ SubcriticalCoreNeighbor D i j

theorem card_subcriticalCoreNeighbor (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :
    Fintype.card (SubcriticalCoreNeighbor D i j) = k - 2 := by
  change Fintype.card ((D.core i).graph.neighborSet j) = k - 2
  rw [SimpleGraph.card_neighborSet_eq_degree, (D.core i).degree_eq]

theorem card_subcriticalCompanionRole (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :
    Fintype.card (SubcriticalCompanionRole D i j) = k := by
  simp only [SubcriticalCompanionRole, Fintype.card_sum, Fintype.card_fin,
    card_subcriticalCoreNeighbor]
  omega

def subcriticalCompanionRoleEquiv (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :
    Fin k ≃ SubcriticalCompanionRole D i j :=
  Fintype.equivOfCardEq (by simp [card_subcriticalCompanionRole hk])

def subcriticalCompanionParent (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :
    SubcriticalCompanionRole D i j → D.PartIndex :=
  Sum.elim (fun _ ↦ ⟨i, j⟩) (fun t ↦ ⟨i, t.val⟩)

def subcriticalCompanionRoleSets (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (X Y : Finset (Fin n)) (Z : SubcriticalCoreNeighbor D i j → Finset (Fin n)) :
    SubcriticalCompanionRole D i j → Finset (Fin n) :=
  Sum.elim (fun a ↦ if a = 0 then X else Y) Z

theorem subcriticalCompanionRoleSets_subset
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (X Y : Finset (Fin n)) (Z : SubcriticalCoreNeighbor D i j → Finset (Fin n))
    (hX : X ⊆ D.parts i j) (hY : Y ⊆ D.parts i j)
    (hZ : ∀ t, Z t ⊆ D.parts i t.val) (a : SubcriticalCompanionRole D i j) :
    subcriticalCompanionRoleSets D i j X Y Z a ⊆
      D.part (subcriticalCompanionParent D i j a) := by
  cases a with
  | inl a =>
      change (if a = 0 then X else Y) ⊆ D.parts i j
      split_ifs <;> assumption
  | inr a => exact hZ a

theorem subcriticalCompanionRoleSets_card
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (X Y : Finset (Fin n)) (Z : SubcriticalCoreNeighbor D i j → Finset (Fin n))
    {s : ℕ} (hX : X.card = s) (hY : Y.card = s) (hZ : ∀ t, (Z t).card = s)
    (a : SubcriticalCompanionRole D i j) :
    (subcriticalCompanionRoleSets D i j X Y Z a).card = s := by
  cases a with
  | inl a => simp only [subcriticalCompanionRoleSets, Sum.elim_inl]; split_ifs <;> assumption
  | inr a => exact hZ a

theorem subcriticalCompanionRoleSets_disjoint
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (X Y : Finset (Fin n)) (Z : SubcriticalCoreNeighbor D i j → Finset (Fin n))
    (hX : X ⊆ D.parts i j) (hY : Y ⊆ D.parts i j)
    (hZ : ∀ t, Z t ⊆ D.parts i t.val) (hXY : Disjoint X Y) :
    Pairwise (fun a b ↦ Disjoint (subcriticalCompanionRoleSets D i j X Y Z a)
      (subcriticalCompanionRoleSets D i j X Y Z b)) := by
  intro a b hab
  by_cases hp : subcriticalCompanionParent D i j a = subcriticalCompanionParent D i j b
  · cases a with
    | inl a =>
        cases b with
        | inl b =>
            fin_cases a <;> fin_cases b <;>
              simp_all [subcriticalCompanionRoleSets, Disjoint.symm]
        | inr b =>
            have h : j = b.val := by simpa [subcriticalCompanionParent] using hp
            exact False.elim ((D.core i).graph.ne_of_adj b.property h)
    | inr a =>
        cases b with
        | inl b =>
            have h : a.val = j := by simpa [subcriticalCompanionParent] using hp
            exact False.elim ((D.core i).graph.ne_of_adj a.property h.symm)
        | inr b =>
            have h : a = b := Subtype.ext (by simpa [subcriticalCompanionParent] using hp)
            exact False.elim (hab (congrArg Sum.inr h))
  · exact (D.part_disjoint hp).mono
      (subcriticalCompanionRoleSets_subset D i j X Y Z hX hY hZ a)
      (subcriticalCompanionRoleSets_subset D i j X Y Z hX hY hZ b)

/-- Different free leaves have different parent parts, even though the
center and one free leaf occupy the same parent. -/
theorem subcriticalCompanionParent_injective_on_leaves
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (a b : SubcriticalCompanionRole D i j)
    (ha : a ≠ Sum.inl 0) (hb : b ≠ Sum.inl 0)
    (hp : subcriticalCompanionParent D i j a = subcriticalCompanionParent D i j b) : a = b := by
  cases a with
  | inl a =>
      cases b with
      | inl b => fin_cases a <;> fin_cases b <;> simp_all
      | inr b =>
          have h : j = b.val := by simpa [subcriticalCompanionParent] using hp
          exact False.elim ((D.core i).graph.ne_of_adj b.property h)
  | inr a =>
      cases b with
      | inl b =>
          have h : a.val = j := by simpa [subcriticalCompanionParent] using hp
          exact False.elim ((D.core i).graph.ne_of_adj a.property h.symm)
      | inr b => exact congrArg Sum.inr (Subtype.ext (by simpa [subcriticalCompanionParent] using hp))

theorem subcriticalCompanionParent_center_weight
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (a : SubcriticalCompanionRole D i j) :
    subcriticalPaletteGap k ≤ subcriticalDivisionPartWeight D
      (subcriticalCompanionParent D i j (Sum.inl 0))
      (subcriticalCompanionParent D i j a) := by
  cases a with
  | inl a =>
      simp only [subcriticalCompanionParent, Sum.elim_inl, subcriticalDivisionPartWeight, ite_true]
      exact (min_le_left _ _).trans (pK_mem_Icc k).2
  | inr a =>
      have hne : (⟨i, j⟩ : D.PartIndex) ≠ ⟨i, a.val⟩ := by
        intro h
        exact (D.core i).graph.ne_of_adj a.property (by simpa using h)
      have ha : D.ActivePart (⟨i, j⟩ : D.PartIndex) ⟨i, a.val⟩ :=
        ⟨i, j, a.val, rfl, rfl, a.property⟩
      change subcriticalPaletteGap k ≤
        if (⟨i, j⟩ : D.PartIndex) = ⟨i, a.val⟩ then 1
        else if D.ActivePart ⟨i, j⟩ ⟨i, a.val⟩ then pK k else 0
      rw [if_neg hne, if_pos ha]
      exact min_le_left _ _

theorem subcriticalDivisionPartWeight_comm
    (D : SubcriticalDivision k (Fin n)) (a b : D.PartIndex) :
    subcriticalDivisionPartWeight D a b = subcriticalDivisionPartWeight D b a := by
  have hc : D.ActivePart a b ↔ D.ActivePart b a := by
    constructor <;> rintro ⟨i, u, v, rfl, rfl, huv⟩ <;>
      exact ⟨i, v, u, rfl, rfl, huv.symm⟩
  simp only [subcriticalDivisionPartWeight, eq_comm, hc]

/-- Every edge/nonedge factor of the free star is positive. In particular,
the two same-parent roles require an edge, never a forbidden clique nonedge. -/
theorem subcriticalCompanionRole_factor_lower
    (D : SubcriticalDivision k (Fin n))
    (i : Fin D.componentCount) (j : Fin (D.core i).order)
    (a b : SubcriticalCompanionRole D i j) (hab : a ≠ b) :
    subcriticalPaletteGap k ≤
      if (SimpleGraph.starGraph (Sum.inl 0 : SubcriticalCompanionRole D i j)).Adj a b then
        subcriticalDivisionPartWeight D (subcriticalCompanionParent D i j a)
          (subcriticalCompanionParent D i j b)
      else 1 - subcriticalDivisionPartWeight D (subcriticalCompanionParent D i j a)
          (subcriticalCompanionParent D i j b) := by
  by_cases ha : a = Sum.inl 0
  · subst a
    rw [if_pos (SimpleGraph.starGraph_adj.mpr ⟨hab, Or.inl rfl⟩)]
    exact subcriticalCompanionParent_center_weight D i j b
  · by_cases hb : b = Sum.inl 0
    · subst b
      rw [if_pos (SimpleGraph.starGraph_adj.mpr ⟨hab, Or.inr rfl⟩),
        subcriticalDivisionPartWeight_comm]
      exact subcriticalCompanionParent_center_weight D i j a
    · rw [if_neg (by simpa [SimpleGraph.starGraph_adj, ha, hb])]
      have hne : subcriticalCompanionParent D i j a ≠ subcriticalCompanionParent D i j b :=
        fun h ↦ hab (subcriticalCompanionParent_injective_on_leaves D i j a b ha hb h)
      have hw := subcriticalDivisionPartWeight_le_pK_of_ne D hne
      exact (min_le_right (pK k) (1 - pK k)).trans (by linarith)

end InducedStars
