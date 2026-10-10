import InducedStars.Structure.Subcritical.Retained
import Mathlib.Data.Finset.Sort

/-!
# The minimal retained key

 Forget every nonretained
component. The existing division record stores just the retained regular
cores and their actual nonempty, disjoint parts; `none` represents no retained
component. Its sparse field is computed, not stored. No graph, remainder
decoration, compatibility certificate, or selector certificate is counted.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The empty key is permitted; a nonempty key reuses the existing finite
core-and-parts record, with every recorded component interpreted as retained. -/
abbrev SubcriticalRetainedKey (k : ℕ) (V : Type*) [Fintype V] [DecidableEq V] :=
  Option (SubcriticalDivision k V)

namespace SubcriticalDivision

/-- Keep a nonempty set of components in inherited increasing order. -/
def restrictComponents (D : SubcriticalDivision k V)
    (I : Finset (Fin D.componentCount)) (hI : I.Nonempty) : SubcriticalDivision k V where
  componentCount := I.card
  componentCount_pos := hI.card_pos
  core i := D.core (I.orderIsoOfFin rfl i).val
  parts i j := D.parts (I.orderIsoOfFin rfl i).val j
  parts_nonempty i j := D.parts_nonempty _ j
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    apply D.part_disjoint
      (a := ⟨(I.orderIsoOfFin rfl a.1).val, a.2⟩)
      (b := ⟨(I.orderIsoOfFin rfl b.1).val, b.2⟩)
    intro hh
    have hij : a.1 = b.1 := (I.orderIsoOfFin rfl).injective
      (Subtype.ext (congrArg Sigma.fst hh))
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    dsimp at hij
    subst j
    have hab' : a = b := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hh
    exact hab (by subst b; rfl)

theorem restrictComponents_mem_support (D : SubcriticalDivision k V)
    (I : Finset (Fin D.componentCount)) (hI : I.Nonempty) (x : V) :
    x ∈ (D.restrictComponents I hI).support ↔ ∃ i ∈ I, x ∈ D.componentSupport i := by
  rw [mem_support_iff]
  change (∃ i j, x ∈ D.parts (I.orderIsoOfFin rfl i).val j) ↔ _
  constructor
  · rintro ⟨i, j, hx⟩
    exact ⟨_, (I.orderIsoOfFin rfl i).property, mem_componentSupport.mpr ⟨j, hx⟩⟩
  · rintro ⟨i, hi, hx⟩
    obtain ⟨j, hj⟩ := mem_componentSupport.mp hx
    obtain ⟨a, ha⟩ := (I.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    have hh := congrArg Subtype.val ha
    refine ⟨a, ?_⟩
    rw [hh]
    exact ⟨j, hj⟩

theorem restrictComponents_samePart (D : SubcriticalDivision k V)
    (I : Finset (Fin D.componentCount)) (hI : I.Nonempty) (x y : V) :
    (D.restrictComponents I hI).SamePart x y ↔
      ∃ i ∈ I, ∃ j, x ∈ D.parts i j ∧ y ∈ D.parts i j := by
  change (∃ a : (D.restrictComponents I hI).PartIndex,
    x ∈ D.parts (I.orderIsoOfFin rfl a.1).val a.2 ∧
    y ∈ D.parts (I.orderIsoOfFin rfl a.1).val a.2) ↔ _
  constructor
  · rintro ⟨⟨i, j⟩, hx, hy⟩
    exact ⟨_, (I.orderIsoOfFin rfl i).property, j, hx, hy⟩
  · rintro ⟨i, hi, j, hx, hy⟩
    obtain ⟨a, ha⟩ := (I.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    have hh := congrArg Subtype.val ha
    rw [Sigma.exists]
    change ∃ a j, x ∈ D.parts (I.orderIsoOfFin rfl a).val j ∧
      y ∈ D.parts (I.orderIsoOfFin rfl a).val j
    refine ⟨a, ?_⟩
    rw [hh]
    exact ⟨j, hx, hy⟩

theorem restrictComponents_activePair (D : SubcriticalDivision k V)
    (I : Finset (Fin D.componentCount)) (hI : I.Nonempty) (x y : V) :
    (D.restrictComponents I hI).ActivePair x y ↔
      ∃ i ∈ I, ∃ a b, (D.core i).graph.Adj a b ∧
        x ∈ D.parts i a ∧ y ∈ D.parts i b := by
  change (∃ i a b, (D.core (I.orderIsoOfFin rfl i).val).graph.Adj a b ∧
    x ∈ D.parts (I.orderIsoOfFin rfl i).val a ∧
    y ∈ D.parts (I.orderIsoOfFin rfl i).val b) ↔ _
  constructor
  · rintro ⟨i, a, b, hab, hx, hy⟩
    exact ⟨_, (I.orderIsoOfFin rfl i).property, a, b, hab, hx, hy⟩
  · rintro ⟨i, hi, a, b, hab, hx, hy⟩
    obtain ⟨j, hj⟩ := (I.orderIsoOfFin rfl).surjective ⟨i, hi⟩
    have hh := congrArg Subtype.val hj
    refine ⟨j, ?_⟩
    rw [hh]
    exact ⟨a, b, hab, hx, hy⟩

end SubcriticalDivision

/-- The finite retained-only normal form, independent of every
component discarded on the complementary vertex set. -/
def retainedKey (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    SubcriticalRetainedKey k V :=
  if h : (D.retainedComponentIndices eta R₀).Nonempty then
    some (D.restrictComponents (D.retainedComponentIndices eta R₀) h) else none

namespace SubcriticalRetainedKey

def support (K : SubcriticalRetainedKey k V) : Finset V := K.elim ∅ (·.support)

def remainder (K : SubcriticalRetainedKey k V) : Finset V := Finset.univ \ K.support

def SamePart (K : SubcriticalRetainedKey k V) (x y : V) : Prop :=
  K.elim False (fun D ↦ D.SamePart x y)

def ActivePair (K : SubcriticalRetainedKey k V) (x y : V) : Prop :=
  K.elim False (fun D ↦ D.ActivePair x y)

@[simp] theorem mem_remainder (K : SubcriticalRetainedKey k V) (x : V) :
    x ∈ K.remainder ↔ x ∉ K.support := by simp [remainder]

end SubcriticalRetainedKey

@[simp] theorem retainedKey_support (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedKey D eta R₀).support = D.retainedVertices eta R₀ := by
  ext x
  rw [D.mem_retainedVertices]
  unfold retainedKey
  split_ifs with h
  · exact D.restrictComponents_mem_support _ h x
  · simp only [SubcriticalRetainedKey.support, Option.elim_none, Finset.notMem_empty,
      false_iff, not_exists, not_and]
    exact fun i hi _ ↦ h ⟨i, hi⟩

@[simp] theorem retainedKey_remainder (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedKey D eta R₀).remainder = D.nonretainedVertices eta R₀ := by
  simp only [SubcriticalRetainedKey.remainder, retainedKey_support,
    SubcriticalDivision.nonretainedVertices]

theorem retainedKey_samePart (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    (retainedKey D eta R₀).SamePart x y ↔
      D.SamePart x y ∧ x ∈ D.retainedVertices eta R₀ := by
  unfold retainedKey
  split_ifs with h
  · rw [SubcriticalRetainedKey.SamePart, Option.elim_some, D.restrictComponents_samePart]
    constructor
    · rintro ⟨i, hi, j, hx, hy⟩
      exact ⟨⟨⟨i, j⟩, hx, hy⟩, (D.mem_retainedVertices eta R₀ x).mpr
        ⟨i, hi, SubcriticalDivision.mem_componentSupport.mpr ⟨j, hx⟩⟩⟩
    · rintro ⟨⟨⟨i, j⟩, hx, hy⟩, hret⟩
      exact ⟨i, (D.mem_retainedVertices_iff_of_mem_componentSupport
        (SubcriticalDivision.mem_componentSupport.mpr ⟨j, hx⟩)).mp hret, j, hx, hy⟩
  · change False ↔ _
    constructor
    · exact False.elim
    · rintro ⟨_, hx⟩
      obtain ⟨i, hi, _⟩ := (D.mem_retainedVertices eta R₀ x).mp hx
      exact h ⟨i, hi⟩

theorem retainedKey_activePair (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    (retainedKey D eta R₀).ActivePair x y ↔
      D.ActivePair x y ∧ x ∈ D.retainedVertices eta R₀ := by
  unfold retainedKey
  split_ifs with h
  · rw [SubcriticalRetainedKey.ActivePair, Option.elim_some, D.restrictComponents_activePair]
    constructor
    · rintro ⟨i, hi, a, b, hab, hx, hy⟩
      exact ⟨⟨i, a, b, hab, hx, hy⟩, (D.mem_retainedVertices eta R₀ x).mpr
        ⟨i, hi, SubcriticalDivision.mem_componentSupport.mpr ⟨a, hx⟩⟩⟩
    · rintro ⟨⟨i, a, b, hab, hx, hy⟩, hret⟩
      exact ⟨i, (D.mem_retainedVertices_iff_of_mem_componentSupport
        (SubcriticalDivision.mem_componentSupport.mpr ⟨a, hx⟩)).mp hret,
        a, b, hab, hx, hy⟩
  · change False ↔ _
    constructor
    · exact False.elim
    · rintro ⟨_, hx⟩
      obtain ⟨i, hi, _⟩ := (D.mem_retainedVertices eta R₀ x).mp hx
      exact h ⟨i, hi⟩

theorem retainedVertices_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    D.retainedVertices eta R₀ = E.retainedVertices eta R₀ := by
  simpa only [retainedKey_support] using congrArg SubcriticalRetainedKey.support h

theorem nonretainedVertices_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    D.nonretainedVertices eta R₀ = E.nonretainedVertices eta R₀ := by
  simpa only [retainedKey_remainder] using congrArg SubcriticalRetainedKey.remainder h

theorem samePart_iff_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) {x y : V}
    (hx : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) :
    D.SamePart x y ↔ E.SamePart x y := by
  have left {x y : V} (hx : x ∈ D.retainedVertices eta R₀) :
      D.SamePart x y ↔ E.SamePart x y := by
    have he : x ∈ E.retainedVertices eta R₀ :=
      retainedVertices_eq_of_retainedKey_eq h ▸ hx
    have hh := congrArg (fun K ↦ K.SamePart x y) h
    simpa only [eq_iff_iff, retainedKey_samePart, hx, he, and_true] using hh
  rcases hx with hx | hy
  · exact left hx
  · rw [D.samePart_comm, E.samePart_comm]
    exact left hy

theorem activePair_iff_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) {x y : V}
    (hx : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) :
    D.ActivePair x y ↔ E.ActivePair x y := by
  have left {x y : V} (hx : x ∈ D.retainedVertices eta R₀) :
      D.ActivePair x y ↔ E.ActivePair x y := by
    have he : x ∈ E.retainedVertices eta R₀ :=
      retainedVertices_eq_of_retainedKey_eq h ▸ hx
    have hh := congrArg (fun K ↦ K.ActivePair x y) h
    simpa only [eq_iff_iff, retainedKey_activePair, hx, he, and_true] using hh
  rcases hx with hx | hy
  · exact left hx
  · rw [D.activePair_comm, E.activePair_comm]
    exact left hy

end InducedStars
