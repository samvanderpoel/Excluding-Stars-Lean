import InducedStars.Graphon.CandidateBlocks
import InducedStars.Structure.Supercritical.Division
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Subcritical divisions

Paper: Definition `dfn:division`.  Component cores are connected regular
graphs; their nonempty parts need not be balanced.  The representation is
independent of the ordering cutoff.  `IsOrderedByCutoff` uses a natural
cutoff, without making an assertion about later real-valued parameters.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

/-- A finite collection of regular-core components with globally disjoint,
nonempty vertex parts.  Vertices not in a part form the sparse remainder. -/
structure SubcriticalDivision (k : ℕ) (V : Type*) [Fintype V]
    [DecidableEq V] where
  componentCount : ℕ
  componentCount_pos : 0 < componentCount
  core : Fin componentCount → RegularBlockCore k
  parts : (i : Fin componentCount) → Fin (core i).order → Finset V
  parts_nonempty : ∀ i j, (parts i j).Nonempty
  parts_pairwiseDisjoint : Set.PairwiseDisjoint
    (Set.univ : Set (Σ i, Fin (core i).order)) (fun a ↦ parts a.1 a.2)

namespace SubcriticalDivision

variable {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]

/-- A component index together with a vertex of its core. -/
abbrev PartIndex (D : SubcriticalDivision k V) := Σ i, Fin (D.core i).order

def part (D : SubcriticalDivision k V) (a : D.PartIndex) : Finset V :=
  D.parts a.1 a.2

def componentSupport (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) : Finset V := Finset.univ.biUnion (D.parts i)

def support (D : SubcriticalDivision k V) : Finset V := Finset.univ.biUnion D.part

def sparse (D : SubcriticalDivision k V) : Finset V := Finset.univ \ D.support

@[simp] theorem mem_componentSupport {D : SubcriticalDivision k V}
    {i : Fin D.componentCount} {v : V} :
    v ∈ D.componentSupport i ↔ ∃ j, v ∈ D.parts i j := by
  simp [componentSupport]

@[simp] theorem mem_support {D : SubcriticalDivision k V} {v : V} :
    v ∈ D.support ↔ ∃ a : D.PartIndex, v ∈ D.part a := by
  simp [support]

theorem mem_support_iff {D : SubcriticalDivision k V} {v : V} :
    v ∈ D.support ↔ ∃ i j, v ∈ D.parts i j := by
  simp [part]

@[simp] theorem mem_sparse {D : SubcriticalDivision k V} {v : V} :
    v ∈ D.sparse ↔ v ∉ D.support := by simp [sparse]

theorem part_nonempty (D : SubcriticalDivision k V) (a : D.PartIndex) :
    (D.part a).Nonempty := D.parts_nonempty a.1 a.2

theorem part_disjoint (D : SubcriticalDivision k V) {a b : D.PartIndex}
    (h : a ≠ b) : Disjoint (D.part a) (D.part b) :=
  D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) h

theorem mem_part_unique (D : SubcriticalDivision k V) {v : V}
    {a b : D.PartIndex} (ha : v ∈ D.part a) (hb : v ∈ D.part b) : a = b := by
  by_contra h
  exact (Finset.disjoint_left.mp (D.part_disjoint h)) ha hb

theorem part_subset_support (D : SubcriticalDivision k V) (a : D.PartIndex) :
    D.part a ⊆ D.support := fun _ h ↦ mem_support.mpr ⟨a, h⟩

theorem componentSupport_subset_support (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) : D.componentSupport i ⊆ D.support := by
  intro v hv
  obtain ⟨j, hj⟩ := mem_componentSupport.mp hv
  exact mem_support.mpr ⟨⟨i, j⟩, hj⟩

theorem componentSupport_nonempty (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) : (D.componentSupport i).Nonempty := by
  obtain ⟨v, hv⟩ := D.parts_nonempty i ⟨0, (D.core i).order_pos⟩
  exact ⟨v, mem_componentSupport.mpr ⟨_, hv⟩⟩

theorem componentSupport_disjoint (D : SubcriticalDivision k V)
    {i j : Fin D.componentCount} (hij : i ≠ j) :
    Disjoint (D.componentSupport i) (D.componentSupport j) := by
  rw [Finset.disjoint_left]
  intro v hi hj
  obtain ⟨a, ha⟩ := mem_componentSupport.mp hi
  obtain ⟨b, hb⟩ := mem_componentSupport.mp hj
  have hab := D.mem_part_unique (a := ⟨i, a⟩) (b := ⟨j, b⟩) ha hb
  exact hij (congrArg Sigma.fst hab)

theorem support_eq_componentSupport_union (D : SubcriticalDivision k V) :
    D.support = Finset.univ.biUnion D.componentSupport := by
  ext v
  simp [part]

@[simp] theorem support_union_sparse (D : SubcriticalDivision k V) :
    D.support ∪ D.sparse = Finset.univ := by
  ext v
  by_cases h : v ∈ D.support <;> simp [h]

theorem support_disjoint_sparse (D : SubcriticalDivision k V) :
    Disjoint D.support D.sparse :=
  Finset.disjoint_left.mpr fun _ hv hs ↦ (mem_sparse.mp hs) hv

@[simp] theorem support_inter_sparse (D : SubcriticalDivision k V) :
    D.support ∩ D.sparse = ∅ := Finset.disjoint_iff_inter_eq_empty.mp
      D.support_disjoint_sparse

theorem sparse_disjoint_part (D : SubcriticalDivision k V) (a : D.PartIndex) :
    Disjoint D.sparse (D.part a) :=
  Finset.disjoint_left.mpr fun _ hs hp ↦ (mem_sparse.mp hs) (D.part_subset_support a hp)

theorem sparse_or_existsUnique_part (D : SubcriticalDivision k V) (v : V) :
    v ∈ D.sparse ∨ ∃! a : D.PartIndex, v ∈ D.part a := by
  by_cases h : v ∈ D.support
  · obtain ⟨a, ha⟩ := mem_support.mp h
    exact Or.inr ⟨a, ha, fun b hb ↦ D.mem_part_unique hb ha⟩
  · exact Or.inl (mem_sparse.mpr h)

theorem card_support (D : SubcriticalDivision k V) :
    D.support.card = ∑ a : D.PartIndex, (D.part a).card := by
  rw [support, Finset.card_biUnion]
  intro a _ b _ hab
  exact D.part_disjoint hab

theorem card_componentSupport (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) :
    (D.componentSupport i).card = ∑ j, (D.parts i j).card := by
  rw [componentSupport, Finset.card_biUnion]
  intro a _ b _ hab
  exact D.part_disjoint (a := ⟨i, a⟩) (b := ⟨i, b⟩) (by simpa using hab)

theorem card_support_add_card_sparse (D : SubcriticalDivision k V) :
    D.support.card + D.sparse.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint D.support_disjoint_sparse]
  simp

theorem card_partIndex_le_card (D : SubcriticalDivision k V) :
    Fintype.card D.PartIndex ≤ Fintype.card V := by
  calc
    Fintype.card D.PartIndex = ∑ _ : D.PartIndex, 1 := by simp
    _ ≤ ∑ a : D.PartIndex, (D.part a).card :=
      Finset.sum_le_sum fun a _ ↦ (D.part_nonempty a).card_pos
    _ = D.support.card := D.card_support.symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

theorem core_order_le_card (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) : (D.core i).order ≤ Fintype.card V := by
  calc
    (D.core i).order = Fintype.card (Fin (D.core i).order) := by simp
    _ ≤ Fintype.card D.PartIndex := Fintype.card_le_of_injective
      (fun j ↦ (⟨i, j⟩ : D.PartIndex)) (by intro a b h; simpa using h)
    _ ≤ Fintype.card V := D.card_partIndex_le_card

theorem componentCount_le_card (D : SubcriticalDivision k V) :
    D.componentCount ≤ Fintype.card V := by
  calc
    D.componentCount = Fintype.card (Fin D.componentCount) := by simp
    _ ≤ Fintype.card D.PartIndex := Fintype.card_le_of_injective
      (fun i ↦ (⟨i, ⟨0, (D.core i).order_pos⟩⟩ : D.PartIndex))
      (fun _ _ h ↦ congrArg Sigma.fst h)
    _ ≤ Fintype.card V := D.card_partIndex_le_card

theorem componentCount_mul_sub_one_le_card (D : SubcriticalDivision k V)
    (hk : 3 ≤ k) : D.componentCount * (k - 1) ≤ Fintype.card V := by
  calc
    D.componentCount * (k - 1) = ∑ _ : Fin D.componentCount, (k - 1) := by simp
    _ ≤ ∑ i : Fin D.componentCount, (D.core i).order :=
      Finset.sum_le_sum fun i _ ↦ (D.core i).k_sub_one_le_order hk
    _ = Fintype.card D.PartIndex := by simp [Fintype.card_sigma]
    _ ≤ Fintype.card V := D.card_partIndex_le_card

/-- Vertices in the same clique part; this relation includes its diagonal
precisely on the support. -/
def SamePart (D : SubcriticalDivision k V) (x y : V) : Prop :=
  ∃ a : D.PartIndex, x ∈ D.part a ∧ y ∈ D.part a

/-- Vertices in distinct parts joined by an edge of their common core. -/
def ActivePair (D : SubcriticalDivision k V) (x y : V) : Prop :=
  ∃ (i : Fin D.componentCount) (a b : Fin (D.core i).order),
    (D.core i).graph.Adj a b ∧ x ∈ D.parts i a ∧ y ∈ D.parts i b

/-- Active geometry on the global part index, before choosing vertices. -/
def ActivePart (D : SubcriticalDivision k V) (a b : D.PartIndex) : Prop :=
  ∃ (i : Fin D.componentCount) (u v : Fin (D.core i).order),
    a = ⟨i, u⟩ ∧ b = ⟨i, v⟩ ∧ (D.core i).graph.Adj u v

theorem samePart_iff_of_mem_parts (D : SubcriticalDivision k V)
    {a b : D.PartIndex} {x y : V} (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    D.SamePart x y ↔ a = b := by
  constructor
  · rintro ⟨c, hxc, hyc⟩
    exact (D.mem_part_unique hx hxc).trans (D.mem_part_unique hyc hy)
  · rintro rfl
    exact ⟨a, hx, hy⟩

theorem activePair_iff_of_mem_parts (D : SubcriticalDivision k V)
    {a b : D.PartIndex} {x y : V} (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    D.ActivePair x y ↔ D.ActivePart a b := by
  constructor
  · rintro ⟨i, u, v, huv, hxu, hyv⟩
    exact ⟨i, u, v, D.mem_part_unique (b := ⟨i, u⟩) hx hxu,
      D.mem_part_unique (b := ⟨i, v⟩) hy hyv, huv⟩
  · rintro ⟨i, u, v, rfl, rfl, huv⟩
    exact ⟨i, u, v, huv, hx, hy⟩

@[simp] theorem activePart_mk_mk (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (u v : Fin (D.core i).order) :
    D.ActivePart ⟨i, u⟩ ⟨i, v⟩ ↔ (D.core i).graph.Adj u v := by
  constructor
  · rintro ⟨j, a, b, ha, hb, hab⟩
    have hij : i = j := congrArg Sigma.fst ha
    subst j
    have hua : u = a := by simpa using ha
    have hvb : v = b := by simpa using hb
    simpa [hua, hvb] using hab
  · intro huv
    exact ⟨i, u, v, rfl, rfl, huv⟩

theorem activePart_same_component {D : SubcriticalDivision k V}
    {a b : D.PartIndex} (h : D.ActivePart a b) : a.1 = b.1 := by
  obtain ⟨i, u, v, rfl, rfl, _⟩ := h
  rfl

theorem samePart_comm (D : SubcriticalDivision k V) (x y : V) :
    D.SamePart x y ↔ D.SamePart y x := by
  constructor <;> rintro ⟨a, hx, hy⟩ <;> exact ⟨a, hy, hx⟩

theorem activePair_comm (D : SubcriticalDivision k V) (x y : V) :
    D.ActivePair x y ↔ D.ActivePair y x := by
  constructor <;> rintro ⟨i, a, b, hab, hx, hy⟩ <;> exact ⟨i, b, a, hab.symm, hy, hx⟩

theorem samePart_imp_support {D : SubcriticalDivision k V} {x y : V}
    (h : D.SamePart x y) : x ∈ D.support ∧ y ∈ D.support := by
  obtain ⟨a, hx, hy⟩ := h
  exact ⟨D.part_subset_support a hx, D.part_subset_support a hy⟩

theorem activePair_imp_support {D : SubcriticalDivision k V} {x y : V}
    (h : D.ActivePair x y) : x ∈ D.support ∧ y ∈ D.support := by
  obtain ⟨i, a, b, _, hx, hy⟩ := h
  exact ⟨D.part_subset_support ⟨i, a⟩ hx, D.part_subset_support ⟨i, b⟩ hy⟩

@[simp] theorem samePart_self (D : SubcriticalDivision k V) (x : V) :
    D.SamePart x x ↔ x ∈ D.support := by simp [SamePart]

theorem not_activePair_of_samePart {D : SubcriticalDivision k V} {x y : V}
    (h : D.SamePart x y) : ¬ D.ActivePair x y := by
  obtain ⟨c, hx, hy⟩ := h
  rintro ⟨i, a, b, hab, hxa, hyb⟩
  have hea := D.mem_part_unique (b := ⟨i, a⟩) hx hxa
  have heb := D.mem_part_unique (b := ⟨i, b⟩) hy hyb
  have : (⟨i, a⟩ : D.PartIndex) = ⟨i, b⟩ := hea.symm.trans heb
  have : a = b := by simpa using this
  exact hab.ne this

@[simp] theorem not_activePair_self (D : SubcriticalDivision k V) (x : V) :
    ¬ D.ActivePair x x := by
  intro h
  exact not_activePair_of_samePart ((D.samePart_self x).mpr (activePair_imp_support h).1) h

/-- A component is visible if at least one of its parts crosses the size
threshold.  This does not assert a lower bound for every visible part. -/
def visibleComponentIndices (D : SubcriticalDivision k V) (theta : ℝ) :
    Finset (Fin D.componentCount) :=
  Finset.univ.filter fun i ↦ ∃ j, theta * Fintype.card V ≤ (D.parts i j).card

/-- All parts of every visible component, including its smaller parts. -/
def visiblePartIndices (D : SubcriticalDivision k V) (theta : ℝ) :
    Finset D.PartIndex := Finset.univ.filter fun a ↦ a.1 ∈ D.visibleComponentIndices theta

@[simp] theorem mem_visibleComponentIndices (D : SubcriticalDivision k V)
    (theta : ℝ) (i : Fin D.componentCount) :
    i ∈ D.visibleComponentIndices theta ↔
      ∃ j, theta * Fintype.card V ≤ (D.parts i j).card := by simp [visibleComponentIndices]

@[simp] theorem mem_visiblePartIndices (D : SubcriticalDivision k V)
    (theta : ℝ) (a : D.PartIndex) :
    a ∈ D.visiblePartIndices theta ↔ a.1 ∈ D.visibleComponentIndices theta := by
  simp [visiblePartIndices]

/-- Reorder components while retaining every core and vertex part. -/
def reindex (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) : SubcriticalDivision k V where
  componentCount := D.componentCount
  componentCount_pos := D.componentCount_pos
  core i := D.core (e i)
  parts i j := D.parts (e i) j
  parts_nonempty i j := D.parts_nonempty (e i) j
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    apply D.part_disjoint (a := ⟨e a.1, a.2⟩) (b := ⟨e b.1, b.2⟩)
    intro h
    have hf := e.injective (congrArg Sigma.fst h)
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    dsimp at hf
    subst j
    have : a = b := by simpa using h
    subst b
    exact hab rfl

@[simp] theorem reindex_componentSupport (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) (i : Fin D.componentCount) :
    (D.reindex e).componentSupport i = D.componentSupport (e i) := rfl

@[simp] theorem reindex_support (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) : (D.reindex e).support = D.support := by
  ext v
  simp only [mem_support_iff]
  change (∃ i j, v ∈ D.parts (e i) j) ↔ ∃ i j, v ∈ D.parts i j
  constructor
  · rintro ⟨i, h⟩
    exact ⟨e i, h⟩
  · rintro ⟨i, h⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, h⟩

@[simp] theorem reindex_sparse (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) : (D.reindex e).sparse = D.sparse := by
  simp [sparse]

@[simp] theorem reindex_samePart (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) (x y : V) :
    (D.reindex e).SamePart x y ↔ D.SamePart x y := by
  simp only [SamePart, part, Sigma.exists]
  change (∃ i j, x ∈ D.parts (e i) j ∧ y ∈ D.parts (e i) j) ↔
    ∃ i j, x ∈ D.parts i j ∧ y ∈ D.parts i j
  constructor
  · rintro ⟨i, h⟩
    exact ⟨e i, h⟩
  · rintro ⟨i, h⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, h⟩

@[simp] theorem reindex_activePair (D : SubcriticalDivision k V)
    (e : Equiv.Perm (Fin D.componentCount)) (x y : V) :
    (D.reindex e).ActivePair x y ↔ D.ActivePair x y := by
  change (∃ i a b, (D.core (e i)).graph.Adj a b ∧
    x ∈ D.parts (e i) a ∧ y ∈ D.parts (e i) b) ↔
      ∃ i a b, (D.core i).graph.Adj a b ∧ x ∈ D.parts i a ∧ y ∈ D.parts i b
  constructor
  · rintro ⟨i, h⟩
    exact ⟨e i, h⟩
  · rintro ⟨i, h⟩
    obtain ⟨j, rfl⟩ := e.surjective i
    exact ⟨j, h⟩

/-- The paper's ordering: small cores first, and nonincreasing component
sizes within either core-size class. -/
def IsOrderedByCutoff (D : SubcriticalDivision k V) (R0 : ℕ) : Prop :=
  ∀ i j : Fin D.componentCount, i ≤ j →
    ((D.core j).order ≤ R0 → (D.core i).order ≤ R0) ∧
    (((D.core i).order ≤ R0 ↔ (D.core j).order ≤ R0) →
      (D.componentSupport j).card ≤ (D.componentSupport i).card)

/-- A bounded natural sorting key; the gap separates the two size classes. -/
def orderingKey (D : SubcriticalDivision k V) (R0 : ℕ)
    (i : Fin D.componentCount) : ℕ :=
  (if (D.core i).order ≤ R0 then 0 else Fintype.card V + 1) +
    (Fintype.card V - (D.componentSupport i).card)

def orderingPermutation (D : SubcriticalDivision k V) (R0 : ℕ) :
    Equiv.Perm (Fin D.componentCount) := Tuple.sort (D.orderingKey R0)

theorem reindex_orderingPermutation_isOrdered (D : SubcriticalDivision k V)
    (R0 : ℕ) : (D.reindex (D.orderingPermutation R0)).IsOrderedByCutoff R0 := by
  intro i j hij
  have hkey := Tuple.monotone_sort (D.orderingKey R0) hij
  change D.orderingKey R0 (D.orderingPermutation R0 i) ≤
    D.orderingKey R0 (D.orderingPermutation R0 j) at hkey
  have hi := Finset.card_le_univ (D.componentSupport (D.orderingPermutation R0 i))
  have hj := Finset.card_le_univ (D.componentSupport (D.orderingPermutation R0 j))
  change ((D.core (D.orderingPermutation R0 j)).order ≤ R0 →
    (D.core (D.orderingPermutation R0 i)).order ≤ R0) ∧
    (((D.core (D.orderingPermutation R0 i)).order ≤ R0 ↔
      (D.core (D.orderingPermutation R0 j)).order ≤ R0) →
    (D.componentSupport (D.orderingPermutation R0 j)).card ≤
      (D.componentSupport (D.orderingPermutation R0 i)).card)
  unfold orderingKey at hkey
  split_ifs at hkey <;> omega

theorem exists_ordered_reindex (D : SubcriticalDivision k V) (R0 : ℕ) :
    ∃ e : Equiv.Perm (Fin D.componentCount), (D.reindex e).IsOrderedByCutoff R0 :=
  ⟨D.orderingPermutation R0, D.reindex_orderingPermutation_isOrdered R0⟩

/-- The one-component adapter retains all supercritical parts and sparse
vertices.  Its core is the complete graph on `k-1` vertices. -/
def ofSupercritical (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    SubcriticalDivision k V where
  componentCount := 1
  componentCount_pos := Nat.zero_lt_one
  core _ := RegularBlockCore.complete k hk
  parts _ j := D.parts j
  parts_nonempty _ j := D.parts_nonempty j
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    apply D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
    intro hj
    rcases a with ⟨i, a⟩
    rcases b with ⟨j, b⟩
    have : i = j := Subsingleton.elim _ _
    subst j
    dsimp at hj
    subst b
    exact hab rfl

theorem ofSupercritical_isOrdered (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (R0 : ℕ) : (ofSupercritical hk D).IsOrderedByCutoff R0 := by
  intro i j _
  have : i = j := @Subsingleton.elim (Fin 1) inferInstance i j
  subst j
  exact ⟨fun h ↦ h, fun _ ↦ le_rfl⟩

theorem exists_of_sub_one_le_card (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) : Nonempty (SubcriticalDivision k V) := by
  obtain ⟨D⟩ := SupercriticalDivision.exists_of_sub_one_le_card (k := k) hcard
  exact ⟨ofSupercritical hk D⟩

theorem exists_ordered_of_sub_one_le_card (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) (R0 : ℕ) :
    ∃ D : SubcriticalDivision k V, D.IsOrderedByCutoff R0 := by
  obtain ⟨D⟩ := SupercriticalDivision.exists_of_sub_one_le_card (k := k) hcard
  exact ⟨ofSupercritical hk D, ofSupercritical_isOrdered hk D R0⟩

/-- A fallback division with singleton parts.  Repairing a graph with
respect to this division never needs to insert an edge. -/
theorem exists_ordered_singleton_parts (hk : 3 ≤ k)
    (hcard : k - 1 ≤ Fintype.card V) (R0 : ℕ) :
    ∃ D : SubcriticalDivision k V, D.IsOrderedByCutoff R0 ∧
      ∀ a : D.PartIndex, (D.part a).card = 1 := by
  obtain ⟨e : Fin (k - 1) ↪ V⟩ :=
    Function.Embedding.nonempty_of_card_le (α := Fin (k - 1)) (β := V)
      (by simpa only [Fintype.card_fin] using hcard)
  let D : SupercriticalDivision k V := {
    parts := fun i ↦ {e i}
    parts_nonempty := fun _ ↦ Finset.singleton_nonempty _
    parts_pairwiseDisjoint := by
      intro i _ j _ hij
      exact Finset.disjoint_singleton.mpr (e.injective.ne hij)
  }
  refine ⟨ofSupercritical hk D, ofSupercritical_isOrdered hk D R0, ?_⟩
  intro a
  simp [part, ofSupercritical, D]

/-- Transport the entire division, not a choice of canonical minimizer,
along an actual vertex equivalence. -/
def relabel [Fintype W] [DecidableEq W] (D : SubcriticalDivision k V)
    (e : V ≃ W) : SubcriticalDivision k W where
  componentCount := D.componentCount
  componentCount_pos := D.componentCount_pos
  core := D.core
  parts i j := (D.parts i j).map e.toEmbedding
  parts_nonempty i j := (D.parts_nonempty i j).map
  parts_pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint ((D.part a).map e.toEmbedding) ((D.part b).map e.toEmbedding)
    exact (Finset.disjoint_map e.toEmbedding).mpr (D.part_disjoint hab)

@[simp] theorem mem_relabel_part [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W)
    (i : Fin D.componentCount) (j : Fin (D.core i).order) (w : W) :
    w ∈ (D.relabel e).parts i j ↔ e.symm w ∈ D.parts i j := by simp [relabel]

@[simp] theorem mem_relabel_support [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (w : W) :
    w ∈ (D.relabel e).support ↔ e.symm w ∈ D.support := by
  simp [part, relabel]

@[simp] theorem mem_relabel_sparse [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (w : W) :
    w ∈ (D.relabel e).sparse ↔ e.symm w ∈ D.sparse := by
  rw [mem_sparse, mem_sparse, mem_relabel_support]

@[simp] theorem relabel_samePart [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (x y : W) :
    (D.relabel e).SamePart x y ↔ D.SamePart (e.symm x) (e.symm y) := by
  simp [SamePart, part, Sigma.exists, relabel]

@[simp] theorem relabel_activePair [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (x y : W) :
    (D.relabel e).ActivePair x y ↔ D.ActivePair (e.symm x) (e.symm y) := by
  simp [ActivePair, relabel]

@[simp] theorem relabel_card_componentSupport [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (i : Fin D.componentCount) :
    ((D.relabel e).componentSupport i).card = (D.componentSupport i).card := by
  rw [(D.relabel e).card_componentSupport i, D.card_componentSupport i]
  simp [relabel]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem relabel_isOrderedByCutoff [Fintype W] [DecidableEq W]
    (D : SubcriticalDivision k V) (e : V ≃ W) (R0 : ℕ) :
    (D.relabel e).IsOrderedByCutoff R0 ↔ D.IsOrderedByCutoff R0 := by
  simp only [IsOrderedByCutoff, relabel_card_componentSupport]
  rfl

/-! Finiteness follows from the already-proved bounds, rather than a
postulated enumeration of divisions.  The finite encoding retains the
labelled core graph and every actual part. -/

private def boundedCoreCode (n : ℕ) (C : {C : RegularBlockCore k // C.order ≤ n}) :
    Σ q : Fin (n + 1), SimpleGraph (Fin q.val) :=
  ⟨⟨C.val.order, Nat.lt_succ_of_le C.property⟩, C.val.graph⟩

private theorem boundedCoreCode_injective (n : ℕ) :
    Function.Injective (boundedCoreCode (k := k) n) := by
  rintro ⟨⟨q, hq, G, hG, hr⟩, hb⟩ ⟨⟨q', hq', G', hG', hr'⟩, hb'⟩ h
  have hqeq : q = q' := congrArg (fun z ↦ z.1.val) h
  subst q'
  have hGG : G = G' := by simpa [boundedCoreCode] using h
  subst G'
  rfl

private instance boundedCore_finite (n : ℕ) :
    Finite {C : RegularBlockCore k // C.order ≤ n} :=
  Finite.of_injective (boundedCoreCode n) (boundedCoreCode_injective n)

private abbrev DivisionCode (k : ℕ) (V : Type*) [Fintype V] :=
  Σ l : Fin (Fintype.card V + 1),
    Σ C : Fin l.val → {C : RegularBlockCore k // C.order ≤ Fintype.card V},
      (i : Fin l.val) → Fin (C i).val.order → Finset V

private def divisionCode (D : SubcriticalDivision k V) : DivisionCode k V :=
  ⟨⟨D.componentCount, Nat.lt_succ_of_le D.componentCount_le_card⟩,
    (fun i ↦ ⟨D.core i, D.core_order_le_card i⟩), D.parts⟩

private theorem divisionCode_injective :
    Function.Injective (divisionCode (k := k) (V := V)) := by
  intro D E h
  have hc : D.componentCount = E.componentCount := congrArg (fun z ↦ z.1.val) h
  rcases D with ⟨l, hl, C, P, hp, hd⟩
  rcases E with ⟨l', hl', C', P', hp', hd'⟩
  dsimp at hc
  subst l'
  have hrest := (Sigma.mk.inj h).2
  have hcodes :
      (fun i ↦ (⟨C i, (SubcriticalDivision.mk l hl C P hp hd).core_order_le_card i⟩ :
        {C : RegularBlockCore k // C.order ≤ Fintype.card V})) =
      (fun i ↦ (⟨C' i, (SubcriticalDivision.mk l hl' C' P' hp' hd').core_order_le_card i⟩ :
        {C : RegularBlockCore k // C.order ≤ Fintype.card V})) := by
    exact congrArg Sigma.fst (eq_of_heq hrest)
  have hC : C = C' := by
    funext i
    exact congrArg Subtype.val (congrFun hcodes i)
  subst C'
  have hPP : P = P' := by simpa [divisionCode] using h
  subst P'
  rfl

/-- There are only finitely many divisions on a fixed finite vertex set. -/
instance finite : Finite (SubcriticalDivision k V) :=
  Finite.of_injective divisionCode divisionCode_injective

end SubcriticalDivision
end InducedStars
