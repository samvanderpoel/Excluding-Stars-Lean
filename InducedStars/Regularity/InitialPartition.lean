import InducedStars.Regularity.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Order.Partition.Equipartition

/-!
# Equitable initial partitions

This file packages the paper's indexed equitable vertex partitions on top of
Mathlib's `Finpartition`.  The wrapper retains Mathlib's useful partition
infrastructure while exposing the paper-facing family `Fin s → Finset V`.
-/

open Finset

namespace InducedStars.Regularity

universe u

section FinsetChoice

variable {V : Type u}

/-- A fixed subset of `A` having any prescribed cardinality at most `#A`. -/
noncomputable def chosenSubsetOfCard (A : Finset V) (m : ℕ) (h : m ≤ A.card) : Finset V := by
  classical
  exact (A.exists_subset_card_eq h).choose

theorem chosenSubsetOfCard_subset (A : Finset V) (m : ℕ) (h : m ≤ A.card) :
    chosenSubsetOfCard A m h ⊆ A := by
  classical
  exact (A.exists_subset_card_eq h).choose_spec.1

@[simp]
theorem card_chosenSubsetOfCard (A : Finset V) (m : ℕ) (h : m ≤ A.card) :
    (chosenSubsetOfCard A m h).card = m := by
  classical
  exact (A.exists_subset_card_eq h).choose_spec.2

end FinsetChoice

section IndexedFinpartition

variable {V : Type u} [Fintype V] [DecidableEq V] {s : ℕ}

/-- Build a partition of the whole finite vertex type from an indexed,
pairwise-disjoint, nonempty covering family. -/
def indexedFinpartition (parts : Fin s → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parts)
    (hcover : Finset.univ.biUnion parts = (Finset.univ : Finset V)) :
    Finpartition (Finset.univ : Finset V) := by
  refine Finpartition.ofExistsUnique (Finset.univ.image parts)
    (fun p _ ↦ Finset.subset_univ p) ?_ ?_
  · intro x _
    have hx : x ∈ Finset.univ.biUnion parts := by
      rw [hcover]
      exact Finset.mem_univ x
    rw [Finset.mem_biUnion] at hx
    obtain ⟨i, _, hxi⟩ := hx
    refine ⟨parts i, ⟨Finset.mem_image_of_mem parts (Finset.mem_univ i), hxi⟩, ?_⟩
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq.1
    by_cases hij : i = j
    · simp [hij]
    · exact (Finset.disjoint_left.mp
        (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hxi hq.2).elim
  · intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    exact (hnonempty i).ne_empty hi

@[simp]
theorem indexedFinpartition_parts (parts : Fin s → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parts)
    (hcover : Finset.univ.biUnion parts = (Finset.univ : Finset V)) :
    (indexedFinpartition parts hnonempty hdisjoint hcover).parts = Finset.univ.image parts :=
  rfl

end IndexedFinpartition

/-- An equitable partition of the vertex set into `s` indexed, nonempty
parts.  The equivalence records an indexing of every Mathlib partition part,
without duplicating its disjointness and cover invariants. -/
structure EquitableInitialPartition (V : Type u) [Fintype V] [DecidableEq V] (s : ℕ) where
  partition : Finpartition (Finset.univ : Finset V)
  indexEquiv : Fin s ≃ partition.parts
  equitable : partition.IsEquipartition

namespace EquitableInitialPartition

variable {V : Type u} [Fintype V] [DecidableEq V] {s : ℕ}

/-- The `i`th part of an indexed equitable partition. -/
def parts (P : EquitableInitialPartition V s) (i : Fin s) : Finset V :=
  (P.indexEquiv i).1

@[simp]
theorem parts_mem_partition (P : EquitableInitialPartition V s) (i : Fin s) :
    P.parts i ∈ P.partition.parts :=
  (P.indexEquiv i).2

theorem parts_nonempty (P : EquitableInitialPartition V s) (i : Fin s) :
    (P.parts i).Nonempty :=
  P.partition.nonempty_of_mem_parts (P.parts_mem_partition i)

theorem parts_subset_univ (P : EquitableInitialPartition V s) (i : Fin s) :
    P.parts i ⊆ (Finset.univ : Finset V) :=
  P.partition.subset (P.parts_mem_partition i)

theorem parts_injective (P : EquitableInitialPartition V s) : Function.Injective P.parts := by
  intro i j hij
  apply P.indexEquiv.injective
  exact Subtype.ext hij

@[simp]
theorem parts_inj (P : EquitableInitialPartition V s) {i j : Fin s} :
    P.parts i = P.parts j ↔ i = j :=
  P.parts_injective.eq_iff

theorem mem_partition_iff (P : EquitableInitialPartition V s) (A : Finset V) :
    A ∈ P.partition.parts ↔ ∃ i : Fin s, P.parts i = A := by
  constructor
  · intro hA
    obtain ⟨i, hi⟩ := P.indexEquiv.surjective ⟨A, hA⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  · rintro ⟨i, rfl⟩
    exact P.parts_mem_partition i

theorem parts_pairwiseDisjoint (P : EquitableInitialPartition V s) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin s)) P.parts := by
  intro i _ j _ hij
  exact P.partition.disjoint (P.parts_mem_partition i) (P.parts_mem_partition j)
    (P.parts_injective.ne hij)

theorem parts_disjoint (P : EquitableInitialPartition V s) {i j : Fin s} (hij : i ≠ j) :
    Disjoint (P.parts i) (P.parts j) :=
  P.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij

@[simp]
theorem cover (P : EquitableInitialPartition V s) :
    Finset.univ.biUnion P.parts = (Finset.univ : Finset V) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · exact fun _ ↦ trivial
  · intro _
    obtain ⟨A, hA, hxA⟩ := P.partition.exists_mem (Finset.mem_univ x)
    obtain ⟨i, hi⟩ := P.indexEquiv.surjective ⟨A, hA⟩
    refine ⟨i, ?_⟩
    have hi' : P.parts i = A := by
      change (P.indexEquiv i).1 = A
      exact congrArg Subtype.val hi
    simpa only [hi'] using hxA

theorem exists_mem_part (P : EquitableInitialPartition V s) (x : V) :
    ∃ i : Fin s, x ∈ P.parts i := by
  have hx : x ∈ Finset.univ.biUnion P.parts := by
    rw [P.cover]
    exact Finset.mem_univ x
  simpa only [Finset.mem_biUnion, Finset.mem_univ, true_and] using hx

theorem existsUnique_mem_part (P : EquitableInitialPartition V s) (x : V) :
    ∃! i : Fin s, x ∈ P.parts i := by
  obtain ⟨i, hxi⟩ := P.exists_mem_part x
  refine ⟨i, hxi, ?_⟩
  intro j hxj
  by_contra hij
  exact Finset.disjoint_left.mp
    (P.parts_disjoint (i := j) (j := i) hij) hxj hxi

@[simp]
theorem card_partition_parts (P : EquitableInitialPartition V s) :
    P.partition.parts.card = s := by
  simpa using (Fintype.card_congr P.indexEquiv).symm

theorem sum_card_parts (P : EquitableInitialPartition V s) :
    ∑ i : Fin s, (P.parts i).card = Fintype.card V := by
  calc
    ∑ i : Fin s, (P.parts i).card =
        ∑ A : P.partition.parts, A.1.card := by
          exact P.indexEquiv.sum_comp (fun A : P.partition.parts ↦ A.1.card)
    _ = ∑ A ∈ P.partition.parts, A.card := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach P.partition.parts (fun A ↦ A.card))
    _ = (Finset.univ : Finset V).card := P.partition.sum_card_parts
    _ = Fintype.card V := Finset.card_univ

theorem partCount_le_card (P : EquitableInitialPartition V s) :
    s ≤ Fintype.card V := by
  rw [← P.card_partition_parts, ← Finset.card_univ]
  exact P.partition.card_parts_le_card

theorem partCount_pos_of_card_pos (P : EquitableInitialPartition V s)
    (hV : 0 < Fintype.card V) : 0 < s := by
  by_contra hs
  have hs0 : s = 0 := Nat.eq_zero_of_not_pos hs
  subst s
  have hsum := P.sum_card_parts
  simp at hsum
  omega

theorem partCount_pos (P : EquitableInitialPartition V s) [Nonempty V] : 0 < s :=
  P.partCount_pos_of_card_pos Fintype.card_pos

@[simp]
theorem partCount_eq_zero_iff (P : EquitableInitialPartition V s) :
    s = 0 ↔ Fintype.card V = 0 := by
  constructor
  · intro hs
    subst s
    have hsum := P.sum_card_parts
    simpa using hsum.symm
  · intro hV
    exact Nat.eq_zero_of_le_zero (hV ▸ P.partCount_le_card)

theorem balanced (P : EquitableInitialPartition V s) (i j : Fin s) :
    Nat.dist (P.parts i).card (P.parts j).card ≤ 1 := by
  have hij := P.equitable (P.parts_mem_partition i) (P.parts_mem_partition j)
  have hji := P.equitable (P.parts_mem_partition j) (P.parts_mem_partition i)
  unfold Nat.dist
  omega

theorem average_le_card_part (P : EquitableInitialPartition V s) (i : Fin s) :
    Fintype.card V / s ≤ (P.parts i).card := by
  have h := P.equitable.average_le_card_part (P.parts_mem_partition i)
  simpa using h

theorem card_part_le_average_add_one (P : EquitableInitialPartition V s) (i : Fin s) :
    (P.parts i).card ≤ Fintype.card V / s + 1 := by
  have h := P.equitable.card_part_le_average_add_one (P.parts_mem_partition i)
  simpa using h

theorem card_part_eq_average_or_add_one (P : EquitableInitialPartition V s) (i : Fin s) :
    (P.parts i).card = Fintype.card V / s ∨
      (P.parts i).card = Fintype.card V / s + 1 := by
  have h := P.equitable.card_parts_eq_average (P.parts_mem_partition i)
  simpa using h

/-- Construct an equitable indexed initial partition from its semantic data. -/
noncomputable def ofParts (parts : Fin s → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parts)
    (hcover : Finset.univ.biUnion parts = (Finset.univ : Finset V))
    (hbalanced : ∀ i j, Nat.dist (parts i).card (parts j).card ≤ 1) :
    EquitableInitialPartition V s := by
  let Q := indexedFinpartition parts hnonempty hdisjoint hcover
  let toPart : Fin s → Q.parts := fun i ↦
    ⟨parts i, by
      rw [indexedFinpartition_parts]
      exact Finset.mem_image_of_mem parts (Finset.mem_univ i)⟩
  have htoPart_injective : Function.Injective toPart := by
    intro i j hij
    by_contra hne
    have hd := hdisjoint (Set.mem_univ i) (Set.mem_univ j) hne
    have heq : parts i = parts j := congrArg Subtype.val hij
    obtain ⟨x, hx⟩ := hnonempty i
    exact Finset.disjoint_left.mp hd hx (heq ▸ hx)
  have htoPart_surjective : Function.Surjective toPart := by
    rintro ⟨A, hA⟩
    rw [indexedFinpartition_parts] at hA
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hA
    exact ⟨i, Subtype.ext hi⟩
  let e : Fin s ≃ Q.parts := Equiv.ofBijective toPart
    ⟨htoPart_injective, htoPart_surjective⟩
  refine ⟨Q, e, ?_⟩
  intro A B hA hB
  obtain ⟨i, hi⟩ := htoPart_surjective ⟨A, hA⟩
  obtain ⟨j, hj⟩ := htoPart_surjective ⟨B, hB⟩
  have hdist := hbalanced i j
  have hAi : A = parts i := congrArg Subtype.val hi.symm
  have hBj : B = parts j := congrArg Subtype.val hj.symm
  rw [hAi, hBj]
  unfold Nat.dist at hdist
  omega

@[simp]
theorem parts_ofParts (parts : Fin s → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin s)) parts)
    (hcover : Finset.univ.biUnion parts = (Finset.univ : Finset V))
    (hbalanced : ∀ i j, Nat.dist (parts i).card (parts j).card ≤ 1)
    (i : Fin s) :
    (ofParts parts hnonempty hdisjoint hcover hbalanced).parts i = parts i := by
  unfold ofParts EquitableInitialPartition.parts
  change parts i = parts i
  rfl

end EquitableInitialPartition

end InducedStars.Regularity
