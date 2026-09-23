import DenseGraph.Combinatorics.ExponentialSums
import DenseGraph.FiniteModels.CoverUniqueness
import InducedStars.Structure.Supercritical.CoPartiteFamilies
import InducedStars.Structure.Supercritical.ProfileReindexing

/-!
# Ordered clique covers and their multiplicity

This file enumerates supercritical divisions and supplies the finite
cover-comparison infrastructure used in the strictly supercritical count.
Part labels are bookkeeping only: cover uniqueness is always stated modulo a
permutation of the `k - 1` main parts.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance coverMultiplicityGraphDecidableEq (n : Nat) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

noncomputable local instance coverMultiplicityEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance coverMultiplicityDivisionDecidableEq
    (k n : Nat) : DecidableEq (SupercriticalDivision k (Fin n)) :=
  Classical.decEq _

/-! ## Encoding and enumerating divisions -/

namespace SupercriticalDivision

variable {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]

/-- Canonical vertex label of a division: `none` means sparse, while
`some i` records membership in the unique main part `i`. -/
noncomputable def assignment (D : SupercriticalDivision k V) :
    V → Option (Fin (k - 1)) := fun v ↦
  if h : ∃ i, v ∈ D.parts i then some (Classical.choose h) else none

@[simp] theorem assignment_eq_some_iff
    (D : SupercriticalDivision k V) (v : V) (i : Fin (k - 1)) :
    D.assignment v = some i ↔ v ∈ D.parts i := by
  classical
  unfold assignment
  split_ifs with h
  · constructor
    · intro heq
      have hi : Classical.choose h = i := Option.some.inj heq
      simpa [hi] using Classical.choose_spec h
    · intro hvi
      congr 1
      exact D.mem_part_unique (Classical.choose_spec h) hvi
  · constructor
    · intro heq
      cases heq
    · intro hvi
      exact False.elim (h ⟨i, hvi⟩)

@[simp] theorem assignment_eq_none_iff
    (D : SupercriticalDivision k V) (v : V) :
    D.assignment v = none ↔ v ∈ D.sparse := by
  classical
  rw [D.mem_sparse]
  simp only [D.mem_support, not_exists]
  constructor
  · intro hn i hi
    have := D.assignment_eq_some_iff v i |>.2 hi
    simp [hn] at this
  · intro hnone
    unfold assignment
    simp [hnone]

theorem ext_parts {D E : SupercriticalDivision k V}
    (h : D.parts = E.parts) : D = E := by
  cases D with
  | mk parts parts_nonempty parts_pairwiseDisjoint =>
      cases E with
      | mk parts' parts_nonempty' parts_pairwiseDisjoint' =>
          simp only [SupercriticalDivision.mk.injEq]
          exact h

theorem assignment_injective :
    Function.Injective
      (@SupercriticalDivision.assignment k V _ _ ) := by
  classical
  intro D E h
  apply ext_parts
  funext i
  ext v
  rw [← D.assignment_eq_some_iff v i,
    ← E.assignment_eq_some_iff v i, h]

/-- An assignment is admissible when every main-part label is used. -/
def AssignmentUsesEveryPart (a : V → Option (Fin (k - 1))) : Prop :=
  ∀ i, ∃ v, a v = some i

instance (a : V → Option (Fin (k - 1))) :
    Decidable (AssignmentUsesEveryPart a) := Classical.propDecidable _

/-- Decode an admissible assignment into the corresponding division. -/
def ofAssignment (a : V → Option (Fin (k - 1)))
    (ha : AssignmentUsesEveryPart a) : SupercriticalDivision k V where
  parts i := Finset.univ.filter fun v ↦ a v = some i
  parts_nonempty i := by
    obtain ⟨v, hv⟩ := ha i
    exact ⟨v, by simp [hv]⟩
  parts_pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint
      (Finset.univ.filter fun v ↦ a v = some i)
      (Finset.univ.filter fun v ↦ a v = some j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvi hvj
    exact hij (Option.some.inj (hvi.symm.trans hvj))

theorem assignment_usesEveryPart (D : SupercriticalDivision k V) :
    AssignmentUsesEveryPart D.assignment := by
  intro i
  obtain ⟨v, hv⟩ := D.parts_nonempty i
  exact ⟨v, D.assignment_eq_some_iff v i |>.2 hv⟩

@[simp] theorem ofAssignment_assignment (D : SupercriticalDivision k V) :
    ofAssignment D.assignment D.assignment_usesEveryPart = D := by
  apply ext_parts
  funext i
  ext v
  simp [ofAssignment, assignment_eq_some_iff]

end SupercriticalDivision

/-- Every division on `Fin n`, enumerated extensionally as a structure. -/
noncomputable def allSupercriticalDivisions (k n : Nat) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact Finset.univ.image fun a :
      {a : Fin n → Option (Fin (k - 1)) //
        SupercriticalDivision.AssignmentUsesEveryPart a} ↦
    SupercriticalDivision.ofAssignment a.1 a.2

@[simp] theorem mem_allSupercriticalDivisions
    {k n : Nat} (D : SupercriticalDivision k (Fin n)) :
    D ∈ allSupercriticalDivisions k n := by
  classical
  rw [allSupercriticalDivisions, Finset.mem_image]
  exact ⟨⟨D.assignment, D.assignment_usesEveryPart⟩,
    Finset.mem_univ _, D.ofAssignment_assignment⟩

/-- There are at most `k^n` divisions.  The positivity guard is necessary:
for `k = 0`, the option-label type does not have cardinality `k`. -/
theorem card_allSupercriticalDivisions_le
    {k n : Nat} (hk : 1 ≤ k) :
    (allSupercriticalDivisions k n).card ≤ k ^ n := by
  classical
  calc
    (allSupercriticalDivisions k n).card ≤
        Fintype.card {a : Fin n → Option (Fin (k - 1)) //
          SupercriticalDivision.AssignmentUsesEveryPart a} := by
      simpa [allSupercriticalDivisions] using
        Finset.card_image_le (f := fun a :
          {a : Fin n → Option (Fin (k - 1)) //
            SupercriticalDivision.AssignmentUsesEveryPart a} ↦
          SupercriticalDivision.ofAssignment a.1 a.2)
          (s := Finset.univ)
    _ ≤ Fintype.card (Fin n → Option (Fin (k - 1))) :=
      Fintype.card_subtype_le _
    _ = k ^ n := by
      rw [Fintype.card_fun]
      simp only [Fintype.card_option, Fintype.card_fin]
      congr 1
      omega

/-- The finite subfamily of full divisions. -/
noncomputable def fullSupercriticalDivisions (k n : Nat) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter SupercriticalDivision.IsFull

@[simp] theorem mem_fullSupercriticalDivisions
    {k n : Nat} {D : SupercriticalDivision k (Fin n)} :
    D ∈ fullSupercriticalDivisions k n ↔ D.IsFull := by
  simp [fullSupercriticalDivisions]

/-! ## Reindexing and equivalence of ordered covers -/

namespace SupercriticalDivision

variable {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem support_reindexParts (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).support = D.support := by
  ext v
  simp only [mem_support, reindexParts_parts]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨sigma.symm i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨sigma i, by simpa⟩

@[simp] theorem sparse_reindexParts (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).sparse = D.sparse := by
  simp [SupercriticalDivision.sparse]

@[simp] theorem isFull_reindexParts (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).IsFull ↔ D.IsFull := by
  simp [IsFull]

@[simp] theorem assignment_reindexParts (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) (v : V) :
    (D.reindexParts sigma).assignment v =
      Option.map sigma (D.assignment v) := by
  cases h : D.assignment v with
  | none =>
      have hv := D.assignment_eq_none_iff v |>.1 h
      have hv' : v ∈ (D.reindexParts sigma).sparse := by simpa using hv
      simpa [h] using
        ((D.reindexParts sigma).assignment_eq_none_iff v).2 hv'
  | some i =>
      have hv := D.assignment_eq_some_iff v i |>.1 h
      have hv' : v ∈ (D.reindexParts sigma).parts (sigma i) := by simpa
      simpa [h] using
        ((D.reindexParts sigma).assignment_eq_some_iff v (sigma i)).2 hv'

@[simp] theorem reindexParts_refl (D : SupercriticalDivision k V) :
    D.reindexParts (Equiv.refl _) = D := by
  apply assignment_injective
  funext v
  simp

@[simp] theorem reindexParts_symm_reindexParts
    (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).reindexParts sigma.symm = D := by
  apply assignment_injective
  funext v
  simp

theorem reindexParts_trans (D : SupercriticalDivision k V)
    (sigma tau : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).reindexParts tau =
      D.reindexParts (sigma.trans tau) := by
  apply assignment_injective
  funext v
  simp

end SupercriticalDivision

/-- Ordered full divisions are equivalent when they differ only by a
permutation of their part labels. -/
def FullDivisionsEquivalent {k : Nat} {V : Type*} [Fintype V]
    [DecidableEq V] (D E : SupercriticalDivision k V) : Prop :=
  ∃ sigma : Equiv.Perm (Fin (k - 1)), E = D.reindexParts sigma

theorem fullDivisionsEquivalent_refl
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) : FullDivisionsEquivalent D D := by
  exact ⟨Equiv.refl _, D.reindexParts_refl.symm⟩

theorem fullDivisionsEquivalent_symm
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E : SupercriticalDivision k V} :
    FullDivisionsEquivalent D E → FullDivisionsEquivalent E D := by
  rintro ⟨sigma, rfl⟩
  exact ⟨sigma.symm, (D.reindexParts_symm_reindexParts sigma).symm⟩

theorem fullDivisionsEquivalent_trans
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E F : SupercriticalDivision k V} :
    FullDivisionsEquivalent D E → FullDivisionsEquivalent E F →
      FullDivisionsEquivalent D F := by
  rintro ⟨sigma, rfl⟩ ⟨tau, rfl⟩
  exact ⟨sigma.trans tau, D.reindexParts_trans sigma tau⟩

theorem fullDivisionsEquivalent_iff_assignment
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    FullDivisionsEquivalent D E ↔
      ∃ sigma : Equiv.Perm (Fin (k - 1)),
        E.assignment = Option.map sigma ∘ D.assignment := by
  constructor
  · rintro ⟨sigma, rfl⟩
    exact ⟨sigma, funext fun v ↦ by simp [Function.comp_apply]⟩
  · rintro ⟨sigma, h⟩
    refine ⟨sigma, SupercriticalDivision.assignment_injective ?_⟩
    funext v
    rw [SupercriticalDivision.assignment_reindexParts]
    exact congrFun h v

/-! ## Unique and balanced covers -/

/-- A graph has one clique cover by `k-1` nonempty parts, up to permutation
of those parts. -/
def HasUniqueCoMultipartiteCover
    (k : Nat) {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop :=
  ∃ D : SupercriticalDivision k V,
    D.IsFull ∧
      (∀ i, G.IsClique (D.parts i : Set V)) ∧
      ∀ E : SupercriticalDivision k V,
        E.IsFull →
        (∀ i, G.IsClique (E.parts i : Set V)) →
        FullDivisionsEquivalent D E

/-- A full division whose part sizes are within `beta*n` of the common real
average. -/
def IsBalancedFullDivision {k n : Nat}
    (D : SupercriticalDivision k (Fin n)) (beta : Real) : Prop :=
  D.IsFull ∧ ∀ i,
    |((D.parts i).card : Real) - (n : Real) / ((k - 1 : Nat) : Real)| ≤
      beta * n

instance {k n : Nat} (D : SupercriticalDivision k (Fin n)) (beta : Real) :
    Decidable (IsBalancedFullDivision D beta) := Classical.propDecidable _

/-- The finite family of balanced full divisions. -/
noncomputable def balancedFullSupercriticalDivisions
    (k n : Nat) (beta : Real) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦
    IsBalancedFullDivision D beta

@[simp] theorem mem_balancedFullSupercriticalDivisions
    {k n : Nat} {beta : Real}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ balancedFullSupercriticalDivisions k n beta ↔
      IsBalancedFullDivision D beta := by
  simp [balancedFullSupercriticalDivisions]

/-! ## Forced cross edges -/

/-- The ambient unordered cross-edge coordinates of a division. -/
def supercriticalCrossEdgeFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) : Finset (Sym2 V) :=
  (supercriticalTaggedCrossChoiceUniverse D).image
    supercriticalTaggedCrossEdge

/-- Cross pairs for `D` which a second clique cover `E` forces to be
present. -/
def forcedCrossEdgesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) : Finset (Sym2 V) :=
  supercriticalCrossEdgeFinset D ∩ supercriticalInternalEdgeFinset E

/-- Tagged `D`-cross coordinates representing the edges forced by the
second cover.  Working in this tagged universe lets us apply the exact
fixed-cardinality containment estimate directly. -/
def forcedCrossChoicesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    Finset (SupercriticalTaggedCrossChoice k V) :=
  (supercriticalTaggedCrossChoiceUniverse D).filter fun z ↦
    supercriticalTaggedCrossEdge z ∈ forcedCrossEdgesBySecondCover D E

theorem forcedCrossChoicesBySecondCover_subset_universe
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    forcedCrossChoicesBySecondCover D E ⊆
      supercriticalTaggedCrossChoiceUniverse D :=
  Finset.filter_subset _ _

@[simp] theorem mem_forcedCrossChoicesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (z : SupercriticalTaggedCrossChoice k V) :
    z ∈ forcedCrossChoicesBySecondCover D E ↔
      z ∈ supercriticalTaggedCrossChoiceUniverse D ∧
        supercriticalTaggedCrossEdge z ∈ forcedCrossEdgesBySecondCover D E := by
  simp [forcedCrossChoicesBySecondCover]

/-- Forgetting the tag maps the forced coordinate set exactly onto the
ambient forced-edge set. -/
theorem image_forcedCrossChoicesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    (forcedCrossChoicesBySecondCover D E).image
        supercriticalTaggedCrossEdge =
      forcedCrossEdgesBySecondCover D E := by
  classical
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp he
    exact (mem_forcedCrossChoicesBySecondCover D E z).mp hz |>.2
  · intro e he
    have heCross : e ∈ supercriticalCrossEdgeFinset D :=
      Finset.inter_subset_left he
    rw [supercriticalCrossEdgeFinset, Finset.mem_image] at heCross
    obtain ⟨z, hzU, rfl⟩ := heCross
    exact Finset.mem_image.mpr ⟨z,
      (mem_forcedCrossChoicesBySecondCover D E z).mpr ⟨hzU, he⟩, rfl⟩

@[simp] theorem card_forcedCrossChoicesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    (forcedCrossChoicesBySecondCover D E).card =
      (forcedCrossEdgesBySecondCover D E).card := by
  classical
  rw [← image_forcedCrossChoicesBySecondCover D E,
    Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact supercriticalTaggedCrossEdge_injectiveOn D
    (forcedCrossChoicesBySecondCover_subset_universe D E hx)
    (forcedCrossChoicesBySecondCover_subset_universe D E hy) hxy

theorem forcedCrossEdgesBySecondCover_subset_crossUniverse
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    forcedCrossEdgesBySecondCover D E ⊆ supercriticalCrossEdgeFinset D :=
  Finset.inter_subset_left

theorem forcedCrossEdgesBySecondCover_subset_edgeFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (G : SimpleGraph V)
    (hclique : ∀ i, G.IsClique (E.parts i : Set V)) :
    forcedCrossEdgesBySecondCover D E ⊆ G.edgeFinset := by
  classical
  intro e he
  have heInternal := Finset.mem_inter.mp he |>.2
  induction e using Sym2.inductionOn with
  | _ x y =>
      obtain ⟨hxy, i, hxi, hyi⟩ :=
        (mk_mem_supercriticalInternalEdgeFinset E x y).mp heInternal
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hclique i hxi hyi hxy

@[simp] theorem mk_mem_supercriticalCrossEdgeFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (x y : V) :
    s(x, y) ∈ supercriticalCrossEdgeFinset D ↔
      ∃ i j : Fin (k - 1), i ≠ j ∧ x ∈ D.parts i ∧ y ∈ D.parts j := by
  classical
  constructor
  · rw [supercriticalCrossEdgeFinset, Finset.mem_image]
    rintro ⟨⟨e, a, b⟩, hz, he⟩
    rw [mem_supercriticalTaggedCrossChoiceUniverse] at hz
    rcases Sym2.eq_iff.mp he with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨e.left, e.right, e.left_ne_right, hz.1, hz.2⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨e.right, e.left, e.left_ne_right.symm, hz.2, hz.1⟩
  · rintro ⟨i, j, hij, hxi, hyj⟩
    rw [supercriticalCrossEdgeFinset, Finset.mem_image]
    by_cases hijlt : i < j
    · let e := SupercriticalPartPair.ofDistinct i j hij
      let z : SupercriticalTaggedCrossChoice k V := ⟨e, (x, y)⟩
      refine ⟨z, ?_, ?_⟩
      · simpa [z, e, SupercriticalPartPair.ofDistinct, hijlt,
          mem_supercriticalTaggedCrossChoiceUniverse] using ⟨hxi, hyj⟩
      · rfl
    · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hijlt) hij.symm
      let e := SupercriticalPartPair.ofDistinct i j hij
      let z : SupercriticalTaggedCrossChoice k V := ⟨e, (y, x)⟩
      refine ⟨z, ?_, ?_⟩
      · simpa [z, e, SupercriticalPartPair.ofDistinct, hijlt,
          mem_supercriticalTaggedCrossChoiceUniverse] using ⟨hyj, hxi⟩
      · simp [z, supercriticalTaggedCrossEdge]

@[simp] theorem mk_mem_forcedCrossEdgesBySecondCover
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (x y : V) :
    s(x, y) ∈ forcedCrossEdgesBySecondCover D E ↔
      (∃ i j : Fin (k - 1), i ≠ j ∧ x ∈ D.parts i ∧ y ∈ D.parts j) ∧
      x ≠ y ∧ ∃ a : Fin (k - 1), x ∈ E.parts a ∧ y ∈ E.parts a := by
  simp [forcedCrossEdgesBySecondCover]

/-! A direct moved--unmoved injection supplies the sharp near-cover lower
bound.  This is the part of the overlap argument responsible for summability
over the Hamming spheres above. -/

namespace SupercriticalDivision

variable {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]

/-- The ordinary part label of a vertex in a full division. -/
noncomputable def fullAssignment (D : SupercriticalDivision k V)
    (hD : D.IsFull) : V → Fin (k - 1) := fun v ↦
  Classical.choose (mem_support.mp (by
    rw [D.support_eq_univ hD]
    exact Finset.mem_univ v))

theorem fullAssignment_mem_part (D : SupercriticalDivision k V)
    (hD : D.IsFull) (v : V) :
    v ∈ D.parts (D.fullAssignment hD v) :=
  Classical.choose_spec (mem_support.mp (by
    rw [D.support_eq_univ hD]
    exact Finset.mem_univ v))

@[simp] theorem assignment_eq_some_fullAssignment
    (D : SupercriticalDivision k V) (hD : D.IsFull) (v : V) :
    D.assignment v = some (D.fullAssignment hD v) :=
  D.assignment_eq_some_iff v _ |>.2 (D.fullAssignment_mem_part hD v)

end SupercriticalDivision

def divisionMovedVertexFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) : Finset V :=
  Finset.univ.filter fun v ↦
    E.assignment v ≠ Option.map sigma (D.assignment v)

@[simp] theorem card_divisionMovedVertexFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (divisionMovedVertexFinset D E sigma).card =
      (Finset.univ.filter fun v ↦
        E.assignment v ≠ Option.map sigma (D.assignment v)).card := rfl

def divisionUnmovedTargetFinset
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (hE : E.IsFull)
    (sigma : Equiv.Perm (Fin (k - 1))) (v : V) : Finset V :=
  D.parts (sigma.symm (E.fullAssignment hE v)) \
    divisionMovedVertexFinset D E sigma

private abbrev DivisionNearForcedDomain
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (hE : E.IsFull)
    (sigma : Equiv.Perm (Fin (k - 1))) :=
  Σ v : {v // v ∈ divisionMovedVertexFinset D E sigma},
    {w // w ∈ divisionUnmovedTargetFinset D E hE sigma v.1}

private def divisionNearForcedEdge
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E : SupercriticalDivision k V} {hE : E.IsFull}
    {sigma : Equiv.Perm (Fin (k - 1))} :
    DivisionNearForcedDomain D E hE sigma → Sym2 V := fun z ↦
  s(z.1.1, z.2.1)

private theorem divisionNearForcedEdge_injective
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E : SupercriticalDivision k V} {hE : E.IsFull}
    {sigma : Equiv.Perm (Fin (k - 1))} :
    Function.Injective
      (@divisionNearForcedEdge k V _ _ D E hE sigma) := by
  rintro ⟨v, w⟩ ⟨v', w'⟩ hzz'
  rcases Sym2.eq_iff.mp hzz' with h | h
  · have hv : v = v' := Subtype.ext h.1
    subst v'
    have hw : w = w' := Subtype.ext h.2
    subst w'
    rfl
  · exfalso
    have hw' := (Finset.mem_sdiff.mp w'.2).2
    apply hw'
    rw [← h.1]
    exact v.2

private theorem divisionNearForcedEdge_mem
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E : SupercriticalDivision k V} (hD : D.IsFull) (hE : E.IsFull)
    {sigma : Equiv.Perm (Fin (k - 1))}
    (z : DivisionNearForcedDomain D E hE sigma) :
    divisionNearForcedEdge z ∈ forcedCrossEdgesBySecondCover D E := by
  let v := z.1.1
  let w := z.2.1
  let a := D.fullAssignment hD v
  let b := sigma.symm (E.fullAssignment hE v)
  have hvMoved : v ∈ divisionMovedVertexFinset D E sigma := z.1.2
  have hwData : w ∈ D.parts b ∧
      w ∉ divisionMovedVertexFinset D E sigma :=
    Finset.mem_sdiff.mp z.2.2
  have hva : v ∈ D.parts a := D.fullAssignment_mem_part hD v
  have hab : a ≠ b := by
    intro hab
    have hvNe : E.assignment v ≠ Option.map sigma (D.assignment v) :=
      (Finset.mem_filter.mp hvMoved).2
    rw [E.assignment_eq_some_fullAssignment hE,
      D.assignment_eq_some_fullAssignment hD] at hvNe
    simp [a, b, hab] at hvNe
  have hvE : v ∈ E.parts (E.fullAssignment hE v) :=
    E.fullAssignment_mem_part hE v
  have hwE : w ∈ E.parts (E.fullAssignment hE v) := by
    have hwEq : E.assignment w = Option.map sigma (D.assignment w) := by
      simpa [divisionMovedVertexFinset] using hwData.2
    have hwb : w ∈ D.parts b := hwData.1
    have hbassign := D.assignment_eq_some_iff w b |>.2 hwb
    rw [hbassign] at hwEq
    apply E.assignment_eq_some_iff w _ |>.1
    simpa [b] using hwEq
  change s(v, w) ∈ forcedCrossEdgesBySecondCover D E
  rw [mk_mem_forcedCrossEdgesBySecondCover]
  refine ⟨⟨a, b, hab, hva, hwData.1⟩, ?_,
    E.fullAssignment hE v, hvE, hwE⟩
  intro hvw
  exact hab (D.mem_part_unique hva (by simpa [hvw] using hwData.1))

private theorem card_divisionUnmovedTargetFinset_ge
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {D E : SupercriticalDivision k V} {hE : E.IsFull}
    {sigma : Equiv.Perm (Fin (k - 1))} {a t : Nat}
    (hpart : ∀ i, a ≤ (D.parts i).card)
    (ht : (divisionMovedVertexFinset D E sigma).card = t) (v : V) :
    a - t ≤ (divisionUnmovedTargetFinset D E hE sigma v).card := by
  have hcover : (D.parts (sigma.symm (E.fullAssignment hE v))).card ≤
      (divisionUnmovedTargetFinset D E hE sigma v).card +
        (divisionMovedVertexFinset D E sigma).card := by
    exact Finset.card_le_card_sdiff_add_card
  rw [ht] at hcover
  exact Nat.sub_le_iff_le_add.mpr ((hpart _).trans hcover)

/-- Near-cover forced-edge estimate, with all rounding kept in natural
numbers. -/
theorem forcedCrossEdges_card_ge_moved_mul_sub
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (hD : D.IsFull) (hE : E.IsFull)
    (sigma : Equiv.Perm (Fin (k - 1))) (a t : Nat)
    (hpart : ∀ i, a ≤ (D.parts i).card)
    (ht : (divisionMovedVertexFinset D E sigma).card = t) :
    t * (a - t) ≤ (forcedCrossEdgesBySecondCover D E).card := by
  classical
  let f : DivisionNearForcedDomain D E hE sigma →
      {e // e ∈ forcedCrossEdgesBySecondCover D E} := fun z ↦
    ⟨divisionNearForcedEdge z, divisionNearForcedEdge_mem hD hE z⟩
  have hf : Function.Injective f := by
    intro z z' h
    exact divisionNearForcedEdge_injective (Subtype.ext_iff.mp h)
  have hdomain : t * (a - t) ≤
      Fintype.card (DivisionNearForcedDomain D E hE sigma) := by
    calc
      t * (a - t) = ∑ _v :
          {v // v ∈ divisionMovedVertexFinset D E sigma}, (a - t) := by
            simp [ht, Nat.mul_comm]
      _ ≤ ∑ v : {v // v ∈ divisionMovedVertexFinset D E sigma},
          (divisionUnmovedTargetFinset D E hE sigma v.1).card := by
            exact Finset.sum_le_sum fun v _ ↦
              card_divisionUnmovedTargetFinset_ge hpart ht v
      _ = Fintype.card (DivisionNearForcedDomain D E hE sigma) := by
            rw [Fintype.card_sigma]
            apply Finset.sum_congr rfl
            intro v _
            exact (Fintype.card_coe _).symm
  exact hdomain.trans (by
    simpa using Fintype.card_le_of_injective f hf)

/-! ## Move distance -/

/-- Vertices whose division labels disagree after reindexing the first
division. -/
def fullDivisionMoveCount
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) : Nat :=
  (Finset.univ.filter fun v ↦
    E.assignment v ≠ Option.map sigma (D.assignment v)).card

/-- Minimum number of vertex moves after the best part-label permutation. -/
def fullDivisionMoveDistance
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) : Nat :=
  (Finset.univ.image (fullDivisionMoveCount D E)).min' (by simp)

/-! ## Dominant overlap cells -/

/-- A row of the `D`/`E` overlap matrix having maximum entry in column `j`. -/
noncomputable def dominantDivisionOverlapIndex
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (j : Fin (k - 1)) : Fin (k - 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i : Fin (k - 1) ↦ (D.parts i ∩ E.parts j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

theorem overlap_le_dominantDivisionOverlap
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (i j : Fin (k - 1)) :
    (D.parts i ∩ E.parts j).card ≤
      (D.parts (dominantDivisionOverlapIndex hk D E j) ∩ E.parts j).card := by
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun i : Fin (k - 1) ↦ (D.parts i ∩ E.parts j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

private theorem sum_card_inter_divisionParts
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (hD : D.IsFull)
    (S : Finset V) :
    ∑ i : Fin (k - 1), (D.parts i ∩ S).card = S.card := by
  classical
  let Q : Fin (k - 1) → Finset V := fun i ↦ D.parts i ∩ S
  have hpair : (↑(Finset.univ : Finset (Fin (k - 1))) :
      Set (Fin (k - 1))).PairwiseDisjoint Q := by
    intro i _ j _ hij
    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left
        (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij))
  have hunion : Finset.univ.biUnion Q = S := by
    ext v
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Q,
      Finset.mem_inter]
    constructor
    · rintro ⟨i, _, hvS⟩
      exact hvS
    · intro hvS
      have hvSupport : v ∈ D.support := by
        rw [D.support_eq_univ hD]
        exact Finset.mem_univ _
      obtain ⟨i, hvi⟩ := D.mem_support.mp hvSupport
      exact ⟨i, hvi, hvS⟩
  calc
    ∑ i : Fin (k - 1), (D.parts i ∩ S).card =
        (Finset.univ.biUnion Q).card := by
          rw [Finset.card_biUnion hpair]
    _ = S.card := congrArg Finset.card hunion

/-- Vertices of `E.parts j` outside its dominant `D`-overlap cell. -/
def divisionOverlapMinority
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (j : Fin (k - 1)) : Finset V :=
  E.parts j \ D.parts (dominantDivisionOverlapIndex hk D E j)

/-- Total minority mass in the column-dominant overlap description. -/
def totalDivisionOverlapMinority
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) : Nat :=
  ∑ j, (divisionOverlapMinority hk D E j).card

private theorem column_card_le_index_mul_dominantOverlap
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) (hD : D.IsFull)
    (j : Fin (k - 1)) :
    (E.parts j).card ≤ (k - 1) *
      (D.parts (dominantDivisionOverlapIndex hk D E j) ∩ E.parts j).card := by
  rw [← sum_card_inter_divisionParts D hD (E.parts j)]
  calc
    ∑ i : Fin (k - 1), (D.parts i ∩ E.parts j).card ≤
        ∑ _i : Fin (k - 1),
          (D.parts (dominantDivisionOverlapIndex hk D E j) ∩ E.parts j).card := by
            exact Finset.sum_le_sum fun i _ ↦
              overlap_le_dominantDivisionOverlap hk D E i j
    _ = (k - 1) *
        (D.parts (dominantDivisionOverlapIndex hk D E j) ∩ E.parts j).card := by
          simp [Nat.mul_comm]

private theorem minority_card_le_index_mul_dominantOverlap
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) (hD : D.IsFull)
    (j : Fin (k - 1)) :
    (divisionOverlapMinority hk D E j).card ≤ (k - 1) *
      (D.parts (dominantDivisionOverlapIndex hk D E j) ∩ E.parts j).card :=
  (Finset.card_le_card Finset.sdiff_subset).trans
    (column_card_le_index_mul_dominantOverlap hk D E hD j)

/-- A column with maximum minority mass. -/
noncomputable def maximalMinorityColumn
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) : Fin (k - 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun j : Fin (k - 1) ↦ (divisionOverlapMinority hk D E j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

private theorem minority_le_maximalMinority
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (j : Fin (k - 1)) :
    (divisionOverlapMinority hk D E j).card ≤
      (divisionOverlapMinority hk D E
        (maximalMinorityColumn hk D E)).card := by
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun j : Fin (k - 1) ↦ (divisionOverlapMinority hk D E j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 j (Finset.mem_univ _)

private theorem totalMinority_le_index_mul_maximalMinority
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) :
    totalDivisionOverlapMinority hk D E ≤ (k - 1) *
      (divisionOverlapMinority hk D E
        (maximalMinorityColumn hk D E)).card := by
  unfold totalDivisionOverlapMinority
  calc
    ∑ j : Fin (k - 1), (divisionOverlapMinority hk D E j).card ≤
        ∑ _j : Fin (k - 1),
          (divisionOverlapMinority hk D E
            (maximalMinorityColumn hk D E)).card := by
              exact Finset.sum_le_sum fun j _ ↦
                minority_le_maximalMinority hk D E j
    _ = (k - 1) *
        (divisionOverlapMinority hk D E
          (maximalMinorityColumn hk D E)).card := by simp [Nat.mul_comm]

/-- A `D`-row having maximum overlap with the minority of the maximally
mixed column. -/
noncomputable def maximalMinorityRow
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) : Fin (k - 1) :=
  Classical.choose (Finset.exists_max_image Finset.univ
    (fun i : Fin (k - 1) ↦
      (D.parts i ∩ divisionOverlapMinority hk D E
        (maximalMinorityColumn hk D E)).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

private theorem minorityOverlap_le_maximalMinorityOverlap
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (i : Fin (k - 1)) :
    (D.parts i ∩ divisionOverlapMinority hk D E
      (maximalMinorityColumn hk D E)).card ≤
      (D.parts (maximalMinorityRow hk D E) ∩
        divisionOverlapMinority hk D E
          (maximalMinorityColumn hk D E)).card := by
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun i : Fin (k - 1) ↦
      (D.parts i ∩ divisionOverlapMinority hk D E
        (maximalMinorityColumn hk D E)).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 i (Finset.mem_univ _)

private theorem maximalMinority_card_le_index_mul_rowOverlap
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) (hD : D.IsFull) :
    (divisionOverlapMinority hk D E
        (maximalMinorityColumn hk D E)).card ≤
      (k - 1) *
        (D.parts (maximalMinorityRow hk D E) ∩
          divisionOverlapMinority hk D E
            (maximalMinorityColumn hk D E)).card := by
  rw [← sum_card_inter_divisionParts D hD
    (divisionOverlapMinority hk D E (maximalMinorityColumn hk D E))]
  calc
    ∑ i : Fin (k - 1),
        (D.parts i ∩ divisionOverlapMinority hk D E
          (maximalMinorityColumn hk D E)).card ≤
      ∑ _i : Fin (k - 1),
        (D.parts (maximalMinorityRow hk D E) ∩
          divisionOverlapMinority hk D E
            (maximalMinorityColumn hk D E)).card := by
              exact Finset.sum_le_sum fun i _ ↦
                minorityOverlap_le_maximalMinorityOverlap hk D E i
    _ = (k - 1) *
        (D.parts (maximalMinorityRow hk D E) ∩
          divisionOverlapMinority hk D E
            (maximalMinorityColumn hk D E)).card := by simp [Nat.mul_comm]

private theorem inter_cell_card_mul_le_forced
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (i l j : Fin (k - 1)) (hil : i ≠ l) :
    (D.parts i ∩ E.parts j).card * (D.parts l ∩ E.parts j).card ≤
      (forcedCrossEdgesBySecondCover D E).card := by
  classical
  let A := D.parts i ∩ E.parts j
  let B := D.parts l ∩ E.parts j
  let R := (A ×ˢ B).image fun p ↦ s(p.1, p.2)
  have hinj : Set.InjOn (fun p : V × V ↦ s(p.1, p.2))
      (↑(A ×ˢ B) : Set (V × V)) := by
    rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hx'y' heq
    change (x, y) ∈ A ×ˢ B at hxy
    change (x', y') ∈ A ×ˢ B at hx'y'
    rw [Finset.mem_product] at hxy hx'y'
    simp only [A, B, Finset.mem_inter] at hxy hx'y'
    rcases Sym2.eq_iff.mp heq with h | h
    · exact Prod.ext h.1 h.2
    · exfalso
      have h1 : x = y' := by simpa using h.1
      have hxl : x ∈ D.parts l := by
        rw [h1]
        exact hx'y'.2.1
      exact (Finset.disjoint_left.mp
        (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ l) hil))
          hxy.1.1 hxl
  have hsub : R ⊆ forcedCrossEdgesBySecondCover D E := by
    intro e he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
    rw [Finset.mem_product] at hxy
    simp only [A, B, Finset.mem_inter] at hxy
    rw [mk_mem_forcedCrossEdgesBySecondCover]
    refine ⟨⟨i, l, hil, hxy.1.1, hxy.2.1⟩, ?_, j, hxy.1.2, hxy.2.2⟩
    intro h
    have h' : x = y := by simpa using h
    have hxl : x ∈ D.parts l := by
      rw [h']
      exact hxy.2.1
    exact (Finset.disjoint_left.mp
      (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ l) hil))
        hxy.1.1 hxl
  calc
    (D.parts i ∩ E.parts j).card * (D.parts l ∩ E.parts j).card =
        (A ×ˢ B).card := by simp [A, B]
    _ = R.card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (forcedCrossEdgesBySecondCover D E).card := Finset.card_le_card hsub

/-- The square of the total column-minority mass is controlled by forced
cross edges.  The deliberately generous fourth power keeps the statement
entirely integral. -/
theorem totalDivisionOverlapMinority_sq_le_forced
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V) (hD : D.IsFull) :
    totalDivisionOverlapMinority hk D E ^ 2 ≤
      (k - 1) ^ 4 * (forcedCrossEdgesBySecondCover D E).card := by
  classical
  let j := maximalMinorityColumn hk D E
  let i := maximalMinorityRow hk D E
  let d := dominantDivisionOverlapIndex hk D E j
  let b := (divisionOverlapMinority hk D E j).card
  let M := (D.parts d ∩ E.parts j).card
  let c := (D.parts i ∩ divisionOverlapMinority hk D E j).card
  by_cases hb : b = 0
  · have htotal : totalDivisionOverlapMinority hk D E = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa [j, b, hb] using totalMinority_le_index_mul_maximalMinority hk D E
    simp [htotal]
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    have hcpos : 0 < c := by
      have hbc := maximalMinority_card_le_index_mul_rowOverlap hk D E hD
      change b ≤ (k - 1) * c at hbc
      by_contra hc
      have : c = 0 := Nat.eq_zero_of_not_pos hc
      simp [this] at hbc
      omega
    have hid : i ≠ d := by
      intro hid
      have hempty : D.parts i ∩ divisionOverlapMinority hk D E j = ∅ := by
        ext v
        simp [divisionOverlapMinority, i, d, j, hid]
      have : c = 0 := by simp [c, hempty]
      omega
    have hcCell : c ≤ (D.parts i ∩ E.parts j).card := by
      apply Finset.card_le_card
      intro v hv
      rw [Finset.mem_inter] at hv ⊢
      exact ⟨hv.1, (Finset.mem_sdiff.mp hv.2).1⟩
    have hrect : M * c ≤ (forcedCrossEdgesBySecondCover D E).card := by
      calc
        M * c ≤ M * (D.parts i ∩ E.parts j).card :=
          Nat.mul_le_mul_left M hcCell
        _ ≤ (forcedCrossEdgesBySecondCover D E).card := by
          simpa [M, d, i, j] using inter_cell_card_mul_le_forced
            D E d i j hid.symm
    have htotal : totalDivisionOverlapMinority hk D E ≤ (k - 1) * b := by
      simpa [j, b] using totalMinority_le_index_mul_maximalMinority hk D E
    have hbM : b ≤ (k - 1) * M := by
      simpa [j, b, M, d] using
        minority_card_le_index_mul_dominantOverlap hk D E hD j
    have hbc : b ≤ (k - 1) * c := by
      simpa [j, b, c, i] using
        maximalMinority_card_le_index_mul_rowOverlap hk D E hD
    calc
      totalDivisionOverlapMinority hk D E ^ 2 ≤ ((k - 1) * b) ^ 2 :=
        Nat.pow_le_pow_left htotal 2
      _ = (k - 1) ^ 2 * (b * b) := by ring
      _ ≤ (k - 1) ^ 2 * (((k - 1) * M) * ((k - 1) * c)) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hbM hbc)
      _ = (k - 1) ^ 4 * (M * c) := by ring
      _ ≤ (k - 1) ^ 4 * (forcedCrossEdgesBySecondCover D E).card :=
        Nat.mul_le_mul_left _ hrect

private theorem fullDivisionMoveDistance_le_moveCount
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    fullDivisionMoveDistance D E ≤ fullDivisionMoveCount D E sigma := by
  rw [fullDivisionMoveDistance]
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨sigma, Finset.mem_univ _, rfl⟩

/-- The optimal move distance, or the minimum reference-part size when the
dominant-column map is not a permutation, is at most `r` times the total
minority mass. -/
theorem min_moveDistance_partSize_le_index_mul_totalMinority
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (hD : D.IsFull) (hE : E.IsFull) (a : Nat)
    (hpart : ∀ i, a ≤ (D.parts i).card) :
    min (fullDivisionMoveDistance D E) a ≤
      (k - 1) * totalDivisionOverlapMinority hk D E := by
  classical
  let d : Fin (k - 1) → Fin (k - 1) := fun j ↦
    dominantDivisionOverlapIndex hk D E j
  let b := (divisionOverlapMinority hk D E
    (maximalMinorityColumn hk D E)).card
  have hunion : (Finset.univ.biUnion fun j ↦
      divisionOverlapMinority hk D E j).card ≤ (k - 1) * b := by
    have h := Finset.card_biUnion_le_card_mul Finset.univ
      (fun j ↦ divisionOverlapMinority hk D E j) b
      (fun j _ ↦ by simpa [b] using minority_le_maximalMinority hk D E j)
    simpa using h
  have hbTotal : b ≤ totalDivisionOverlapMinority hk D E := by
    unfold totalDivisionOverlapMinority
    simpa [b] using Finset.single_le_sum
      (f := fun j : Fin (k - 1) ↦ (divisionOverlapMinority hk D E j).card)
      (s := Finset.univ) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ (maximalMinorityColumn hk D E))
  by_cases hsurj : Function.Surjective d
  · have hbij : Function.Bijective d := Finite.surjective_iff_bijective.mp hsurj
    let tau : Equiv.Perm (Fin (k - 1)) := Equiv.ofBijective d hbij
    have hmoved : divisionMovedVertexFinset D E tau.symm ⊆
        Finset.univ.biUnion fun j ↦ divisionOverlapMinority hk D E j := by
      intro v hv
      let j := E.fullAssignment hE v
      have hvE : v ∈ E.parts j := E.fullAssignment_mem_part hE v
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hvE, ?_⟩⟩
      intro hvD
      have hlabel : D.fullAssignment hD v = d j :=
        D.mem_part_unique (D.fullAssignment_mem_part hD v) hvD
      have hvne := (Finset.mem_filter.mp hv).2
      rw [E.assignment_eq_some_fullAssignment hE,
        D.assignment_eq_some_fullAssignment hD] at hvne
      have htau : ∀ x, tau x = d x := fun _ ↦ rfl
      simp [j, hlabel, ← htau] at hvne
    have hmove : fullDivisionMoveCount D E tau.symm ≤ (k - 1) * b := by
      change (divisionMovedVertexFinset D E tau.symm).card ≤ (k - 1) * b
      exact (Finset.card_le_card hmoved).trans hunion
    calc
      min (fullDivisionMoveDistance D E) a ≤ fullDivisionMoveDistance D E := min_le_left _ _
      _ ≤ fullDivisionMoveCount D E tau.symm :=
        fullDivisionMoveDistance_le_moveCount D E tau.symm
      _ ≤ (k - 1) * b := hmove
      _ ≤ (k - 1) * totalDivisionOverlapMinority hk D E :=
        Nat.mul_le_mul_left _ hbTotal
  · have hnot : ∃ i, ∀ j, d j ≠ i := by
      simpa only [Function.Surjective, not_forall, not_exists,
        not_not] using hsurj
    obtain ⟨i, hi⟩ := hnot
    have hsubset : D.parts i ⊆ Finset.univ.biUnion fun j ↦
        divisionOverlapMinority hk D E j := by
      intro v hvD
      let j := E.fullAssignment hE v
      have hvE : v ∈ E.parts j := E.fullAssignment_mem_part hE v
      apply Finset.mem_biUnion.mpr
      refine ⟨j, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hvE, ?_⟩⟩
      intro hvdom
      exact hi j (D.mem_part_unique hvdom hvD)
    calc
      min (fullDivisionMoveDistance D E) a ≤ a := min_le_right _ _
      _ ≤ (D.parts i).card := hpart i
      _ ≤ (Finset.univ.biUnion fun j ↦
          divisionOverlapMinority hk D E j).card := Finset.card_le_card hsubset
      _ ≤ (k - 1) * b := hunion
      _ ≤ (k - 1) * totalDivisionOverlapMinority hk D E :=
        Nat.mul_le_mul_left _ hbTotal

/-- Far-overlap inequality in an integer-scaled form. -/
theorem min_moveDistance_partSize_sq_le_forced
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (hD : D.IsFull) (hE : E.IsFull) (a : Nat)
    (hpart : ∀ i, a ≤ (D.parts i).card) :
    min (fullDivisionMoveDistance D E) a ^ 2 ≤
      (k - 1) ^ 6 * (forcedCrossEdgesBySecondCover D E).card := by
  calc
    min (fullDivisionMoveDistance D E) a ^ 2 ≤
        ((k - 1) * totalDivisionOverlapMinority hk D E) ^ 2 :=
      Nat.pow_le_pow_left
        (min_moveDistance_partSize_le_index_mul_totalMinority
          hk D E hD hE a hpart) 2
    _ = (k - 1) ^ 2 * totalDivisionOverlapMinority hk D E ^ 2 := by ring
    _ ≤ (k - 1) ^ 2 * ((k - 1) ^ 4 *
        (forcedCrossEdgesBySecondCover D E).card) :=
      Nat.mul_le_mul_left _ (totalDivisionOverlapMinority_sq_le_forced hk D E hD)
    _ = (k - 1) ^ 6 * (forcedCrossEdgesBySecondCover D E).card := by ring

theorem exists_moveCount_eq_moveDistance
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    ∃ sigma : Equiv.Perm (Fin (k - 1)),
      fullDivisionMoveCount D E sigma = fullDivisionMoveDistance D E := by
  simpa [fullDivisionMoveDistance] using
    Finset.min'_mem (Finset.univ.image (fullDivisionMoveCount D E)) (by simp)

theorem fullDivisionMoveDistance_eq_zero_iff
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    fullDivisionMoveDistance D E = 0 ↔ FullDivisionsEquivalent D E := by
  classical
  rw [fullDivisionsEquivalent_iff_assignment]
  constructor
  · intro hzero
    obtain ⟨sigma, hsigma⟩ := exists_moveCount_eq_moveDistance D E
    refine ⟨sigma, funext fun v ↦ ?_⟩
    have hempty : Finset.univ.filter (fun w ↦
        E.assignment w ≠ Option.map sigma (D.assignment w)) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [fullDivisionMoveCount, hzero] using hsigma
    by_contra hv
    change E.assignment v ≠ Option.map sigma (D.assignment v) at hv
    have : v ∈ Finset.univ.filter (fun w ↦
        E.assignment w ≠ Option.map sigma (D.assignment w)) := by simp [hv]
    simpa [hempty] using this
  · rintro ⟨sigma, hsigma⟩
    have hmem : 0 ∈ Finset.univ.image (fullDivisionMoveCount D E) := by
      refine Finset.mem_image.mpr ⟨sigma, Finset.mem_univ _, ?_⟩
      simp [fullDivisionMoveCount, congrFun hsigma]
    apply Nat.eq_zero_of_le_zero
    exact Finset.min'_le _ _ hmem

/-- The near-cover injection expressed at an attained minimizing
permutation. -/
theorem forcedCrossEdges_card_ge_distance_mul_sub
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (hD : D.IsFull) (hE : E.IsFull)
    (a : Nat) (hpart : ∀ i, a ≤ (D.parts i).card) :
    fullDivisionMoveDistance D E * (a - fullDivisionMoveDistance D E) ≤
      (forcedCrossEdgesBySecondCover D E).card := by
  obtain ⟨sigma, hsigma⟩ := exists_moveCount_eq_moveDistance D E
  apply forcedCrossEdges_card_ge_moved_mul_sub D E hD hE sigma
    a (fullDivisionMoveDistance D E) hpart
  change fullDivisionMoveCount D E sigma = fullDivisionMoveDistance D E
  exact hsigma

/-- Quantitative cover dichotomy.  A genuinely different full cover either
lies in the near regime, where every moved vertex forces linearly many cross
edges, or in the far regime, where the dominant-overlap estimate forces a
quadratic number of cross edges.  The constants are intentionally integral
and uniform in the two covers. -/
theorem forcedCrossEdges_near_or_far
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D E : SupercriticalDivision k V)
    (hD : D.IsFull) (hE : E.IsFull) (a : Nat)
    (hpart : ∀ i, a ≤ (D.parts i).card)
    (hscale : Fintype.card V ≤ 2 * (k - 1) * a)
    (hne : ¬ FullDivisionsEquivalent D E) :
    let t := fullDivisionMoveDistance D E
    let q := (forcedCrossEdgesBySecondCover D E).card
    (1 ≤ t ∧ 2 * t ≤ a ∧ t * Fintype.card V ≤ 4 * (k - 1) * q) ∨
      (a < 2 * t ∧ (Fintype.card V) ^ 2 ≤ 16 * (k - 1) ^ 8 * q) := by
  dsimp only
  let t := fullDivisionMoveDistance D E
  let q := (forcedCrossEdgesBySecondCover D E).card
  have htpos : 1 ≤ t := by
    rw [Nat.one_le_iff_ne_zero]
    intro ht
    exact hne ((fullDivisionMoveDistance_eq_zero_iff D E).mp ht)
  by_cases hnear : 2 * t ≤ a
  · left
    refine ⟨htpos, hnear, ?_⟩
    have ha : a ≤ 2 * (a - t) := by omega
    have hforced : t * (a - t) ≤ q := by
      simpa [t, q] using
        forcedCrossEdges_card_ge_distance_mul_sub D E hD hE a hpart
    calc
      t * Fintype.card V ≤ t * (2 * (k - 1) * a) :=
        Nat.mul_le_mul_left t hscale
      _ = 2 * (k - 1) * (t * a) := by ring
      _ ≤ 2 * (k - 1) * (t * (2 * (a - t))) := by
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ha)
      _ = 4 * (k - 1) * (t * (a - t)) := by ring
      _ ≤ 4 * (k - 1) * q := Nat.mul_le_mul_left _ hforced
  · right
    have hfar : a < 2 * t := by omega
    refine ⟨hfar, ?_⟩
    have haMin : a ≤ 2 * min t a := by
      rcases le_total t a with hta | hat
      · rw [min_eq_left hta]
        omega
      · rw [min_eq_right hat]
        omega
    have hnMin : Fintype.card V ≤ 4 * (k - 1) * min t a := by
      calc
        Fintype.card V ≤ 2 * (k - 1) * a := hscale
        _ ≤ 2 * (k - 1) * (2 * min t a) :=
          Nat.mul_le_mul_left _ haMin
        _ = 4 * (k - 1) * min t a := by ring
    have hforced : min t a ^ 2 ≤ (k - 1) ^ 6 * q := by
      simpa [t, q] using
        min_moveDistance_partSize_sq_le_forced hk D E hD hE a hpart
    calc
      (Fintype.card V) ^ 2 ≤ (4 * (k - 1) * min t a) ^ 2 :=
        Nat.pow_le_pow_left hnMin 2
      _ = 16 * (k - 1) ^ 2 * min t a ^ 2 := by ring
      _ ≤ 16 * (k - 1) ^ 2 * ((k - 1) ^ 6 * q) :=
        Nat.mul_le_mul_left _ hforced
      _ = 16 * (k - 1) ^ 8 * q := by ring

/-! ## Counting divisions at a fixed move distance -/

theorem fullDivisionMoveCount_eq_hamming
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) (hD : D.IsFull) (hE : E.IsFull)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    fullDivisionMoveCount D E sigma =
      (Finset.univ.filter fun v ↦
        E.fullAssignment hE v ≠ sigma (D.fullAssignment hD v)).card := by
  unfold fullDivisionMoveCount
  congr 1
  ext v
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [E.assignment_eq_some_fullAssignment hE,
    D.assignment_eq_some_fullAssignment hD]
  simp

/-- Full divisions at exact best-permutation move distance `t` from `D`. -/
noncomputable def fullDivisionsAtMoveDistance
    {k n : Nat} (D : SupercriticalDivision k (Fin n)) (t : Nat) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact ((allSupercriticalDivisions k n).filter fun E ↦ E.IsFull ∧
    fullDivisionMoveDistance D E = t)

@[simp] theorem mem_fullDivisionsAtMoveDistance
    {k n : Nat} {D E : SupercriticalDivision k (Fin n)} {t : Nat} :
    E ∈ fullDivisionsAtMoveDistance D t ↔
      E.IsFull ∧ fullDivisionMoveDistance D E = t := by
  classical
  simp [fullDivisionsAtMoveDistance]

/-- For a fixed ordered full division, the number of full divisions at move
distance `t` is at most `(k-1)! * choose(|V|,t) * (k-1)^t`. -/
theorem card_fullDivisionsAtMoveDistance_le
    {k n : Nat} (D : SupercriticalDivision k (Fin n))
    (hD : D.IsFull) (t : Nat) :
    (fullDivisionsAtMoveDistance D t).card ≤
      (k - 1).factorial * Nat.choose n t * (k - 1) ^ t := by
  classical
  let minimizingPermutation (E : SupercriticalDivision k (Fin n)) :
      Equiv.Perm (Fin (k - 1)) := Classical.choose
        (exists_moveCount_eq_moveDistance D E)
  have hmin (E : SupercriticalDivision k (Fin n)) :
      fullDivisionMoveCount D E (minimizingPermutation E) =
        fullDivisionMoveDistance D E :=
    Classical.choose_spec (exists_moveCount_eq_moveDistance D E)
  let Code := Σ sigma : Equiv.Perm (Fin (k - 1)),
    {q : Fin n → Fin (k - 1) //
      q ∈ DenseGraph.assignmentHammingSphere
        (fun v ↦ sigma (D.fullAssignment hD v)) t}
  let encode : {E // E ∈ fullDivisionsAtMoveDistance D t} → Code :=
    fun E ↦ ⟨minimizingPermutation E.1,
      ⟨E.1.fullAssignment (mem_fullDivisionsAtMoveDistance.mp E.2).1, by
        rw [DenseGraph.mem_assignmentHammingSphere]
        rw [← fullDivisionMoveCount_eq_hamming D E.1 hD
          (mem_fullDivisionsAtMoveDistance.mp E.2).1]
        rw [hmin E.1, (mem_fullDivisionsAtMoveDistance.mp E.2).2]⟩⟩
  have hencode : Function.Injective encode := by
    intro E F hEF
    apply Subtype.ext
    apply SupercriticalDivision.assignment_injective
    funext v
    rw [E.1.assignment_eq_some_fullAssignment
      (mem_fullDivisionsAtMoveDistance.mp E.2).1]
    rw [F.1.assignment_eq_some_fullAssignment
      (mem_fullDivisionsAtMoveDistance.mp F.2).1]
    congr 1
    exact congrFun (congrArg (fun c : Code ↦ c.2.1) hEF) v
  calc
    (fullDivisionsAtMoveDistance D t).card =
        Fintype.card {E // E ∈ fullDivisionsAtMoveDistance D t} := by
          exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card Code := Fintype.card_le_of_injective encode hencode
    _ = ∑ sigma : Equiv.Perm (Fin (k - 1)),
          (DenseGraph.assignmentHammingSphere
            (fun v ↦ sigma (D.fullAssignment hD v)) t).card := by
          rw [show Fintype.card Code =
              ∑ sigma : Equiv.Perm (Fin (k - 1)),
                Fintype.card {q : Fin n → Fin (k - 1) //
                  q ∈ DenseGraph.assignmentHammingSphere
                    (fun v ↦ sigma (D.fullAssignment hD v)) t} by
              simp only [Code, Fintype.card_sigma]]
          apply Finset.sum_congr rfl
          intro sigma _
          exact Fintype.card_coe _
    _ ≤ ∑ _sigma : Equiv.Perm (Fin (k - 1)),
          (Nat.choose n t * (k - 1) ^ t) := by
          apply Finset.sum_le_sum
          intro sigma _
          simpa using DenseGraph.card_assignmentHammingSphere_le
            (fun v ↦ sigma (D.fullAssignment hD v)) t
    _ = (k - 1).factorial * Nat.choose n t *
          (k - 1) ^ t := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin]
          simp [Nat.mul_assoc]

/-! ## Fibers inside the global family -/

/-- A prescribed full-division fiber is a subfamily of the global labeled
co-multipartite exact-edge family. -/
theorem supercriticalCoPartiteFiber_subset_global
    {k n m : Nat} (D : SupercriticalDivision k (Fin n)) :
    supercriticalCoPartiteFiber D m ⊆
      coMultipartiteGraphFinsetWithEdges (k - 1) n m := by
  intro G hG
  rw [mem_coMultipartiteGraphFinsetWithEdges]
  refine ⟨supercriticalCoPartiteFiber_isCoMultipartite hG, ?_⟩
  rw [← finiteGraphEdges_card_eq_edgeFinset_card]
  exact card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber hG

/-! ## Balanced cover pairs -/

/-- Pairs `(D,G)` consisting of a balanced ordered full division and a graph
in its exact co-multipartite fiber. -/
noncomputable def balancedCoMultipartiteCoverPairFinset
    (k n m : Nat) (beta : Real) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) :=
  (balancedFullSupercriticalDivisions k n beta).biUnion fun D ↦
    (supercriticalCoPartiteFiber D m).image fun G ↦ (D, G)

@[simp] theorem mem_balancedCoMultipartiteCoverPairFinset
    {k n m : Nat} {beta : Real}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ balancedCoMultipartiteCoverPairFinset k n m beta ↔
      IsBalancedFullDivision p.1 beta ∧
        p.2 ∈ supercriticalCoPartiteFiber p.1 m := by
  classical
  constructor
  · intro hp
    rw [balancedCoMultipartiteCoverPairFinset, Finset.mem_biUnion] at hp
    obtain ⟨D, hD, hp⟩ := hp
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨mem_balancedFullSupercriticalDivisions.mp hD, hG⟩
  · rintro ⟨hD, hG⟩
    rw [balancedCoMultipartiteCoverPairFinset, Finset.mem_biUnion]
    exact ⟨p.1, mem_balancedFullSupercriticalDivisions.mpr hD,
      Finset.mem_image.mpr ⟨p.2, hG, Prod.eta p⟩⟩

/-- Exact dependent-sum formula for balanced cover pairs. -/
theorem card_balancedCoMultipartiteCoverPairFinset
    (k n m : Nat) (beta : Real) :
    (balancedCoMultipartiteCoverPairFinset k n m beta).card =
      ∑ D ∈ balancedFullSupercriticalDivisions k n beta,
        (supercriticalCoPartiteFiber D m).card := by
  classical
  rw [balancedCoMultipartiteCoverPairFinset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.card_image_iff.mpr]
    intro G _ H _ h
    exact Prod.mk.inj h |>.2
  · intro D hD E hE hDE
    change Disjoint
      ((supercriticalCoPartiteFiber D m).image fun G ↦ (D, G))
      ((supercriticalCoPartiteFiber E m).image fun G ↦ (E, G))
    rw [Finset.disjoint_left]
    rintro p hpD hpE
    obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hpD
    obtain ⟨H, _, heq⟩ := Finset.mem_image.mp hpE
    exact hDE (Prod.mk.inj heq.symm).1

/-- Balanced ordered covers of one fixed graph. -/
noncomputable def balancedCoverDivisionFinset
    {k n : Nat} (m : Nat) (beta : Real) (G : SimpleGraph (Fin n)) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (balancedFullSupercriticalDivisions k n beta).filter fun D ↦
    G ∈ supercriticalCoPartiteFiber D m

@[simp] theorem mem_balancedCoverDivisionFinset
    {k n m : Nat} {beta : Real} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ balancedCoverDivisionFinset m beta G ↔
      IsBalancedFullDivision D beta ∧
        G ∈ supercriticalCoPartiteFiber D m := by
  simp [balancedCoverDivisionFinset]

/-- A graph with a unique unordered clique cover has at most `(k-1)!`
balanced ordered covers. -/
theorem card_balancedCoverDivisionFinset_le_factorial_of_unique
    {k n m : Nat} {beta : Real} {G : SimpleGraph (Fin n)}
    (hunique : HasUniqueCoMultipartiteCover k G) :
    (balancedCoverDivisionFinset (k := k) m beta G).card ≤
      (k - 1).factorial := by
  classical
  obtain ⟨D0, hD0full, hD0clique, hunique⟩ := hunique
  let choosePerm : {D // D ∈ balancedCoverDivisionFinset (k := k) m beta G} →
      Equiv.Perm (Fin (k - 1)) := fun D ↦
    Classical.choose (hunique D.1 (mem_balancedCoverDivisionFinset.mp D.2).1.1
      (fun i ↦ supercriticalCoPartiteFiber_isClique
        (mem_balancedCoverDivisionFinset.mp D.2).2 i))
  have hchoose : ∀ D : {D // D ∈ balancedCoverDivisionFinset (k := k) m beta G},
      D.1 = D0.reindexParts (choosePerm D) := fun D ↦
    Classical.choose_spec (hunique D.1
      (mem_balancedCoverDivisionFinset.mp D.2).1.1
      (fun i ↦ supercriticalCoPartiteFiber_isClique
        (mem_balancedCoverDivisionFinset.mp D.2).2 i))
  have hinj : Function.Injective choosePerm := by
    intro D E hperm
    apply Subtype.ext
    rw [hchoose D, hchoose E, hperm]
  calc
    (balancedCoverDivisionFinset (k := k) m beta G).card =
        Fintype.card {D // D ∈ balancedCoverDivisionFinset (k := k) m beta G} := by
          simp
    _ ≤ Fintype.card (Equiv.Perm (Fin (k - 1))) :=
      Fintype.card_le_of_injective choosePerm hinj
    _ = (k - 1).factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]

/-! ## Fixed-density cost of a second cover -/

/-- The portion of a prescribed `D`-fiber whose graphs also make every
part of `E` a clique. -/
noncomputable def supercriticalCoPartiteFiberWithSecondCover
    {k n : Nat} (D E : SupercriticalDivision k (Fin n)) (m : Nat) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCoPartiteFiber D m).filter fun G ↦
    ∀ i, G.IsClique (E.parts i : Set (Fin n))

@[simp] theorem mem_supercriticalCoPartiteFiberWithSecondCover
    {k n m : Nat} {D E : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCoPartiteFiberWithSecondCover D E m ↔
      G ∈ supercriticalCoPartiteFiber D m ∧
        ∀ i, G.IsClique (E.parts i : Set (Fin n)) := by
  simp [supercriticalCoPartiteFiberWithSecondCover]

private theorem forcedCrossChoices_subset_selected
    {k n : Nat} {D E : SupercriticalDivision k (Fin n)}
    {A : Finset (SupercriticalTaggedCrossChoice k (Fin n))}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D)
    (hclique : ∀ i,
      (supercriticalGraphOfCrossChoice D A).IsClique
        (E.parts i : Set (Fin n))) :
    forcedCrossChoicesBySecondCover D E ⊆ A := by
  intro z hz
  have hzData := (mem_forcedCrossChoicesBySecondCover D E z).mp hz
  have hedge : supercriticalTaggedCrossEdge z ∈
      (supercriticalGraphOfCrossChoice D A).edgeFinset :=
    forcedCrossEdgesBySecondCover_subset_edgeFinset D E
      (supercriticalGraphOfCrossChoice D A) hclique hzData.2
  have hadj : (supercriticalGraphOfCrossChoice D A).Adj z.2.1 z.2.2 := by
    simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      supercriticalTaggedCrossEdge] using hedge
  exact (supercriticalGraphOfCrossChoice_adj_iff D hA hzData.1).mp hadj

/-- Graphs with two prescribed clique covers inject into fixed-cardinality
cross-edge samples containing all coordinates forced by the second cover. -/
theorem card_supercriticalCoPartiteFiberWithSecondCover_le_containing
    {k n m : Nat} (D E : SupercriticalDivision k (Fin n)) :
    (supercriticalCoPartiteFiberWithSecondCover D E m).card ≤
      (DenseGraph.fixedCardinalityContainingFinset
        (supercriticalTaggedCrossChoiceUniverse D)
        (forcedCrossChoicesBySecondCover D E)
        (m - divisionInternalCliqueCapacity D)).card := by
  classical
  let containing := DenseGraph.fixedCardinalityContainingFinset
    (supercriticalTaggedCrossChoiceUniverse D)
    (forcedCrossChoicesBySecondCover D E)
    (m - divisionInternalCliqueCapacity D)
  let target := containing.image (supercriticalGraphOfCrossChoice D)
  have hsubset : supercriticalCoPartiteFiberWithSecondCover D E m ⊆ target := by
    intro G hG
    obtain ⟨hfiber, hclique⟩ :=
      mem_supercriticalCoPartiteFiberWithSecondCover.mp hG
    obtain ⟨_hfull, _hcapacity, A, hA, hAcard, hgraph⟩ :=
      mem_supercriticalCoPartiteFiber.mp hfiber
    apply Finset.mem_image.mpr
    refine ⟨A, ?_, hgraph⟩
    apply DenseGraph.mem_fixedCardinalityContainingFinset.mpr
    refine ⟨hA, hAcard, ?_⟩
    apply forcedCrossChoices_subset_selected hA
    intro i
    rw [hgraph]
    exact hclique i
  calc
    (supercriticalCoPartiteFiberWithSecondCover D E m).card ≤
        target.card := Finset.card_le_card hsubset
    _ ≤ containing.card := Finset.card_image_le

/-- Hypergeometric containment estimate for the second-cover subfiber. -/
theorem card_supercriticalCoPartiteFiberWithSecondCover_real_le
    {k n m : Nat} (D E : SupercriticalDivision k (Fin n))
    (hD : D.IsFull)
    (hlower : divisionInternalCliqueCapacity D ≤ m)
    (hupper : m ≤ divisionInternalCliqueCapacity D +
      supercriticalTotalCrossCapacity D)
    (hcross : 0 < supercriticalTotalCrossCapacity D) :
    ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
      ((supercriticalCoPartiteFiber D m).card : Real) *
        (((m - divisionInternalCliqueCapacity D : Nat) : Real) /
          (supercriticalTotalCrossCapacity D : Real)) ^
            (forcedCrossEdgesBySecondCover D E).card := by
  classical
  let U := supercriticalTaggedCrossChoiceUniverse D
  let F := forcedCrossChoicesBySecondCover D E
  let L := m - divisionInternalCliqueCapacity D
  have hFU : F ⊆ U := forcedCrossChoicesBySecondCover_subset_universe D E
  have hLU : L ≤ U.card := by
    simpa [L, U] using (show m - divisionInternalCliqueCapacity D ≤
        supercriticalTotalCrossCapacity D by omega)
  have hUpos : 0 < U.card := by simpa [U] using hcross
  have hcontain := card_supercriticalCoPartiteFiberWithSecondCover_le_containing
    (m := m) D E
  have hcontainReal :
      ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        ((DenseGraph.fixedCardinalityContainingFinset U F L).card : Real) := by
    exact_mod_cast hcontain
  have hprob := DenseGraph.fixedCardinality_probability_contains_le_density_pow
    hFU hLU hUpos
  have hchoose : (Nat.choose U.card L : Real) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hLU
  have hcontainEq :
      ((DenseGraph.fixedCardinalityContainingFinset U F L).card : Real) =
        DenseGraph.fixedCardinalityContainmentProbability U F L *
          (Nat.choose U.card L : Real) := by
    unfold DenseGraph.fixedCardinalityContainmentProbability
    field_simp
  have hfiber : ((supercriticalCoPartiteFiber D m).card : Real) =
      (Nat.choose U.card L : Real) := by
    rw [card_supercriticalCoPartiteFiber D hD, if_pos hlower]
    simp [U, L]
  calc
    ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        ((DenseGraph.fixedCardinalityContainingFinset U F L).card : Real) :=
      hcontainReal
    _ = DenseGraph.fixedCardinalityContainmentProbability U F L *
        (Nat.choose U.card L : Real) := hcontainEq
    _ ≤ (((L : Nat) : Real) / (U.card : Real)) ^ F.card *
        (Nat.choose U.card L : Real) := by
      exact mul_le_mul_of_nonneg_right hprob (by positivity)
    _ = ((supercriticalCoPartiteFiber D m).card : Real) *
        (((m - divisionInternalCliqueCapacity D : Nat) : Real) /
          (supercriticalTotalCrossCapacity D : Real)) ^
            (forcedCrossEdgesBySecondCover D E).card := by
      rw [hfiber, card_forcedCrossChoicesBySecondCover]
      simp [U, L, mul_comm]

/-- With at least two main parts, the cross-coordinate universe is
nonempty. -/
theorem supercriticalTotalCrossCapacity_pos
    {k : Nat} (hk : 3 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) :
    0 < supercriticalTotalCrossCapacity D := by
  let i : Fin (k - 1) := ⟨0, by omega⟩
  let j : Fin (k - 1) := ⟨1, by omega⟩
  let e : SupercriticalPartPair k :=
    SupercriticalPartPair.ofDistinct i j (by simp [i, j])
  unfold supercriticalTotalCrossCapacity
  exact Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _)
    ⟨e, Finset.mem_univ _, crossEdgeCapacity_pos D e⟩

/-- Graphs in a fixed fiber for which the displayed cover is not the unique
unordered clique cover. -/
noncomputable def supercriticalCoPartiteFiberNonuniqueCover
    {k n : Nat} (D : SupercriticalDivision k (Fin n)) (m : Nat) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCoPartiteFiber D m).filter fun G ↦
    ¬ HasUniqueCoMultipartiteCover k G

@[simp] theorem mem_supercriticalCoPartiteFiberNonuniqueCover
    {k n m : Nat} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCoPartiteFiberNonuniqueCover D m ↔
      G ∈ supercriticalCoPartiteFiber D m ∧
        ¬ HasUniqueCoMultipartiteCover k G := by
  simp [supercriticalCoPartiteFiberNonuniqueCover]

/-- Full competing covers which are genuinely different from `D` modulo
part relabeling. -/
noncomputable def competingFullSupercriticalDivisions
    {k n : Nat} (D : SupercriticalDivision k (Fin n)) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact (fullSupercriticalDivisions k n).filter fun E ↦
    ¬ FullDivisionsEquivalent D E

@[simp] theorem mem_competingFullSupercriticalDivisions
    {k n : Nat} {D E : SupercriticalDivision k (Fin n)} :
    E ∈ competingFullSupercriticalDivisions D ↔
      E.IsFull ∧ ¬ FullDivisionsEquivalent D E := by
  simp [competingFullSupercriticalDivisions]

/-- Every nonunique graph in the `D`-fiber is witnessed by a genuinely
different full second cover. -/
theorem supercriticalCoPartiteFiberNonuniqueCover_subset_biUnion
    {k n m : Nat} (D : SupercriticalDivision k (Fin n)) :
    supercriticalCoPartiteFiberNonuniqueCover D m ⊆
      (competingFullSupercriticalDivisions D).biUnion fun E ↦
        supercriticalCoPartiteFiberWithSecondCover D E m := by
  classical
  intro G hG
  obtain ⟨hGD, hnotUnique⟩ :=
    mem_supercriticalCoPartiteFiberNonuniqueCover.mp hG
  have hDfull := (mem_supercriticalCoPartiteFiber.mp hGD).1
  have hDclique : ∀ i, G.IsClique (D.parts i : Set (Fin n)) :=
    fun i ↦ supercriticalCoPartiteFiber_isClique hGD i
  have hexists : ∃ E : SupercriticalDivision k (Fin n),
      E.IsFull ∧ (∀ i, G.IsClique (E.parts i : Set (Fin n))) ∧
        ¬ FullDivisionsEquivalent D E := by
    by_contra hnone
    apply hnotUnique
    refine ⟨D, hDfull, hDclique, ?_⟩
    intro E hEfull hEclique
    by_contra hnot
    exact hnone ⟨E, hEfull, hEclique, hnot⟩
  obtain ⟨E, hEfull, hEclique, hnotEquiv⟩ := hexists
  apply Finset.mem_biUnion.mpr
  exact ⟨E, mem_competingFullSupercriticalDivisions.mpr
    ⟨hEfull, hnotEquiv⟩,
    mem_supercriticalCoPartiteFiberWithSecondCover.mpr ⟨hGD, hEclique⟩⟩

theorem card_supercriticalCoPartiteFiberNonuniqueCover_le_sum
    {k n m : Nat} (D : SupercriticalDivision k (Fin n)) :
    (supercriticalCoPartiteFiberNonuniqueCover D m).card ≤
      ∑ E ∈ competingFullSupercriticalDivisions D,
        (supercriticalCoPartiteFiberWithSecondCover D E m).card := by
  calc
    (supercriticalCoPartiteFiberNonuniqueCover D m).card ≤
        ((competingFullSupercriticalDivisions D).biUnion fun E ↦
          supercriticalCoPartiteFiberWithSecondCover D E m).card :=
      Finset.card_le_card
        (supercriticalCoPartiteFiberNonuniqueCover_subset_biUnion D)
    _ ≤ ∑ E ∈ competingFullSupercriticalDivisions D,
          (supercriticalCoPartiteFiberWithSecondCover D E m).card :=
      Finset.card_biUnion_le

/-- The cross-edge density in a feasible full fiber is at most the total
edge density. -/
theorem coPartiteFiber_crossDensity_le_totalDensity
    {k n m : Nat} (D : SupercriticalDivision k (Fin n))
    (hD : D.IsFull)
    (hlower : divisionInternalCliqueCapacity D ≤ m)
    (hcross : 0 < supercriticalTotalCrossCapacity D)
    (hm : m ≤ completeEdgeCount n) :
    ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
        (supercriticalTotalCrossCapacity D : Real) ≤
      (m : Real) / (completeEdgeCount n : Real) := by
  have hsum := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hD] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  change ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
        (supercriticalTotalCrossCapacity D : Real) ≤
      (m : Real) / (Nat.choose n 2 : Real)
  rw [← hsum]
  push_cast
  have hcrossPos : (0 : Real) < supercriticalTotalCrossCapacity D := by
    exact_mod_cast hcross
  have htotalPos : (0 : Real) <
      supercriticalTotalCrossCapacity D + divisionInternalCliqueCapacity D := by
    positivity
  rw [div_le_div_iff₀ hcrossPos htotalPos]
  rw [Nat.cast_sub hlower]
  have hmNat : m ≤ supercriticalTotalCrossCapacity D +
      divisionInternalCliqueCapacity D := by
    unfold completeEdgeCount at hm
    omega
  have hm' : (m : Real) ≤
      supercriticalTotalCrossCapacity D + divisionInternalCliqueCapacity D := by
    exact_mod_cast hmNat
  nlinarith

/-- Exponential form of the fixed-density second-cover cost. -/
theorem card_supercriticalCoPartiteFiberWithSecondCover_le_exp_forced
    {k n m : Nat} (D E : SupercriticalDivision k (Fin n))
    (hD : D.IsFull)
    (hlower : divisionInternalCliqueCapacity D ≤ m)
    (hupper : m ≤ divisionInternalCliqueCapacity D +
      supercriticalTotalCrossCapacity D)
    (hcross : 0 < supercriticalTotalCrossCapacity D)
    {c : Real} (hc : 0 ≤ c)
    (hdensity :
      ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
          (supercriticalTotalCrossCapacity D : Real) ≤ Real.exp (-c)) :
    ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
      ((supercriticalCoPartiteFiber D m).card : Real) *
        Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) := by
  have hbase0 : (0 : Real) ≤
      ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
        (supercriticalTotalCrossCapacity D : Real) := by positivity
  have hpow := pow_le_pow_left₀ hbase0 hdensity
    (forcedCrossEdgesBySecondCover D E).card
  have hmain := card_supercriticalCoPartiteFiberWithSecondCover_real_le
    D E hD hlower hupper hcross
  calc
    ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        ((supercriticalCoPartiteFiber D m).card : Real) *
          (((m - divisionInternalCliqueCapacity D : Nat) : Real) /
            (supercriticalTotalCrossCapacity D : Real)) ^
              (forcedCrossEdgesBySecondCover D E).card := hmain
    _ ≤ ((supercriticalCoPartiteFiber D m).card : Real) *
          (Real.exp (-c)) ^ (forcedCrossEdgesBySecondCover D E).card := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((supercriticalCoPartiteFiber D m).card : Real) *
        Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

theorem fullDivisionMoveDistance_le_card
    {k : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    (D E : SupercriticalDivision k V) :
    fullDivisionMoveDistance D E ≤ Fintype.card V := by
  obtain ⟨sigma, hsigma⟩ := exists_moveCount_eq_moveDistance D E
  rw [← hsigma]
  unfold fullDivisionMoveCount
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
    Finset.card_univ

private theorem exp_forced_le_exp_near
    {k n : Nat} (hk : 3 ≤ k) {c : Real} (hc : 0 ≤ c)
    {t q : Nat} (hforced : t * n ≤ 4 * (k - 1) * q) :
    Real.exp (-(c * q)) ≤
      Real.exp (-((c / (4 * (k - 1))) * t * n)) := by
  apply Real.exp_le_exp.mpr
  have hkr : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (by omega : 0 < k - 1)
  have hr : (0 : Real) < 4 * (k - 1 : Nat) := mul_pos (by norm_num) hkr
  have hforcedReal : (t : Real) * n ≤
      (4 * (k - 1 : Nat) : Real) * q := by exact_mod_cast hforced
  have hdiv : ((t : Real) * n) / (4 * (k - 1 : Nat) : Real) ≤ q := by
    exact (div_le_iff₀ hr).mpr (by simpa [mul_comm, mul_left_comm] using hforcedReal)
  have := mul_le_mul_of_nonneg_left hdiv hc
  have heq : c * (((t : Real) * n) / (4 * (k - 1 : Nat) : Real)) =
      (c / (4 * (k - 1 : Nat))) * t * n := by
    field_simp
    <;> ring
  rw [heq] at this
  simpa [Nat.cast_sub (by omega : 1 ≤ k)] using neg_le_neg this

private theorem exp_forced_le_exp_far
    {k n : Nat} (hk : 3 ≤ k) {c : Real} (hc : 0 ≤ c)
    {q : Nat} (hforced : n ^ 2 ≤ 16 * (k - 1) ^ 8 * q) :
    Real.exp (-(c * q)) ≤
      Real.exp (-((c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2)) := by
  apply Real.exp_le_exp.mpr
  have hkr : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (by omega : 0 < k - 1)
  have hr : (0 : Real) < 16 * (k - 1 : Nat) ^ 8 :=
    mul_pos (by norm_num) (pow_pos hkr _)
  have hforcedReal : (n : Real) ^ 2 ≤
      (16 * (k - 1 : Nat) ^ 8 : Real) * q := by exact_mod_cast hforced
  have hdiv : (n : Real) ^ 2 /
      (16 * (k - 1 : Nat) ^ 8 : Real) ≤ q := by
    exact (div_le_iff₀ hr).mpr (by simpa [mul_comm] using hforcedReal)
  have := mul_le_mul_of_nonneg_left hdiv hc
  have heq : c * ((n : Real) ^ 2 /
      (16 * (k - 1 : Nat) ^ 8 : Real)) =
      (c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2 := by
    field_simp
    <;> ring
  rw [heq] at this
  exact neg_le_neg this

private theorem sum_group_by_moveDistance
    {k n : Nat} (D : SupercriticalDivision k (Fin n))
    (S : Finset (SupercriticalDivision k (Fin n)))
    (hpos : ∀ E ∈ S, 1 ≤ fullDivisionMoveDistance D E)
    (f : Nat → Real) :
    ∑ E ∈ S, f (fullDivisionMoveDistance D E) =
      ∑ t ∈ Finset.Icc 1 n,
        ((S.filter fun E ↦ fullDivisionMoveDistance D E = t).card : Real) *
          f t := by
  classical
  let d := fun E : SupercriticalDivision k (Fin n) ↦
    fullDivisionMoveDistance D E
  have hdmem : ∀ E ∈ S, d E ∈ Finset.Icc 1 n := by
    intro E hE
    exact Finset.mem_Icc.mpr ⟨hpos E hE,
      by simpa [d] using fullDivisionMoveDistance_le_card D E⟩
  calc
    ∑ E ∈ S, f (fullDivisionMoveDistance D E) =
        ∑ E ∈ S, ∑ t ∈ Finset.Icc 1 n,
          if d E = t then f t else 0 := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_eq_single (d E)]
      · simp [d]
      · intro t ht hne
        simp [hne.symm]
      · exact fun hnot ↦ (hnot (hdmem E hE)).elim
    _ = ∑ t ∈ Finset.Icc 1 n, ∑ E ∈ S,
          if d E = t then f t else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ Finset.Icc 1 n,
        ((S.filter fun E ↦ fullDivisionMoveDistance D E = t).card : Real) *
          f t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter]
      simp [d]

/-- Explicit finite near/far union bound for all competing covers of one
full division.  This is the quantitative core of cover uniqueness; the two
terms are respectively summed by Hamming distance and by the crude `k^n`
enumeration. -/
theorem card_supercriticalCoPartiteFiberNonuniqueCover_le_near_far
    {k n m a : Nat} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n))
    (hD : D.IsFull)
    (hpart : ∀ i, a ≤ (D.parts i).card)
    (hscale : n ≤ 2 * (k - 1) * a)
    (hlower : divisionInternalCliqueCapacity D ≤ m)
    (hupper : m ≤ divisionInternalCliqueCapacity D +
      supercriticalTotalCrossCapacity D)
    {c : Real} (hc : 0 < c)
    (hdensity :
      ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
          (supercriticalTotalCrossCapacity D : Real) ≤ Real.exp (-c)) :
    ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
      ((supercriticalCoPartiteFiber D m).card : Real) *
        (∑ t ∈ Finset.Icc 1 n,
          (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
            Real.exp (-((c / (4 * (k - 1 : Nat))) * t * n)) +
        ((k ^ n : Nat) : Real) *
          Real.exp (-((c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2))) := by
  classical
  let S := competingFullSupercriticalDivisions D
  let N := S.filter fun E ↦ 2 * fullDivisionMoveDistance D E ≤ a
  let F := S.filter fun E ↦ ¬ 2 * fullDivisionMoveDistance D E ≤ a
  let fiber : Real := (supercriticalCoPartiteFiber D m).card
  let cNear : Real := c / (4 * (k - 1 : Nat))
  let cFar : Real := c / (16 * (k - 1 : Nat) ^ 8)
  have hcross := supercriticalTotalCrossCapacity_pos hk D
  have hcardNat :=
    card_supercriticalCoPartiteFiberNonuniqueCover_le_sum (m := m) D
  have hcard : ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
      ∑ E ∈ S,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) := by
    exact_mod_cast hcardNat
  have hsplit :
      (∑ E ∈ S,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) =
      (∑ E ∈ N,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) +
      (∑ E ∈ F,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) := by
    simpa [N, F] using
      (Finset.sum_filter_add_sum_filter_not S
        (fun E ↦ 2 * fullDivisionMoveDistance D E ≤ a)
        (fun E ↦
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real))).symm
  have hbase (E : SupercriticalDivision k (Fin n)) :
      ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        fiber * Real.exp (-(c * (forcedCrossEdgesBySecondCover D E).card)) := by
    simpa [fiber] using
      card_supercriticalCoPartiteFiberWithSecondCover_le_exp_forced
        D E hD hlower hupper hcross hc.le hdensity
  have hnearPoint (E : SupercriticalDivision k (Fin n)) (hEN : E ∈ N) :
      ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        fiber * Real.exp (-(cNear * fullDivisionMoveDistance D E * n)) := by
    have hES : E ∈ S := (Finset.mem_filter.mp hEN).1
    have hnear : 2 * fullDivisionMoveDistance D E ≤ a :=
      (Finset.mem_filter.mp hEN).2
    obtain ⟨hEfull, hnotEquiv⟩ :=
      mem_competingFullSupercriticalDivisions.mp hES
    have hdich := forcedCrossEdges_near_or_far hk D E hD hEfull a
      hpart (by simpa using hscale) hnotEquiv
    dsimp only at hdich
    have hforced : fullDivisionMoveDistance D E * n ≤
        4 * (k - 1) * (forcedCrossEdgesBySecondCover D E).card := by
      rcases hdich with hnearData | hfarData
      · simpa using hnearData.2.2
      · omega
    exact (hbase E).trans (mul_le_mul_of_nonneg_left
      (by simpa [cNear, Nat.cast_sub (by omega : 1 ≤ k)] using
        exp_forced_le_exp_near hk hc.le hforced)
      (by positivity))
  have hfarPoint (E : SupercriticalDivision k (Fin n)) (hEF : E ∈ F) :
      ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) ≤
        fiber * Real.exp (-(cFar * (n : Real) ^ 2)) := by
    have hES : E ∈ S := (Finset.mem_filter.mp hEF).1
    have hnotNear : ¬ 2 * fullDivisionMoveDistance D E ≤ a :=
      (Finset.mem_filter.mp hEF).2
    obtain ⟨hEfull, hnotEquiv⟩ :=
      mem_competingFullSupercriticalDivisions.mp hES
    have hdich := forcedCrossEdges_near_or_far hk D E hD hEfull a
      hpart (by simpa using hscale) hnotEquiv
    dsimp only at hdich
    have hforced : n ^ 2 ≤
        16 * (k - 1) ^ 8 * (forcedCrossEdgesBySecondCover D E).card := by
      rcases hdich with hnearData | hfarData
      · exact False.elim (hnotNear hnearData.2.1)
      · simpa using hfarData.2
    exact (hbase E).trans (mul_le_mul_of_nonneg_left
      (by simpa [cFar] using exp_forced_le_exp_far hk hc.le hforced)
      (by positivity))
  have hNpos : ∀ E ∈ N, 1 ≤ fullDivisionMoveDistance D E := by
    intro E hEN
    have hES : E ∈ S := (Finset.mem_filter.mp hEN).1
    have hnot := (mem_competingFullSupercriticalDivisions.mp hES).2
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    exact hnot ((fullDivisionMoveDistance_eq_zero_iff D E).mp hzero)
  have hnearSum :
      (∑ E ∈ N,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) ≤
      fiber * (∑ t ∈ Finset.Icc 1 n,
        (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
          Real.exp (-(cNear * t * n))) := by
    calc
      (∑ E ∈ N,
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) ≤
          ∑ E ∈ N, fiber *
            Real.exp (-(cNear * fullDivisionMoveDistance D E * n)) := by
        exact Finset.sum_le_sum fun E hE ↦ hnearPoint E hE
      _ = fiber * ∑ E ∈ N,
            Real.exp (-(cNear * fullDivisionMoveDistance D E * n)) := by
        rw [Finset.mul_sum]
      _ = fiber * ∑ t ∈ Finset.Icc 1 n,
          (((N.filter fun E ↦ fullDivisionMoveDistance D E = t).card : Real) *
            Real.exp (-(cNear * t * n))) := by
        congr 1
        simpa using sum_group_by_moveDistance D N hNpos
          (fun t ↦ Real.exp (-(cNear * (t : Real) * (n : Real))))
      _ ≤ fiber * (∑ t ∈ Finset.Icc 1 n,
          (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
            Real.exp (-(cNear * t * n))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro t ht
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact_mod_cast (calc
          (N.filter fun E ↦ fullDivisionMoveDistance D E = t).card ≤
              (fullDivisionsAtMoveDistance D t).card := by
            apply Finset.card_le_card
            intro E hE
            have hEN := (Finset.mem_filter.mp hE).1
            have hES := (Finset.mem_filter.mp hEN).1
            exact mem_fullDivisionsAtMoveDistance.mpr
              ⟨(mem_competingFullSupercriticalDivisions.mp hES).1,
                (Finset.mem_filter.mp hE).2⟩
          _ ≤ (k - 1).factorial * Nat.choose n t * (k - 1) ^ t :=
            card_fullDivisionsAtMoveDistance_le D hD t)
  have hFcard : F.card ≤ k ^ n := by
    calc
      F.card ≤ (allSupercriticalDivisions k n).card := by
        apply Finset.card_le_card
        intro E hEF
        exact mem_allSupercriticalDivisions E
      _ ≤ k ^ n := card_allSupercriticalDivisions_le (by omega)
  have hfarSum :
      (∑ E ∈ F,
        ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) ≤
      fiber * ((k ^ n : Nat) : Real) *
        Real.exp (-(cFar * (n : Real) ^ 2)) := by
    calc
      (∑ E ∈ F,
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) ≤
          ∑ _E ∈ F, fiber * Real.exp (-(cFar * (n : Real) ^ 2)) := by
        exact Finset.sum_le_sum fun E hE ↦ hfarPoint E hE
      _ = (F.card : Real) *
          (fiber * Real.exp (-(cFar * (n : Real) ^ 2))) := by simp
      _ ≤ ((k ^ n : Nat) : Real) *
          (fiber * Real.exp (-(cFar * (n : Real) ^ 2))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast hFcard
      _ = fiber * ((k ^ n : Nat) : Real) *
          Real.exp (-(cFar * (n : Real) ^ 2)) := by ring
  calc
    ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
        ∑ E ∈ S,
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real) := hcard
    _ = (∑ E ∈ N,
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) +
        (∑ E ∈ F,
          ((supercriticalCoPartiteFiberWithSecondCover D E m).card : Real)) := hsplit
    _ ≤ fiber * (∑ t ∈ Finset.Icc 1 n,
          (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
            Real.exp (-(cNear * t * n))) +
        fiber * ((k ^ n : Nat) : Real) *
          Real.exp (-(cFar * (n : Real) ^ 2)) := add_le_add hnearSum hfarSum
    _ = ((supercriticalCoPartiteFiber D m).card : Real) *
        (∑ t ∈ Finset.Icc 1 n,
          (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
            Real.exp (-((c / (4 * (k - 1 : Nat))) * t * n)) +
        ((k ^ n : Nat) : Real) *
          Real.exp (-((c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2))) := by
      simp only [fiber, cNear, cFar]
      ring

/-! ## Uniform exponential uniqueness -/

private theorem eventually_coverNearSum_le
    (r : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in Filter.atTop,
      ∑ t ∈ Finset.Icc 1 n,
        ((r.factorial * Nat.choose n t * r ^ t : Nat) : Real) *
          Real.exp (-(c * (t : Real) * (n : Real))) ≤
        Real.exp (-((c / 4) * (n : Real))) := by
  let A := (r.factorial + 1) * (r + 1)
  have hcHalf : 0 < c / 2 := half_pos hc
  filter_upwards [DenseGraph.eventually_natCast_mul_le_exp_mul A hcHalf,
      DenseGraph.eventually_sum_Icc_exp_neg_mul_le hcHalf,
      Filter.eventually_ge_atTop 1] with n hnExp hnSum hnPos
  have hterm (t : Nat) (ht : t ∈ Finset.Icc 1 n) :
      ((r.factorial * Nat.choose n t * r ^ t : Nat) : Real) *
          Real.exp (-(c * (t : Real) * (n : Real))) ≤
        Real.exp (-((c / 2) * (t : Real) * (n : Real))) := by
    have htPos : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have hfacBase : (1 : Real) ≤ (r.factorial + 1 : Nat) := by norm_num
    have hrBase : (1 : Real) ≤ (r + 1 : Nat) := by norm_num
    have hfac : (r.factorial : Real) ≤
        ((r.factorial + 1 : Nat) : Real) ^ t := by
      calc
        (r.factorial : Real) ≤ (r.factorial + 1 : Nat) := by norm_num
        _ = (((r.factorial + 1 : Nat) : Real) ^ 1) := by simp
        _ ≤ (((r.factorial + 1 : Nat) : Real) ^ t) :=
          pow_le_pow_right₀ hfacBase htPos
    have hr : (r : Real) ^ t ≤ ((r + 1 : Nat) : Real) ^ t := by
      exact pow_le_pow_left₀ (by positivity) (by norm_num) t
    have hchoose : (Nat.choose n t : Real) ≤ (n : Real) ^ t := by
      exact_mod_cast Nat.choose_le_pow n t
    have hoverhead :
        ((r.factorial * Nat.choose n t * r ^ t : Nat) : Real) ≤
          (((A : Real) * (n : Real)) ^ t) := by
      push_cast
      calc
        (r.factorial : Real) * Nat.choose n t * (r : Real) ^ t ≤
            ((r.factorial + 1 : Nat) : Real) ^ t *
              (n : Real) ^ t * ((r + 1 : Nat) : Real) ^ t := by
          gcongr
        _ = (((A : Real) * (n : Real)) ^ t) := by
          simp only [A, Nat.cast_mul, mul_pow]
          ring
    have hpowExp : (((A : Real) * (n : Real)) ^ t) ≤
        (Real.exp ((c / 2) * (n : Real))) ^ t :=
      pow_le_pow_left₀ (by positivity) hnExp t
    calc
      ((r.factorial * Nat.choose n t * r ^ t : Nat) : Real) *
          Real.exp (-(c * (t : Real) * (n : Real))) ≤
        (Real.exp ((c / 2) * (n : Real))) ^ t *
          Real.exp (-(c * (t : Real) * (n : Real))) := by
        gcongr
        exact hoverhead.trans hpowExp
      _ = Real.exp (-((c / 2) * (t : Real) * (n : Real))) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
  calc
    ∑ t ∈ Finset.Icc 1 n,
        ((r.factorial * Nat.choose n t * r ^ t : Nat) : Real) *
          Real.exp (-(c * (t : Real) * (n : Real))) ≤
      ∑ t ∈ Finset.Icc 1 n,
        Real.exp (-((c / 2) * (t : Real) * (n : Real))) := by
      exact Finset.sum_le_sum fun t ht ↦ hterm t ht
    _ ≤ Real.exp (-(((c / 2) / 2) * (n : Real))) := hnSum
    _ = Real.exp (-((c / 4) * (n : Real))) := by ring_nf

private theorem eventually_pow_mul_exp_neg_sq_le
    (r : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in Filter.atTop,
      ((r ^ n : Nat) : Real) * Real.exp (-(c * (n : Real) ^ 2)) ≤
        Real.exp (-((c / 2) * (n : Real) ^ 2)) := by
  have hcHalf : 0 < c / 2 := half_pos hc
  filter_upwards [DenseGraph.eventually_natCast_mul_le_exp_mul (r + 1) hcHalf,
      Filter.eventually_ge_atTop 1] with n hnExp hnPos
  have hr : (r : Real) ≤ ((r + 1 : Nat) : Real) * n := by
    calc
      (r : Real) ≤ (r + 1 : Nat) := by norm_num
      _ ≤ ((r + 1 : Nat) : Real) * n := by
        nlinarith [show (1 : Real) ≤ n by exact_mod_cast hnPos]
  have hrExp : ((r ^ n : Nat) : Real) ≤
      (Real.exp ((c / 2) * (n : Real))) ^ n := by
    push_cast
    exact pow_le_pow_left₀ (by positivity) (hr.trans hnExp) n
  calc
    ((r ^ n : Nat) : Real) * Real.exp (-(c * (n : Real) ^ 2)) ≤
        (Real.exp ((c / 2) * (n : Real))) ^ n *
          Real.exp (-(c * (n : Real) ^ 2)) := by
      gcongr
    _ = Real.exp (-((c / 2) * (n : Real) ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- The rate retained after absorbing both the Hamming-sphere and far-cover
overheads. -/
def supercriticalCoverUniquenessRate (k : Nat) (c : Real) : Real :=
  min (c / (16 * (k - 1 : Nat)))
      (c / (32 * (k - 1 : Nat) ^ 8)) / 2

theorem supercriticalCoverUniquenessRate_pos
    {k : Nat} (hk : 3 ≤ k) {c : Real} (hc : 0 < c) :
    0 < supercriticalCoverUniquenessRate k c := by
  unfold supercriticalCoverUniquenessRate
  have hkr : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (by omega : 0 < k - 1)
  exact half_pos (lt_min
    (div_pos hc (mul_pos (by norm_num) hkr))
    (div_pos hc (mul_pos (by norm_num) (pow_pos hkr _))))

/-- Uniform exponential nonuniqueness estimate once the elementary balance
and density hypotheses needed by the forced-edge dichotomy are supplied. -/
theorem eventually_balancedCoPartiteFiber_nonuniqueCover_card_le_of_geometry
    {k : Nat} (hk : 3 ≤ k) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m a : Nat,
      ∀ D : SupercriticalDivision k (Fin n),
        D.IsFull →
        (∀ i, a ≤ (D.parts i).card) →
        n ≤ 2 * (k - 1) * a →
        divisionInternalCliqueCapacity D ≤ m →
        m ≤ divisionInternalCliqueCapacity D +
          supercriticalTotalCrossCapacity D →
        ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
            (supercriticalTotalCrossCapacity D : Real) ≤ Real.exp (-c) →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
          ((supercriticalCoPartiteFiber D m).card : Real) *
            Real.exp (-(supercriticalCoverUniquenessRate k c * (n : Real))) := by
  let dNear : Real := c / (16 * (k - 1 : Nat))
  let dFar : Real := c / (32 * (k - 1 : Nat) ^ 8)
  let d : Real := min dNear dFar
  have hkr : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (by omega : 0 < k - 1)
  have hcNear : 0 < c / (4 * (k - 1 : Nat)) :=
    div_pos hc (mul_pos (by norm_num) hkr)
  have hcFar : 0 < c / (16 * (k - 1 : Nat) ^ 8) :=
    div_pos hc (mul_pos (by norm_num) (pow_pos hkr _))
  have hdNear : 0 < dNear := by
    exact div_pos hc (mul_pos (by norm_num) hkr)
  have hdFar : 0 < dFar := by
    exact div_pos hc (mul_pos (by norm_num) (pow_pos hkr _))
  have hd : 0 < d := lt_min hdNear hdFar
  filter_upwards [eventually_coverNearSum_le (k - 1) hcNear,
      eventually_pow_mul_exp_neg_sq_le k hcFar,
      DenseGraph.eventually_natCast_mul_le_exp_mul 2 (half_pos hd),
      Filter.eventually_ge_atTop 1] with n hNear hFar hTwo hnPos
      m a D hD hpart hscale hlower hupper hdensity
  have hfinite := card_supercriticalCoPartiteFiberNonuniqueCover_le_near_far
    hk D hD hpart hscale hlower hupper hc hdensity
  have hfarLinear :
      Real.exp (-((c / (32 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2)) ≤
        Real.exp (-(d * (n : Real))) := by
    apply Real.exp_le_exp.mpr
    have hnReal : (1 : Real) ≤ n := by exact_mod_cast hnPos
    have hsq : (n : Real) ≤ (n : Real) ^ 2 := by nlinarith
    have hdle : d ≤ dFar := min_le_right _ _
    have := mul_le_mul hdle hsq (by positivity) hdFar.le
    simpa [dFar] using neg_le_neg this
  have hnearLinear :
      Real.exp (-((c / (16 * (k - 1 : Nat))) * (n : Real))) ≤
        Real.exp (-(d * (n : Real))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left dNear dFar)
      (by positivity))
  have htwoSimple : (2 : Real) ≤ Real.exp ((d / 2) * (n : Real)) := by
    have hnReal : (1 : Real) ≤ n := by exact_mod_cast hnPos
    calc
      (2 : Real) ≤ 2 * (n : Real) := by nlinarith
      _ ≤ Real.exp ((d / 2) * (n : Real)) := by simpa using hTwo
  have hNear' :
      ∑ t ∈ Finset.Icc 1 n,
          (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
            Real.exp (-((c / (4 * (k - 1 : Nat))) * t * n)) ≤
        Real.exp (-(dNear * (n : Real))) := by
    convert hNear using 1 <;> simp only [dNear] <;> ring
  have hFar' :
      ((k ^ n : Nat) : Real) *
          Real.exp (-((c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2)) ≤
        Real.exp (-(dFar * (n : Real) ^ 2)) := by
    convert hFar using 1 <;> simp only [dFar] <;> ring
  calc
    ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
        ((supercriticalCoPartiteFiber D m).card : Real) *
          (∑ t ∈ Finset.Icc 1 n,
            (((k - 1).factorial * Nat.choose n t * (k - 1) ^ t : Nat) : Real) *
              Real.exp (-((c / (4 * (k - 1 : Nat))) * t * n)) +
          ((k ^ n : Nat) : Real) *
            Real.exp (-((c / (16 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2))) :=
      hfinite
    _ ≤ ((supercriticalCoPartiteFiber D m).card : Real) *
          (Real.exp (-((c / (16 * (k - 1 : Nat))) * (n : Real))) +
            Real.exp (-((c / (32 * (k - 1 : Nat) ^ 8)) * (n : Real) ^ 2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add hNear' hFar'
    _ ≤ ((supercriticalCoPartiteFiber D m).card : Real) *
          (2 * Real.exp (-(d * (n : Real)))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    _ ≤ ((supercriticalCoPartiteFiber D m).card : Real) *
          Real.exp (-((d / 2) * (n : Real))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        2 * Real.exp (-(d * (n : Real))) ≤
            Real.exp ((d / 2) * (n : Real)) *
              Real.exp (-(d * (n : Real))) := by gcongr
        _ = Real.exp (-((d / 2) * (n : Real))) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = ((supercriticalCoPartiteFiber D m).card : Real) *
          Real.exp (-(supercriticalCoverUniquenessRate k c * (n : Real))) := by
      simp [supercriticalCoverUniquenessRate, d, dNear, dFar]

/-- Fixed balance radius used by the cover-multiplicity argument. -/
def supercriticalCoverBalanceRadius (k : Nat) : Real :=
  1 / (8 * (k - 1 : Nat))

/-- A fixed density neighborhood which remains strictly below one. -/
def supercriticalCoverDensityTolerance (gamma : Real) : Real :=
  (1 - gamma) / 2

/-- Exponential containment rate associated with the upper density
`(1+gamma)/2`. -/
def supercriticalCoverLogRate (gamma : Real) : Real :=
  -Real.log ((gamma + 1) / 2)

theorem supercriticalCoverBalanceRadius_pos
    {k : Nat} (hk : 3 ≤ k) :
    0 < supercriticalCoverBalanceRadius k := by
  unfold supercriticalCoverBalanceRadius
  have hkr : (0 : Real) < (k - 1 : Nat) := by exact_mod_cast (by omega : 0 < k - 1)
  positivity

theorem supercriticalCoverDensityTolerance_pos
    {gamma : Real} (hgamma : gamma < 1) :
    0 < supercriticalCoverDensityTolerance gamma := by
  unfold supercriticalCoverDensityTolerance
  linarith

theorem supercriticalCoverLogRate_pos
    {gamma : Real} (hgamma : gamma ∈ Set.Ioo (0 : Real) 1) :
    0 < supercriticalCoverLogRate gamma := by
  unfold supercriticalCoverLogRate
  have hbase0 : 0 < (gamma + 1) / 2 := by
    norm_num [div_eq_mul_inv]
    linarith [hgamma.1]
  have hbase1 : (gamma + 1) / 2 < 1 := by
    norm_num [div_eq_mul_inv]
    linarith [hgamma.2]
  exact neg_pos.mpr (Real.log_neg hbase0 hbase1)

@[simp] theorem exp_neg_supercriticalCoverLogRate
    {gamma : Real} (hgamma : 0 < gamma) :
    Real.exp (-supercriticalCoverLogRate gamma) = (gamma + 1) / 2 := by
  unfold supercriticalCoverLogRate
  have hbase0 : 0 < (gamma + 1) / 2 := by linarith
  rw [neg_neg, Real.exp_log hbase0]

/-- Common balanced-fiber estimate from the selected cross-coordinate density.
The shared geometry supplies the finite preparation for balanced-cover multiplicity and the
fixed-sparse core estimate, including infeasible (empty) fibers. -/
theorem eventually_balancedCoPartiteFiber_nonuniqueCover_card_le_of_density
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ m : ℕ,
      ∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c) →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : ℝ) ≤
          ((supercriticalCoPartiteFiber D m).card : ℝ) *
            Real.exp (-(supercriticalCoverUniquenessRate k c * (q : ℝ))) := by
  let r := k - 1
  filter_upwards
      [eventually_balancedCoPartiteFiber_nonuniqueCover_card_le_of_geometry
        hk hc,
       Filter.eventually_ge_atTop (8 * r)] with q hgeometry hqLarge m D
      hbalanced hdensity
  by_cases hfiber : (supercriticalCoPartiteFiber D m).Nonempty
  · obtain ⟨G, hG⟩ := hfiber
    obtain ⟨hD, hlower, A, hA, _hAcard, _hgraph⟩ :=
      mem_supercriticalCoPartiteFiber.mp hG
    let a := q / (2 * r) + 1
    have hrNat : 0 < r := by dsimp [r]; omega
    have hrReal : (0 : ℝ) < r := by exact_mod_cast hrNat
    have hpart : ∀ i, a ≤ (D.parts i).card := by
      intro i
      have hbalLower := (abs_le.mp (hbalanced.2 i)).1
      have hbetaEq : supercriticalCoverBalanceRadius k =
          1 / (8 * (r : ℝ)) := by
        simp [supercriticalCoverBalanceRadius, r]
      rw [hbetaEq] at hbalLower
      have hpartReal : 7 * (q : ℝ) / (8 * r) ≤ (D.parts i).card := by
        have heq : (q : ℝ) / r - (1 / (8 * r)) * q =
            7 * (q : ℝ) / (8 * r) := by
          field_simp
          <;> ring
        rw [← heq]
        linarith
      have hdiv : ((q / (2 * r) : ℕ) : ℝ) ≤
          (q : ℝ) / (2 * r : ℕ) := Nat.cast_div_le
      have hqReal : (8 : ℝ) * r ≤ q := by exact_mod_cast hqLarge
      have hone : (1 : ℝ) ≤ 3 * (q : ℝ) / (8 * r) := by
        apply (le_div_iff₀ (mul_pos (by norm_num) hrReal)).mpr
        nlinarith
      have haReal : (a : ℝ) ≤ 7 * (q : ℝ) / (8 * r) := by
        dsimp [a]
        push_cast
        calc
          ((q / (2 * r) : ℕ) : ℝ) + 1 ≤
              (q : ℝ) / (2 * r) + 1 := by
            simpa [Nat.cast_mul, add_comm] using add_le_add_right hdiv 1
          _ ≤ 7 * (q : ℝ) / (8 * r) := by
            have heq : (q : ℝ) / (2 * r) +
                3 * (q : ℝ) / (8 * r) =
                7 * (q : ℝ) / (8 * r) := by
              field_simp
              <;> ring
            rw [← heq]
            linarith
      exact_mod_cast haReal.trans hpartReal
    have hscale : q ≤ 2 * (k - 1) * a := by
      let d := 2 * r
      have hd : 0 < d := by dsimp [d]; positivity
      have hmod := Nat.mod_lt q hd
      have hdecomp := Nat.div_add_mod q d
      have hlt : q < (q / d + 1) * d := by
        calc
          q = d * (q / d) + q % d := hdecomp.symm
          _ < d * (q / d) + d := Nat.add_lt_add_left hmod _
          _ = (q / d + 1) * d := by ring
      calc
        q ≤ (q / d + 1) * d := hlt.le
        _ = 2 * (k - 1) * a := by
          dsimp [d, a, r]
          ring
    have hupper : m ≤ divisionInternalCliqueCapacity D +
        supercriticalTotalCrossCapacity D := by
      have hAcardLe : A.card ≤
          (supercriticalTaggedCrossChoiceUniverse D).card :=
        Finset.card_le_card hA
      simp only [card_supercriticalTaggedCrossChoiceUniverse] at hAcardLe
      omega
    exact hgeometry m a D hD hpart hscale hlower hupper hdensity
  · have hfiberEmpty : supercriticalCoPartiteFiber D m = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [supercriticalCoPartiteFiberNonuniqueCover, hfiberEmpty]

/-- Explicit uniform uniqueness theorem for balanced exact-density fibers.
The balance radius, density tolerance, and decay rate are all fixed functions
of `k` and `gamma`, and the estimate is uniform in `m` and in the displayed
ordered division, as required by `lemma:balanced-cover-multiplicity-K1k`. -/
theorem eventually_balancedCoPartiteFiber_nonuniqueCover_card_le
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      ∀ D : SupercriticalDivision k (Fin n),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        |(m : Real) / (completeEdgeCount n : Real) - gamma| <
          supercriticalCoverDensityTolerance gamma →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
          ((supercriticalCoPartiteFiber D m).card : Real) *
            Real.exp (-(supercriticalCoverUniquenessRate k
              (supercriticalCoverLogRate gamma) * (n : Real))) := by
  have hgamma01 : gamma ∈ Set.Ioo (0 : Real) 1 :=
    ⟨(gammaK_pos hk).trans hgamma.1, hgamma.2⟩
  have hc := supercriticalCoverLogRate_pos hgamma01
  filter_upwards
      [eventually_balancedCoPartiteFiber_nonuniqueCover_card_le_of_density hk hc]
      with n hcore m D hbalanced hdensityTotal
  by_cases hfiber : (supercriticalCoPartiteFiber D m).Nonempty
  · obtain ⟨G, hG⟩ := hfiber
    obtain ⟨hD, hlower, _, _, _, _⟩ := mem_supercriticalCoPartiteFiber.mp hG
    have hcross := supercriticalTotalCrossCapacity_pos hk D
    have hm : m ≤ completeEdgeCount n := by
      have hmG := card_edgeFinset_le_completeEdgeCount G
      have hmEq := card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber hG
      rw [finiteGraphEdges_card_eq_edgeFinset_card] at hmEq
      omega
    have hcrossDensity := coPartiteFiber_crossDensity_le_totalDensity
      D hD hlower hcross hm
    have htotalUpper :
        (m : Real) / (completeEdgeCount n : Real) ≤ (gamma + 1) / 2 := by
      have h := (abs_lt.mp hdensityTotal).2
      unfold supercriticalCoverDensityTolerance at h
      linarith
    have hdensity :
        ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
            (supercriticalTotalCrossCapacity D : Real) ≤
          Real.exp (-supercriticalCoverLogRate gamma) := by
      rw [exp_neg_supercriticalCoverLogRate hgamma01.1]
      exact hcrossDensity.trans htotalUpper
    exact hcore m D hbalanced hdensity
  · have hfiberEmpty : supercriticalCoPartiteFiber D m = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hfiber
    simp [supercriticalCoPartiteFiberNonuniqueCover, hfiberEmpty]

/-! ## From fiber uniqueness to the balanced cover-pair bound -/

noncomputable def balancedCoMultipartiteUniqueCoverPairFinset
    (k n m : Nat) (beta : Real) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) := by
  classical
  exact (balancedCoMultipartiteCoverPairFinset k n m beta).filter fun p ↦
    HasUniqueCoMultipartiteCover k p.2

noncomputable def balancedCoMultipartiteNonuniqueCoverPairFinset
    (k n m : Nat) (beta : Real) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) := by
  classical
  exact (balancedCoMultipartiteCoverPairFinset k n m beta).filter fun p ↦
    ¬ HasUniqueCoMultipartiteCover k p.2

@[simp] theorem mem_balancedCoMultipartiteUniqueCoverPairFinset
    {k n m : Nat} {beta : Real}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ balancedCoMultipartiteUniqueCoverPairFinset k n m beta ↔
      p ∈ balancedCoMultipartiteCoverPairFinset k n m beta ∧
        HasUniqueCoMultipartiteCover k p.2 := by
  simp [balancedCoMultipartiteUniqueCoverPairFinset]

@[simp] theorem mem_balancedCoMultipartiteNonuniqueCoverPairFinset
    {k n m : Nat} {beta : Real}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta ↔
      p ∈ balancedCoMultipartiteCoverPairFinset k n m beta ∧
        ¬ HasUniqueCoMultipartiteCover k p.2 := by
  simp [balancedCoMultipartiteNonuniqueCoverPairFinset]

theorem card_balancedCoMultipartiteCoverPairFinset_eq_unique_add_nonunique
    (k n m : Nat) (beta : Real) :
    (balancedCoMultipartiteCoverPairFinset k n m beta).card =
      (balancedCoMultipartiteUniqueCoverPairFinset k n m beta).card +
        (balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta).card := by
  classical
  simpa [balancedCoMultipartiteUniqueCoverPairFinset,
    balancedCoMultipartiteNonuniqueCoverPairFinset] using
      (Finset.card_filter_add_card_filter_not
        (s := balancedCoMultipartiteCoverPairFinset k n m beta)
        (p := fun p ↦ HasUniqueCoMultipartiteCover k p.2)).symm

/-- Unique-cover pairs contribute at most one factorial of ordered
relabelings per global co-multipartite graph. -/
theorem card_balancedCoMultipartiteUniqueCoverPairFinset_le
    (k n m : Nat) (beta : Real) :
    (balancedCoMultipartiteUniqueCoverPairFinset k n m beta).card ≤
      (k - 1).factorial * coMultipartiteGraphCountWithEdges (k - 1) n m := by
  classical
  let good := coMultipartiteGraphFinsetWithEdges (k - 1) n m
  let uniqueGood := good.filter (HasUniqueCoMultipartiteCover k)
  let target := uniqueGood.biUnion fun G ↦
    (balancedCoverDivisionFinset (k := k) m beta G).image fun D ↦ (D, G)
  have hsubset : balancedCoMultipartiteUniqueCoverPairFinset k n m beta ⊆
      target := by
    rintro ⟨D, G⟩ hp
    obtain ⟨hpair, hunique⟩ :=
      mem_balancedCoMultipartiteUniqueCoverPairFinset.mp hp
    obtain ⟨hD, hG⟩ := mem_balancedCoMultipartiteCoverPairFinset.mp hpair
    have hglobal := supercriticalCoPartiteFiber_subset_global D hG
    apply Finset.mem_biUnion.mpr
    refine ⟨G, Finset.mem_filter.mpr ⟨hglobal, hunique⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨D,
      mem_balancedCoverDivisionFinset.mpr ⟨hD, hG⟩, rfl⟩
  calc
    (balancedCoMultipartiteUniqueCoverPairFinset k n m beta).card ≤
        target.card := Finset.card_le_card hsubset
    _ ≤ ∑ G ∈ uniqueGood,
          (balancedCoverDivisionFinset (k := k) m beta G).card := by
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun G hG ↦
        Finset.card_image_le)
    _ ≤ ∑ _G ∈ uniqueGood, (k - 1).factorial := by
      apply Finset.sum_le_sum
      intro G hG
      exact card_balancedCoverDivisionFinset_le_factorial_of_unique
        (Finset.mem_filter.mp hG).2
    _ = uniqueGood.card * (k - 1).factorial := by simp
    _ ≤ good.card * (k - 1).factorial := by
      exact Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.filter_subset _ _))
    _ = (k - 1).factorial *
        coMultipartiteGraphCountWithEdges (k - 1) n m := by
      simp [good, coMultipartiteGraphCountWithEdges, Nat.mul_comm]

/-- Nonunique balanced cover-pairs are controlled by the sum of the
nonunique portions of the individual fibers. -/
theorem card_balancedCoMultipartiteNonuniqueCoverPairFinset_le_sum
    (k n m : Nat) (beta : Real) :
    (balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta).card ≤
      ∑ D ∈ balancedFullSupercriticalDivisions k n beta,
        (supercriticalCoPartiteFiberNonuniqueCover D m).card := by
  classical
  let target := (balancedFullSupercriticalDivisions k n beta).biUnion fun D ↦
    (supercriticalCoPartiteFiberNonuniqueCover D m).image fun G ↦ (D, G)
  have hsubset : balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta ⊆
      target := by
    rintro ⟨D, G⟩ hp
    obtain ⟨hpair, hnotUnique⟩ :=
      mem_balancedCoMultipartiteNonuniqueCoverPairFinset.mp hp
    obtain ⟨hD, hG⟩ := mem_balancedCoMultipartiteCoverPairFinset.mp hpair
    apply Finset.mem_biUnion.mpr
    refine ⟨D, mem_balancedFullSupercriticalDivisions.mpr hD, ?_⟩
    exact Finset.mem_image.mpr ⟨G,
      mem_supercriticalCoPartiteFiberNonuniqueCover.mpr ⟨hG, hnotUnique⟩, rfl⟩
  calc
    (balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta).card ≤
        target.card := Finset.card_le_card hsubset
    _ ≤ ∑ D ∈ balancedFullSupercriticalDivisions k n beta,
          (supercriticalCoPartiteFiberNonuniqueCover D m).card := by
      exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun D hD ↦
        Finset.card_image_le)

/-- Sum a uniform bound on each balanced fiber over its displayed covers. -/
theorem card_balancedCoMultipartiteNonuniqueCoverPairFinset_le_mul_of_fiber
    (k n m : Nat) (beta factor : Real)
    (hfiber : ∀ D : SupercriticalDivision k (Fin n),
      IsBalancedFullDivision D beta →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
          ((supercriticalCoPartiteFiber D m).card : Real) * factor) :
    ((balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta).card : Real) ≤
      ((balancedCoMultipartiteCoverPairFinset k n m beta).card : Real) * factor := by
  calc
    ((balancedCoMultipartiteNonuniqueCoverPairFinset k n m beta).card : Real) ≤
        ∑ D ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) := by
      exact_mod_cast card_balancedCoMultipartiteNonuniqueCoverPairFinset_le_sum k n m beta
    _ ≤ ∑ D ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalCoPartiteFiber D m).card : Real) * factor :=
      Finset.sum_le_sum fun D hD ↦ hfiber D (mem_balancedFullSupercriticalDivisions.mp hD)
    _ = ((balancedCoMultipartiteCoverPairFinset k n m beta).card : Real) * factor := by
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        ← card_balancedCoMultipartiteCoverPairFinset]

/-- Uniform nonunique-pair self-bound at the explicit balance radius. -/
theorem eventually_card_balancedCoMultipartiteNonuniqueCoverPairFinset_le
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      |(m : Real) / (completeEdgeCount n : Real) - gamma| <
          supercriticalCoverDensityTolerance gamma →
      ((balancedCoMultipartiteNonuniqueCoverPairFinset k n m
        (supercriticalCoverBalanceRadius k)).card : Real) ≤
        ((balancedCoMultipartiteCoverPairFinset k n m
          (supercriticalCoverBalanceRadius k)).card : Real) *
          Real.exp (-(supercriticalCoverUniquenessRate k
            (supercriticalCoverLogRate gamma) * (n : Real))) := by
  filter_upwards
      [eventually_balancedCoPartiteFiber_nonuniqueCover_card_le hk gamma hgamma]
      with n hfiber m hdensity
  exact card_balancedCoMultipartiteNonuniqueCoverPairFinset_le_mul_of_fiber
    k n m (supercriticalCoverBalanceRadius k) _
    (fun D hD ↦ hfiber m D hD hdensity)

/-- The permanent balanced cover-pair endpoint: the sum over all balanced
ordered fibers is eventually at most twice the factorial relabeling factor
times the global co-multipartite count. -/
theorem eventually_card_balancedCoMultipartiteCoverPairFinset_le
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      |(m : Real) / (completeEdgeCount n : Real) - gamma| <
          supercriticalCoverDensityTolerance gamma →
      ((balancedCoMultipartiteCoverPairFinset k n m
        (supercriticalCoverBalanceRadius k)).card : Real) ≤
        (2 * (k - 1).factorial : Nat) *
          (coMultipartiteGraphCountWithEdges (k - 1) n m : Real) := by
  have hgamma01 : gamma ∈ Set.Ioo (0 : Real) 1 :=
    ⟨(gammaK_pos hk).trans hgamma.1, hgamma.2⟩
  have hc := supercriticalCoverLogRate_pos hgamma01
  have hrate := supercriticalCoverUniquenessRate_pos hk hc
  filter_upwards
      [eventually_card_balancedCoMultipartiteNonuniqueCoverPairFinset_le
        hk gamma hgamma,
       DenseGraph.eventually_natCast_mul_le_exp_mul 2 hrate,
       Filter.eventually_ge_atTop 1] with n hnonunique hgrowth hnPos m hdensity
  let P : Real := (balancedCoMultipartiteCoverPairFinset k n m
    (supercriticalCoverBalanceRadius k)).card
  let U : Real := (balancedCoMultipartiteUniqueCoverPairFinset k n m
    (supercriticalCoverBalanceRadius k)).card
  let Q : Real := (balancedCoMultipartiteNonuniqueCoverPairFinset k n m
    (supercriticalCoverBalanceRadius k)).card
  let A : Real := (k - 1).factorial *
    coMultipartiteGraphCountWithEdges (k - 1) n m
  let rate := supercriticalCoverUniquenessRate k
    (supercriticalCoverLogRate gamma)
  have hsplitNat :=
    card_balancedCoMultipartiteCoverPairFinset_eq_unique_add_nonunique
      k n m (supercriticalCoverBalanceRadius k)
  have hsplit : P = U + Q := by
    dsimp [P, U, Q]
    exact_mod_cast hsplitNat
  have huniqueNat := card_balancedCoMultipartiteUniqueCoverPairFinset_le
    k n m (supercriticalCoverBalanceRadius k)
  have hunique : U ≤ A := by
    dsimp [U, A]
    exact_mod_cast huniqueNat
  have hnonunique' : Q ≤ P * Real.exp (-(rate * (n : Real))) := by
    simpa [P, Q, rate] using hnonunique m hdensity
  have hnReal : (1 : Real) ≤ n := by exact_mod_cast hnPos
  have htwo : (2 : Real) ≤ Real.exp (rate * (n : Real)) := by
    calc
      (2 : Real) ≤ 2 * (n : Real) := by nlinarith
      _ ≤ Real.exp (rate * (n : Real)) := by simpa [rate] using hgrowth
  have hexpHalf : Real.exp (-(rate * (n : Real))) ≤ (1 : Real) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : Real) < 2)]
    calc
      Real.exp (-(rate * (n : Real))) * 2 ≤
          Real.exp (-(rate * (n : Real))) *
            Real.exp (rate * (n : Real)) := by
        exact mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
      _ = 1 := by
        rw [← Real.exp_add]
        simp
  have hQhalf : Q ≤ P / 2 := by
    calc
      Q ≤ P * Real.exp (-(rate * (n : Real))) := hnonunique'
      _ ≤ P * ((1 : Real) / 2) :=
        mul_le_mul_of_nonneg_left hexpHalf (by positivity)
      _ = P / 2 := by ring
  have hPA : P ≤ A + P / 2 := by
    calc
      P = U + Q := hsplit
      _ ≤ A + P / 2 := add_le_add hunique hQhalf
  have : P ≤ 2 * A := by linarith
  dsimp [P, A] at this ⊢
  convert this using 1 <;> push_cast <;> ring

/-- Paper-facing name for the uniform balanced-fiber uniqueness estimate. -/
theorem balancedCoPartiteFiber_nonuniqueCover_card_le
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      ∀ D : SupercriticalDivision k (Fin n),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        |(m : Real) / (completeEdgeCount n : Real) - gamma| <
          supercriticalCoverDensityTolerance gamma →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : Real) ≤
          ((supercriticalCoPartiteFiber D m).card : Real) *
            Real.exp (-(supercriticalCoverUniquenessRate k
              (supercriticalCoverLogRate gamma) * (n : Real))) :=
  eventually_balancedCoPartiteFiber_nonuniqueCover_card_le hk gamma hgamma

/-- Paper-facing name for the balanced ordered-cover sum comparison. -/
theorem balancedCoverPair_card_le_mul_coMultipartiteCount
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      |(m : Real) / (completeEdgeCount n : Real) - gamma| <
          supercriticalCoverDensityTolerance gamma →
      ((balancedCoMultipartiteCoverPairFinset k n m
        (supercriticalCoverBalanceRadius k)).card : Real) ≤
        (2 * (k - 1).factorial : Nat) *
          (coMultipartiteGraphCountWithEdges (k - 1) n m : Real) :=
  eventually_card_balancedCoMultipartiteCoverPairFinset_le hk gamma hgamma

end InducedStars
