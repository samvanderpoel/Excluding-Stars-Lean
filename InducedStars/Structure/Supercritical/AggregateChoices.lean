import InducedStars.Structure.Supercritical.CleanSparseEncoding
import InducedStars.Structure.Supercritical.SparseAbsorption
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Preimage
import Mathlib.Tactic

/-!
# Exact aggregate choice spaces for supercritical divisions

This file supplies finite, axiom-free bookkeeping for aggregating over all
cross-edge profiles and all graphs on the sparse set. Cross coordinates are
tagged by their unordered part pair, so their disjoint union is literal rather
than a quotient. The resulting powerset layer gives a finite Vandermonde
decomposition without any asymptotics.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Exact capacities -/

/-- Total capacity of all cross cells between distinct main parts. -/
def supercriticalTotalCrossCapacity (D : SupercriticalDivision k V) : ℕ :=
  ∑ e : SupercriticalPartPair k, crossEdgeCapacity D e

/-- Capacity of the arbitrary graph induced by the sparse set. -/
def supercriticalSparseChoiceCapacity (D : SupercriticalDivision k V) : ℕ :=
  Nat.choose D.sparse.card 2

/-- Paper-facing name for the capacity of the graph internal to the sparse
set. -/
def supercriticalSparsePotentialCapacity (D : SupercriticalDivision k V) : ℕ :=
  Nat.choose D.sparse.card 2

/-- Number of old variable coordinates before absorbing the sparse set. -/
def supercriticalPreAbsorptionVariableCapacity
    (D : SupercriticalDivision k V) : ℕ :=
  supercriticalTotalCrossCapacity D + supercriticalSparsePotentialCapacity D

/-- Exact number of new forced clique edges when the sparse set is absorbed
into the selected smallest part. -/
def supercriticalAbsorptionEdgeShift
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) : ℕ :=
  (D.parts (supercriticalSmallestPartIndex hk D)).card * D.sparse.card +
    Nat.choose D.sparse.card 2

@[simp] theorem supercriticalSparsePotentialCapacity_eq
    (D : SupercriticalDivision k V) :
    supercriticalSparsePotentialCapacity D = Nat.choose D.sparse.card 2 :=
  rfl

@[simp] theorem card_supercriticalSparsePotentialEdges_eq_capacity
    (D : SupercriticalDivision k V) :
    (supercriticalSparsePotentialEdges D).card =
      supercriticalSparsePotentialCapacity D := by
  simp [supercriticalSparsePotentialCapacity]

theorem divisionInternalCliqueCapacity_absorbSparse_eq_add_shift
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    divisionInternalCliqueCapacity (supercriticalAbsorbSparseDivision hk D) =
      divisionInternalCliqueCapacity D +
        supercriticalAbsorptionEdgeShift hk D := by
  rw [divisionInternalCliqueCapacity_absorbSparse]
  simp [supercriticalAbsorptionEdgeShift, Nat.add_assoc]

private theorem two_mul_choose_two (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.mul_comm 2, Nat.choose_two_right,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]

/-- Splitting the ordered square of the part-size sum into its diagonal and
the two orientations of each unordered part pair. -/
private theorem sum_partCard_mul_sum_partCard
    (D : SupercriticalDivision k V) :
    (∑ i, (D.parts i).card) * (∑ j, (D.parts j).card) =
      (∑ i, (D.parts i).card * (D.parts i).card) +
        2 * supercriticalTotalCrossCapacity D := by
  classical
  let I := Fin (k - 1)
  let f : I → I → ℕ := fun i j ↦ (D.parts i).card * (D.parts j).card
  let pairs : Finset (I × I) := Finset.univ ×ˢ Finset.univ
  let ltPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 < p.2
  let gtPairs : Finset (I × I) := pairs.filter fun p ↦ p.2 < p.1
  let diagPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 = p.2
  have hsplit :
      (∑ p ∈ pairs, f p.1 p.2) =
        (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le]
    · simp [heq, lt_irrefl p.2]
    · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le]
  have hdiag :
      (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) =
        ∑ i : I, f i i := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ diagPairs, f p.1 p.2) = _
    apply Finset.sum_bij (fun p _ ↦ p.1)
    · intro p _hp
      simp
    · intro p hp q hq hpq
      have hpEq := (Finset.mem_filter.mp hp).2
      have hqEq := (Finset.mem_filter.mp hq).2
      apply Prod.ext hpq
      simpa [hpEq, hqEq] using hpq
    · intro i _hi
      refine ⟨(i, i), ?_, rfl⟩
      simp [diagPairs, pairs]
    · intro p hp
      have hpEq := (Finset.mem_filter.mp hp).2
      simpa [hpEq]
  have hlt :
      (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) =
        supercriticalTotalCrossCapacity D := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ ltPairs, f p.1 p.2) = _
    unfold supercriticalTotalCrossCapacity
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p _hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.left hpq)
        (congrArg SupercriticalPartPair.right hpq)
    · intro e _he
      refine ⟨(e.left, e.right), ?_, ?_⟩
      · simp [ltPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p _hp
      rfl
  have hgt :
      (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) =
        supercriticalTotalCrossCapacity D := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ gtPairs, f p.1 p.2) = _
    unfold supercriticalTotalCrossCapacity
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.2, p.1, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p _hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.right hpq)
        (congrArg SupercriticalPartPair.left hpq)
    · intro e _he
      refine ⟨(e.right, e.left), ?_, ?_⟩
      · simp [gtPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p _hp
      simp [f, crossEdgeCapacity, Nat.mul_comm]
  change (∑ i : I, (D.parts i).card) *
      (∑ j : I, (D.parts j).card) =
    (∑ i : I, (D.parts i).card * (D.parts i).card) +
      2 * supercriticalTotalCrossCapacity D
  calc
    (∑ i : I, (D.parts i).card) *
        (∑ j : I, (D.parts j).card) =
        ∑ p ∈ pairs, f p.1 p.2 := by
      rw [Finset.sum_mul_sum]
      simpa [pairs, f] using
        (Fintype.sum_prod_type (fun p : I × I ↦ f p.1 p.2)).symm
    _ = (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) :=
      hsplit
    _ = (∑ i : I, (D.parts i).card * (D.parts i).card) +
          2 * supercriticalTotalCrossCapacity D := by
      rw [hdiag, hlt, hgt]
      simp [f, two_mul, Nat.add_assoc]

/-- Every unordered pair in the main support is either internal to one part
or crosses one unique unordered pair of parts. -/
theorem supercriticalTotalCrossCapacity_add_internal
    (D : SupercriticalDivision k V) :
    supercriticalTotalCrossCapacity D + divisionInternalCliqueCapacity D =
      Nat.choose D.support.card 2 := by
  classical
  have hsquare := sum_partCard_mul_sum_partCard D
  have hsupport := D.card_support
  have hinternal :
      2 * divisionInternalCliqueCapacity D =
        ∑ i, (D.parts i).card * ((D.parts i).card - 1) := by
    unfold divisionInternalCliqueCapacity
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    exact two_mul_choose_two _
  have hdiag :
      (∑ i, (D.parts i).card * (D.parts i).card) =
        (∑ i, (D.parts i).card * ((D.parts i).card - 1)) +
          ∑ i, (D.parts i).card := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    have hpos := (D.parts_nonempty i).card_pos
    have ha : (D.parts i).card - 1 + 1 = (D.parts i).card := by
      omega
    calc
      (D.parts i).card * (D.parts i).card =
          (D.parts i).card * ((D.parts i).card - 1 + 1) := by rw [ha]
      _ = (D.parts i).card * ((D.parts i).card - 1) +
          (D.parts i).card := by rw [Nat.mul_add, Nat.mul_one]
  have hchoose := two_mul_choose_two D.support.card
  rw [hsupport] at hchoose
  rw [hdiag] at hsquare
  rw [← hinternal] at hsquare
  rw [hsupport]
  let S := ∑ i, (D.parts i).card
  have hsquareSplit : S * S = S * (S - 1) + S := by
    rcases Nat.eq_zero_or_pos S with hS | hS
    · simp [hS]
    · have hsub : S - 1 + 1 = S := by omega
      calc
        S * S = S * (S - 1 + 1) := by rw [hsub]
        _ = S * (S - 1) + S := by rw [Nat.mul_add, Nat.mul_one]
  change S * S = _ at hsquare
  change 2 * Nat.choose S 2 = _ at hchoose
  change supercriticalTotalCrossCapacity D +
    divisionInternalCliqueCapacity D = Nat.choose S 2
  have htwiceAdd :
      2 * (supercriticalTotalCrossCapacity D +
          divisionInternalCliqueCapacity D) + S =
        2 * Nat.choose S 2 + S := by
    calc
      2 * (supercriticalTotalCrossCapacity D +
          divisionInternalCliqueCapacity D) + S = S * S := by
        rw [hsquare]
        omega
      _ = S * (S - 1) + S := hsquareSplit
      _ = 2 * Nat.choose S 2 + S := by rw [hchoose]
  omega

private theorem choose_add_two_aggregate (a s : ℕ) :
    Nat.choose (a + s) 2 =
      Nat.choose a 2 + a * s + Nat.choose s 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      change Nat.choose ((a + s) + 1) 2 =
        Nat.choose a 2 + a * (s + 1) + Nat.choose (s + 1) 2
      rw [Nat.choose_succ_succ, ih, Nat.choose_succ_succ]
      simp [Nat.choose_one_right, Nat.mul_succ] at *
      omega

/-- Absorbing the sparse set enlarges total cross capacity by exactly the
sparse size times the vertices in the other main parts. -/
theorem supercriticalTotalCrossCapacity_absorbSparse_eq
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D) =
      supercriticalTotalCrossCapacity D +
        D.sparse.card *
          (D.support.card -
            (D.parts (supercriticalSmallestPartIndex hk D)).card) := by
  let DStar := supercriticalAbsorbSparseDivision hk D
  let a := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s := D.sparse.card
  let N := D.support.card
  have hstar := supercriticalTotalCrossCapacity_add_internal DStar
  have hold := supercriticalTotalCrossCapacity_add_internal D
  have hinter := divisionInternalCliqueCapacity_absorbSparse hk D
  have hcover : DStar.support.card = Fintype.card V := by
    simp [DStar]
  have hvertices : N + s = Fintype.card V := by
    simpa [N, s] using D.card_support_add_card_sparse
  have hchoose := choose_add_two_aggregate N s
  have ha : a ≤ N := by
    dsimp [a, N]
    exact Finset.card_le_card
      (D.part_subset_support (supercriticalSmallestPartIndex hk D))
  have hmul : a * s + s * (N - a) = N * s := by
    rw [Nat.mul_comm s (N - a), ← Nat.add_mul,
      Nat.add_sub_of_le ha]
  rw [hcover, ← hvertices, hchoose] at hstar
  simp only [DStar, a, s, N] at *
  omega

/-- Under the natural nonnegativity hypothesis, the absorbed cross capacity
minus the old cross-plus-sparse capacity is exactly the net new capacity. -/
theorem supercriticalAbsorbedCapacity_sub_preAbsorption
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (hcapacity : Nat.choose D.sparse.card 2 ≤
      D.sparse.card *
        (D.support.card -
          (D.parts (supercriticalSmallestPartIndex hk D)).card)) :
    supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D) -
        supercriticalPreAbsorptionVariableCapacity D =
      D.sparse.card *
          (D.support.card -
            (D.parts (supercriticalSmallestPartIndex hk D)).card) -
        Nat.choose D.sparse.card 2 := by
  rw [supercriticalTotalCrossCapacity_absorbSparse_eq]
  unfold supercriticalPreAbsorptionVariableCapacity
  simp only [supercriticalSparsePotentialCapacity]
  omega

/-- Total number of variable coordinates in a clean graph with division D:
all main-part cross cells together with all sparse--sparse pairs. -/
def supercriticalCombinedChoiceCapacity (D : SupercriticalDivision k V) : ℕ :=
  supercriticalTotalCrossCapacity D + supercriticalSparseChoiceCapacity D

@[simp] theorem supercriticalCombinedChoiceCapacity_eq_preAbsorption
    (D : SupercriticalDivision k V) :
    supercriticalCombinedChoiceCapacity D =
      supercriticalPreAbsorptionVariableCapacity D :=
  rfl

@[simp] theorem supercriticalSparseChoiceCapacity_eq
    (D : SupercriticalDivision k V) :
    supercriticalSparseChoiceCapacity D = Nat.choose D.sparse.card 2 :=
  rfl

/-- The exact coordinatewise absorption identity, summed over all cross
cells. This form retains the orientation-independent conditional correction
from the coordinate formula. -/
theorem supercriticalTotalCrossCapacity_absorbSparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    supercriticalTotalCrossCapacity (supercriticalAbsorbSparseDivision hk D) =
      supercriticalTotalCrossCapacity D +
        ∑ e : SupercriticalPartPair k,
          (if e.left = supercriticalSmallestPartIndex hk D then
            D.sparse.card * (D.parts e.right).card
          else if e.right = supercriticalSmallestPartIndex hk D then
            (D.parts e.left).card * D.sparse.card
          else 0) := by
  classical
  unfold supercriticalTotalCrossCapacity
  simp_rw [crossEdgeCapacity_absorbSparse_eq hk D]
  exact Finset.sum_add_distrib

@[simp] theorem supercriticalSparseChoiceCapacity_absorbSparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    supercriticalSparseChoiceCapacity
        (supercriticalAbsorbSparseDivision hk D) = 0 := by
  simp [supercriticalSparseChoiceCapacity]

theorem supercriticalCombinedChoiceCapacity_absorbSparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    supercriticalCombinedChoiceCapacity
        (supercriticalAbsorbSparseDivision hk D) =
      supercriticalTotalCrossCapacity D +
        ∑ e : SupercriticalPartPair k,
          (if e.left = supercriticalSmallestPartIndex hk D then
            D.sparse.card * (D.parts e.right).card
          else if e.right = supercriticalSmallestPartIndex hk D then
            (D.parts e.left).card * D.sparse.card
          else 0) := by
  rw [supercriticalCombinedChoiceCapacity,
    supercriticalSparseChoiceCapacity_absorbSparse,
    Nat.add_zero, supercriticalTotalCrossCapacity_absorbSparse]

/-! ## Tagged cross and sparse coordinates -/

/-- A cross coordinate retains its part-pair tag and oriented endpoints. -/
abbrev SupercriticalTaggedCrossChoice (k : ℕ) (V : Type*) :=
  Σ _e : SupercriticalPartPair k, V × V

/-- A clean variable coordinate is either tagged cross data or an unordered
sparse--sparse pair. -/
abbrev SupercriticalCombinedChoice (k : ℕ) (V : Type*) :=
  SupercriticalTaggedCrossChoice k V ⊕ Sym2 V

/-- The literal disjoint union of all oriented cross cells. -/
def supercriticalTaggedCrossChoiceUniverse
    (D : SupercriticalDivision k V) :
    Finset (SupercriticalTaggedCrossChoice k V) :=
  Finset.univ.sigma fun e ↦ D.parts e.left ×ˢ D.parts e.right

@[simp] theorem mem_supercriticalTaggedCrossChoiceUniverse
    (D : SupercriticalDivision k V)
    (z : SupercriticalTaggedCrossChoice k V) :
    z ∈ supercriticalTaggedCrossChoiceUniverse D ↔
      z.2.1 ∈ D.parts z.1.left ∧ z.2.2 ∈ D.parts z.1.right := by
  simp [supercriticalTaggedCrossChoiceUniverse]

@[simp] theorem card_supercriticalTaggedCrossChoiceUniverse
    (D : SupercriticalDivision k V) :
    (supercriticalTaggedCrossChoiceUniverse D).card =
      supercriticalTotalCrossCapacity D := by
  classical
  simp [supercriticalTaggedCrossChoiceUniverse,
    supercriticalTotalCrossCapacity, crossEdgeCapacity]

/-- The tagged disjoint union of cross coordinates and sparse potential
edges. -/
def supercriticalCombinedChoiceUniverse
    (D : SupercriticalDivision k V) :
    Finset (SupercriticalCombinedChoice k V) :=
  (supercriticalTaggedCrossChoiceUniverse D).disjSum
    (supercriticalSparsePotentialEdges D)

@[simp] theorem card_supercriticalCombinedChoiceUniverse
    (D : SupercriticalDivision k V) :
    (supercriticalCombinedChoiceUniverse D).card =
      supercriticalCombinedChoiceCapacity D := by
  simp [supercriticalCombinedChoiceUniverse,
    supercriticalCombinedChoiceCapacity, supercriticalSparseChoiceCapacity]

/-- Prompt-facing name for the old cross-plus-sparse coordinate universe. -/
abbrev supercriticalPreAbsorptionChoiceUniverse :=
  @supercriticalCombinedChoiceUniverse

@[simp] theorem card_supercriticalPreAbsorptionChoiceUniverse
    (D : SupercriticalDivision k V) :
    (supercriticalPreAbsorptionChoiceUniverse D).card =
      supercriticalPreAbsorptionVariableCapacity D := by
  simp

/-- All clean variable-edge selections of one fixed total size. -/
def supercriticalCombinedChoiceLayer
    (D : SupercriticalDivision k V) (q : ℕ) :
    Finset (Finset (SupercriticalCombinedChoice k V)) :=
  (supercriticalCombinedChoiceUniverse D).powersetCard q

@[simp] theorem mem_supercriticalCombinedChoiceLayer
    (D : SupercriticalDivision k V) (q : ℕ)
    (A : Finset (SupercriticalCombinedChoice k V)) :
    A ∈ supercriticalCombinedChoiceLayer D q ↔
      A ⊆ supercriticalCombinedChoiceUniverse D ∧ A.card = q := by
  simp [supercriticalCombinedChoiceLayer]

@[simp] theorem card_supercriticalCombinedChoiceLayer
    (D : SupercriticalDivision k V) (q : ℕ) :
    (supercriticalCombinedChoiceLayer D q).card =
      Nat.choose (supercriticalCombinedChoiceCapacity D) q := by
  simp [supercriticalCombinedChoiceLayer]

/-- Prompt-facing name for the fixed-size old choice layer. -/
abbrev supercriticalPreAbsorptionChoiceFinset :=
  @supercriticalCombinedChoiceLayer

@[simp] theorem card_supercriticalPreAbsorptionChoiceFinset
    (D : SupercriticalDivision k V) (L : ℕ) :
    (supercriticalPreAbsorptionChoiceFinset D L).card =
      Nat.choose (supercriticalPreAbsorptionVariableCapacity D) L := by
  simp

/-! ## Combining one profile choice and one sparse choice -/

/-- Tag every selected cross coordinate and place it in disjoint sum with
the selected sparse edges. -/
def supercriticalCombineProfileSparseChoice
    (cross : SupercriticalPartPair k → Finset (V × V))
    (sparse : Finset (Sym2 V)) :
    Finset (SupercriticalCombinedChoice k V) :=
  (Finset.univ.sigma cross).disjSum sparse

@[simp] theorem supercriticalCombineProfileSparseChoice_toLeft
    (cross : SupercriticalPartPair k → Finset (V × V))
    (sparse : Finset (Sym2 V)) :
    (supercriticalCombineProfileSparseChoice cross sparse).toLeft =
      Finset.univ.sigma cross := by
  simp [supercriticalCombineProfileSparseChoice]

@[simp] theorem supercriticalCombineProfileSparseChoice_toRight
    (cross : SupercriticalPartPair k → Finset (V × V))
    (sparse : Finset (Sym2 V)) :
    (supercriticalCombineProfileSparseChoice cross sparse).toRight = sparse := by
  simp [supercriticalCombineProfileSparseChoice]

theorem supercriticalCombineProfileSparseChoice_injective :
    Function.Injective
      (fun x :
          (SupercriticalPartPair k → Finset (V × V)) × Finset (Sym2 V) ↦
        supercriticalCombineProfileSparseChoice x.1 x.2) := by
  classical
  rintro ⟨cross, sparse⟩ ⟨cross', sparse'⟩ h
  have hleft := congrArg Finset.toLeft h
  have hright := congrArg Finset.toRight h
  simp only [supercriticalCombineProfileSparseChoice_toLeft] at hleft
  simp only [supercriticalCombineProfileSparseChoice_toRight] at hright
  have hcross : cross = cross' := by
    funext e
    ext xy
    have hmem := congrArg
      (fun A : Finset (SupercriticalTaggedCrossChoice k V) ↦
        (⟨e, xy⟩ : SupercriticalTaggedCrossChoice k V) ∈ A) hleft
    simpa using hmem
  exact Prod.ext hcross hright

/-- The concrete combined choices with fixed cross profile and exactly t
sparse edges. -/
def supercriticalProfileSparseCombinedChoiceFinset
    (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (t : ℕ) :
    Finset (Finset (SupercriticalCombinedChoice k V)) := by
  classical
  exact ((supercriticalProfileChoiceFinset D profile).product
    ((supercriticalSparsePotentialEdges D).powersetCard t)).image
      (fun x ↦ supercriticalCombineProfileSparseChoice x.1 x.2)

@[simp] theorem card_supercriticalProfileSparseCombinedChoiceFinset
    (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (t : ℕ) :
    (supercriticalProfileSparseCombinedChoiceFinset D profile t).card =
      supercriticalProfileMultiplicity profile *
        Nat.choose (supercriticalSparseChoiceCapacity D) t := by
  classical
  rw [supercriticalProfileSparseCombinedChoiceFinset,
    Finset.card_image_of_injective _]
  · simp [supercriticalSparseChoiceCapacity,
      card_supercriticalProfileChoiceFinset]
  · exact supercriticalCombineProfileSparseChoice_injective

theorem supercriticalProfileSparseCombinedChoiceFinset_subset_layer
    (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (t : ℕ) :
    supercriticalProfileSparseCombinedChoiceFinset D profile t ⊆
      supercriticalCombinedChoiceLayer D (profileTotal profile + t) := by
  classical
  intro A hA
  rw [supercriticalProfileSparseCombinedChoiceFinset,
    Finset.mem_image] at hA
  obtain ⟨x, hx, rfl⟩ := hA
  have hx' :
      x.1 ∈ supercriticalProfileChoiceFinset D profile ∧
        x.2 ∈ (supercriticalSparsePotentialEdges D).powersetCard t := by
    simpa using hx
  rw [mem_supercriticalCombinedChoiceLayer]
  constructor
  · rw [supercriticalCombinedChoiceUniverse, Finset.subset_disjSum]
    constructor
    · intro z hz
      rw [supercriticalCombineProfileSparseChoice_toLeft,
        Finset.mem_sigma] at hz
      rw [mem_supercriticalTaggedCrossChoiceUniverse]
      simpa only [Finset.mem_product] using
        ((mem_supercriticalProfileChoiceFinset D profile x.1).mp hx'.1 z.1 |>.1 hz.2)
    · rw [supercriticalCombineProfileSparseChoice_toRight]
      exact (Finset.mem_powersetCard.mp hx'.2).1
  · rw [supercriticalCombineProfileSparseChoice, Finset.card_disjSum,
      Finset.card_sigma]
    have hcross :
        (∑ e : SupercriticalPartPair k, (x.1 e).card) =
          profileTotal profile := by
      unfold profileTotal
      apply Finset.sum_congr rfl
      intro e _
      exact (mem_supercriticalProfileChoiceFinset D profile x.1).mp hx'.1 e |>.2
    rw [hcross, (Finset.mem_powersetCard.mp hx'.2).2]

/-! ## Every feasible profile and the finite Vandermonde decomposition -/

/-- Turn a count vector carrying its feasibility proof into the corresponding
dependent edge profile. -/
def supercriticalEdgeProfileOfCountVector
    (D : SupercriticalDivision k V)
    (f : ↑(supercriticalProfileCountVectorFinset D)) :
    SupercriticalEdgeProfile D where
  count := f.1
  count_le_capacity :=
    (mem_supercriticalProfileCountVectorFinset D f.1).mp f.2

/-- The finite set of all feasible cross-edge profiles. -/
def supercriticalAllEdgeProfilesFinset
    (D : SupercriticalDivision k V) :
    Finset (SupercriticalEdgeProfile D) := by
  classical
  exact (supercriticalProfileCountVectorFinset D).attach.image
    (supercriticalEdgeProfileOfCountVector D)

@[simp] theorem mem_supercriticalAllEdgeProfilesFinset
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D) :
    profile ∈ supercriticalAllEdgeProfilesFinset D := by
  classical
  rw [supercriticalAllEdgeProfilesFinset, Finset.mem_image]
  let f : ↑(supercriticalProfileCountVectorFinset D) :=
    ⟨profile.count,
      (mem_supercriticalProfileCountVectorFinset D profile.count).mpr
        profile.count_le_capacity⟩
  refine ⟨f, Finset.mem_attach _ _, ?_⟩
  apply SupercriticalEdgeProfile.ext
  rfl

/-- Recover the choice in one tagged cross cell from a combined choice. -/
def supercriticalCrossChoiceOfCombined
    (A : Finset (SupercriticalCombinedChoice k V))
    (e : SupercriticalPartPair k) : Finset (V × V) := by
  classical
  exact (A.toLeft.filter fun z ↦ z.1 = e).image fun z ↦ z.2

@[simp] theorem mem_supercriticalCrossChoiceOfCombined
    (A : Finset (SupercriticalCombinedChoice k V))
    (e : SupercriticalPartPair k) (xy : V × V) :
    xy ∈ supercriticalCrossChoiceOfCombined A e ↔
      (⟨e, xy⟩ : SupercriticalTaggedCrossChoice k V) ∈ A.toLeft := by
  classical
  constructor
  · rw [supercriticalCrossChoiceOfCombined, Finset.mem_image]
    rintro ⟨⟨e', xy'⟩, hz, hxy⟩
    rw [Finset.mem_filter] at hz
    cases hz.2
    cases hxy
    exact hz.1
  · intro h
    rw [supercriticalCrossChoiceOfCombined, Finset.mem_image]
    exact ⟨⟨e, xy⟩, by simp [h], rfl⟩

@[simp] theorem sigma_supercriticalCrossChoiceOfCombined
    (A : Finset (SupercriticalCombinedChoice k V)) :
    Finset.univ.sigma (supercriticalCrossChoiceOfCombined A) = A.toLeft := by
  classical
  ext z
  simp

/-- The finite indexing set for all profile/sparse-count fibers with total
selected count `L`. -/
def supercriticalProfileSparseIndexFinset
    (D : SupercriticalDivision k V) (L : ℕ) :
    Finset (ℕ × SupercriticalEdgeProfile D) := by
  classical
  exact ((Finset.range (supercriticalSparseChoiceCapacity D + 1)).product
    (supercriticalAllEdgeProfilesFinset D)).filter fun tp ↦
      profileTotal tp.2 + tp.1 = L

@[simp] theorem mem_supercriticalProfileSparseIndexFinset
    (D : SupercriticalDivision k V) (L t : ℕ)
    (profile : SupercriticalEdgeProfile D) :
    (t, profile) ∈ supercriticalProfileSparseIndexFinset D L ↔
      t ≤ supercriticalSparseChoiceCapacity D ∧
        profileTotal profile + t = L := by
  classical
  simp [supercriticalProfileSparseIndexFinset, Nat.lt_succ_iff]

/-- The disjointly indexed realization space underlying the finite
Vandermonde decomposition. -/
def supercriticalProfileSparseIndexedChoices
    (D : SupercriticalDivision k V) (L : ℕ) :
    Finset (Σ _tp : ℕ × SupercriticalEdgeProfile D,
      (SupercriticalPartPair k → Finset (V × V)) × Finset (Sym2 V)) := by
  classical
  exact (supercriticalProfileSparseIndexFinset D L).sigma fun tp ↦
    (supercriticalProfileChoiceFinset D tp.2).product
      ((supercriticalSparsePotentialEdges D).powersetCard tp.1)

/-- Forget the profile and sparse-count tags and combine the two literal
edge selections. -/
def supercriticalProfileSparseIndexedChoiceMap
    (D : SupercriticalDivision k V)
    (z : Σ _tp : ℕ × SupercriticalEdgeProfile D,
      (SupercriticalPartPair k → Finset (V × V)) × Finset (Sym2 V)) :
    Finset (SupercriticalCombinedChoice k V) :=
  supercriticalCombineProfileSparseChoice z.2.1 z.2.2

theorem supercriticalProfileSparseIndexedChoiceMap_injective
    (D : SupercriticalDivision k V) (L : ℕ) :
    Set.InjOn (supercriticalProfileSparseIndexedChoiceMap D)
      (↑(supercriticalProfileSparseIndexedChoices D L) : Set _) := by
  classical
  rintro ⟨⟨t, p⟩, cross, sparse⟩ hz
    ⟨⟨t', p'⟩, cross', sparse'⟩ hz' hmap
  have hz0 : ⟨(t, p), (cross, sparse)⟩ ∈
      supercriticalProfileSparseIndexedChoices D L := hz
  have hz0' : ⟨(t', p'), (cross', sparse')⟩ ∈
      supercriticalProfileSparseIndexedChoices D L := hz'
  rw [supercriticalProfileSparseIndexedChoices, Finset.mem_sigma] at hz0 hz0'
  have hchoice := supercriticalCombineProfileSparseChoice_injective hmap
  have hcross : cross = cross' := congrArg Prod.fst hchoice
  have hsparse : sparse = sparse' := congrArg Prod.snd hchoice
  have ht : t = t' := by
    have hcard := congrArg Finset.card hsparse
    have ht0 : sparse.card = t := by
      simpa using (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp hz0.2).2).2
    have ht1 : sparse'.card = t' := by
      simpa using (Finset.mem_powersetCard.mp
        (Finset.mem_product.mp hz0'.2).2).2
    exact ht0.symm.trans (hcard.trans ht1)
  have hp : p = p' := by
    apply SupercriticalEdgeProfile.ext
    funext e
    have hcard := congrArg (fun f ↦ (f e).card) hcross
    have hp0 : (cross e).card = p.count e := by
      simpa using ((mem_supercriticalProfileChoiceFinset D p cross).mp
        (Finset.mem_product.mp hz0.2).1 e |>.2)
    have hp1 : (cross' e).card = p'.count e := by
      simpa using ((mem_supercriticalProfileChoiceFinset D p' cross').mp
        (Finset.mem_product.mp hz0'.2).1 e |>.2)
    omega
  subst t'
  subst p'
  subst cross'
  subst sparse'
  rfl

theorem supercriticalProfileSparseIndexedChoiceMap_mem_layer
    (D : SupercriticalDivision k V) (L : ℕ)
    {z : Σ _tp : ℕ × SupercriticalEdgeProfile D,
      (SupercriticalPartPair k → Finset (V × V)) × Finset (Sym2 V)}
    (hz : z ∈ supercriticalProfileSparseIndexedChoices D L) :
    supercriticalProfileSparseIndexedChoiceMap D z ∈
      supercriticalCombinedChoiceLayer D L := by
  classical
  rw [supercriticalProfileSparseIndexedChoices, Finset.mem_sigma] at hz
  have hindex := (mem_supercriticalProfileSparseIndexFinset
    D L z.1.1 z.1.2).mp hz.1
  have hmem := supercriticalProfileSparseCombinedChoiceFinset_subset_layer
    D z.1.2 z.1.1
  have hzfiber : supercriticalProfileSparseIndexedChoiceMap D z ∈
      supercriticalProfileSparseCombinedChoiceFinset D z.1.2 z.1.1 := by
    rw [supercriticalProfileSparseCombinedChoiceFinset, Finset.mem_image]
    exact ⟨z.2, hz.2, rfl⟩
  simpa [hindex.2] using hmem hzfiber

/-- Every fixed-size combined choice is represented by an indexed
profile/sparse realization. -/
theorem exists_indexedChoice_of_mem_supercriticalCombinedChoiceLayer
    (D : SupercriticalDivision k V) (L : ℕ)
    {A : Finset (SupercriticalCombinedChoice k V)}
    (hA : A ∈ supercriticalCombinedChoiceLayer D L) :
    ∃ z ∈ supercriticalProfileSparseIndexedChoices D L,
      supercriticalProfileSparseIndexedChoiceMap D z = A := by
  classical
  have hAsub := (mem_supercriticalCombinedChoiceLayer D L A).mp hA |>.1
  let cross := supercriticalCrossChoiceOfCombined A
  let sparse := A.toRight
  have hcrossSubset (e : SupercriticalPartPair k) :
      cross e ⊆ D.parts e.left ×ˢ D.parts e.right := by
    intro xy hxy
    have htag : (⟨e, xy⟩ : SupercriticalTaggedCrossChoice k V) ∈ A.toLeft := by
      simpa [cross] using hxy
    have hleft : A.toLeft ⊆ supercriticalTaggedCrossChoiceUniverse D := by
      rw [supercriticalCombinedChoiceUniverse, Finset.subset_disjSum] at hAsub
      exact hAsub.1
    have hzU := hleft htag
    simpa only [Finset.mem_product] using
      (mem_supercriticalTaggedCrossChoiceUniverse D ⟨e, xy⟩).mp hzU
  let profile : SupercriticalEdgeProfile D :=
    { count := fun e ↦ (cross e).card
      count_le_capacity := fun e ↦ by
        simpa [crossEdgeCapacity] using Finset.card_le_card (hcrossSubset e) }
  let t := sparse.card
  let z : Σ _tp : ℕ × SupercriticalEdgeProfile D,
      (SupercriticalPartPair k → Finset (V × V)) × Finset (Sym2 V) :=
    ⟨(t, profile), (cross, sparse)⟩
  have hsparseSubset : sparse ⊆ supercriticalSparsePotentialEdges D := by
    rw [supercriticalCombinedChoiceUniverse, Finset.subset_disjSum] at hAsub
    simpa [sparse] using hAsub.2
  have htotal : profileTotal profile + t = L := by
    have hcard := (mem_supercriticalCombinedChoiceLayer D L A).mp hA |>.2
    have hsplit := Finset.card_toLeft_add_card_toRight (u := A)
    have hleft : A.toLeft.card = ∑ e, (cross e).card := by
      rw [← sigma_supercriticalCrossChoiceOfCombined A, Finset.card_sigma]
    simp only [profileTotal, profile, t, sparse] at *
    omega
  have hzmem : z ∈ supercriticalProfileSparseIndexedChoices D L := by
    rw [supercriticalProfileSparseIndexedChoices, Finset.mem_sigma]
    constructor
    · rw [mem_supercriticalProfileSparseIndexFinset]
      exact ⟨by
        simpa [t, supercriticalSparseChoiceCapacity] using
          Finset.card_le_card hsparseSubset, htotal⟩
    · change (cross, sparse) ∈
        (supercriticalProfileChoiceFinset D profile).product
          ((supercriticalSparsePotentialEdges D).powersetCard t)
      apply Finset.mem_product.mpr
      constructor
      · apply (mem_supercriticalProfileChoiceFinset D profile cross).mpr
        intro e
        exact ⟨hcrossSubset e, rfl⟩
      · apply Finset.mem_powersetCard.mpr
        exact ⟨hsparseSubset, rfl⟩
  refine ⟨z, hzmem, ?_⟩
  ext q
  cases q with
  | inl q =>
      simp [supercriticalProfileSparseIndexedChoiceMap,
        supercriticalCombineProfileSparseChoice, z, cross, sparse]
  | inr q =>
      simp [supercriticalProfileSparseIndexedChoiceMap,
        supercriticalCombineProfileSparseChoice, z, sparse]

/-- The indexed realization space and the ordinary fixed-size powerset
layer have the same cardinality. -/
theorem card_supercriticalProfileSparseIndexedChoices
    (D : SupercriticalDivision k V) (L : ℕ) :
    (supercriticalProfileSparseIndexedChoices D L).card =
      (supercriticalCombinedChoiceLayer D L).card := by
  classical
  let f := supercriticalProfileSparseIndexedChoiceMap D
  have hinj : Set.InjOn f
      (↑(supercriticalProfileSparseIndexedChoices D L) : Set _) :=
    supercriticalProfileSparseIndexedChoiceMap_injective D L
  have himage :
      (supercriticalProfileSparseIndexedChoices D L).image f =
        supercriticalCombinedChoiceLayer D L := by
    ext A
    constructor
    · intro hA
      rw [Finset.mem_image] at hA
      obtain ⟨z, hz, rfl⟩ := hA
      exact supercriticalProfileSparseIndexedChoiceMap_mem_layer D L hz
    · intro hA
      obtain ⟨z, hz, rfl⟩ :=
        exists_indexedChoice_of_mem_supercriticalCombinedChoiceLayer D L hA
      exact Finset.mem_image.mpr ⟨z, hz, rfl⟩
  rw [← himage, Finset.card_image_iff.mpr hinj]

/-- Exact finite Vandermonde decomposition by sparse edge count and feasible
cross profile. -/
theorem supercriticalProfileVandermondeDecomposition
    (D : SupercriticalDivision k V) (L : ℕ) :
    Nat.choose (supercriticalPreAbsorptionVariableCapacity D) L =
      ∑ t ∈ Finset.range (supercriticalSparsePotentialCapacity D + 1),
        ∑ profile ∈ supercriticalAllEdgeProfilesFinset D,
          if profileTotal profile + t = L then
            supercriticalProfileMultiplicity profile *
              Nat.choose (supercriticalSparsePotentialCapacity D) t
          else 0 := by
  classical
  rw [← card_supercriticalPreAbsorptionChoiceFinset D L,
    ← card_supercriticalProfileSparseIndexedChoices D L]
  simp [supercriticalProfileSparseIndexedChoices,
    supercriticalProfileSparseIndexFinset,
    card_supercriticalProfileChoiceFinset,
    supercriticalSparseChoiceCapacity,
    supercriticalSparsePotentialCapacity]
  rw [Finset.sum_filter, Finset.sum_product]

/-! ## A prescribed absorbed co-partite fiber -/

/-- Forget the part-pair tag and regard an oriented cross coordinate as its
ambient unordered graph edge. -/
def supercriticalTaggedCrossEdge
    (z : SupercriticalTaggedCrossChoice k V) : Sym2 V :=
  s(z.2.1, z.2.2)

/-- On the valid cross-coordinate universe, forgetting the tag loses no
information: disjoint parts determine the tag and its increasing
orientation uniquely. -/
theorem supercriticalTaggedCrossEdge_injectiveOn
    (D : SupercriticalDivision k V) :
    Set.InjOn
      (fun z : SupercriticalTaggedCrossChoice k V ↦
        supercriticalTaggedCrossEdge z)
      (↑(supercriticalTaggedCrossChoiceUniverse D) :
        Set (SupercriticalTaggedCrossChoice k V)) := by
  classical
  rintro ⟨e, x, y⟩ hz ⟨e', x', y'⟩ hz' heq
  change ⟨e, (x, y)⟩ ∈ supercriticalTaggedCrossChoiceUniverse D at hz
  change ⟨e', (x', y')⟩ ∈ supercriticalTaggedCrossChoiceUniverse D at hz'
  rw [mem_supercriticalTaggedCrossChoiceUniverse] at hz hz'
  rcases Sym2.eq_iff.mp heq with h | h
  · rcases h with ⟨rfl, rfl⟩
    have hl : e.left = e'.left := D.mem_part_unique hz.1 hz'.1
    have hr : e.right = e'.right := D.mem_part_unique hz.2 hz'.2
    have he : e = e' := SupercriticalPartPair.ext hl hr
    subst e'
    rfl
  · rcases h with ⟨rfl, rfl⟩
    have hlr : e.left = e'.right := D.mem_part_unique hz.1 hz'.2
    have hrl : e.right = e'.left := D.mem_part_unique hz.2 hz'.1
    have hback : e'.right < e'.left := by
      simpa [hlr, hrl] using e.left_lt_right
    exact False.elim (lt_asymm e'.left_lt_right hback)

/-- The graph containing precisely a selected finite set of valid cross
edges and no other edges. -/
def supercriticalSelectedCrossGraph
    (A : Finset (SupercriticalTaggedCrossChoice k V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet
    (↑(A.image supercriticalTaggedCrossEdge) : Set (Sym2 V))

theorem supercriticalTaggedCrossChoice_ne
    (D : SupercriticalDivision k V)
    {z : SupercriticalTaggedCrossChoice k V}
    (hz : z ∈ supercriticalTaggedCrossChoiceUniverse D) :
    z.2.1 ≠ z.2.2 := by
  intro hxy
  rw [mem_supercriticalTaggedCrossChoiceUniverse] at hz
  have := D.mem_part_unique hz.1 (hxy ▸ hz.2)
  exact z.1.left_ne_right this

theorem supercriticalSelectedCrossGraph_adj_iff
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D)
    {z : SupercriticalTaggedCrossChoice k V}
    (hz : z ∈ supercriticalTaggedCrossChoiceUniverse D) :
    (supercriticalSelectedCrossGraph A).Adj z.2.1 z.2.2 ↔ z ∈ A := by
  classical
  rw [supercriticalSelectedCrossGraph, SimpleGraph.fromEdgeSet_adj]
  change supercriticalTaggedCrossEdge z ∈
      A.image supercriticalTaggedCrossEdge ∧ z.2.1 ≠ z.2.2 ↔ z ∈ A
  have himage : supercriticalTaggedCrossEdge z ∈
      A.image supercriticalTaggedCrossEdge ↔ z ∈ A := by
    constructor
    · rw [Finset.mem_image]
      rintro ⟨z', hz'A, hedge⟩
      have hz'U := hA hz'A
      have : z' = z := supercriticalTaggedCrossEdge_injectiveOn D hz'U hz hedge
      simpa [this] using hz'A
    · exact fun hzA ↦ Finset.mem_image.mpr ⟨z, hzA, rfl⟩
  rw [himage]
  simp [supercriticalTaggedCrossChoice_ne D hz]

/-- Complete every prescribed part to a clique while retaining exactly the
selected cross edges. -/
def supercriticalGraphOfCrossChoice
    (D : SupercriticalDivision k V)
    (A : Finset (SupercriticalTaggedCrossChoice k V)) : SimpleGraph V :=
  DenseGraph.completeWithinParts (supercriticalSelectedCrossGraph A) D.parts

theorem supercriticalGraphOfCrossChoice_adj_iff
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D)
    {z : SupercriticalTaggedCrossChoice k V}
    (hz : z ∈ supercriticalTaggedCrossChoiceUniverse D) :
    (supercriticalGraphOfCrossChoice D A).Adj z.2.1 z.2.2 ↔ z ∈ A := by
  classical
  rw [supercriticalGraphOfCrossChoice, DenseGraph.completeWithinParts_adj,
    supercriticalSelectedCrossGraph_adj_iff D hA hz]
  have hnotInternal :
      ¬ (z.2.1 ≠ z.2.2 ∧
        ∃ i, z.2.1 ∈ D.parts i ∧ z.2.2 ∈ D.parts i) := by
    rintro ⟨_hne, i, hxi, hyi⟩
    rw [mem_supercriticalTaggedCrossChoiceUniverse] at hz
    have hil : i = z.1.left := D.mem_part_unique hxi hz.1
    have hir : i = z.1.right := D.mem_part_unique hyi hz.2
    exact z.1.left_ne_right (hil.symm.trans hir)
  simp [hnotInternal]

theorem supercriticalGraphOfCrossChoice_injectiveOn
    (D : SupercriticalDivision k V) :
    Set.InjOn (supercriticalGraphOfCrossChoice D)
      {A : Finset (SupercriticalTaggedCrossChoice k V) |
        A ⊆ supercriticalTaggedCrossChoiceUniverse D} := by
  classical
  intro A hA B hB hgraph
  ext z
  by_cases hz : z ∈ supercriticalTaggedCrossChoiceUniverse D
  · have hadj := congrArg
      (fun G : SimpleGraph V ↦ G.Adj z.2.1 z.2.2) hgraph
    simpa [supercriticalGraphOfCrossChoice_adj_iff D hA hz,
      supercriticalGraphOfCrossChoice_adj_iff D hB hz] using hadj
  · have hzA : z ∉ A := fun h ↦ hz (hA h)
    have hzB : z ∉ B := fun h ↦ hz (hB h)
    simp [hzA, hzB]

/-! The following finite edge-set lemmas certify that the constructor has
exactly the selected cross edges in addition to the forced clique edges. -/

private theorem mk_mem_supercriticalInternalEdgeCell
    (S : Finset V) (x y : V) :
    s(x, y) ∈ S.offDiag.image Sym2.mk.uncurry ↔
      x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  classical
  constructor
  · rw [Finset.mem_image]
    rintro ⟨⟨a, b⟩, hab, heq⟩
    rw [Finset.mem_offDiag] at hab
    rcases Sym2.eq_iff.mp heq with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact hab
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨hab.2.1, hab.1, hab.2.2.symm⟩
  · rintro ⟨hx, hy, hxy⟩
    rw [Finset.mem_image]
    exact ⟨(x, y), by simp [hx, hy, hxy], rfl⟩

/-- The unordered edges forced by completing every prescribed part. -/
def supercriticalInternalEdgeFinset
    (D : SupercriticalDivision k V) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i ↦
    (D.parts i).offDiag.image Sym2.mk.uncurry

@[simp] theorem mk_mem_supercriticalInternalEdgeFinset
    (D : SupercriticalDivision k V) (x y : V) :
    s(x, y) ∈ supercriticalInternalEdgeFinset D ↔
      x ≠ y ∧ ∃ i, x ∈ D.parts i ∧ y ∈ D.parts i := by
  classical
  simp only [supercriticalInternalEdgeFinset, Finset.mem_biUnion,
    Finset.mem_univ, true_and, mk_mem_supercriticalInternalEdgeCell]
  tauto

@[simp] theorem card_supercriticalInternalEdgeFinset
    (D : SupercriticalDivision k V) :
    (supercriticalInternalEdgeFinset D).card =
      divisionInternalCliqueCapacity D := by
  classical
  have hdisjoint : Set.PairwiseDisjoint
      (↑(Finset.univ : Finset (Fin (k - 1))) : Set (Fin (k - 1)))
      (fun i ↦ (D.parts i).offDiag.image Sym2.mk.uncurry) := by
    intro i _hi j _hj hij
    change Disjoint
      ((D.parts i).offDiag.image Sym2.mk.uncurry)
      ((D.parts j).offDiag.image Sym2.mk.uncurry)
    rw [Finset.disjoint_left]
    intro e hei hej
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hi := (mk_mem_supercriticalInternalEdgeCell
          (D.parts i) x y).mp hei
        have hj := (mk_mem_supercriticalInternalEdgeCell
          (D.parts j) x y).mp hej
        exact (Finset.disjoint_left.mp
          (D.parts_pairwiseDisjoint (Set.mem_univ i)
            (Set.mem_univ j) hij)) hi.1 hj.1
  rw [supercriticalInternalEdgeFinset, Finset.card_biUnion hdisjoint]
  unfold divisionInternalCliqueCapacity
  apply Finset.sum_congr rfl
  intro i _hi
  exact Sym2.card_image_offDiag (D.parts i)

theorem finiteGraphEdges_partitionCliqueGraph
    (D : SupercriticalDivision k V) :
    finiteGraphEdges (DenseGraph.partitionCliqueGraph D.parts) =
      supercriticalInternalEdgeFinset D := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [mk_mem_finiteGraphEdges,
        mk_mem_supercriticalInternalEdgeFinset]
      exact DenseGraph.partitionCliqueGraph_adj D.parts x y

theorem finiteGraphEdges_supercriticalSelectedCrossGraph
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D) :
    finiteGraphEdges (supercriticalSelectedCrossGraph A) =
      A.image supercriticalTaggedCrossEdge := by
  classical
  ext e
  rw [mem_finiteGraphEdges, supercriticalSelectedCrossGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  constructor
  · exact fun he ↦ he.1
  · intro he
    refine ⟨he, ?_⟩
    rw [Finset.mem_image] at he
    obtain ⟨z, hzA, rfl⟩ := he
    rw [Sym2.mem_diagSet]
    simpa [supercriticalTaggedCrossEdge, Sym2.mk_isDiag_iff] using
      (supercriticalTaggedCrossChoice_ne D (hA hzA))

theorem finiteGraphEdges_supercriticalGraphOfCrossChoice
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D) :
    finiteGraphEdges (supercriticalGraphOfCrossChoice D A) =
      A.image supercriticalTaggedCrossEdge ∪
        supercriticalInternalEdgeFinset D := by
  classical
  ext e
  simp only [mem_finiteGraphEdges, supercriticalGraphOfCrossChoice,
    DenseGraph.completeWithinParts, SimpleGraph.edgeSet_sup, Set.mem_union,
    Finset.mem_union]
  rw [← mem_finiteGraphEdges,
    finiteGraphEdges_supercriticalSelectedCrossGraph D hA,
    ← mem_finiteGraphEdges, finiteGraphEdges_partitionCliqueGraph D]

theorem supercriticalSelectedCrossEdges_disjoint_internal
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D) :
    Disjoint (A.image supercriticalTaggedCrossEdge)
      (supercriticalInternalEdgeFinset D) := by
  classical
  rw [Finset.disjoint_left]
  intro e heA heInternal
  rw [Finset.mem_image] at heA
  obtain ⟨⟨p, x, y⟩, hzA, rfl⟩ := heA
  have hzU := hA hzA
  rw [mem_supercriticalTaggedCrossChoiceUniverse] at hzU
  change s(x, y) ∈ supercriticalInternalEdgeFinset D at heInternal
  rw [mk_mem_supercriticalInternalEdgeFinset] at heInternal
  obtain ⟨_hxy, i, hxi, hyi⟩ := heInternal
  have hleft : p.left = i := D.mem_part_unique hzU.1 hxi
  have hright : p.right = i := D.mem_part_unique hzU.2 hyi
  exact p.left_ne_right (hleft.trans hright.symm)

/-- Exact edge count of the explicit selected-cross-edge constructor. -/
theorem card_finiteGraphEdges_supercriticalGraphOfCrossChoice
    (D : SupercriticalDivision k V)
    {A : Finset (SupercriticalTaggedCrossChoice k V)}
    (hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D) :
    (finiteGraphEdges (supercriticalGraphOfCrossChoice D A)).card =
      A.card + divisionInternalCliqueCapacity D := by
  classical
  rw [finiteGraphEdges_supercriticalGraphOfCrossChoice D hA,
    Finset.card_union_of_disjoint
      (supercriticalSelectedCrossEdges_disjoint_internal D hA),
    Finset.card_image_iff.mpr, card_supercriticalInternalEdgeFinset]
  intro x hx y hy hxy
  exact supercriticalTaggedCrossEdge_injectiveOn D
    (by exact_mod_cast hA hx) (by exact_mod_cast hA hy) hxy

/-- Graphs with the prescribed absorbed division, all absorbed parts made
cliques, and exactly `m - e(D_*^c)` selected cross edges. No canonical
division or unique-cover condition is imposed. -/
def supercriticalAbsorbedCoPartiteGraphFinset
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ) :
    Finset (SimpleGraph V) := by
  classical
  let DStar := supercriticalAbsorbSparseDivision hk D
  exact if divisionInternalCliqueCapacity DStar ≤ m then
    ((supercriticalTaggedCrossChoiceUniverse DStar).powersetCard
      (m - divisionInternalCliqueCapacity DStar)).image
        (supercriticalGraphOfCrossChoice DStar)
  else ∅

@[simp] theorem mem_supercriticalAbsorbedCoPartiteGraphFinset
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ)
    (G : SimpleGraph V) :
    G ∈ supercriticalAbsorbedCoPartiteGraphFinset hk D m ↔
      divisionInternalCliqueCapacity
          (supercriticalAbsorbSparseDivision hk D) ≤ m ∧
      ∃ A : Finset (SupercriticalTaggedCrossChoice k V),
        A ⊆ supercriticalTaggedCrossChoiceUniverse
          (supercriticalAbsorbSparseDivision hk D) ∧
        A.card = m - divisionInternalCliqueCapacity
          (supercriticalAbsorbSparseDivision hk D) ∧
        supercriticalGraphOfCrossChoice
          (supercriticalAbsorbSparseDivision hk D) A = G := by
  classical
  by_cases hcapacity : divisionInternalCliqueCapacity
      (supercriticalAbsorbSparseDivision hk D) ≤ m
  · simp [supercriticalAbsorbedCoPartiteGraphFinset, hcapacity,
      Finset.mem_powersetCard, and_assoc]
  · simp [supercriticalAbsorbedCoPartiteGraphFinset, hcapacity]

/-- Every member contains a clique on each part of the prescribed absorbed
division. -/
theorem supercriticalAbsorbedCoPartiteGraph_isClique
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ)
    {G : SimpleGraph V}
    (hG : G ∈ supercriticalAbsorbedCoPartiteGraphFinset hk D m)
    (i : Fin (k - 1)) :
    G.IsClique
      ((supercriticalAbsorbSparseDivision hk D).parts i : Set V) := by
  obtain ⟨_capacity, A, hA, hAcard, hAG⟩ :=
    (mem_supercriticalAbsorbedCoPartiteGraphFinset hk D m G).mp hG
  subst G
  exact DenseGraph.completeWithinParts_isClique
    (supercriticalSelectedCrossGraph A)
    (supercriticalAbsorbSparseDivision hk D).parts i

/-- The prescribed absorbed parts cover the entire ambient vertex set. -/
theorem supercriticalAbsorbedCoPartiteParts_cover
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    Finset.univ.biUnion
        (supercriticalAbsorbSparseDivision hk D).parts =
      (Finset.univ : Finset V) := by
  change (supercriticalAbsorbSparseDivision hk D).support = Finset.univ
  exact supercriticalAbsorbSparseDivision_support hk D

/-- Membership really means exact edge count `m`; the lower-capacity guard
rules out the truncated-subtraction artifact when the forced clique edges
already exceed `m`. -/
theorem card_finiteGraphEdges_eq_of_mem_supercriticalAbsorbedCoPartiteGraphFinset
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ)
    {G : SimpleGraph V}
    (hG : G ∈ supercriticalAbsorbedCoPartiteGraphFinset hk D m) :
    (finiteGraphEdges G).card = m := by
  obtain ⟨hcapacity, A, hA, hAcard, hAG⟩ :=
    (mem_supercriticalAbsorbedCoPartiteGraphFinset hk D m G).mp hG
  subst G
  rw [card_finiteGraphEdges_supercriticalGraphOfCrossChoice _ hA,
    hAcard]
  omega

/-- Consequently every member is co-`(k-1)`-partite through the displayed
absorbed cover, with no assertion that this cover is canonical or unique. -/
theorem supercriticalAbsorbedCoPartiteGraph_isCoMultipartite
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ)
    {G : SimpleGraph V}
    (hG : G ∈ supercriticalAbsorbedCoPartiteGraphFinset hk D m) :
    DenseGraph.IsCoMultipartite G (k - 1) := by
  obtain ⟨_capacity, A, hA, hAcard, hAG⟩ :=
    (mem_supercriticalAbsorbedCoPartiteGraphFinset hk D m G).mp hG
  subst G
  exact DenseGraph.completeWithinParts_isCoMultipartite
    (supercriticalSelectedCrossGraph A)
    (supercriticalAbsorbSparseDivision hk D).parts
    (supercriticalAbsorbedCoPartiteParts_cover hk D)
    (supercriticalAbsorbSparseDivision hk D).parts_pairwiseDisjoint

/-- Exact size of the fixed-edge prescribed absorbed co-partite fiber. -/
@[simp] theorem card_supercriticalAbsorbedCoPartiteGraphFinset
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (m : ℕ)
    (hcapacity : divisionInternalCliqueCapacity
      (supercriticalAbsorbSparseDivision hk D) ≤ m) :
    (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card =
      Nat.choose
        (supercriticalTotalCrossCapacity
          (supercriticalAbsorbSparseDivision hk D))
        (m - divisionInternalCliqueCapacity
          (supercriticalAbsorbSparseDivision hk D)) := by
  classical
  let DStar := supercriticalAbsorbSparseDivision hk D
  rw [supercriticalAbsorbedCoPartiteGraphFinset, if_pos hcapacity,
    Finset.card_image_iff.mpr]
  · simp [DStar]
  · intro A hA B hB hgraph
    apply supercriticalGraphOfCrossChoice_injectiveOn DStar
    · exact (Finset.mem_powersetCard.mp hA).1
    · exact (Finset.mem_powersetCard.mp hB).1
    · exact hgraph



end InducedStars
