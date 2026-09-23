import InducedStars.Structure.Supercritical.ProfileRealization
import Mathlib.Tactic

/-!
# Sparse absorption for supercritical divisions

This file implements the paper's division `Π_*`: the sparse set is moved into
a canonically selected smallest main part.  It records the exact change in
internal clique capacity and transports a dependent cross-edge profile without
changing any of its coordinate counts.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The canonical smallest part -/

/-- A fixed noncomputable least-cardinality main part.  The proof never
depends on how equal-cardinality minimizers are resolved. -/
noncomputable def supercriticalSmallestPartIndex
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) : Fin (k - 1) :=
  Function.argminOn (fun i : Fin (k - 1) ↦ (D.parts i).card)
    Set.univ ⟨⟨0, by omega⟩, Set.mem_univ _⟩

/-- The selected part has no more vertices than any other main part. -/
theorem supercriticalSmallestPartIndex_card_le
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (j : Fin (k - 1)) :
    (D.parts (supercriticalSmallestPartIndex hk D)).card ≤
      (D.parts j).card := by
  exact Function.argminOn_le
    (fun i : Fin (k - 1) ↦ (D.parts i).card) Set.univ (Set.mem_univ j)

/-- Summing the smallest-part bound over all `k - 1` parts bounds it by the
whole main support. -/
theorem supercriticalSmallestPartIndex_mul_card_le_support
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    (k - 1) * (D.parts (supercriticalSmallestPartIndex hk D)).card ≤
      D.support.card := by
  rw [D.card_support]
  calc
    (k - 1) * (D.parts (supercriticalSmallestPartIndex hk D)).card =
        ∑ _j : Fin (k - 1),
          (D.parts (supercriticalSmallestPartIndex hk D)).card := by simp
    _ ≤ ∑ j : Fin (k - 1), (D.parts j).card := by
      exact Finset.sum_le_sum fun j _ ↦
        supercriticalSmallestPartIndex_card_le hk D j

/-! ## Absorbing the sparse set -/

/-- Move every sparse vertex into the canonical smallest main part. -/
def supercriticalAbsorbSparseDivision
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    SupercriticalDivision k V where
  parts i :=
    if i = supercriticalSmallestPartIndex hk D then
      D.parts i ∪ D.sparse
    else
      D.parts i
  parts_nonempty i := by
    by_cases hi : i = supercriticalSmallestPartIndex hk D
    · rw [if_pos hi]
      exact (D.parts_nonempty i).mono Finset.subset_union_left
    · rw [if_neg hi]
      exact D.parts_nonempty i
  parts_pairwiseDisjoint := by
    intro i _hi j _hj hij
    change Disjoint
      (if i = supercriticalSmallestPartIndex hk D then
        D.parts i ∪ D.sparse else D.parts i)
      (if j = supercriticalSmallestPartIndex hk D then
        D.parts j ∪ D.sparse else D.parts j)
    by_cases hi : i = supercriticalSmallestPartIndex hk D
    · subst i
      have hj : j ≠ supercriticalSmallestPartIndex hk D := by
        exact fun h ↦ hij h.symm
      rw [if_pos rfl, if_neg hj]
      exact Finset.disjoint_union_left.mpr ⟨
        D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij,
        D.sparse_disjoint_part j⟩
    · by_cases hj : j = supercriticalSmallestPartIndex hk D
      · subst j
        rw [if_neg hi, if_pos rfl]
        exact Finset.disjoint_union_right.mpr ⟨
          D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij,
          D.part_disjoint_sparse i⟩
      · rw [if_neg hi, if_neg hj]
        exact D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hij

@[simp] theorem supercriticalAbsorbSparseDivision_part_smallest
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    (supercriticalAbsorbSparseDivision hk D).parts
        (supercriticalSmallestPartIndex hk D) =
      D.parts (supercriticalSmallestPartIndex hk D) ∪ D.sparse := by
  simp [supercriticalAbsorbSparseDivision]

theorem supercriticalAbsorbSparseDivision_part_of_ne
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {i : Fin (k - 1)}
    (hi : i ≠ supercriticalSmallestPartIndex hk D) :
    (supercriticalAbsorbSparseDivision hk D).parts i = D.parts i := by
  simp [supercriticalAbsorbSparseDivision, hi]

@[simp] theorem supercriticalAbsorbSparseDivision_support
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    (supercriticalAbsorbSparseDivision hk D).support = Finset.univ := by
  ext v
  simp only [SupercriticalDivision.mem_support, Finset.mem_univ, iff_true]
  rcases D.sparse_or_existsUnique_part v with hv | ⟨i, hvi, _⟩
  · refine ⟨supercriticalSmallestPartIndex hk D, ?_⟩
    rw [supercriticalAbsorbSparseDivision_part_smallest]
    exact Finset.mem_union_right _ hv
  · refine ⟨i, ?_⟩
    by_cases hi : i = supercriticalSmallestPartIndex hk D
    · subst i
      rw [supercriticalAbsorbSparseDivision_part_smallest]
      exact Finset.mem_union_left _ hvi
    · rw [supercriticalAbsorbSparseDivision_part_of_ne hk D hi]
      exact hvi

@[simp] theorem supercriticalAbsorbSparseDivision_sparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    (supercriticalAbsorbSparseDivision hk D).sparse = ∅ := by
  simp [SupercriticalDivision.sparse]

@[simp] theorem supercriticalAbsorbSparseDivision_part_smallest_card
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    ((supercriticalAbsorbSparseDivision hk D).parts
        (supercriticalSmallestPartIndex hk D)).card =
      (D.parts (supercriticalSmallestPartIndex hk D)).card + D.sparse.card := by
  rw [supercriticalAbsorbSparseDivision_part_smallest,
    Finset.card_union_of_disjoint
      (D.part_disjoint_sparse (supercriticalSmallestPartIndex hk D))]

theorem supercriticalAbsorbSparseDivision_part_card_of_ne
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {i : Fin (k - 1)}
    (hi : i ≠ supercriticalSmallestPartIndex hk D) :
    ((supercriticalAbsorbSparseDivision hk D).parts i).card =
      (D.parts i).card := by
  rw [supercriticalAbsorbSparseDivision_part_of_ne hk D hi]

/-! ## Exact change of internal clique capacity -/

private theorem choose_add_two (a s : ℕ) :
    Nat.choose (a + s) 2 = Nat.choose a 2 + a * s + Nat.choose s 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      change Nat.choose ((a + s) + 1) 2 =
        Nat.choose a 2 + a * (s + 1) + Nat.choose (s + 1) 2
      rw [Nat.choose_succ_succ, ih, Nat.choose_succ_succ]
      simp [Nat.choose_one_right, Nat.mul_succ] at *
      omega

/-- Absorbing a sparse set of size `s` into a part of size `a` creates
exactly `a*s + choose s 2` new internal clique positions. -/
theorem divisionInternalCliqueCapacity_absorbSparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    divisionInternalCliqueCapacity (supercriticalAbsorbSparseDivision hk D) =
      divisionInternalCliqueCapacity D +
        (D.parts (supercriticalSmallestPartIndex hk D)).card * D.sparse.card +
        Nat.choose D.sparse.card 2 := by
  classical
  let iStar := supercriticalSmallestPartIndex hk D
  let DStar := supercriticalAbsorbSparseDivision hk D
  have hi : iStar ∈ (Finset.univ : Finset (Fin (k - 1))) := Finset.mem_univ _
  have haway :
      (∑ i ∈ (Finset.univ : Finset (Fin (k - 1))).erase iStar,
          (DStar.parts i).card.choose 2) =
        ∑ i ∈ (Finset.univ : Finset (Fin (k - 1))).erase iStar,
          (D.parts i).card.choose 2 := by
    apply Finset.sum_congr rfl
    intro i hii
    have hne : i ≠ iStar := Finset.ne_of_mem_erase hii
    rw [show DStar.parts i = D.parts i by
      exact supercriticalAbsorbSparseDivision_part_of_ne hk D hne]
  have hstar :
      (DStar.parts iStar).card.choose 2 =
        (D.parts iStar).card.choose 2 +
          (D.parts iStar).card * D.sparse.card +
          D.sparse.card.choose 2 := by
    rw [show (DStar.parts iStar).card =
        (D.parts iStar).card + D.sparse.card by
      exact supercriticalAbsorbSparseDivision_part_smallest_card hk D]
    exact choose_add_two _ _
  unfold divisionInternalCliqueCapacity
  calc
    ∑ i : Fin (k - 1), (DStar.parts i).card.choose 2 =
        (DStar.parts iStar).card.choose 2 +
          ∑ i ∈ (Finset.univ : Finset (Fin (k - 1))).erase iStar,
            (DStar.parts i).card.choose 2 := by
      exact (Finset.add_sum_erase Finset.univ _ hi).symm
    _ = (D.parts iStar).card.choose 2 +
          (D.parts iStar).card * D.sparse.card +
          D.sparse.card.choose 2 +
          ∑ i ∈ (Finset.univ : Finset (Fin (k - 1))).erase iStar,
            (D.parts i).card.choose 2 := by
      rw [hstar, haway]
    _ = (∑ i : Fin (k - 1), (D.parts i).card.choose 2) +
          (D.parts iStar).card * D.sparse.card +
          D.sparse.card.choose 2 := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun i ↦ (D.parts i).card.choose 2) hi]
      omega

/-! ## Transporting cross-edge profiles -/

/-- Reuse all cross-edge counts after absorbing the sparse set.  Feasibility
is preserved because every main part only grows. -/
def supercriticalAbsorbSparseProfile
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) :
    SupercriticalEdgeProfile (supercriticalAbsorbSparseDivision hk D) where
  count := profile.count
  count_le_capacity e := by
    apply profile.count_le_capacity e |>.trans
    unfold crossEdgeCapacity
    apply Nat.mul_le_mul
    · apply Finset.card_le_card
      intro v hv
      by_cases he : e.left = supercriticalSmallestPartIndex hk D
      · rw [he, supercriticalAbsorbSparseDivision_part_smallest]
        exact Finset.mem_union_left _ (by simpa [he] using hv)
      · rw [supercriticalAbsorbSparseDivision_part_of_ne hk D he]
        exact hv
    · apply Finset.card_le_card
      intro v hv
      by_cases he : e.right = supercriticalSmallestPartIndex hk D
      · rw [he, supercriticalAbsorbSparseDivision_part_smallest]
        exact Finset.mem_union_left _ (by simpa [he] using hv)
      · rw [supercriticalAbsorbSparseDivision_part_of_ne hk D he]
        exact hv

@[simp] theorem supercriticalAbsorbSparseProfile_count
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k) :
    (supercriticalAbsorbSparseProfile hk D profile).count e = profile.count e :=
  rfl

@[simp] theorem profileTotal_supercriticalAbsorbSparseProfile
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) :
    profileTotal (supercriticalAbsorbSparseProfile hk D profile) =
      profileTotal profile :=
  rfl

/-! ## Exact cross-capacity formulas -/

/-- Absorption weakly enlarges every cross-cell capacity. -/
theorem crossEdgeCapacity_le_absorbSparse
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) :
    crossEdgeCapacity D e ≤
      crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e := by
  unfold crossEdgeCapacity
  apply Nat.mul_le_mul <;> apply Finset.card_le_card
  · intro v hv
    by_cases he : e.left = supercriticalSmallestPartIndex hk D
    · rw [he, supercriticalAbsorbSparseDivision_part_smallest]
      exact Finset.mem_union_left _ (by simpa [he] using hv)
    · rw [supercriticalAbsorbSparseDivision_part_of_ne hk D he]
      exact hv
  · intro v hv
    by_cases he : e.right = supercriticalSmallestPartIndex hk D
    · rw [he, supercriticalAbsorbSparseDivision_part_smallest]
      exact Finset.mem_union_left _ (by simpa [he] using hv)
    · rw [supercriticalAbsorbSparseDivision_part_of_ne hk D he]
      exact hv

/-- A single orientation-independent formula for all absorbed cross-cell
capacities.  At most one conditional correction can be nonzero because a
part pair has distinct endpoints. -/
theorem crossEdgeCapacity_absorbSparse_eq
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) :
    crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e =
      crossEdgeCapacity D e +
        (if e.left = supercriticalSmallestPartIndex hk D then
          D.sparse.card * (D.parts e.right).card
        else if e.right = supercriticalSmallestPartIndex hk D then
          (D.parts e.left).card * D.sparse.card
        else 0) := by
  unfold crossEdgeCapacity
  by_cases hl : e.left = supercriticalSmallestPartIndex hk D
  · have hr : e.right ≠ supercriticalSmallestPartIndex hk D := by
      exact fun h ↦ e.left_ne_right (hl.trans h.symm)
    rw [hl, supercriticalAbsorbSparseDivision_part_smallest_card,
      supercriticalAbsorbSparseDivision_part_card_of_ne hk D hr]
    simp [Nat.add_mul]
  · by_cases hr : e.right = supercriticalSmallestPartIndex hk D
    · rw [hr, supercriticalAbsorbSparseDivision_part_card_of_ne hk D hl,
        supercriticalAbsorbSparseDivision_part_smallest_card]
      simp [hl, Nat.mul_add]
    · rw [supercriticalAbsorbSparseDivision_part_card_of_ne hk D hl,
        supercriticalAbsorbSparseDivision_part_card_of_ne hk D hr,
        if_neg hl, if_neg hr]
      omega

/-- Cross capacities away from the absorbed part are unchanged. -/
theorem crossEdgeCapacity_absorbSparse_of_not_incident
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k)
    (hl : e.left ≠ supercriticalSmallestPartIndex hk D)
    (hr : e.right ≠ supercriticalSmallestPartIndex hk D) :
    crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e =
      crossEdgeCapacity D e := by
  rw [crossEdgeCapacity_absorbSparse_eq, if_neg hl, if_neg hr, Nat.add_zero]

/-- If `e` is incident with the absorbed part and `j` is its other endpoint,
the capacity grows by exactly `s * |P_j|`, independently of the stored
orientation of `e`. -/
theorem crossEdgeCapacity_absorbSparse_of_incident
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) (j : Fin (k - 1))
    (hj :
      (e.left = supercriticalSmallestPartIndex hk D ∧ e.right = j) ∨
      (e.right = supercriticalSmallestPartIndex hk D ∧ e.left = j)) :
    crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e =
      crossEdgeCapacity D e + D.sparse.card * (D.parts j).card := by
  rcases hj with ⟨hl, rfl⟩ | ⟨hr, rfl⟩
  · rw [crossEdgeCapacity_absorbSparse_eq, if_pos hl]
  · have hl : e.left ≠ supercriticalSmallestPartIndex hk D := by
      exact fun h ↦ e.left_ne_right (h.trans hr.symm)
    rw [crossEdgeCapacity_absorbSparse_eq, if_neg hl, if_pos hr]
    simp only [Nat.mul_comm]

/-! ## Density transport -/

/-- A profile density is literally unchanged on a cell not incident with the
absorbed part. -/
theorem profileDensity_supercriticalAbsorbSparseProfile_of_not_incident
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k)
    (hl : e.left ≠ supercriticalSmallestPartIndex hk D)
    (hr : e.right ≠ supercriticalSmallestPartIndex hk D) :
    profileDensity (supercriticalAbsorbSparseProfile hk D profile) e =
      profileDensity profile e := by
  unfold profileDensity
  rw [supercriticalAbsorbSparseDivision_part_card_of_ne hk D hl,
    supercriticalAbsorbSparseDivision_part_card_of_ne hk D hr]
  rfl

/-- On a cell incident with the absorbed part, the density is multiplied by
the exact dilution factor `a / (a + s)`.  The formula is independent of the
stored orientation of the unordered part pair. -/
theorem profileDensity_supercriticalAbsorbSparseProfile_of_incident
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k)
    (hincident :
      e.left = supercriticalSmallestPartIndex hk D ∨
        e.right = supercriticalSmallestPartIndex hk D) :
    profileDensity (supercriticalAbsorbSparseProfile hk D profile) e =
      profileDensity profile e *
        (((D.parts (supercriticalSmallestPartIndex hk D)).card : ℝ) /
          ((D.parts (supercriticalSmallestPartIndex hk D)).card +
            D.sparse.card : ℕ)) := by
  have ha : 0 < ((D.parts (supercriticalSmallestPartIndex hk D)).card : ℝ) := by
    exact_mod_cast (D.parts_nonempty
      (supercriticalSmallestPartIndex hk D)).card_pos
  rcases hincident with hl | hr
  · have hright : e.right ≠ supercriticalSmallestPartIndex hk D := by
      exact fun h ↦ e.left_ne_right (hl.trans h.symm)
    have hb : 0 < ((D.parts e.right).card : ℝ) := by
      exact_mod_cast (D.parts_nonempty e.right).card_pos
    unfold profileDensity
    rw [hl, supercriticalAbsorbSparseDivision_part_smallest_card,
      supercriticalAbsorbSparseDivision_part_card_of_ne hk D hright]
    push_cast
    simp only [supercriticalAbsorbSparseProfile_count]
    field_simp
  · have hleft : e.left ≠ supercriticalSmallestPartIndex hk D := by
      exact fun h ↦ e.left_ne_right (h.trans hr.symm)
    have hb : 0 < ((D.parts e.left).card : ℝ) := by
      exact_mod_cast (D.parts_nonempty e.left).card_pos
    unfold profileDensity
    rw [hr, supercriticalAbsorbSparseDivision_part_card_of_ne hk D hleft,
      supercriticalAbsorbSparseDivision_part_smallest_card]
    push_cast
    simp only [supercriticalAbsorbSparseProfile_count]
    field_simp

/-- Absorbing vertices can only dilute a transported cross density. -/
theorem profileDensity_supercriticalAbsorbSparseProfile_le
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k) :
    profileDensity (supercriticalAbsorbSparseProfile hk D profile) e ≤
      profileDensity profile e := by
  by_cases hl : e.left = supercriticalSmallestPartIndex hk D
  · rw [profileDensity_supercriticalAbsorbSparseProfile_of_incident
      hk D profile e (Or.inl hl)]
    have hdensity : 0 ≤ profileDensity profile e := by
      unfold profileDensity
      positivity
    apply mul_le_of_le_one_right hdensity
    apply (div_le_one (by
      exact_mod_cast Nat.add_pos_left
        (D.parts_nonempty (supercriticalSmallestPartIndex hk D)).card_pos
        D.sparse.card)).2
    exact_mod_cast Nat.le_add_right
      (D.parts (supercriticalSmallestPartIndex hk D)).card D.sparse.card
  · by_cases hr : e.right = supercriticalSmallestPartIndex hk D
    · rw [profileDensity_supercriticalAbsorbSparseProfile_of_incident
        hk D profile e (Or.inr hr)]
      have hdensity : 0 ≤ profileDensity profile e := by
        unfold profileDensity
        positivity
      apply mul_le_of_le_one_right hdensity
      apply (div_le_one (by
        exact_mod_cast Nat.add_pos_left
          (D.parts_nonempty (supercriticalSmallestPartIndex hk D)).card_pos
          D.sparse.card)).2
      exact_mod_cast Nat.le_add_right
        (D.parts (supercriticalSmallestPartIndex hk D)).card D.sparse.card
    · exact le_of_eq
        (profileDensity_supercriticalAbsorbSparseProfile_of_not_incident
          hk D profile e hl hr)

/-- Balance and the paper's sparse-size bound control the relative size of
the absorbed set compared with the selected smallest part. -/
theorem sparse_card_div_smallestPart_card_le
    {n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2) :
    (D.sparse.card : ℝ) /
        (D.parts (supercriticalSmallestPartIndex hk D)).card ≤
      ((k - 1 : ℕ) : ℝ) * delta := by
  let iStar := supercriticalSmallestPartIndex hk D
  let r : ℝ := (k - 1 : ℕ)
  let a : ℝ := (D.parts iStar).card
  let s : ℝ := D.sparse.card
  change s / a ≤ r * delta
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have ha : 0 < a := by
    dsimp [a, iStar]
    exact_mod_cast (D.parts_nonempty
      (supercriticalSmallestPartIndex hk D)).card_pos
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have halower : (n : ℝ) / (2 * r) ≤ a := by
    have hraw := hclose iStar
    have hlower : (n : ℝ) / r - delta * n ≤ a := by
      dsimp [a, r]
      rw [abs_le] at hraw
      linarith
    have hcoeff : delta ≤ 1 / (2 * r) := by
      calc
        delta ≤ 1 / (6 * r) := by simpa [r] using hdelta
        _ ≤ 1 / (2 * r) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).2
          nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hcoeff hn0
    have hid : (n : ℝ) / r - 1 / (2 * r) * n = n / (2 * r) := by
      field_simp
      ring
    rw [← hid]
    linarith
  have hn_le : (n : ℝ) ≤ 2 * r * a := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * r)).mp halower
    simpa [mul_assoc, mul_comm, mul_left_comm] using this
  have hs : s ≤ delta * n / 2 := by simpa [s] using hsparse
  have hscale := mul_le_mul_of_nonneg_left hn_le
    (div_nonneg hdelta0 (show (0 : ℝ) ≤ 2 by norm_num))
  have hsra : s ≤ r * delta * a := by
    calc
      s ≤ delta * n / 2 := hs
      _ = (delta / 2) * n := by ring
      _ ≤ (delta / 2) * (2 * r * a) := hscale
      _ = r * delta * a := by ring
  apply (div_le_iff₀ ha).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hsra

private theorem one_sub_div_le_div_add (a s : ℝ) (ha : 0 < a)
    (hs : 0 ≤ s) :
    1 - s / a ≤ a / (a + s) := by
  have has : 0 < a + s := by linarith
  rw [show 1 - s / a = (a - s) / a by field_simp]
  apply (div_le_div_iff₀ ha has).2
  have hnon : 0 ≤ s * (a + s - (a - s)) :=
    mul_nonneg hs (by linarith)
  nlinarith

private theorem widened_density_product_lower
    {rho delta r d q : ℝ}
    (hrho1 : rho ≤ 1) (hdelta0 : 0 ≤ delta)
    (hr0 : 0 ≤ r) (hrd : r * delta ≤ 1)
    (hd : rho - delta ≤ d) (hd0 : 0 ≤ d)
    (hq : 1 - r * delta ≤ q) :
    rho - (r + 1) * delta ≤ d * q := by
  have hfactor : 0 ≤ 1 - r * delta := by linarith
  have hfirst := mul_le_mul hd hq hfactor hd0
  have hrdelta : 0 ≤ r * delta := mul_nonneg hr0 hdelta0
  have hrhomul : rho * (r * delta) ≤ r * delta :=
    mul_le_of_le_one_left hrdelta hrho1
  have hsquare : 0 ≤ r * delta * delta :=
    mul_nonneg hrdelta hdelta0
  nlinarith

/-- The transported profile remains in an explicit widened density band.
Coordinates away from the absorbed part retain the original band exactly;
incident coordinates lose at most `k * delta` on the lower side. -/
theorem supercriticalAbsorbSparseProfile_density_bounds
    {n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D) {rho delta : ℝ}
    (hrho1 : rho ≤ 1) (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2)
    (hprofile : ∀ e, rho - delta ≤ profileDensity profile e ∧
      profileDensity profile e ≤ rho + delta) :
    ∀ e, rho - (k : ℝ) * delta ≤
        profileDensity (supercriticalAbsorbSparseProfile hk D profile) e ∧
      profileDensity (supercriticalAbsorbSparseProfile hk D profile) e ≤
        rho + delta := by
  let a : ℝ := (D.parts (supercriticalSmallestPartIndex hk D)).card
  let s : ℝ := D.sparse.card
  let r : ℝ := (k - 1 : ℕ)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (D.parts_nonempty
      (supercriticalSmallestPartIndex hk D)).card_pos
  have hs : 0 ≤ s := by positivity
  have hrpos : 0 < r := by
    dsimp [r]
    exact_mod_cast (by omega : 0 < k - 1)
  have hratio : 1 - r * delta ≤ a / (a + s) := by
    calc
      1 - r * delta ≤ 1 - s / a := by
        have hsa := sparse_card_div_smallestPart_card_le
          hk D hdelta0 hdelta hclose hsparse
        change s / a ≤ r * delta at hsa
        linarith
      _ ≤ a / (a + s) := one_sub_div_le_div_add a s ha hs
  have hrd : r * delta ≤ 1 := by
    have hdelta' : delta ≤ 1 / (6 * r) := by simpa [r] using hdelta
    have hmul := mul_le_mul_of_nonneg_left hdelta' hrpos.le
    have heq : r * (1 / (6 * r)) = (1 : ℝ) / 6 := by
      field_simp
    rw [heq] at hmul
    linarith
  have hcast : (k : ℝ) = r + 1 := by
    dsimp [r]
    norm_num [Nat.cast_sub (by omega : 1 ≤ k)]
  have hproduct (e : SupercriticalPartPair k) :
      rho - (r + 1) * delta ≤
        profileDensity profile e * (a / (a + s)) := by
    exact widened_density_product_lower hrho1 hdelta0 hrpos.le hrd
      (hprofile e).1 (by unfold profileDensity; positivity) hratio
  intro e
  constructor
  · by_cases hl : e.left = supercriticalSmallestPartIndex hk D
    · rw [profileDensity_supercriticalAbsorbSparseProfile_of_incident
        hk D profile e (Or.inl hl), hcast]
      simpa [a, s] using hproduct e
    · by_cases hr : e.right = supercriticalSmallestPartIndex hk D
      · rw [profileDensity_supercriticalAbsorbSparseProfile_of_incident
          hk D profile e (Or.inr hr), hcast]
        simpa [a, s] using hproduct e
      · rw [profileDensity_supercriticalAbsorbSparseProfile_of_not_incident
          hk D profile e hl hr]
        have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
        exact (hprofile e).1.trans' (by
          nlinarith [mul_le_mul_of_nonneg_right hkreal hdelta0])
  · exact (profileDensity_supercriticalAbsorbSparseProfile_le
      hk D profile e).trans (hprofile e).2

/-! ## The exact edge equation after absorption -/

/-- The number of new internal clique positions not already paid for by the
`t` sparse edges in the original exact profile equation. -/
def supercriticalSparseAbsorptionExcess
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (t : ℕ) : ℕ :=
  (D.parts (supercriticalSmallestPartIndex hk D)).card * D.sparse.card +
    Nat.choose D.sparse.card 2 - t

/-- If `t` is a feasible sparse-edge count, the absorption excess retains
at least the full old-part--sparse cross term. -/
theorem smallest_mul_sparse_le_supercriticalSparseAbsorptionExcess
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) (t : ℕ)
    (ht : t ≤ Nat.choose D.sparse.card 2) :
    (D.parts (supercriticalSmallestPartIndex hk D)).card * D.sparse.card ≤
      supercriticalSparseAbsorptionExcess hk D t := by
  unfold supercriticalSparseAbsorptionExcess
  omega

/-- Transporting a profile and absorbing the sparse vertices turns the old
shift-`t` edge equation into the displayed capacity identity with the exact
absorption excess on the right. This identity retains the excess rather than
producing a zero-shift profile at the original target `m`.
`supercriticalShiftedProfileAggregate_le_absorbedCoPartite` in
`JointAbsorption` compares the shifted aggregate with the absorbed fiber at
that target by a joint capacity and selected-count estimate. -/
theorem supercriticalAbsorbSparseProfile_edgeCount_identity
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {m : ℕ} {rho delta : ℝ} {t : ℕ}
    (profile : SupercriticalEdgeProfile D)
    (ht : t ≤ Nat.choose D.sparse.card 2)
    (hatShift : SupercriticalProfileAtShift D m rho delta (t : ℤ) profile) :
    profileTotal (supercriticalAbsorbSparseProfile hk D profile) +
        divisionInternalCliqueCapacity (supercriticalAbsorbSparseDivision hk D) =
      m + supercriticalSparseAbsorptionExcess hk D t := by
  have hold : profileTotal profile + divisionInternalCliqueCapacity D + t = m := by
    exact_mod_cast hatShift.1
  rw [profileTotal_supercriticalAbsorbSparseProfile,
    divisionInternalCliqueCapacity_absorbSparse]
  unfold supercriticalSparseAbsorptionExcess
  omega

end InducedStars
