import InducedStars.Structure.Supercritical.SparseAbsorption
import InducedStars.Structure.Supercritical.ProfileReindexing
import DenseGraph.Combinatorics.BinomialCapacity
import Mathlib.Tactic

/-!
# Cross-profile multiplicity under sparse absorption

Absorbing the sparse set into one main part enlarges precisely the cross
cells incident with that part.  This file compares the old and enlarged
binomial products, retaining the exact exponential gain supplied by those
incident coordinates.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Incident coordinates -/

/-- The total profile count in cells incident with the part selected for
sparse absorption.  Indexing by the *other* endpoint makes explicit that
every other main part is counted exactly once. -/
def supercriticalIncidentProfileCount
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) : ℕ :=
  ∑ j : {j : Fin (k - 1) //
      j ≠ supercriticalSmallestPartIndex hk D},
    profile.count
      (SupercriticalPartPair.ofDistinct
        (supercriticalSmallestPartIndex hk D) j
        j.property.symm)

/-- A cross-cell is incident with the part selected for sparse absorption. -/
def supercriticalPartPairIncident
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) : Prop :=
  e.left = supercriticalSmallestPartIndex hk D ∨
    e.right = supercriticalSmallestPartIndex hk D

instance supercriticalPartPairIncidentDecidable
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) :
    Decidable (supercriticalPartPairIncident hk D e) := by
  unfold supercriticalPartPairIncident
  infer_instance

private def supercriticalOtherPartToIncidentPair
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    {j : Fin (k - 1) // j ≠ supercriticalSmallestPartIndex hk D} →
      {e : SupercriticalPartPair k // supercriticalPartPairIncident hk D e} :=
  fun j ↦ ⟨SupercriticalPartPair.ofDistinct
      (supercriticalSmallestPartIndex hk D) j j.property.symm, by
    unfold supercriticalPartPairIncident
    unfold SupercriticalPartPair.ofDistinct
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr rfl⟩

private theorem supercriticalOtherPartToIncidentPair_injective
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    Function.Injective (supercriticalOtherPartToIncidentPair hk D) := by
  intro i j hij
  apply Subtype.ext
  have hpairs := congrArg
    (fun e : {e : SupercriticalPartPair k //
        supercriticalPartPairIncident hk D e} ↦ e.1.toSym2) hij
  simp only [supercriticalOtherPartToIncidentPair,
    SupercriticalPartPair.ofDistinct_toSym2] at hpairs
  rw [Sym2.eq_iff] at hpairs
  rcases hpairs with h | h
  · exact h.2
  · exact (i.property h.2).elim

private theorem supercriticalOtherPartToIncidentPair_surjective
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    Function.Surjective (supercriticalOtherPartToIncidentPair hk D) := by
  rintro ⟨e, he⟩
  change e.left = supercriticalSmallestPartIndex hk D ∨
    e.right = supercriticalSmallestPartIndex hk D at he
  rcases he with hl | hr
  · let j : {j : Fin (k - 1) //
        j ≠ supercriticalSmallestPartIndex hk D} :=
      ⟨e.right, fun h ↦ e.left_ne_right (hl.trans h.symm)⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change SupercriticalPartPair.ofDistinct
      (supercriticalSmallestPartIndex hk D) e.right
        (fun h ↦ e.left_ne_right (hl.trans h)) = e
    apply SupercriticalPartPair.toSym2_injective
    rw [SupercriticalPartPair.ofDistinct_toSym2]
    simp only [SupercriticalPartPair.toSym2, hl]
  · let j : {j : Fin (k - 1) //
        j ≠ supercriticalSmallestPartIndex hk D} :=
      ⟨e.left, fun h ↦ e.right_ne_left (hr.trans h.symm)⟩
    refine ⟨j, ?_⟩
    apply Subtype.ext
    change SupercriticalPartPair.ofDistinct
      (supercriticalSmallestPartIndex hk D) e.left
        (fun h ↦ e.right_ne_left (hr.trans h)) = e
    apply SupercriticalPartPair.toSym2_injective
    rw [SupercriticalPartPair.ofDistinct_toSym2]
    simp only [SupercriticalPartPair.toSym2, hr]
    exact Sym2.eq_swap

private noncomputable def supercriticalOtherPartIncidentEquiv
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    {j : Fin (k - 1) // j ≠ supercriticalSmallestPartIndex hk D} ≃
      {e : SupercriticalPartPair k // supercriticalPartPairIncident hk D e} :=
  Equiv.ofBijective (supercriticalOtherPartToIncidentPair hk D)
    ⟨supercriticalOtherPartToIncidentPair_injective hk D,
      supercriticalOtherPartToIncidentPair_surjective hk D⟩

/-- Summing over incident pair coordinates agrees with the explicit sum over
all other part labels. -/
theorem sum_profileCount_of_incident_eq
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) :
    (∑ e : SupercriticalPartPair k,
        if supercriticalPartPairIncident hk D e then profile.count e else 0) =
      supercriticalIncidentProfileCount hk D profile := by
  classical
  let E := supercriticalOtherPartIncidentEquiv hk D
  have hsubtype :
      (∑ e : SupercriticalPartPair k,
          if supercriticalPartPairIncident hk D e then profile.count e else 0) =
        ∑ e : {e : SupercriticalPartPair k //
          supercriticalPartPairIncident hk D e}, profile.count e := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij
        (fun e he ↦ ⟨e, (Finset.mem_filter.mp he).2⟩)
    · intro e he
      simp
    · intro e he f hf hef
      exact congrArg Subtype.val hef
    · intro e he
      refine ⟨e.1, ?_, ?_⟩
      · simp [e.2]
      · exact Subtype.ext rfl
    · intro e he
      rfl
  calc
    (∑ e : SupercriticalPartPair k,
        if supercriticalPartPairIncident hk D e then profile.count e else 0) =
        ∑ e : {e : SupercriticalPartPair k //
          supercriticalPartPairIncident hk D e}, profile.count e := hsubtype
    _ = ∑ j : {j : Fin (k - 1) //
          j ≠ supercriticalSmallestPartIndex hk D},
        profile.count
          (SupercriticalPartPair.ofDistinct
            (supercriticalSmallestPartIndex hk D) j j.property.symm) := by
      symm
      apply Fintype.sum_equiv E
      intro j
      rfl
    _ = supercriticalIncidentProfileCount hk D profile := rfl

/-! ## Coordinate and product comparisons -/

private theorem nat_absorption_ratio
    (m a s b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (m : ℝ) * (s * b : ℕ) / (a * b + s * b : ℕ) =
      ((s : ℝ) / (a + s : ℕ)) * (m : ℝ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  push_cast
  field_simp

private theorem choose_coordinate_le_absorbed_mul_exp
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k) :
    ((crossEdgeCapacity D e).choose (profile.count e) : ℝ) ≤
      ((crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e).choose
          ((supercriticalAbsorbSparseProfile hk D profile).count e) : ℝ) *
        Real.exp (-(if supercriticalPartPairIncident hk D e then
          ((D.sparse.card : ℝ) /
            ((D.parts (supercriticalSmallestPartIndex hk D)).card +
              D.sparse.card : ℕ)) * (profile.count e : ℝ)
        else 0)) := by
  classical
  let iStar := supercriticalSmallestPartIndex hk D
  by_cases hl : e.left = iStar
  · have hr : e.right ≠ iStar := by
      exact fun h ↦ e.left_ne_right (hl.trans h.symm)
    have hcap :
        crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e =
          crossEdgeCapacity D e +
            D.sparse.card * (D.parts e.right).card :=
      crossEdgeCapacity_absorbSparse_of_incident hk D e e.right (Or.inl ⟨hl, rfl⟩)
    have hbase := DenseGraph.choose_le_choose_add_mul_exp_neg
      (N := crossEdgeCapacity D e)
      (Q := D.sparse.card * (D.parts e.right).card)
      (m := profile.count e) (profile.count_le_capacity e)
      (Nat.add_pos_left (crossEdgeCapacity_pos D e) _)
    have hratio :
        (profile.count e : ℝ) *
              (D.sparse.card * (D.parts e.right).card : ℕ) /
            (crossEdgeCapacity D e +
              D.sparse.card * (D.parts e.right).card : ℕ) =
          ((D.sparse.card : ℝ) /
            ((D.parts iStar).card + D.sparse.card : ℕ)) *
              (profile.count e : ℝ) := by
      rw [crossEdgeCapacity, hl]
      exact nat_absorption_ratio _ _ _ _
        (D.parts_nonempty iStar).card_pos
        (D.parts_nonempty e.right).card_pos
    push_cast at hratio
    rw [hcap, supercriticalAbsorbSparseProfile_count]
    simp only [supercriticalPartPairIncident, iStar, hl, true_or, ite_true]
    push_cast at hbase ⊢
    rw [← hratio]
    exact hbase
  · by_cases hr : e.right = iStar
    · have hcap :
          crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e =
            crossEdgeCapacity D e +
              D.sparse.card * (D.parts e.left).card :=
        crossEdgeCapacity_absorbSparse_of_incident hk D e e.left (Or.inr ⟨hr, rfl⟩)
      have hbase := DenseGraph.choose_le_choose_add_mul_exp_neg
        (N := crossEdgeCapacity D e)
        (Q := D.sparse.card * (D.parts e.left).card)
        (m := profile.count e) (profile.count_le_capacity e)
        (Nat.add_pos_left (crossEdgeCapacity_pos D e) _)
      have hratio :
          (profile.count e : ℝ) *
                (D.sparse.card * (D.parts e.left).card : ℕ) /
              (crossEdgeCapacity D e +
                D.sparse.card * (D.parts e.left).card : ℕ) =
            ((D.sparse.card : ℝ) /
              ((D.parts iStar).card + D.sparse.card : ℕ)) *
                (profile.count e : ℝ) := by
        rw [crossEdgeCapacity, hr,
          Nat.mul_comm (D.parts e.left).card (D.parts iStar).card]
        exact nat_absorption_ratio _ _ _ _
          (D.parts_nonempty iStar).card_pos
          (D.parts_nonempty e.left).card_pos
      push_cast at hratio
      rw [hcap, supercriticalAbsorbSparseProfile_count]
      simp only [supercriticalPartPairIncident, iStar, hl, hr, false_or, ite_true]
      push_cast at hbase ⊢
      rw [← hratio]
      exact hbase
    · have hcap :=
        crossEdgeCapacity_absorbSparse_of_not_incident hk D e hl hr
      simp [supercriticalPartPairIncident, iStar, hl, hr, hcap]

/-- Exact multiplicity gain from enlarging every cross cell incident with the
absorbed part.  All nonincident coordinate factors are unchanged. -/
theorem supercriticalProfileMultiplicity_le_absorbed_mul_exp
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (profile : SupercriticalEdgeProfile D) :
    (supercriticalProfileMultiplicity profile : ℝ) ≤
      (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (-((D.sparse.card : ℝ) /
            ((D.parts (supercriticalSmallestPartIndex hk D)).card +
              D.sparse.card : ℕ)) *
          (supercriticalIncidentProfileCount hk D profile : ℝ)) := by
  classical
  let r : ℝ := (D.sparse.card : ℝ) /
    ((D.parts (supercriticalSmallestPartIndex hk D)).card +
      D.sparse.card : ℕ)
  calc
    (supercriticalProfileMultiplicity profile : ℝ) =
        ∏ e : SupercriticalPartPair k,
          ((crossEdgeCapacity D e).choose (profile.count e) : ℝ) := by
      simp [supercriticalProfileMultiplicity]
    _ ≤ ∏ e : SupercriticalPartPair k,
        (((crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e).choose
            ((supercriticalAbsorbSparseProfile hk D profile).count e) : ℝ) *
          Real.exp (-(if supercriticalPartPairIncident hk D e then
            r * (profile.count e : ℝ) else 0))) := by
      apply Finset.prod_le_prod
      · intro e _
        positivity
      · intro e _
        simpa [r] using choose_coordinate_le_absorbed_mul_exp hk D profile e
    _ = (∏ e : SupercriticalPartPair k,
          ((crossEdgeCapacity (supercriticalAbsorbSparseDivision hk D) e).choose
            ((supercriticalAbsorbSparseProfile hk D profile).count e) : ℝ)) *
        (∏ e : SupercriticalPartPair k,
          Real.exp (-(if supercriticalPartPairIncident hk D e then
            r * (profile.count e : ℝ) else 0))) := by
      rw [Finset.prod_mul_distrib]
    _ = (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (∑ e : SupercriticalPartPair k,
          -(if supercriticalPartPairIncident hk D e then
            r * (profile.count e : ℝ) else 0)) := by
      rw [← Real.exp_sum]
      simp [supercriticalProfileMultiplicity]
    _ = (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (-r * (supercriticalIncidentProfileCount hk D profile : ℝ)) := by
      congr 2
      have hsum :
        (∑ e : SupercriticalPartPair k,
            if supercriticalPartPairIncident hk D e then
              r * (profile.count e : ℝ) else 0) =
            r * (supercriticalIncidentProfileCount hk D profile : ℝ) := by
        calc
          (∑ e : SupercriticalPartPair k,
              if supercriticalPartPairIncident hk D e then
                r * (profile.count e : ℝ) else 0) =
            r * ∑ e : SupercriticalPartPair k,
              if supercriticalPartPairIncident hk D e then
                (profile.count e : ℝ) else 0 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            split_ifs <;> simp
          _ = r * (supercriticalIncidentProfileCount hk D profile : ℝ) := by
            congr 1
            exact_mod_cast sum_profileCount_of_incident_eq hk D profile
      calc
        (∑ e : SupercriticalPartPair k,
            -(if supercriticalPartPairIncident hk D e then
              r * (profile.count e : ℝ) else 0)) =
            -(∑ e : SupercriticalPartPair k,
              if supercriticalPartPairIncident hk D e then
                r * (profile.count e : ℝ) else 0) := by
          rw [Finset.sum_neg_distrib]
        _ = -(r * (supercriticalIncidentProfileCount hk D profile : ℝ)) := by
          rw [hsum]
        _ = -r * (supercriticalIncidentProfileCount hk D profile : ℝ) := by
          ring
    _ = (supercriticalProfileMultiplicity
          (supercriticalAbsorbSparseProfile hk D profile) : ℝ) *
        Real.exp (-((D.sparse.card : ℝ) /
            ((D.parts (supercriticalSmallestPartIndex hk D)).card +
              D.sparse.card : ℕ)) *
          (supercriticalIncidentProfileCount hk D profile : ℝ)) := by
      rfl

end InducedStars
