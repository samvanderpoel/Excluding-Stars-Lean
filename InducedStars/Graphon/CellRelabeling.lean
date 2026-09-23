import InducedStars.Graphon.Metric
import InducedStars.Graphon.Step
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.MeasureTheory.Group.MeasurableEquiv

/-!
# Relabeling equal-cell graphons

This file realizes permutations of a finite equal-cell partition by
measure-preserving measurable equivalences of the unit interval.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

/-- The `i`-th half-open equal cell, viewed as a subset of the real line. -/
def realEqualCell {q : ℕ} (i : Fin q) : Set ℝ :=
  Ico ((i : ℝ) / q) (((i : ℕ) + 1 : ℝ) / q)

@[measurability] theorem measurableSet_realEqualCell {q : ℕ} (i : Fin q) :
    MeasurableSet (realEqualCell i) :=
  measurableSet_Ico

/-- Distinct real equal cells are disjoint. -/
theorem realEqualCell_eq_of_mem {q : ℕ} {i j : Fin q} {x : ℝ}
    (hi : x ∈ realEqualCell i) (hj : x ∈ realEqualCell j) : i = j := by
  change (i : ℝ) / q ≤ x ∧ x < ((i : ℕ) + 1 : ℝ) / q at hi
  change (j : ℝ) / q ≤ x ∧ x < ((j : ℕ) + 1 : ℝ) / q at hj
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hs : ((i : ℕ) + 1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hd : (((i : ℕ) + 1 : ℝ) / q) ≤ (j : ℝ) / q :=
      div_le_div_of_nonneg_right hs hq
    exact (not_lt_of_ge hj.1) (hi.2.trans_le hd)
  · have hs : ((j : ℕ) + 1 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hji)
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hd : (((j : ℕ) + 1 : ℝ) / q) ≤ (i : ℝ) / q :=
      div_le_div_of_nonneg_right hs hq
    exact (not_lt_of_ge hi.1) (hj.2.trans_le hd)

/-- The union of all real equal cells. -/
def realEqualCellUnion (q : ℕ) : Set ℝ := ⋃ i : Fin q, realEqualCell i

@[measurability] theorem measurableSet_realEqualCellUnion (q : ℕ) :
    MeasurableSet (realEqualCellUnion q) := by
  exact MeasurableSet.iUnion fun i ↦ measurableSet_realEqualCell i

/-- Translation taking the `i`-th cell to the `σ i`-th cell. -/
def realCellShift {q : ℕ} (perm : Equiv.Perm (Fin q)) (i : Fin q) : ℝ :=
  ((perm i : ℕ) : ℝ) / q - (i : ℝ) / q

/-- The piecewise translation of `ℝ` which permutes equal cells by `σ` and is
the identity off their union. -/
def realCellPermFun {q : ℕ} (perm : Equiv.Perm (Fin q)) (x : ℝ) : ℝ :=
  (∑ i : Fin q,
      (realEqualCell i).indicator (fun y ↦ y + realCellShift perm i) x) +
    (realEqualCellUnion q)ᶜ.indicator id x

theorem realCellPermFun_of_mem {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) {x : ℝ} (hx : x ∈ realEqualCell i) :
    realCellPermFun perm x = x + realCellShift perm i := by
  classical
  have hxi (j : Fin q) : x ∈ realEqualCell j ↔ j = i := by
    constructor
    · intro hj
      exact realEqualCell_eq_of_mem hj hx
    · rintro rfl
      exact hx
  have hxU : x ∈ realEqualCellUnion q := Set.mem_iUnion.2 ⟨i, hx⟩
  unfold realCellPermFun
  rw [Finset.sum_eq_single i]
  · simp [hx, hxU]
  · intro j hj hji
    exact Set.indicator_of_notMem (fun h ↦ hji ((hxi j).mp h)) _
  · simp

theorem realCellPermFun_of_not_mem {q : ℕ} (perm : Equiv.Perm (Fin q))
    {x : ℝ} (hx : x ∉ realEqualCellUnion q) :
    realCellPermFun perm x = x := by
  classical
  have hxi (i : Fin q) : x ∉ realEqualCell i := by
    intro hi
    exact hx (Set.mem_iUnion.2 ⟨i, hi⟩)
  simp [realCellPermFun, hx, hxi]

theorem add_realCellShift_mem {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) {x : ℝ} (hx : x ∈ realEqualCell i) :
    x + realCellShift perm i ∈ realEqualCell (perm i) := by
  have hq : (q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  rcases hx with ⟨hx₀, hx₁⟩
  constructor <;>
    simp only [realCellShift] at hx₀ hx₁ ⊢
  · calc
      ((perm i : ℕ) : ℝ) / q = (i : ℝ) / q + realCellShift perm i := by
        simp only [realCellShift]
        ring
      _ ≤ x + realCellShift perm i := by
        simpa [add_comm] using add_le_add_right hx₀ (realCellShift perm i)
  · calc
      x + realCellShift perm i < (((i : ℕ) + 1 : ℝ) / q) + realCellShift perm i :=
        by simpa [add_comm] using add_lt_add_right hx₁ (realCellShift perm i)
      _ = (((perm i : ℕ) + 1 : ℝ) / q) := by
        simp only [realCellShift]
        field_simp
        ring

theorem realCellPermFun_mem {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) {x : ℝ} (hx : x ∈ realEqualCell i) :
    realCellPermFun perm x ∈ realEqualCell (perm i) := by
  rw [realCellPermFun_of_mem perm i hx]
  exact add_realCellShift_mem perm i hx

@[fun_prop] theorem measurable_realCellPermFun {q : ℕ} (perm : Equiv.Perm (Fin q)) :
    Measurable (realCellPermFun perm) := by
  classical
  unfold realCellPermFun
  apply Measurable.add
  · exact Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_id.add measurable_const).indicator (measurableSet_realEqualCell i)
  · exact measurable_id.indicator (measurableSet_realEqualCellUnion q).compl

@[simp] theorem realCellShift_symm_apply {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) :
    realCellShift perm.symm (perm i) = -realCellShift perm i := by
  simp only [realCellShift, Equiv.symm_apply_apply]
  ring

theorem realCellPermFun_leftInverse {q : ℕ} (perm : Equiv.Perm (Fin q)) :
    Function.LeftInverse (realCellPermFun perm.symm) (realCellPermFun perm) := by
  intro x
  by_cases hx : x ∈ realEqualCellUnion q
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    have himage : x + realCellShift perm i ∈ realEqualCell (perm i) :=
      add_realCellShift_mem perm i hi
    rw [realCellPermFun_of_mem perm i hi]
    rw [realCellPermFun_of_mem perm.symm (perm i) himage,
      realCellShift_symm_apply]
    ring
  · rw [realCellPermFun_of_not_mem perm hx,
      realCellPermFun_of_not_mem perm.symm hx]

theorem realCellPermFun_rightInverse {q : ℕ} (perm : Equiv.Perm (Fin q)) :
    Function.RightInverse (realCellPermFun perm.symm) (realCellPermFun perm) := by
  intro x
  simpa only [Equiv.symm_symm] using realCellPermFun_leftInverse perm.symm x

/-- The measurable equivalence of `ℝ` obtained by permuting equal cells. -/
def realCellPermMeasurableEquiv {q : ℕ} (perm : Equiv.Perm (Fin q)) : ℝ ≃ᵐ ℝ where
  toEquiv :=
    { toFun := realCellPermFun perm
      invFun := realCellPermFun perm.symm
      left_inv := realCellPermFun_leftInverse perm
      right_inv := realCellPermFun_rightInverse perm }
  measurable_toFun := measurable_realCellPermFun perm
  measurable_invFun := measurable_realCellPermFun perm.symm

@[simp] theorem realCellPermMeasurableEquiv_apply {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (x : ℝ) :
    realCellPermMeasurableEquiv perm x = realCellPermFun perm x :=
  rfl

theorem realCellPermFun_preimage_cell {q : ℕ} (perm : Equiv.Perm (Fin q))
    (j : Fin q) :
    realCellPermFun perm ⁻¹' realEqualCell j = realEqualCell (perm.symm j) := by
  ext x
  constructor
  · intro hx
    change realCellPermFun perm x ∈ realEqualCell j at hx
    by_cases hxU : x ∈ realEqualCellUnion q
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU
      have himage := realCellPermFun_mem perm i hi
      have hij : perm i = j := realEqualCell_eq_of_mem himage hx
      have hi' : i = perm.symm j := by
        rw [← hij]
        exact (perm.symm_apply_apply i).symm
      simpa [hi'] using hi
    · rw [realCellPermFun_of_not_mem perm hxU] at hx
      exact False.elim (hxU (Set.mem_iUnion.2 ⟨j, hx⟩))
  · intro hx
    have himage := realCellPermFun_mem perm (perm.symm j) hx
    simpa using himage

theorem realCellPermFun_preimage_union {q : ℕ} (perm : Equiv.Perm (Fin q)) :
    realCellPermFun perm ⁻¹' realEqualCellUnion q = realEqualCellUnion q := by
  ext x
  constructor
  · intro hx
    change realCellPermFun perm x ∈ realEqualCellUnion q at hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have hj' : x ∈ realEqualCell (perm.symm j) := by
      have hpre : x ∈ realCellPermFun perm ⁻¹' realEqualCell j := hj
      rwa [realCellPermFun_preimage_cell perm j] at hpre
    exact Set.mem_iUnion.2 ⟨perm.symm j, hj'⟩
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨perm i, realCellPermFun_mem perm i hi⟩

theorem add_realCellShift_mem_iff {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) (x : ℝ) :
    x + realCellShift perm i ∈ realEqualCell (perm i) ↔
      x ∈ realEqualCell i := by
  constructor
  · intro hx
    rcases hx with ⟨hx₀, hx₁⟩
    change (i : ℝ) / q ≤ x ∧ x < ((i : ℕ) + 1 : ℝ) / q
    have hleft : ((perm i : ℕ) : ℝ) / q =
        (i : ℝ) / q + realCellShift perm i := by
      simp only [realCellShift]
      ring
    have hright : (((perm i : ℕ) + 1 : ℝ) / q) =
        (((i : ℕ) + 1 : ℝ) / q) + realCellShift perm i := by
      have hq : (q : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
      simp only [realCellShift]
      field_simp
      ring
    constructor
    · rw [hleft] at hx₀
      exact (add_le_add_iff_right (realCellShift perm i)).mp hx₀
    · rw [hright] at hx₁
      exact (add_lt_add_iff_right (realCellShift perm i)).mp hx₁
  · exact add_realCellShift_mem perm i

theorem add_realCellShift_preimage {q : ℕ} (perm : Equiv.Perm (Fin q))
    (i : Fin q) :
    (fun x : ℝ ↦ x + realCellShift perm i) ⁻¹' realEqualCell (perm i) =
      realEqualCell i := by
  ext x
  exact add_realCellShift_mem_iff perm i x

/-- Translation carries restricted Lebesgue measure on one equal cell to the
restricted measure on its permuted cell. -/
theorem map_restrict_realEqualCell_add_shift {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (i : Fin q) :
    Measure.map (fun x : ℝ ↦ x + realCellShift perm i)
        (volume.restrict (realEqualCell i)) =
      volume.restrict (realEqualCell (perm i)) := by
  let trans : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (realCellShift perm i)
  have hrestrict := trans.restrict_map volume (realEqualCell (perm i))
  have hmap : Measure.map (fun x : ℝ ↦ x + realCellShift perm i) volume = volume :=
    map_add_right_eq_self volume (realCellShift perm i)
  change (Measure.map (fun x : ℝ ↦ x + realCellShift perm i) volume).restrict
      (realEqualCell (perm i)) =
    Measure.map (fun x : ℝ ↦ x + realCellShift perm i)
      (volume.restrict ((fun x : ℝ ↦ x + realCellShift perm i) ⁻¹'
        realEqualCell (perm i))) at hrestrict
  rw [hmap, add_realCellShift_preimage perm i] at hrestrict
  exact hrestrict.symm

/-- A finite measurable cover used to prove invariance of the piecewise map. -/
def realCellPermPiece (q : ℕ) : Option (Fin q) → Set ℝ
  | none => (realEqualCellUnion q)ᶜ
  | some i => realEqualCell i

theorem iUnion_realCellPermPiece (q : ℕ) :
    ⋃ o : Option (Fin q), realCellPermPiece q o = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  by_cases hx : x ∈ realEqualCellUnion q
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨some i, hi⟩
  · exact ⟨none, hx⟩

/-- The real equal-cell permutation preserves Lebesgue measure. -/
theorem measurePreserving_realCellPermMeasurableEquiv {q : ℕ}
    (perm : Equiv.Perm (Fin q)) :
    MeasurePreserving (realCellPermMeasurableEquiv perm) volume volume := by
  refine ⟨(realCellPermMeasurableEquiv perm).measurable, ?_⟩
  apply Measure.ext_of_iUnion_eq_univ (iUnion_realCellPermPiece q)
  intro o
  cases o with
  | some j =>
      rw [(realCellPermMeasurableEquiv perm).restrict_map]
      change Measure.map (realCellPermFun perm)
          (volume.restrict (realCellPermFun perm ⁻¹' realEqualCell j)) =
        volume.restrict (realEqualCell j)
      rw [realCellPermFun_preimage_cell perm j]
      calc
        Measure.map (realCellPermFun perm)
            (volume.restrict (realEqualCell (perm.symm j))) =
            Measure.map
              (fun x : ℝ ↦ x + realCellShift perm (perm.symm j))
              (volume.restrict (realEqualCell (perm.symm j))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem (measurableSet_realEqualCell (perm.symm j))]
            with x hx
          exact realCellPermFun_of_mem perm (perm.symm j) hx
        _ = volume.restrict (realEqualCell (perm (perm.symm j))) :=
          map_restrict_realEqualCell_add_shift perm (perm.symm j)
        _ = volume.restrict (realEqualCell j) := by simp
  | none =>
      rw [(realCellPermMeasurableEquiv perm).restrict_map]
      change Measure.map (realCellPermFun perm)
          (volume.restrict (realCellPermFun perm ⁻¹' (realEqualCellUnion q)ᶜ)) =
        volume.restrict (realEqualCellUnion q)ᶜ
      rw [preimage_compl, realCellPermFun_preimage_union]
      calc
        Measure.map (realCellPermFun perm)
            (volume.restrict (realEqualCellUnion q)ᶜ) =
            Measure.map id (volume.restrict (realEqualCellUnion q)ᶜ) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem (measurableSet_realEqualCellUnion q).compl]
            with x hx
          simpa using realCellPermFun_of_not_mem perm hx
        _ = volume.restrict (realEqualCellUnion q)ᶜ := Measure.map_id

theorem realEqualCell_subset_Icc {q : ℕ} (i : Fin q) :
    realEqualCell i ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨hx₀, hx₁⟩
  constructor
  · exact (by positivity : (0 : ℝ) ≤ (i : ℝ) / q).trans hx₀
  · exact hx₁.le.trans <| by
      apply (div_le_one (by exact_mod_cast (Nat.zero_lt_of_lt i.isLt))).2
      exact_mod_cast i.isLt

theorem realCellPermFun_mem_Icc {q : ℕ} (perm : Equiv.Perm (Fin q))
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    realCellPermFun perm x ∈ Icc (0 : ℝ) 1 := by
  by_cases hxU : x ∈ realEqualCellUnion q
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hxU
    exact realEqualCell_subset_Icc (perm i) (realCellPermFun_mem perm i hi)
  · simpa [realCellPermFun_of_not_mem perm hxU] using hx

theorem realCellPermFun_preimage_Icc {q : ℕ} (perm : Equiv.Perm (Fin q)) :
    realCellPermFun perm ⁻¹' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    have hback := realCellPermFun_mem_Icc perm.symm hx
    rw [realCellPermFun_leftInverse perm x] at hback
    exact hback
  · exact realCellPermFun_mem_Icc perm

theorem map_restrict_Icc_realCellPermFun {q : ℕ}
    (perm : Equiv.Perm (Fin q)) :
    Measure.map (realCellPermFun perm) (volume.restrict (Icc (0 : ℝ) 1)) =
      volume.restrict (Icc (0 : ℝ) 1) := by
  have hrestrict :=
    (realCellPermMeasurableEquiv perm).restrict_map volume (Icc (0 : ℝ) 1)
  change (Measure.map (realCellPermFun perm) volume).restrict (Icc (0 : ℝ) 1) =
    Measure.map (realCellPermFun perm)
      (volume.restrict (realCellPermFun perm ⁻¹' Icc (0 : ℝ) 1)) at hrestrict
  have hmap : Measure.map (realCellPermFun perm) volume = volume := by
    change Measure.map (⇑(realCellPermMeasurableEquiv perm)) volume = volume
    exact (measurePreserving_realCellPermMeasurableEquiv perm).map_eq
  rw [hmap, realCellPermFun_preimage_Icc perm] at hrestrict
  exact hrestrict.symm

/-- The measurable equivalence of the unit interval induced by a permutation of
its equal cells. -/
def unitCellPermMeasurableEquiv {q : ℕ}
    (perm : Equiv.Perm (Fin q)) : UnitInterval ≃ᵐ UnitInterval where
  toEquiv :=
    { toFun := fun x ↦ ⟨realCellPermFun perm x, realCellPermFun_mem_Icc perm x.property⟩
      invFun := fun x ↦
        ⟨realCellPermFun perm.symm x, realCellPermFun_mem_Icc perm.symm x.property⟩
      left_inv := fun x ↦ Subtype.ext (realCellPermFun_leftInverse perm x)
      right_inv := fun x ↦ Subtype.ext (realCellPermFun_rightInverse perm x) }
  measurable_toFun := by
    change Measurable (fun x : UnitInterval ↦
      (⟨realCellPermFun perm x, realCellPermFun_mem_Icc perm x.property⟩ : UnitInterval))
    exact ((measurable_realCellPermFun perm).comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    change Measurable (fun x : UnitInterval ↦
      (⟨realCellPermFun perm.symm x,
        realCellPermFun_mem_Icc perm.symm x.property⟩ : UnitInterval))
    exact ((measurable_realCellPermFun perm.symm).comp measurable_subtype_coe).subtype_mk

@[simp] theorem coe_unitCellPermMeasurableEquiv_apply {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (x : UnitInterval) :
    ((unitCellPermMeasurableEquiv perm x : UnitInterval) : ℝ) =
      realCellPermFun perm x :=
  rfl

/-- The unit-interval equal-cell permutation preserves normalized volume. -/
theorem measurePreserving_unitCellPermMeasurableEquiv {q : ℕ}
    (perm : Equiv.Perm (Fin q)) :
    MeasurePreserving (unitCellPermMeasurableEquiv perm) volume volume := by
  refine ⟨(unitCellPermMeasurableEquiv perm).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe
      (unitCellPermMeasurableEquiv perm).measurable]
  change Measure.map (realCellPermFun perm ∘ ((↑) : UnitInterval → ℝ)) volume =
    Measure.map ((↑) : UnitInterval → ℝ) volume
  rw [← Measure.map_map (measurable_realCellPermFun perm) measurable_subtype_coe,
    unitInterval.measurePreserving_coe.map_eq,
    map_restrict_Icc_realCellPermFun]

/-- A graphon relabeling which permutes the canonical equal cells. -/
def cellPermRelabeling {q : ℕ} (perm : Equiv.Perm (Fin q)) : GraphonRelabeling where
  toMeasurableEquiv := unitCellPermMeasurableEquiv perm
  measurePreserving := measurePreserving_unitCellPermMeasurableEquiv perm

@[simp] theorem coe_cellPermRelabeling_apply {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (x : UnitInterval) :
    ((cellPermRelabeling perm x : UnitInterval) : ℝ) = realCellPermFun perm x :=
  rfl

theorem mem_equalCell_iff_mem_realEqualCell {q : ℕ} (i : Fin q)
    (x : UnitInterval) :
    x ∈ equalCell i ↔ (x : ℝ) ∈ realEqualCell i := by
  rfl

/-- Exact action of `cellPermRelabeling` on every half-open equal cell. -/
theorem cellPermRelabeling_mem_equalCell_iff {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (i : Fin q) (x : UnitInterval) :
    cellPermRelabeling perm x ∈ equalCell (perm i) ↔ x ∈ equalCell i := by
  rw [mem_equalCell_iff_mem_realEqualCell,
    mem_equalCell_iff_mem_realEqualCell]
  change realCellPermFun perm x ∈ realEqualCell (perm i) ↔
    (x : ℝ) ∈ realEqualCell i
  have hpre := realCellPermFun_preimage_cell perm (perm i)
  have hx : (x : ℝ) ∈ realCellPermFun perm ⁻¹' realEqualCell (perm i) ↔
      (x : ℝ) ∈ realEqualCell (perm.symm (perm i)) := by
    rw [hpre]
  simpa using hx

theorem cellPermRelabeling_mapsTo_equalCell {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (i : Fin q) :
    MapsTo (cellPermRelabeling perm) (equalCell i) (equalCell (perm i)) := by
  intro x hx
  exact (cellPermRelabeling_mem_equalCell_iff perm i x).2 hx

/-- Every point strictly below `1` belongs to a unique equal cell. -/
theorem exists_mem_equalCell_lt_one {q : ℕ} (hq : 0 < q) (x : UnitInterval)
    (hx : (x : ℝ) < 1) :
    ∃ i : Fin q, x ∈ equalCell i := by
  let a : ℝ := (q : ℝ) * (x : ℝ)
  have ha_nonneg : 0 ≤ a := mul_nonneg (Nat.cast_nonneg q) x.2.1
  have ha_lt : a < q := by
    dsimp [a]
    nlinarith [show (0 : ℝ) < q by exact_mod_cast hq]
  have hi_lt : ⌊a⌋₊ < q := (Nat.floor_lt ha_nonneg).2 (by exact_mod_cast ha_lt)
  let i : Fin q := ⟨⌊a⌋₊, hi_lt⟩
  refine ⟨i, ?_⟩
  simp only [equalCell, Set.mem_Ico]
  have hq_real : (0 : ℝ) < q := by exact_mod_cast hq
  constructor
  · apply Subtype.coe_le_coe.mp
    change ((i : ℕ) : ℝ) / q ≤ (x : ℝ)
    rw [div_le_iff₀ hq_real]
    simpa [i, a, mul_comm] using Nat.floor_le ha_nonneg
  · apply Subtype.coe_lt_coe.mp
    simp only [equalCellRight]
    rw [lt_div_iff₀ hq_real]
    simpa [i, a, mul_comm] using Nat.lt_floor_add_one a

theorem ae_exists_mem_equalCell {q : ℕ} (hq : 0 < q) :
    ∀ᵐ x : UnitInterval ∂volume, ∃ i : Fin q, x ∈ equalCell i := by
  filter_upwards [Measure.ae_ne (volume : Measure UnitInterval) (1 : UnitInterval)]
    with x hx
  apply exists_mem_equalCell_lt_one hq x
  apply lt_of_le_of_ne x.2.2
  intro heq
  apply hx
  exact Subtype.ext heq

/-- Reindex both coordinates of a square matrix by a permutation. -/
def permuteMatrix {q : ℕ} (perm : Equiv.Perm (Fin q))
    (M : Matrix (Fin q) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  M.submatrix perm perm

theorem permuteMatrix_isSymm {q : ℕ} (perm : Equiv.Perm (Fin q))
    {M : Matrix (Fin q) (Fin q) ℝ} (hM : M.IsSymm) :
    (permuteMatrix perm M).IsSymm :=
  hM.submatrix perm

theorem permuteMatrix_nonneg {q : ℕ} (perm : Equiv.Perm (Fin q))
    {M : Matrix (Fin q) (Fin q) ℝ} (h₀ : ∀ i j, 0 ≤ M i j) :
    ∀ i j, 0 ≤ permuteMatrix perm M i j := by
  intro i j
  exact h₀ (perm i) (perm j)

theorem permuteMatrix_le_one {q : ℕ} (perm : Equiv.Perm (Fin q))
    {M : Matrix (Fin q) (Fin q) ℝ} (h₁ : ∀ i j, M i j ≤ 1) :
    ∀ i j, permuteMatrix perm M i j ≤ 1 := by
  intro i j
  exact h₁ (perm i) (perm j)

/-- Reindexing a finite matrix is exactly equal-cell graphon relabeling. -/
theorem matrixGraphon_permuteMatrix_eq_relabel {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) :
    matrixGraphon (permuteMatrix perm M) (permuteMatrix_isSymm perm hM)
        (permuteMatrix_nonneg perm h₀) (permuteMatrix_le_one perm h₁) =
      (matrixGraphon M hM h₀ h₁).relabel (cellPermRelabeling perm) := by
  by_cases hq : 0 < q
  · let W := matrixGraphon M hM h₀ h₁
    let Wp := matrixGraphon (permuteMatrix perm M) (permuteMatrix_isSymm perm hM)
      (permuteMatrix_nonneg perm h₀) (permuteMatrix_le_one perm h₁)
    apply Graphon.ext
    have hleft := matrixGraphon_ae_eq_kernel (permuteMatrix perm M)
      (permuteMatrix_isSymm perm hM) (permuteMatrix_nonneg perm h₀)
      (permuteMatrix_le_one perm h₁)
    have hrel := W.relabel_ae_eq_value (cellPermRelabeling perm)
    have hvalue := (cellPermRelabeling perm).measurePreserving_prodEquiv.quasiMeasurePreserving.ae
      W.value_ae_eq
    have hkernel := (cellPermRelabeling perm).measurePreserving_prodEquiv.quasiMeasurePreserving.ae
      (matrixGraphon_ae_eq_kernel M hM h₀ h₁)
    have hcover₁ : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
        ∃ i : Fin q, z.1 ∈ equalCell i := by
      exact (measurePreserving_fst (μ := (volume : Measure UnitInterval))
        (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae
          (ae_exists_mem_equalCell hq)
    have hcover₂ : ∀ᵐ z : UnitSquare ∂unitSquareMeasure,
        ∃ j : Fin q, z.2 ∈ equalCell j := by
      exact (measurePreserving_snd (μ := (volume : Measure UnitInterval))
        (ν := (volume : Measure UnitInterval))).quasiMeasurePreserving.ae
          (ae_exists_mem_equalCell hq)
    filter_upwards [hleft, hrel, hvalue, hkernel, hcover₁, hcover₂]
      with z hzleft hzrel hzvalue hzkernel hz₁ hz₂
    obtain ⟨i, hi⟩ := hz₁
    obtain ⟨j, hj⟩ := hz₂
    have hi' : cellPermRelabeling perm z.1 ∈ equalCell (perm i) :=
      (cellPermRelabeling_mem_equalCell_iff perm i z.1).2 hi
    have hj' : cellPermRelabeling perm z.2 ∈ equalCell (perm j) :=
      (cellPermRelabeling_mem_equalCell_iff perm j z.2).2 hj
    rw [hzleft, matrixKernel_of_mem (permuteMatrix perm M) i j z hi hj]
    rw [hzrel]
    change M (perm i) (perm j) =
      W.value (cellPermRelabeling perm z.1, cellPermRelabeling perm z.2)
    have hzvalue' :
        W.value (cellPermRelabeling perm z.1, cellPermRelabeling perm z.2) =
          W (cellPermRelabeling perm z.1, cellPermRelabeling perm z.2) := by
      simpa using hzvalue
    have hzkernel' :
        W (cellPermRelabeling perm z.1, cellPermRelabeling perm z.2) =
          matrixKernel M (cellPermRelabeling perm z.1,
            cellPermRelabeling perm z.2) := by
      simpa [W] using hzkernel
    rw [hzvalue', hzkernel',
      matrixKernel_of_mem M (perm i) (perm j)
        (cellPermRelabeling perm z.1, cellPermRelabeling perm z.2) hi' hj']
  · have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
    subst q
    have he : cellPermRelabeling perm = GraphonRelabeling.refl := by
      apply GraphonRelabeling.ext
      apply MeasurableEquiv.ext
      funext x
      apply Subtype.ext
      simp [cellPermRelabeling, unitCellPermMeasurableEquiv,
        realCellPermFun, realEqualCellUnion]
    have hleft_eq :
        matrixGraphon (permuteMatrix perm M) (permuteMatrix_isSymm perm hM)
            (permuteMatrix_nonneg perm h₀) (permuteMatrix_le_one perm h₁) =
          matrixGraphon M hM h₀ h₁ := by
      apply Graphon.ext
      filter_upwards [matrixGraphon_ae_eq_kernel (permuteMatrix perm M)
          (permuteMatrix_isSymm perm hM) (permuteMatrix_nonneg perm h₀)
          (permuteMatrix_le_one perm h₁),
        matrixGraphon_ae_eq_kernel M hM h₀ h₁] with z hz₁ hz₂
      rw [hz₁, hz₂]
      simp [matrixKernel]
    rw [hleft_eq, he, Graphon.relabel_refl]

/-- Reindexing a bounded symmetric matrix does not change its graphon up to cut distance. -/
theorem cutDist_matrixGraphon_permuteMatrix_eq_zero {q : ℕ}
    (perm : Equiv.Perm (Fin q)) (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) :
    cutDist
        (matrixGraphon (permuteMatrix perm M) (permuteMatrix_isSymm perm hM)
          (permuteMatrix_nonneg perm h₀) (permuteMatrix_le_one perm h₁))
        (matrixGraphon M hM h₀ h₁) = 0 := by
  calc
    cutDist
        (matrixGraphon (permuteMatrix perm M) (permuteMatrix_isSymm perm hM)
          (permuteMatrix_nonneg perm h₀) (permuteMatrix_le_one perm h₁))
        (matrixGraphon M hM h₀ h₁) =
        cutDist ((matrixGraphon M hM h₀ h₁).relabel (cellPermRelabeling perm))
          (matrixGraphon M hM h₀ h₁) := congrArg
            (fun W ↦ cutDist W (matrixGraphon M hM h₀ h₁))
            (matrixGraphon_permuteMatrix_eq_relabel perm M hM h₀ h₁)
    _ = 0 := cutDist_relabel_self _ _

theorem graphAdjacencyMatrix_comap_perm {n : ℕ}
    (perm : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    graphAdjacencyMatrix (G.comap perm) =
      permuteMatrix perm (graphAdjacencyMatrix G) := by
  classical
  ext i j
  simp [graphAdjacencyMatrix, permuteMatrix]

/-- Pulling a finite graph back by a vertex permutation is equal-cell graphon
relabeling. -/
theorem graphGraphon_comap_perm_eq_relabel {n : ℕ}
    (perm : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    graphGraphon (G.comap perm) =
      (graphGraphon G).relabel (cellPermRelabeling perm) := by
  simpa only [graphGraphon, graphAdjacencyMatrix_comap_perm] using
    matrixGraphon_permuteMatrix_eq_relabel perm (graphAdjacencyMatrix G)
      (graphAdjacencyMatrix_isSymm G) (graphAdjacencyMatrix_nonneg G)
      (graphAdjacencyMatrix_le_one G)

/-- Pulling back a finite graph by a vertex permutation has cut distance zero
from the original adjacency graphon. -/
theorem cutDist_graphGraphon_comap_perm_eq_zero {n : ℕ}
    (perm : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    cutDist (graphGraphon (G.comap perm)) (graphGraphon G) = 0 := by
  rw [graphGraphon_comap_perm_eq_relabel, cutDist_relabel_self]

/-- Isomorphic finite graphs on `Fin n` have adjacency graphons at cut distance zero. -/
theorem cutDist_graphGraphon_eq_zero_of_iso {n : ℕ}
    {G H : SimpleGraph (Fin n)} (e : G ≃g H) :
    cutDist (graphGraphon G) (graphGraphon H) = 0 := by
  have hGH : G = H.comap e.toEquiv := by
    ext i j
    simp only [SimpleGraph.comap_adj]
    exact e.map_rel_iff.symm
  rw [hGH, graphGraphon_comap_perm_eq_relabel, cutDist_relabel_self]

end InducedStars
