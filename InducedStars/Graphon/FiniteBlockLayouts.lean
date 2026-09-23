import InducedStars.Graphon.BlockTail
import InducedStars.Graphon.CellRelabeling
import Mathlib.Order.Interval.Set.Union
import Mathlib.Tactic

/-!
# Auxiliary finite profile-block layouts

Unlike `AdmissibleBlockSequence`, these analytic layouts permit zero blocks
and need not be sorted.  They are used only while truncating, permuting, and
passing to limits; the candidate family continues to use the stricter
sequence structure.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology unitInterval symmDiff

namespace InducedStars

/-- A finite, possibly empty and arbitrarily ordered family of profile
blocks. -/
structure FiniteProfileBlockLayout (k : ℕ) where
  count : ℕ
  alpha : Fin count → ℝ
  core : Fin count → RegularBlockCore k
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  sum_alpha_le_one : ∑ i, alpha i ≤ 1

/-- An admissible finite vector of block lengths.  Separating lengths from
cores makes fixed-core continuity statements definitionally transparent. -/
structure FiniteProfileBlockLengths (q : ℕ) where
  alpha : Fin q → ℝ
  alpha_nonneg : ∀ i, 0 ≤ alpha i
  sum_alpha_le_one : ∑ i, alpha i ≤ 1

namespace FiniteProfileBlockLengths

variable {q k : ℕ}

/-- Attach a fixed finite list of regular cores to a length vector. -/
def layout (a : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) : FiniteProfileBlockLayout k where
  count := q
  alpha := a.alpha
  core := C
  alpha_nonneg := a.alpha_nonneg
  sum_alpha_le_one := a.sum_alpha_le_one

@[simp] theorem layout_count (a : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) : (a.layout C).count = q := rfl

@[simp] theorem layout_alpha (a : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) (i : Fin q) :
    (a.layout C).alpha i = a.alpha i := rfl

@[simp] theorem layout_core (a : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) (i : Fin q) :
    (a.layout C).core i = C i := rfl

end FiniteProfileBlockLengths

namespace FiniteProfileBlockLayout

variable {k : ℕ} (A : FiniteProfileBlockLayout k)

/-- Moving the two endpoints of a half-open interval changes it only near
those endpoints. -/
theorem Ico_symmDiff_subset_uIcc_union (a b c d : UnitInterval) :
    Ico a b ∆ Ico c d ⊆ uIcc a c ∪ uIcc b d := by
  intro x hx
  rw [Set.mem_symmDiff] at hx
  rcases hx with ⟨hxab, hxcd⟩ | ⟨hxcd, hxab⟩
  · by_cases hcx : c ≤ x
    · right
      have hdx : d ≤ x := by
        by_contra h
        exact hxcd ⟨hcx, lt_of_not_ge h⟩
      exact Set.mem_uIcc_of_ge hdx hxab.2.le
    · left
      exact Set.mem_uIcc_of_le hxab.1 (le_of_not_ge hcx)
  · by_cases hax : a ≤ x
    · right
      have hbx : b ≤ x := by
        by_contra h
        exact hxab ⟨hax, lt_of_not_ge h⟩
      exact Set.mem_uIcc_of_le hbx hxcd.2.le
    · left
      exact Set.mem_uIcc_of_ge hxcd.1 (le_of_not_ge hax)

/-- Real-measure bound for two half-open unit intervals with moving
endpoints. -/
theorem measureReal_Ico_symmDiff_le (a b c d : UnitInterval) :
    volume.real (Ico a b ∆ Ico c d) ≤
      |(a : ℝ) - c| + |(b : ℝ) - d| := by
  calc
    volume.real (Ico a b ∆ Ico c d) ≤
        volume.real (uIcc a c ∪ uIcc b d) :=
      measureReal_mono (Ico_symmDiff_subset_uIcc_union a b c d)
    _ ≤ volume.real (uIcc a c) + volume.real (uIcc b d) :=
      measureReal_union_le _ _
    _ = |(a : ℝ) - c| + |(b : ℝ) - d| := by
      simp [Measure.real, edist_dist, Subtype.dist_eq, Real.dist_eq,
        abs_sub_comm]

/-- Extend the finite length vector by zero. -/
def alphaNat (i : ℕ) : ℝ :=
  if hi : i < A.count then A.alpha ⟨i, hi⟩ else 0

@[simp] theorem alphaNat_of_lt {i : ℕ} (hi : i < A.count) :
    A.alphaNat i = A.alpha ⟨i, hi⟩ := by
  simp [alphaNat, hi]

theorem alphaNat_nonneg (i : ℕ) : 0 ≤ A.alphaNat i := by
  unfold alphaNat
  split_ifs with hi
  · exact A.alpha_nonneg _
  · exact le_rfl

/-- Prefix sum before natural-number position `i`. -/
def blockStart (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, A.alphaNat j

def blockEnd (i : Fin A.count) : ℝ :=
  A.blockStart i + A.alpha i

@[simp] theorem blockStart_zero : A.blockStart 0 = 0 := by
  simp [blockStart]

theorem blockStart_succ (i : Fin A.count) :
    A.blockStart (i + 1) = A.blockEnd i := by
  simp [blockStart, blockEnd, Finset.sum_range_succ, A.alphaNat_of_lt i.isLt]

theorem blockStart_nonneg (i : ℕ) : 0 ≤ A.blockStart i := by
  exact Finset.sum_nonneg fun j _ ↦ A.alphaNat_nonneg j

theorem blockStart_mono : Monotone A.blockStart := by
  intro i j hij
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hij
  · intro n _ _
    exact A.alphaNat_nonneg n

theorem blockStart_count_eq_sum :
    A.blockStart A.count = ∑ i, A.alpha i := by
  rw [blockStart]
  apply Finset.sum_bij
      (fun j hj ↦ (⟨j, Finset.mem_range.mp hj⟩ : Fin A.count))
  · simp
  · intro a ha b hb hab
    exact congrArg Fin.val hab
  · intro i hi
    exact ⟨i, Finset.mem_range.mpr i.isLt, by simp⟩
  · intro j hj
    rw [A.alphaNat_of_lt (Finset.mem_range.mp hj)]

theorem blockStart_count_le_one : A.blockStart A.count ≤ 1 := by
  rw [A.blockStart_count_eq_sum]
  exact A.sum_alpha_le_one

theorem alpha_le_one (i : Fin A.count) : A.alpha i ≤ 1 := by
  calc
    A.alpha i ≤ ∑ j, A.alpha j :=
      Finset.single_le_sum (fun j _ ↦ A.alpha_nonneg j) (Finset.mem_univ i)
    _ ≤ 1 := A.sum_alpha_le_one

theorem blockStart_le_one {i : ℕ} (hi : i ≤ A.count) :
    A.blockStart i ≤ 1 :=
  (A.blockStart_mono hi).trans A.blockStart_count_le_one

theorem blockEnd_nonneg (i : Fin A.count) : 0 ≤ A.blockEnd i :=
  add_nonneg (A.blockStart_nonneg i) (A.alpha_nonneg i)

theorem blockEnd_le_one (i : Fin A.count) : A.blockEnd i ≤ 1 := by
  rw [← A.blockStart_succ]
  exact A.blockStart_le_one (Nat.succ_le_iff.mpr i.isLt)

def blockStartUI (i : Fin A.count) : UnitInterval :=
  ⟨A.blockStart i, A.blockStart_nonneg i, A.blockStart_le_one i.isLt.le⟩

def blockEndUI (i : Fin A.count) : UnitInterval :=
  ⟨A.blockEnd i, A.blockEnd_nonneg i, A.blockEnd_le_one i⟩

def blockInterval (i : Fin A.count) : Set UnitInterval :=
  Ico (A.blockStartUI i) (A.blockEndUI i)

@[measurability] theorem measurableSet_blockInterval (i : Fin A.count) :
    MeasurableSet (A.blockInterval i) := measurableSet_Ico

theorem pairwise_disjoint_blockInterval :
    Pairwise fun i j : Fin A.count ↦
      Disjoint (A.blockInterval i) (A.blockInterval j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep : A.blockEnd i ≤ A.blockStart j := by
      rw [← A.blockStart_succ]
      exact A.blockStart_mono (Nat.succ_le_iff.mpr hlt)
    exact (not_lt_of_ge (hsep.trans hxj.1)) hxi.2
  · have hsep : A.blockEnd j ≤ A.blockStart i := by
      rw [← A.blockStart_succ]
      exact A.blockStart_mono (Nat.succ_le_iff.mpr hgt)
    exact (not_lt_of_ge (hsep.trans hxi.1)) hxj.2

def cellLeft (i : Fin A.count) (v : Fin (A.core i).order) : ℝ :=
  A.blockStart i + A.alpha i * ((v : ℝ) / (A.core i).order)

def cellRight (i : Fin A.count) (v : Fin (A.core i).order) : ℝ :=
  A.blockStart i + A.alpha i * (((v : ℕ) + 1 : ℝ) / (A.core i).order)

theorem cellLeft_mem_Icc (i : Fin A.count) (v : Fin (A.core i).order) :
    A.cellLeft i v ∈ Icc (0 : ℝ) 1 := by
  have hr0 : 0 ≤ (v : ℝ) / (A.core i).order := by positivity
  have hr1 : (v : ℝ) / (A.core i).order ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (A.core i).order_pos)]
    exact_mod_cast v.isLt.le
  constructor
  · exact add_nonneg (A.blockStart_nonneg i)
      (mul_nonneg (A.alpha_nonneg i) hr0)
  · calc
      A.cellLeft i v ≤ A.blockStart i + A.alpha i * 1 := by
        unfold cellLeft
        have hmul := mul_le_mul_of_nonneg_left hr1 (A.alpha_nonneg i)
        linarith
      _ = A.blockEnd i := by simp [blockEnd]
      _ ≤ 1 := A.blockEnd_le_one i

theorem cellRight_mem_Icc (i : Fin A.count) (v : Fin (A.core i).order) :
    A.cellRight i v ∈ Icc (0 : ℝ) 1 := by
  have hr0 : 0 ≤ (((v : ℕ) + 1 : ℝ) / (A.core i).order) := by positivity
  have hr1 : (((v : ℕ) + 1 : ℝ) / (A.core i).order) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast (A.core i).order_pos)]
    exact_mod_cast v.isLt
  constructor
  · exact add_nonneg (A.blockStart_nonneg i)
      (mul_nonneg (A.alpha_nonneg i) hr0)
  · calc
      A.cellRight i v ≤ A.blockStart i + A.alpha i * 1 := by
        unfold cellRight
        have hmul := mul_le_mul_of_nonneg_left hr1 (A.alpha_nonneg i)
        linarith
      _ = A.blockEnd i := by simp [blockEnd]
      _ ≤ 1 := A.blockEnd_le_one i

def cellLeftUI (i : Fin A.count) (v : Fin (A.core i).order) : UnitInterval :=
  ⟨A.cellLeft i v, (A.cellLeft_mem_Icc i v).1, (A.cellLeft_mem_Icc i v).2⟩

def cellRightUI (i : Fin A.count) (v : Fin (A.core i).order) : UnitInterval :=
  ⟨A.cellRight i v, (A.cellRight_mem_Icc i v).1, (A.cellRight_mem_Icc i v).2⟩

def blockCell (i : Fin A.count) (v : Fin (A.core i).order) : Set UnitInterval :=
  Ico (A.cellLeftUI i v) (A.cellRightUI i v)

@[measurability] theorem measurableSet_blockCell (i : Fin A.count)
    (v : Fin (A.core i).order) : MeasurableSet (A.blockCell i v) :=
  measurableSet_Ico

theorem blockCell_subset_interval (i : Fin A.count)
    (v : Fin (A.core i).order) : A.blockCell i v ⊆ A.blockInterval i := by
  intro x hx
  constructor
  · exact hx.1.trans' (by
      change A.blockStart i ≤ A.cellLeft i v
      exact le_add_of_nonneg_right
        (mul_nonneg (A.alpha_nonneg i) (by positivity)))
  · exact hx.2.trans_le (by
      change A.cellRight i v ≤ A.blockEnd i
      have hr : (((v : ℕ) + 1 : ℝ) / (A.core i).order) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast (A.core i).order_pos)]
        exact_mod_cast v.isLt
      unfold cellRight blockEnd
      have hmul := mul_le_mul_of_nonneg_left hr (A.alpha_nonneg i)
      linarith)

theorem blockCell_index_eq_of_mem {i j : Fin A.count}
    {v : Fin (A.core i).order} {w : Fin (A.core j).order}
    {x : UnitInterval} (hiv : x ∈ A.blockCell i v)
    (hjw : x ∈ A.blockCell j w) : i = j := by
  by_contra hij
  exact Set.disjoint_left.1 (A.pairwise_disjoint_blockInterval hij)
    (A.blockCell_subset_interval i v hiv)
    (A.blockCell_subset_interval j w hjw)

theorem blockCell_vertex_eq_of_mem {i : Fin A.count}
    {v w : Fin (A.core i).order} {x : UnitInterval}
    (hv : x ∈ A.blockCell i v) (hw : x ∈ A.blockCell i w) : v = w := by
  apply Fin.ext
  by_contra hvw
  rcases lt_or_gt_of_ne hvw with hvw | hwv
  · have hsep : A.cellRight i v ≤ A.cellLeft i w := by
      unfold cellRight cellLeft
      have hr : (((v : ℕ) + 1 : ℝ) / (A.core i).order) ≤
          (w : ℝ) / (A.core i).order := by
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast (A.core i).order_pos)]
        exact_mod_cast (Nat.succ_le_iff.mpr hvw)
      have hmul := mul_le_mul_of_nonneg_left hr (A.alpha_nonneg i)
      linarith
    exact (not_lt_of_ge hsep) (hw.1.trans_lt hv.2)
  · have hsep : A.cellRight i w ≤ A.cellLeft i v := by
      unfold cellRight cellLeft
      have hr : (((w : ℕ) + 1 : ℝ) / (A.core i).order) ≤
          (v : ℝ) / (A.core i).order := by
        rw [div_le_div_iff_of_pos_right (by exact_mod_cast (A.core i).order_pos)]
        exact_mod_cast (Nat.succ_le_iff.mpr hwv)
      have hmul := mul_le_mul_of_nonneg_left hr (A.alpha_nonneg i)
      linarith
    exact (not_lt_of_ge hsep) (hv.1.trans_lt hw.2)

/-- Raw kernel of a finite layout. -/
def kernel (p : ℝ) (z : UnitSquare) : ℝ :=
  ∑ i : Fin A.count, ∑ v : Fin (A.core i).order,
    ∑ w : Fin (A.core i).order,
      (A.blockCell i v ×ˢ A.blockCell i w).indicator
        (fun _ ↦ profileXiMatrix p (A.core i) v w) z

@[fun_prop] theorem measurable_kernel (p : ℝ) : Measurable (A.kernel p) := by
  unfold kernel
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro v _
  apply Finset.measurable_sum
  intro w _
  exact measurable_const.indicator
    ((A.measurableSet_blockCell i v).prod (A.measurableSet_blockCell i w))

theorem kernel_nonneg {p : ℝ} (hp : 0 ≤ p) (z : UnitSquare) :
    0 ≤ A.kernel p z := by
  classical
  unfold kernel
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro w _
  rw [Set.indicator_apply]
  split
  · exact profileXiMatrix_nonneg hp _ _ _
  · exact le_rfl

theorem kernel_of_mem (p : ℝ) (i : Fin A.count)
    (v w : Fin (A.core i).order) (z : UnitSquare)
    (hzv : z.1 ∈ A.blockCell i v) (hzw : z.2 ∈ A.blockCell i w) :
    A.kernel p z = profileXiMatrix p (A.core i) v w := by
  classical
  unfold kernel
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single v]
    · rw [Finset.sum_eq_single w]
      · simp [hzv, hzw]
      · intro b _ hbw
        apply Set.indicator_of_notMem
        intro hb
        exact hbw (A.blockCell_vertex_eq_of_mem hb.2 hzw)
      · simp
    · intro a _ hav
      apply Finset.sum_eq_zero
      intro b _
      apply Set.indicator_of_notMem
      intro hab
      exact hav (A.blockCell_vertex_eq_of_mem hab.1 hzv)
    · simp
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    apply Set.indicator_of_notMem
    intro hab
    exact hji (A.blockCell_index_eq_of_mem hab.1 hzv)
  · simp

theorem kernel_eq_zero_of_no_leftCell (p : ℝ) (z : UnitSquare)
    (hz : ∀ i : Fin A.count, ∀ v : Fin (A.core i).order,
      z.1 ∉ A.blockCell i v) : A.kernel p z = 0 := by
  classical
  unfold kernel
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro v _
  apply Finset.sum_eq_zero
  intro w _
  exact Set.indicator_of_notMem (fun h ↦ hz i v h.1) _

theorem kernel_le_one {p : ℝ} (hp : p ≤ 1) (z : UnitSquare) :
    A.kernel p z ≤ 1 := by
  classical
  by_cases hx : ∃ i : Fin A.count, ∃ v : Fin (A.core i).order,
      z.1 ∈ A.blockCell i v
  · obtain ⟨i, v, hv⟩ := hx
    by_cases hy : ∃ w : Fin (A.core i).order, z.2 ∈ A.blockCell i w
    · obtain ⟨w, hw⟩ := hy
      rw [A.kernel_of_mem p i v w z hv hw]
      exact profileXiMatrix_le_one hp _ _ _
    · have hzero : A.kernel p z = 0 := by
        unfold kernel
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        have hji := A.blockCell_index_eq_of_mem hab.1 hv
        subst j
        exact hy ⟨b, hab.2⟩
      simp [hzero]
  · rw [A.kernel_eq_zero_of_no_leftCell p z (by simpa only [not_exists] using hx)]
    exact zero_le_one

theorem kernel_symm (p : ℝ) (z : UnitSquare) :
    A.kernel p (z.2, z.1) = A.kernel p z := by
  classical
  simp only [kernel, Set.indicator_apply, Set.mem_prod]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [(profileXiMatrix_isSymm p (A.core i)).apply]
  simp [and_comm]

theorem integrable_kernel {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    Integrable (A.kernel p) unitSquareMeasure := by
  apply Integrable.of_bound (A.measurable_kernel p).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (A.kernel_nonneg hp.1 z)]
  exact A.kernel_le_one hp.2 z

/-- Graphon represented by a finite layout. -/
def graphon (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) : Graphon :=
  Graphon.ofFun (A.kernel p) (A.integrable_kernel hp)
    (ae_of_all _ (A.kernel_nonneg hp.1))
    (ae_of_all _ (A.kernel_le_one hp.2))
    (A.kernel_symm p)

theorem graphon_ae_eq_kernel (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure, A.graphon p hp z = A.kernel p z :=
  Graphon.coe_ofFun _ _ _ _ _

theorem graphon_value_ae_eq_kernel (p : ℝ)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure, (A.graphon p hp).value z = A.kernel p z := by
  filter_upwards [(A.graphon p hp).value_ae_eq,
    A.graphon_ae_eq_kernel p hp] with z hz hzk
  exact hz.trans hzk

/-! ## Layouts associated with finite admissible sequences -/

/-- The first `N` ranks of an arbitrary admissible block sequence, retaining
their original packed coordinates.  This auxiliary layout is allowed to have
zero-length blocks. -/
def ofPrefix (L : AdmissibleBlockSequence k) (N : ℕ) :
    FiniteProfileBlockLayout k where
  count := N
  alpha := fun i ↦ L.alpha i
  core := fun i ↦ L.core i
  alpha_nonneg := fun i ↦ L.alpha_nonneg i
  sum_alpha_le_one := by
    calc
      ∑ i : Fin N, L.alpha i ≤ ∑' i : ℕ, L.alpha i := by
        rw [Fin.sum_univ_eq_sum_range]
        exact L.summable_alpha.sum_le_tsum
          (Finset.range N) (fun i _ ↦ L.alpha_nonneg i)
      _ ≤ 1 := L.tsum_alpha_le_one

@[simp] theorem ofPrefix_count (L : AdmissibleBlockSequence k) (N : ℕ) :
    (ofPrefix L N).count = N := rfl

@[simp] theorem ofPrefix_alpha (L : AdmissibleBlockSequence k) (N : ℕ)
    (i : Fin N) : (ofPrefix L N).alpha i = L.alpha i := rfl

@[simp] theorem ofPrefix_core (L : AdmissibleBlockSequence k) (N : ℕ)
    (i : Fin N) : (ofPrefix L N).core i = L.core i := rfl

theorem ofPrefix_blockStart (L : AdmissibleBlockSequence k) (N : ℕ)
    {i : ℕ} (hi : i ≤ N) :
    (ofPrefix L N).blockStart i = L.blockStart i := by
  unfold blockStart AdmissibleBlockSequence.blockStart
  apply Finset.sum_congr rfl
  intro j hj
  have hjN : j < N := (Finset.mem_range.mp hj).trans_le hi
  simp [alphaNat, ofPrefix, hjN]

theorem ofPrefix_blockInterval (L : AdmissibleBlockSequence k) (N : ℕ)
    (i : Fin N) :
    (ofPrefix L N).blockInterval i = L.blockInterval i := by
  have hs := ofPrefix_blockStart L N i.isLt.le
  have he := ofPrefix_blockStart L N (Nat.succ_le_iff.mpr i.isLt)
  unfold blockInterval blockStartUI blockEndUI blockEnd
    AdmissibleBlockSequence.blockInterval
    AdmissibleBlockSequence.blockStartUI
    AdmissibleBlockSequence.blockEndUI
    AdmissibleBlockSequence.blockEnd
  simp only [ofPrefix_alpha]
  congr 1 <;> apply Subtype.ext <;> simp only [hs, he]

theorem ofPrefix_blockCell (L : AdmissibleBlockSequence k) (N : ℕ)
    (i : Fin N) (v : Fin (L.core i).order) :
    (ofPrefix L N).blockCell i v = L.blockCell i v := by
  have hs := ofPrefix_blockStart L N i.isLt.le
  unfold blockCell cellLeftUI cellRightUI cellLeft cellRight
    AdmissibleBlockSequence.blockCell AdmissibleBlockSequence.cellLeftUI
    AdmissibleBlockSequence.cellRightUI AdmissibleBlockSequence.cellLeft
    AdmissibleBlockSequence.cellRight
  simp only [ofPrefix_alpha, ofPrefix_core]
  congr 1 <;> apply Subtype.ext <;> simp only [hs]

/-- The union of the block squares with ranks `N,N+1,…`. -/
def tailBlockSquares (L : AdmissibleBlockSequence k) (N : ℕ) :
    Set UnitSquare :=
  ⋃ j : ℕ, L.blockSquare (N + j)

@[measurability] theorem measurableSet_tailBlockSquares
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    MeasurableSet (tailBlockSquares L N) :=
  MeasurableSet.iUnion fun j ↦ L.measurableSet_blockSquare (N + j)

theorem measureReal_blockSquare (L : AdmissibleBlockSequence k) (i : ℕ) :
    unitSquareMeasure.real (L.blockSquare i) = L.alpha i ^ 2 := by
  rw [AdmissibleBlockSequence.blockSquare, measureReal_prod_prod,
    Measure.real, L.volume_blockInterval,
    ENNReal.toReal_ofReal (L.alpha_nonneg i)]
  ring

/-- The tail support has exactly the square-tail measure. -/
theorem measureReal_tailBlockSquares
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    unitSquareMeasure.real (tailBlockSquares L N) = L.alphaSquareTail N := by
  have hpair : Pairwise fun i j : ℕ ↦
      Disjoint (L.blockSquare (N + i)) (L.blockSquare (N + j)) := by
    intro i j hij
    exact L.pairwise_disjoint_blockSquare (fun h ↦ hij (Nat.add_left_cancel h))
  unfold tailBlockSquares AdmissibleBlockSequence.alphaSquareTail
  rw [Measure.real, measure_iUnion hpair
      (fun j ↦ L.measurableSet_blockSquare (N + j)),
    ENNReal.tsum_toReal_eq (fun j ↦ measure_ne_top _ _)]
  exact tsum_congr fun j ↦ measureReal_blockSquare L (N + j)

/-- Off the discarded block squares, the finite prefix kernel agrees
pointwise with the countable profile kernel. -/
theorem kernel_ofPrefix_eq_profileKernel_of_not_mem_tailBlockSquares
    (hk : 3 ≤ k) (p : ℝ) (L : AdmissibleBlockSequence k) (N : ℕ)
    (z : UnitSquare) (hz : z ∉ tailBlockSquares L N) :
    (ofPrefix L N).kernel p z = L.profileKernel p z := by
  let A := ofPrefix L N
  by_cases hx : ∃ i : Fin N, ∃ v : Fin (L.core i).order,
      z.1 ∈ A.blockCell i v
  · obtain ⟨i, v, hv⟩ := hx
    have hvL : z.1 ∈ L.blockCell i v := by
      rw [← ofPrefix_blockCell L N i v]
      exact hv
    by_cases hy : ∃ w : Fin (L.core i).order, z.2 ∈ A.blockCell i w
    · obtain ⟨w, hw⟩ := hy
      have hwL : z.2 ∈ L.blockCell i w := by
        rw [← ofPrefix_blockCell L N i w]
        exact hw
      rw [A.kernel_of_mem p i v w z hv hw,
        L.profileKernel_of_mem hk p i v w z hvL hwL]
      rfl
    · have hAzero : A.kernel p z = 0 := by
        unfold kernel
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        have hji := A.blockCell_index_eq_of_mem hab.1 hv
        subst j
        exact hy ⟨b, hab.2⟩
      have hLzero : L.profileKernel p z = 0 := by
        rw [AdmissibleBlockSequence.profileKernel,
          L.kernel_eq_blockKernel_of_mem i z
            (L.blockCell_subset_interval i v hvL),
          L.blockKernel_eq_zero_of_no_rightCell]
        · simp
        · intro w hwL
          apply hy
          refine ⟨w, ?_⟩
          rw [ofPrefix_blockCell L N i w]
          exact hwL
      rw [hAzero, hLzero]
  · have hAzero : A.kernel p z = 0 := by
      apply A.kernel_eq_zero_of_no_leftCell
      intro i v hiv
      exact hx ⟨i, v, hiv⟩
    by_cases hLx : ∃ i : ℕ, ∃ v : Fin (L.core i).order,
        z.1 ∈ L.blockCell i v
    · obtain ⟨i, v, hv⟩ := hLx
      have hi : N ≤ i := by
        by_contra hNi
        have hiN : i < N := Nat.lt_of_not_ge hNi
        apply hx
        refine ⟨⟨i, hiN⟩, v, ?_⟩
        rw [ofPrefix_blockCell L N ⟨i, hiN⟩ v]
        exact hv
      have hvInterval : z.1 ∈ L.blockInterval i :=
        L.blockCell_subset_interval i v hv
      have hyInterval : z.2 ∉ L.blockInterval i := by
        intro hy
        apply hz
        apply Set.mem_iUnion.2
        refine ⟨i - N, ?_⟩
        have hindex : N + (i - N) = i := Nat.add_sub_of_le hi
        rw [hindex]
        exact ⟨hvInterval, hy⟩
      have hLzero : L.profileKernel p z = 0 :=
        L.profileKernel_eq_zero_of_not_mem p i z (Or.inr hyInterval) hvInterval
      rw [hAzero, hLzero]
    · have hLcells : ∀ i : ℕ, ∀ v : Fin (L.core i).order,
          z.1 ∉ L.blockCell i v := by
        simpa only [not_exists] using hLx
      have hLzero : L.profileKernel p z = 0 := by
        rw [AdmissibleBlockSequence.profileKernel,
          L.kernel_eq_zero_of_no_leftCell z hLcells]
        simp
      rw [hAzero, hLzero]

/-- Deleting every rank at least `N` from an arbitrary admissible sequence
costs at most its square tail in fixed-coordinate `L¹`. -/
theorem graphonL1Dist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    graphonL1Dist (profileWLambda p L hp) ((ofPrefix L N).graphon p hp) ≤
      L.alphaSquareTail N := by
  rw [graphonL1Dist_eq_integral]
  let D := tailBlockSquares L N
  have hD : MeasurableSet D := measurableSet_tailBlockSquares L N
  calc
    (∫ z, |profileWLambda p L hp z - (ofPrefix L N).graphon p hp z|
        ∂unitSquareMeasure) ≤
        ∫ z, D.indicator (fun _ ↦ (1 : ℝ)) z ∂unitSquareMeasure := by
      apply integral_mono_ae
      · exact (profileWLambda p L hp).integrable.sub
          ((ofPrefix L N).graphon p hp).integrable |>.abs
      · exact (integrable_const (1 : ℝ)).indicator hD
      filter_upwards [profileWLambda_ae_eq_profileKernel p L hp,
        (ofPrefix L N).graphon_ae_eq_kernel p hp,
        (profileWLambda p L hp).ae_mem_Icc,
        ((ofPrefix L N).graphon p hp).ae_mem_Icc]
        with z hzL hzA hbL hbA
      rcases hbL with ⟨hbL0, hbL1⟩
      rcases hbA with ⟨hbA0, hbA1⟩
      by_cases hz : z ∈ D
      · rw [Set.indicator_of_mem hz]
        rw [abs_le]
        constructor <;> linarith
      · rw [Set.indicator_of_notMem hz, hzL, hzA,
          ← kernel_ofPrefix_eq_profileKernel_of_not_mem_tailBlockSquares
            hk p L N z hz]
        simp
    _ = unitSquareMeasure.real D := by
      rw [integral_indicator_const (1 : ℝ) hD]
      simp
    _ = L.alphaSquareTail N := measureReal_tailBlockSquares L N

/-- Fully explicit first-`N` approximation bound. -/
theorem graphonL1Dist_profileWLambda_graphon_ofPrefix_le_inv_succ
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    graphonL1Dist (profileWLambda p L hp) ((ofPrefix L N).graphon p hp) ≤
      1 / ((N + 1 : ℕ) : ℝ) :=
  (graphonL1Dist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
      hk p hp L N).trans (L.alphaSquareTail_le_inv_succ N)

theorem cutDist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) (N : ℕ) :
    cutDist (profileWLambda p L hp) ((ofPrefix L N).graphon p hp) ≤
      L.alphaSquareTail N :=
  (cutDist_le_graphonL1Dist _ _).trans
    (graphonL1Dist_profileWLambda_graphon_ofPrefix_le_alphaSquareTail
      hk p hp L N)

/-- Forget the ordering/strict-positivity fields of a finite admissible
sequence. -/
def ofFiniteSequence (L : AdmissibleBlockSequence k) (n : ℕ)
    (hcount : L.count = some n) : FiniteProfileBlockLayout k where
  count := n
  alpha := fun i ↦ L.alpha i
  core := fun i ↦ L.core i
  alpha_nonneg := fun i ↦ L.alpha_nonneg i
  sum_alpha_le_one := by
    calc
      ∑ i : Fin n, L.alpha i ≤ ∑' i : ℕ, L.alpha i := by
        rw [Fin.sum_univ_eq_sum_range]
        exact L.summable_alpha.sum_le_tsum
          (Finset.range n) (fun i _ ↦ L.alpha_nonneg i)
      _ ≤ 1 := L.tsum_alpha_le_one

@[simp] theorem ofFiniteSequence_count (L : AdmissibleBlockSequence k)
    (n : ℕ) (hcount : L.count = some n) :
    (ofFiniteSequence L n hcount).count = n := rfl

@[simp] theorem ofFiniteSequence_alpha (L : AdmissibleBlockSequence k)
    (n : ℕ) (hcount : L.count = some n) (i : Fin n) :
    (ofFiniteSequence L n hcount).alpha i = L.alpha i := rfl

@[simp] theorem ofFiniteSequence_core (L : AdmissibleBlockSequence k)
    (n : ℕ) (hcount : L.count = some n) (i : Fin n) :
    (ofFiniteSequence L n hcount).core i = L.core i := rfl

theorem ofFiniteSequence_blockStart (L : AdmissibleBlockSequence k)
    (n : ℕ) (hcount : L.count = some n) {i : ℕ} (hi : i ≤ n) :
    (ofFiniteSequence L n hcount).blockStart i = L.blockStart i := by
  unfold blockStart AdmissibleBlockSequence.blockStart
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j < n := (Finset.mem_range.mp hj).trans_le hi
  simp [alphaNat, ofFiniteSequence, hjn]

theorem ofFiniteSequence_blockCell (L : AdmissibleBlockSequence k)
    (n : ℕ) (hcount : L.count = some n) (i : Fin n)
    (v : Fin (L.core i).order) :
    (ofFiniteSequence L n hcount).blockCell i v = L.blockCell i v := by
  have hs := ofFiniteSequence_blockStart L n hcount i.isLt.le
  unfold blockCell cellLeftUI cellRightUI cellLeft cellRight
    AdmissibleBlockSequence.blockCell AdmissibleBlockSequence.cellLeftUI
    AdmissibleBlockSequence.cellRightUI AdmissibleBlockSequence.cellLeft
    AdmissibleBlockSequence.cellRight
  simp only [ofFiniteSequence_alpha, ofFiniteSequence_core]
  congr 1 <;> apply Subtype.ext <;> simp only [hs]

private theorem sequence_blockCell_empty_of_alpha_eq_zero
    (L : AdmissibleBlockSequence k) {i : ℕ} (hi : L.alpha i = 0)
    (v : Fin (L.core i).order) : L.blockCell i v = ∅ := by
  ext x
  simp only [AdmissibleBlockSequence.blockCell, Set.mem_Ico, Set.mem_empty_iff_false,
    iff_false]
  intro hx
  have hlt : L.cellLeft i v < L.cellRight i v :=
    (show L.cellLeftUI i v ≤ x from hx.1).trans_lt
      (show x < L.cellRightUI i v from hx.2)
  simp [AdmissibleBlockSequence.cellLeft,
    AdmissibleBlockSequence.cellRight, hi] at hlt

private theorem sequence_blockCell_eq_layout_of_lt
    (L : AdmissibleBlockSequence k) (n : ℕ) (hcount : L.count = some n)
    {i : ℕ} (hi : i < n) (v : Fin (L.core i).order) :
    L.blockCell i v =
      (ofFiniteSequence L n hcount).blockCell ⟨i, hi⟩ v := by
  exact (ofFiniteSequence_blockCell L n hcount ⟨i, hi⟩ v).symm

/-- Exact compatibility with the existing graphon of a finite admissible
sequence. -/
theorem graphon_ofFiniteSequence_eq_profileWLambda
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (hcount : L.count = some n) :
    (ofFiniteSequence L n hcount).graphon p hp = profileWLambda p L hp := by
  let A := ofFiniteSequence L n hcount
  apply Graphon.ext
  filter_upwards [A.graphon_ae_eq_kernel p hp,
    profileWLambda_ae_eq_profileKernel p L hp] with z hzA hzL
  rw [hzA, hzL]
  by_cases hx : ∃ i : Fin n, ∃ v : Fin (L.core i).order,
      z.1 ∈ A.blockCell i v
  · obtain ⟨i, v, hv⟩ := hx
    have hvL : z.1 ∈ L.blockCell i v := by
      rw [← ofFiniteSequence_blockCell L n hcount i v]
      exact hv
    by_cases hy : ∃ w : Fin (L.core i).order, z.2 ∈ A.blockCell i w
    · obtain ⟨w, hw⟩ := hy
      have hwL : z.2 ∈ L.blockCell i w := by
        rw [← ofFiniteSequence_blockCell L n hcount i w]
        exact hw
      rw [A.kernel_of_mem p i v w z hv hw,
        L.profileKernel_of_mem hk p i v w z hvL hwL]
      rfl
    · have hAzero : A.kernel p z = 0 := by
        unfold kernel
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro a _
        apply Finset.sum_eq_zero
        intro b _
        apply Set.indicator_of_notMem
        intro hab
        have hji := A.blockCell_index_eq_of_mem hab.1 hv
        subst j
        exact hy ⟨b, hab.2⟩
      have hLzero : L.profileKernel p z = 0 := by
        rw [AdmissibleBlockSequence.profileKernel,
          L.kernel_eq_blockKernel_of_mem i z
            (L.blockCell_subset_interval i v hvL),
          L.blockKernel_eq_zero_of_no_rightCell]
        · simp
        · intro w hwL
          apply hy
          refine ⟨w, ?_⟩
          rw [ofFiniteSequence_blockCell L n hcount i w]
          exact hwL
      rw [hAzero, hLzero]
  · have hAzero : A.kernel p z = 0 := by
      apply A.kernel_eq_zero_of_no_leftCell
      intro i v hiv
      exact hx ⟨i, v, hiv⟩
    have hLcells : ∀ i : ℕ, ∀ v : Fin (L.core i).order,
        z.1 ∉ L.blockCell i v := by
      intro i v hiv
      by_cases hi : i < n
      · apply hx
        have hmem : z.1 ∈
            (ofFiniteSequence L n hcount).blockCell ⟨i, hi⟩ v := by
          rwa [← sequence_blockCell_eq_layout_of_lt L n hcount hi v]
        change z.1 ∈ A.blockCell ⟨i, hi⟩ v at hmem
        exact ⟨⟨i, hi⟩, v, hmem⟩
      · have hzero : L.alpha i = 0 :=
          L.alpha_eq_zero_of_count_eq_some hcount (Nat.le_of_not_gt hi)
        rw [sequence_blockCell_empty_of_alpha_eq_zero L hzero v] at hiv
        exact hiv
    have hLzero : L.profileKernel p z = 0 := by
      rw [AdmissibleBlockSequence.profileKernel,
        L.kernel_eq_zero_of_no_leftCell z hLcells]
      simp
    rw [hAzero, hLzero]

/-! ## Variable-length block permutations -/

/-- Permute lengths and core labels together. -/
def permute (perm : Equiv.Perm (Fin A.count)) :
    FiniteProfileBlockLayout k where
  count := A.count
  alpha := fun i ↦ A.alpha (perm i)
  core := fun i ↦ A.core (perm i)
  alpha_nonneg := fun i ↦ A.alpha_nonneg (perm i)
  sum_alpha_le_one := by
    rw [Equiv.sum_comp perm]
    exact A.sum_alpha_le_one

@[simp] theorem permute_count (perm : Equiv.Perm (Fin A.count)) :
    (A.permute perm).count = A.count := rfl

@[simp] theorem permute_alpha (perm : Equiv.Perm (Fin A.count))
    (i : Fin A.count) : (A.permute perm).alpha i = A.alpha (perm i) := rfl

@[simp] theorem permute_core (perm : Equiv.Perm (Fin A.count))
    (i : Fin A.count) : (A.permute perm).core i = A.core (perm i) := rfl

@[simp] theorem permute_sum (perm : Equiv.Perm (Fin A.count)) :
    ∑ i, (A.permute perm).alpha i = ∑ i, A.alpha i := by
  exact Equiv.sum_comp perm A.alpha

theorem permute_blockStart_count (perm : Equiv.Perm (Fin A.count)) :
    (A.permute perm).blockStart A.count = A.blockStart A.count := by
  change (A.permute perm).blockStart (A.permute perm).count =
    A.blockStart A.count
  rw [(A.permute perm).blockStart_count_eq_sum, A.blockStart_count_eq_sum,
    A.permute_sum perm]

/-- Real-coordinate version of a layout block. -/
def realBlockInterval (i : Fin A.count) : Set ℝ :=
  Ico (A.blockStart i) (A.blockEnd i)

@[measurability] theorem measurableSet_realBlockInterval (i : Fin A.count) :
    MeasurableSet (A.realBlockInterval i) := measurableSet_Ico

def realBlockUnion : Set ℝ := ⋃ i : Fin A.count, A.realBlockInterval i

@[measurability] theorem measurableSet_realBlockUnion :
    MeasurableSet A.realBlockUnion :=
  MeasurableSet.iUnion fun i ↦ A.measurableSet_realBlockInterval i

theorem realBlockInterval_eq_of_mem {i j : Fin A.count} {x : ℝ}
    (hi : x ∈ A.realBlockInterval i) (hj : x ∈ A.realBlockInterval j) :
    i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hsep : A.blockEnd i ≤ A.blockStart j := by
      rw [← A.blockStart_succ]
      exact A.blockStart_mono (Nat.succ_le_iff.mpr hlt)
    exact (not_lt_of_ge (hsep.trans hj.1)) hi.2
  · have hsep : A.blockEnd j ≤ A.blockStart i := by
      rw [← A.blockStart_succ]
      exact A.blockStart_mono (Nat.succ_le_iff.mpr hgt)
    exact (not_lt_of_ge (hsep.trans hi.1)) hj.2

/-- Consecutive layout blocks fill precisely the interval before the unused
tail, even when some lengths vanish. -/
theorem realBlockUnion_eq_Ico :
    A.realBlockUnion = Ico 0 (A.blockStart A.count) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    refine ⟨(A.blockStart_nonneg i).trans hi.1, ?_⟩
    exact hi.2.trans_le <| by
      rw [← A.blockStart_succ]
      exact A.blockStart_mono (Nat.succ_le_iff.mpr i.isLt)
  · intro x hx
    have hx' := Ico_subset_biUnion_Ico A.count A.blockStart hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨i, hi, hxi⟩ := hx'
    have hin : i < A.count := Finset.mem_range.mp hi
    refine Set.mem_iUnion.2 ⟨(⟨i, hin⟩ : Fin A.count), ?_⟩
    change x ∈ Ico (A.blockStart i) (A.blockEnd ⟨i, hin⟩)
    rwa [← A.blockStart_succ]

/-- Translation carrying source block `i` in the permuted layout to its
originally labeled destination block. -/
def variableBlockShift (perm : Equiv.Perm (Fin A.count))
    (i : Fin A.count) : ℝ :=
  A.blockStart (perm i) - (A.permute perm).blockStart i

def variableBlockInvShift (perm : Equiv.Perm (Fin A.count))
    (j : Fin A.count) : ℝ :=
  (A.permute perm).blockStart (perm.symm j) - A.blockStart j

@[simp] theorem variableBlockInvShift_apply
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count) :
    A.variableBlockInvShift perm (perm i) = -A.variableBlockShift perm i := by
  simp [variableBlockInvShift, variableBlockShift]

/-- Piecewise translation from the permuted layout coordinates back to the
coordinates of `A`; it fixes the common unused tail and all of `ℝ` outside
the active union. -/
def realVariableBlockPermFun (perm : Equiv.Perm (Fin A.count)) (x : ℝ) : ℝ :=
  (∑ i : Fin A.count,
      ((A.permute perm).realBlockInterval i).indicator
        (fun y ↦ y + A.variableBlockShift perm i) x) +
    ((A.permute perm).realBlockUnion)ᶜ.indicator id x

def realVariableBlockPermInvFun
    (perm : Equiv.Perm (Fin A.count)) (x : ℝ) : ℝ :=
  (∑ j : Fin A.count,
      (A.realBlockInterval j).indicator
        (fun y ↦ y + A.variableBlockInvShift perm j) x) +
    A.realBlockUnionᶜ.indicator id x

theorem realVariableBlockPermFun_of_mem
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count) {x : ℝ}
    (hx : x ∈ (A.permute perm).realBlockInterval i) :
    A.realVariableBlockPermFun perm x = x + A.variableBlockShift perm i := by
  classical
  unfold realVariableBlockPermFun
  rw [Finset.sum_eq_single i]
  · have hxU : x ∈ (A.permute perm).realBlockUnion :=
      Set.mem_iUnion.2 ⟨i, hx⟩
    simp [hx, hxU]
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    exact hji ((A.permute perm).realBlockInterval_eq_of_mem hj hx)
  · simp

theorem realVariableBlockPermInvFun_of_mem
    (perm : Equiv.Perm (Fin A.count)) (j : Fin A.count) {x : ℝ}
    (hx : x ∈ A.realBlockInterval j) :
    A.realVariableBlockPermInvFun perm x =
      x + A.variableBlockInvShift perm j := by
  classical
  unfold realVariableBlockPermInvFun
  rw [Finset.sum_eq_single j]
  · have hxU : x ∈ A.realBlockUnion := Set.mem_iUnion.2 ⟨j, hx⟩
    simp [hx, hxU]
  · intro i _ hij
    apply Set.indicator_of_notMem
    intro hi
    exact hij (A.realBlockInterval_eq_of_mem hi hx)
  · simp

theorem realVariableBlockPermFun_of_not_mem
    (perm : Equiv.Perm (Fin A.count)) {x : ℝ}
    (hx : x ∉ (A.permute perm).realBlockUnion) :
    A.realVariableBlockPermFun perm x = x := by
  classical
  have hxi (i : Fin A.count) :
      x ∉ (A.permute perm).realBlockInterval i :=
    fun hi ↦ hx (Set.mem_iUnion.2 ⟨i, hi⟩)
  simp [realVariableBlockPermFun, hx, hxi]

theorem realVariableBlockPermInvFun_of_not_mem
    (perm : Equiv.Perm (Fin A.count)) {x : ℝ}
    (hx : x ∉ A.realBlockUnion) :
    A.realVariableBlockPermInvFun perm x = x := by
  classical
  have hxj (j : Fin A.count) : x ∉ A.realBlockInterval j :=
    fun hj ↦ hx (Set.mem_iUnion.2 ⟨j, hj⟩)
  simp [realVariableBlockPermInvFun, hx, hxj]

theorem realVariableBlockPermFun_mem
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count) {x : ℝ}
    (hx : x ∈ (A.permute perm).realBlockInterval i) :
    A.realVariableBlockPermFun perm x ∈ A.realBlockInterval (perm i) := by
  rw [A.realVariableBlockPermFun_of_mem perm i hx]
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · dsimp [variableBlockShift] at *
    linarith
  · have hlen : (A.permute perm).alpha i = A.alpha (perm i) := rfl
    simp only [realBlockInterval, blockEnd] at hx1 ⊢
    dsimp [variableBlockShift]
    rw [hlen] at hx1
    linarith

theorem realVariableBlockPermInvFun_mem
    (perm : Equiv.Perm (Fin A.count)) (j : Fin A.count) {x : ℝ}
    (hx : x ∈ A.realBlockInterval j) :
    A.realVariableBlockPermInvFun perm x ∈
      (A.permute perm).realBlockInterval (perm.symm j) := by
  rw [A.realVariableBlockPermInvFun_of_mem perm j hx]
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · dsimp [variableBlockInvShift] at *
    linarith
  · simp only [realBlockInterval, blockEnd] at hx1 ⊢
    dsimp [variableBlockInvShift]
    simp only [perm.apply_symm_apply]
    linarith

@[fun_prop] theorem measurable_realVariableBlockPermFun
    (perm : Equiv.Perm (Fin A.count)) :
    Measurable (A.realVariableBlockPermFun perm) := by
  classical
  unfold realVariableBlockPermFun
  apply Measurable.add
  · exact Finset.measurable_sum Finset.univ fun i _ ↦
      (measurable_id.add measurable_const).indicator
        ((A.permute perm).measurableSet_realBlockInterval i)
  · exact measurable_id.indicator (A.permute perm).measurableSet_realBlockUnion.compl

@[fun_prop] theorem measurable_realVariableBlockPermInvFun
    (perm : Equiv.Perm (Fin A.count)) :
    Measurable (A.realVariableBlockPermInvFun perm) := by
  classical
  unfold realVariableBlockPermInvFun
  apply Measurable.add
  · exact Finset.measurable_sum Finset.univ fun j _ ↦
      (measurable_id.add measurable_const).indicator
        (A.measurableSet_realBlockInterval j)
  · exact measurable_id.indicator A.measurableSet_realBlockUnion.compl

theorem realBlockUnion_permute_eq
    (perm : Equiv.Perm (Fin A.count)) :
    (A.permute perm).realBlockUnion = A.realBlockUnion := by
  rw [(A.permute perm).realBlockUnion_eq_Ico, A.realBlockUnion_eq_Ico]
  congr 1
  exact A.permute_blockStart_count perm

theorem realVariableBlockPermFun_leftInverse
    (perm : Equiv.Perm (Fin A.count)) :
    Function.LeftInverse (A.realVariableBlockPermInvFun perm)
      (A.realVariableBlockPermFun perm) := by
  intro x
  by_cases hx : x ∈ (A.permute perm).realBlockUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    let i' : Fin A.count := ⟨i, by simpa using i.isLt⟩
    have hii : (i : Fin A.count) = i' := Fin.ext rfl
    have hi' : x ∈ (A.permute perm).realBlockInterval i' := by
      simpa [realBlockInterval, blockEnd, permute, hii] using hi
    have himage := A.realVariableBlockPermFun_mem perm i' hi'
    have himage' : x + A.variableBlockShift perm i' ∈
        A.realBlockInterval (perm i') := by
      rwa [← A.realVariableBlockPermFun_of_mem perm i' hi']
    rw [A.realVariableBlockPermFun_of_mem perm i' hi',
      A.realVariableBlockPermInvFun_of_mem perm (perm i') himage',
      A.variableBlockInvShift_apply]
    ring
  · rw [A.realVariableBlockPermFun_of_not_mem perm hx]
    have hx' : x ∉ A.realBlockUnion := by
      rwa [← A.realBlockUnion_permute_eq perm]
    rw [A.realVariableBlockPermInvFun_of_not_mem perm hx']

theorem realVariableBlockPermFun_rightInverse
    (perm : Equiv.Perm (Fin A.count)) :
    Function.RightInverse (A.realVariableBlockPermInvFun perm)
      (A.realVariableBlockPermFun perm) := by
  intro x
  by_cases hx : x ∈ A.realBlockUnion
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hx
    have himage := A.realVariableBlockPermInvFun_mem perm j hj
    have himage' : x + A.variableBlockInvShift perm j ∈
        (A.permute perm).realBlockInterval (perm.symm j) := by
      rwa [← A.realVariableBlockPermInvFun_of_mem perm j hj]
    rw [A.realVariableBlockPermInvFun_of_mem perm j hj,
      A.realVariableBlockPermFun_of_mem perm (perm.symm j) himage']
    simp [variableBlockInvShift, variableBlockShift]
    ring
  · rw [A.realVariableBlockPermInvFun_of_not_mem perm hx]
    have hx' : x ∉ (A.permute perm).realBlockUnion := by
      rwa [A.realBlockUnion_permute_eq perm]
    rw [A.realVariableBlockPermFun_of_not_mem perm hx']

def realVariableBlockPermMeasurableEquiv
    (perm : Equiv.Perm (Fin A.count)) : ℝ ≃ᵐ ℝ where
  toEquiv :=
    { toFun := A.realVariableBlockPermFun perm
      invFun := A.realVariableBlockPermInvFun perm
      left_inv := A.realVariableBlockPermFun_leftInverse perm
      right_inv := A.realVariableBlockPermFun_rightInverse perm }
  measurable_toFun := A.measurable_realVariableBlockPermFun perm
  measurable_invFun := A.measurable_realVariableBlockPermInvFun perm

theorem map_restrict_realBlockInterval_add_shift
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count) :
    Measure.map (fun x : ℝ ↦ x + A.variableBlockShift perm i)
        (volume.restrict ((A.permute perm).realBlockInterval i)) =
      volume.restrict (A.realBlockInterval (perm i)) := by
  let trans : ℝ ≃ᵐ ℝ := MeasurableEquiv.addRight (A.variableBlockShift perm i)
  have hrestrict := trans.restrict_map volume (A.realBlockInterval (perm i))
  have hmap : Measure.map (fun x : ℝ ↦ x + A.variableBlockShift perm i)
      volume = volume := map_add_right_eq_self volume _
  have hpre : (fun x : ℝ ↦ x + A.variableBlockShift perm i) ⁻¹'
      A.realBlockInterval (perm i) = (A.permute perm).realBlockInterval i := by
    ext x
    constructor
    · intro hx
      have hback := A.realVariableBlockPermInvFun_mem perm (perm i) hx
      rw [A.realVariableBlockPermInvFun_of_mem perm (perm i) hx,
        A.variableBlockInvShift_apply] at hback
      simpa using hback
    · intro hx
      change x + A.variableBlockShift perm i ∈ A.realBlockInterval (perm i)
      have him := A.realVariableBlockPermFun_mem perm i hx
      rw [A.realVariableBlockPermFun_of_mem perm i hx] at him
      exact him
  change (Measure.map (fun x : ℝ ↦ x + A.variableBlockShift perm i) volume).restrict
      (A.realBlockInterval (perm i)) =
    Measure.map (fun x : ℝ ↦ x + A.variableBlockShift perm i)
      (volume.restrict ((fun x : ℝ ↦ x + A.variableBlockShift perm i) ⁻¹'
        A.realBlockInterval (perm i))) at hrestrict
  rw [hmap, hpre] at hrestrict
  exact hrestrict.symm

def realVariableBlockPermPiece : Option (Fin A.count) → Set ℝ
  | none => A.realBlockUnionᶜ
  | some i => A.realBlockInterval i

theorem iUnion_realVariableBlockPermPiece :
    ⋃ o : Option (Fin A.count), A.realVariableBlockPermPiece o = univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  by_cases hx : x ∈ A.realBlockUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
    exact ⟨some i, hi⟩
  · exact ⟨none, hx⟩

theorem realVariableBlockPermFun_preimage_interval
    (perm : Equiv.Perm (Fin A.count)) (j : Fin A.count) :
    A.realVariableBlockPermFun perm ⁻¹' A.realBlockInterval j =
      (A.permute perm).realBlockInterval (perm.symm j) := by
  ext x
  constructor
  · intro hx
    change A.realVariableBlockPermFun perm x ∈ A.realBlockInterval j at hx
    by_cases hU : x ∈ (A.permute perm).realBlockUnion
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hU
      let i' : Fin A.count := ⟨i, by simpa using i.isLt⟩
      have hii : (i : Fin A.count) = i' := Fin.ext rfl
      have hi' : x ∈ (A.permute perm).realBlockInterval i' := by
        simpa [realBlockInterval, blockEnd, permute, hii] using hi
      have him := A.realVariableBlockPermFun_mem perm i' hi'
      have hij := A.realBlockInterval_eq_of_mem him hx
      have hii : i' = perm.symm j := by
        apply perm.injective
        simpa using hij
      simpa [hii] using hi'
    · rw [A.realVariableBlockPermFun_of_not_mem perm hU] at hx
      have hxU : x ∈ A.realBlockUnion := Set.mem_iUnion.2 ⟨j, hx⟩
      exact False.elim (hU (by rwa [A.realBlockUnion_permute_eq perm]))
  · intro hx
    have him := A.realVariableBlockPermFun_mem perm (perm.symm j) hx
    simpa using him

theorem measurePreserving_realVariableBlockPermMeasurableEquiv
    (perm : Equiv.Perm (Fin A.count)) :
    MeasurePreserving (A.realVariableBlockPermMeasurableEquiv perm) volume volume := by
  refine ⟨(A.realVariableBlockPermMeasurableEquiv perm).measurable, ?_⟩
  apply Measure.ext_of_iUnion_eq_univ A.iUnion_realVariableBlockPermPiece
  intro o
  cases o with
  | some j =>
      rw [(A.realVariableBlockPermMeasurableEquiv perm).restrict_map]
      change Measure.map (A.realVariableBlockPermFun perm)
          (volume.restrict (A.realVariableBlockPermFun perm ⁻¹'
            A.realBlockInterval j)) = volume.restrict (A.realBlockInterval j)
      rw [A.realVariableBlockPermFun_preimage_interval perm j]
      calc
        Measure.map (A.realVariableBlockPermFun perm)
            (volume.restrict ((A.permute perm).realBlockInterval (perm.symm j))) =
            Measure.map (fun x : ℝ ↦
              x + A.variableBlockShift perm (perm.symm j))
              (volume.restrict ((A.permute perm).realBlockInterval (perm.symm j))) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem
            ((A.permute perm).measurableSet_realBlockInterval (perm.symm j))]
            with x hx
          exact A.realVariableBlockPermFun_of_mem perm (perm.symm j) hx
        _ = volume.restrict (A.realBlockInterval (perm (perm.symm j))) :=
          A.map_restrict_realBlockInterval_add_shift perm (perm.symm j)
        _ = volume.restrict (A.realBlockInterval j) := by simp
  | none =>
      rw [(A.realVariableBlockPermMeasurableEquiv perm).restrict_map]
      have hpre : A.realVariableBlockPermFun perm ⁻¹' A.realBlockUnionᶜ =
          (A.permute perm).realBlockUnionᶜ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_compl_iff]
        constructor
        · intro hx hU
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hU
          exact hx (Set.mem_iUnion.2
            ⟨perm i, A.realVariableBlockPermFun_mem perm i hi⟩)
        · intro hx hU
          by_cases hsrc : x ∈ (A.permute perm).realBlockUnion
          · exact hx hsrc
          · rw [A.realVariableBlockPermFun_of_not_mem perm hsrc] at hU
            exact hx (by rwa [A.realBlockUnion_permute_eq perm])
      change Measure.map (A.realVariableBlockPermFun perm)
          (volume.restrict (A.realVariableBlockPermFun perm ⁻¹'
            A.realBlockUnionᶜ)) = volume.restrict A.realBlockUnionᶜ
      rw [hpre]
      calc
        Measure.map (A.realVariableBlockPermFun perm)
            (volume.restrict (A.permute perm).realBlockUnionᶜ) =
            Measure.map id (volume.restrict (A.permute perm).realBlockUnionᶜ) := by
          apply Measure.map_congr
          filter_upwards [ae_restrict_mem
            (A.permute perm).measurableSet_realBlockUnion.compl] with x hx
          simpa using A.realVariableBlockPermFun_of_not_mem perm hx
        _ = volume.restrict (A.permute perm).realBlockUnionᶜ := Measure.map_id
        _ = volume.restrict A.realBlockUnionᶜ := by
          rw [A.realBlockUnion_permute_eq perm]

theorem realBlockInterval_subset_Icc (i : Fin A.count) :
    A.realBlockInterval i ⊆ Icc (0 : ℝ) 1 := by
  intro x hx
  exact ⟨(A.blockStart_nonneg i).trans hx.1,
    hx.2.le.trans (A.blockEnd_le_one i)⟩

theorem realVariableBlockPermFun_mem_Icc
    (perm : Equiv.Perm (Fin A.count)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    A.realVariableBlockPermFun perm x ∈ Icc (0 : ℝ) 1 := by
  by_cases hU : x ∈ (A.permute perm).realBlockUnion
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hU
    exact A.realBlockInterval_subset_Icc (perm i)
      (A.realVariableBlockPermFun_mem perm i hi)
  · simpa [A.realVariableBlockPermFun_of_not_mem perm hU] using hx

theorem realVariableBlockPermInvFun_mem_Icc
    (perm : Equiv.Perm (Fin A.count)) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    A.realVariableBlockPermInvFun perm x ∈ Icc (0 : ℝ) 1 := by
  by_cases hU : x ∈ A.realBlockUnion
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hU
    exact (A.permute perm).realBlockInterval_subset_Icc (perm.symm j)
      (A.realVariableBlockPermInvFun_mem perm j hj)
  · simpa [A.realVariableBlockPermInvFun_of_not_mem perm hU] using hx

theorem realVariableBlockPermFun_preimage_Icc
    (perm : Equiv.Perm (Fin A.count)) :
    A.realVariableBlockPermFun perm ⁻¹' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx
    have hback := A.realVariableBlockPermInvFun_mem_Icc perm hx
    rw [A.realVariableBlockPermFun_leftInverse perm x] at hback
    exact hback
  · exact A.realVariableBlockPermFun_mem_Icc perm

theorem map_restrict_Icc_realVariableBlockPermFun
    (perm : Equiv.Perm (Fin A.count)) :
    Measure.map (A.realVariableBlockPermFun perm)
        (volume.restrict (Icc (0 : ℝ) 1)) =
      volume.restrict (Icc (0 : ℝ) 1) := by
  have hrestrict :=
    (A.realVariableBlockPermMeasurableEquiv perm).restrict_map volume
      (Icc (0 : ℝ) 1)
  change (Measure.map (A.realVariableBlockPermFun perm) volume).restrict
      (Icc (0 : ℝ) 1) =
    Measure.map (A.realVariableBlockPermFun perm)
      (volume.restrict (A.realVariableBlockPermFun perm ⁻¹' Icc (0 : ℝ) 1))
      at hrestrict
  have hmap : Measure.map (A.realVariableBlockPermFun perm) volume = volume := by
    change Measure.map (⇑(A.realVariableBlockPermMeasurableEquiv perm)) volume = volume
    exact (A.measurePreserving_realVariableBlockPermMeasurableEquiv perm).map_eq
  rw [hmap, A.realVariableBlockPermFun_preimage_Icc perm] at hrestrict
  exact hrestrict.symm

/-- The unit-interval interval exchange carrying the permuted block layout
back to the original block labels. -/
def variableBlockPermMeasurableEquiv
    (perm : Equiv.Perm (Fin A.count)) : UnitInterval ≃ᵐ UnitInterval where
  toEquiv :=
    { toFun := fun x ↦ ⟨A.realVariableBlockPermFun perm x,
          A.realVariableBlockPermFun_mem_Icc perm x.property⟩
      invFun := fun x ↦ ⟨A.realVariableBlockPermInvFun perm x,
          A.realVariableBlockPermInvFun_mem_Icc perm x.property⟩
      left_inv := fun x ↦ Subtype.ext
        (A.realVariableBlockPermFun_leftInverse perm x)
      right_inv := fun x ↦ Subtype.ext
        (A.realVariableBlockPermFun_rightInverse perm x) }
  measurable_toFun := by
    exact ((A.measurable_realVariableBlockPermFun perm).comp
      measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    exact ((A.measurable_realVariableBlockPermInvFun perm).comp
      measurable_subtype_coe).subtype_mk

@[simp] theorem coe_variableBlockPermMeasurableEquiv_apply
    (perm : Equiv.Perm (Fin A.count)) (x : UnitInterval) :
    ((A.variableBlockPermMeasurableEquiv perm x : UnitInterval) : ℝ) =
      A.realVariableBlockPermFun perm x := rfl

theorem measurePreserving_variableBlockPermMeasurableEquiv
    (perm : Equiv.Perm (Fin A.count)) :
    MeasurePreserving (A.variableBlockPermMeasurableEquiv perm) volume volume := by
  refine ⟨(A.variableBlockPermMeasurableEquiv perm).measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe
      (A.variableBlockPermMeasurableEquiv perm).measurable]
  change Measure.map
      (A.realVariableBlockPermFun perm ∘ ((↑) : UnitInterval → ℝ)) volume =
    Measure.map ((↑) : UnitInterval → ℝ) volume
  rw [← Measure.map_map (A.measurable_realVariableBlockPermFun perm)
      measurable_subtype_coe,
    unitInterval.measurePreserving_coe.map_eq,
    A.map_restrict_Icc_realVariableBlockPermFun perm]

/-- Explicit graphon relabeling attached to a variable-length block
permutation. -/
def variableBlockPermRelabeling
    (perm : Equiv.Perm (Fin A.count)) : GraphonRelabeling where
  toMeasurableEquiv := A.variableBlockPermMeasurableEquiv perm
  measurePreserving := A.measurePreserving_variableBlockPermMeasurableEquiv perm

theorem permute_cellLeft_add_shift
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count)
    (v : Fin ((A.permute perm).core i).order) :
    (A.permute perm).cellLeft i v + A.variableBlockShift perm i =
      A.cellLeft (perm i) v := by
  simp only [cellLeft, permute_alpha, permute_core, variableBlockShift]
  ring

theorem permute_cellRight_add_shift
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count)
    (v : Fin ((A.permute perm).core i).order) :
    (A.permute perm).cellRight i v + A.variableBlockShift perm i =
      A.cellRight (perm i) v := by
  simp only [cellRight, permute_alpha, permute_core, variableBlockShift]
  ring

/-- Exact action of the interval exchange on every profile cell. -/
theorem variableBlockPermRelabeling_mem_blockCell_iff
    (perm : Equiv.Perm (Fin A.count)) (i : Fin A.count)
    (v : Fin ((A.permute perm).core i).order) (x : UnitInterval) :
    A.variableBlockPermRelabeling perm x ∈ A.blockCell (perm i) v ↔
      x ∈ (A.permute perm).blockCell i v := by
  have hleft := A.permute_cellLeft_add_shift perm i v
  have hright := A.permute_cellRight_add_shift perm i v
  constructor
  · intro hx
    have hxBlock : (A.realVariableBlockPermFun perm x) ∈
        A.realBlockInterval (perm i) := by
      exact A.blockCell_subset_interval (perm i) v hx
    have hpre : (x : ℝ) ∈
        A.realVariableBlockPermFun perm ⁻¹' A.realBlockInterval (perm i) :=
      hxBlock
    rw [A.realVariableBlockPermFun_preimage_interval perm (perm i)] at hpre
    have hsrc : (x : ℝ) ∈
        (A.permute perm).realBlockInterval i := by simpa using hpre
    have hfun := A.realVariableBlockPermFun_of_mem perm i hsrc
    change A.cellLeft (perm i) v ≤ A.realVariableBlockPermFun perm x ∧
      A.realVariableBlockPermFun perm x < A.cellRight (perm i) v at hx
    change (A.permute perm).cellLeft i v ≤ (x : ℝ) ∧
      (x : ℝ) < (A.permute perm).cellRight i v
    rw [hfun] at hx
    constructor <;> linarith
  · intro hx
    have hsrcBlock : (x : ℝ) ∈
        (A.permute perm).realBlockInterval i :=
      (A.permute perm).blockCell_subset_interval i v hx
    have hfun := A.realVariableBlockPermFun_of_mem perm i hsrcBlock
    change (A.permute perm).cellLeft i v ≤ (x : ℝ) ∧
      (x : ℝ) < (A.permute perm).cellRight i v at hx
    change A.cellLeft (perm i) v ≤ A.realVariableBlockPermFun perm x ∧
      A.realVariableBlockPermFun perm x < A.cellRight (perm i) v
    rw [hfun]
    constructor <;> linarith

/-- Pulling the original kernel back along the explicit interval exchange is
pointwise the kernel with lengths and core labels permuted together. -/
theorem kernel_permute_eq_relabel
    (p : ℝ) (perm : Equiv.Perm (Fin A.count)) (z : UnitSquare) :
    (A.permute perm).kernel p z =
      A.kernel p (A.variableBlockPermRelabeling perm z.1,
        A.variableBlockPermRelabeling perm z.2) := by
  classical
  unfold kernel
  rw [← Equiv.sum_comp perm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  simp only [Set.indicator_apply, Set.mem_prod, permute_core]
  rw [A.variableBlockPermRelabeling_mem_blockCell_iff perm i v z.1,
    A.variableBlockPermRelabeling_mem_blockCell_iff perm i w z.2]
  rfl

/-- A variable-length block permutation is exactly graphon relabeling by the
explicit measure-preserving interval exchange above. -/
theorem graphon_permute_eq_relabel
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (perm : Equiv.Perm (Fin A.count)) :
    (A.permute perm).graphon p hp =
      (A.graphon p hp).relabel (A.variableBlockPermRelabeling perm) := by
  apply Graphon.ext
  have hleft := (A.permute perm).graphon_ae_eq_kernel p hp
  have hrel := (A.graphon p hp).relabel_ae_eq_value
    (A.variableBlockPermRelabeling perm)
  have hvalue := (A.variableBlockPermRelabeling perm).measurePreserving_prodEquiv
    |>.quasiMeasurePreserving.ae (A.graphon p hp).value_ae_eq
  have hkernel := (A.variableBlockPermRelabeling perm).measurePreserving_prodEquiv
    |>.quasiMeasurePreserving.ae (A.graphon_ae_eq_kernel p hp)
  filter_upwards [hleft, hrel, hvalue, hkernel]
    with z hzleft hzrel hzvalue hzkernel
  rw [hzleft, hzrel, A.kernel_permute_eq_relabel p perm z]
  exact hzkernel.symm.trans hzvalue.symm

/-- Permuting finitely many variable-length profile blocks costs zero in cut
distance. -/
theorem cutDist_graphon_permute_eq_zero
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (perm : Equiv.Perm (Fin A.count)) :
    cutDist ((A.permute perm).graphon p hp) (A.graphon p hp) = 0 := by
  rw [A.graphon_permute_eq_relabel p hp perm, cutDist_relabel_self]

/-! ## Exact block masses and prefix deletion -/

theorem volume_blockCell (i : Fin A.count) (v : Fin (A.core i).order) :
    volume (A.blockCell i v) =
      ENNReal.ofReal (A.alpha i / (A.core i).order) := by
  rw [blockCell, unitInterval.volume_Ico]
  congr 1
  simp only [cellLeftUI, cellRightUI, cellLeft, cellRight]
  have hr : (((A.core i).order : ℝ)) ≠ 0 := by
    exact_mod_cast (A.core i).order_pos.ne'
  field_simp [hr]
  ring

theorem measureReal_blockCell_prod (i : Fin A.count)
    (v w : Fin (A.core i).order) :
    unitSquareMeasure.real (A.blockCell i v ×ˢ A.blockCell i w) =
      (A.alpha i / (A.core i).order) ^ 2 := by
  change ((volume : Measure UnitInterval).prod (volume : Measure UnitInterval)).real
      (A.blockCell i v ×ˢ A.blockCell i w) = _
  rw [Measure.real, Measure.prod_prod, A.volume_blockCell, A.volume_blockCell,
    pow_two, ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (div_nonneg (A.alpha_nonneg i) (by positivity))]

/-- Kernel contributed by one block of a finite layout. -/
def layoutBlockKernel (p : ℝ) (i : Fin A.count) (z : UnitSquare) : ℝ :=
  ∑ v : Fin (A.core i).order, ∑ w : Fin (A.core i).order,
    (A.blockCell i v ×ˢ A.blockCell i w).indicator
      (fun _ ↦ profileXiMatrix p (A.core i) v w) z

@[fun_prop] theorem measurable_layoutBlockKernel (p : ℝ) (i : Fin A.count) :
    Measurable (A.layoutBlockKernel p i) := by
  unfold layoutBlockKernel
  apply Finset.measurable_sum
  intro v _
  apply Finset.measurable_sum
  intro w _
  exact measurable_const.indicator
    ((A.measurableSet_blockCell i v).prod (A.measurableSet_blockCell i w))

theorem integrable_layoutBlockKernel (p : ℝ) (i : Fin A.count) :
    Integrable (A.layoutBlockKernel p i) unitSquareMeasure := by
  unfold layoutBlockKernel
  apply integrable_finsetSum
  intro v _
  apply integrable_finsetSum
  intro w _
  exact (integrable_const _).indicator
    ((A.measurableSet_blockCell i v).prod (A.measurableSet_blockCell i w))

theorem layoutBlockKernel_nonneg {p : ℝ} (hp : 0 ≤ p)
    (i : Fin A.count) (z : UnitSquare) :
    0 ≤ A.layoutBlockKernel p i z := by
  classical
  unfold layoutBlockKernel
  apply Finset.sum_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro w _
  rw [Set.indicator_apply]
  split
  · exact profileXiMatrix_nonneg hp _ _ _
  · exact le_rfl

theorem kernel_eq_sum_layoutBlockKernel (p : ℝ) (z : UnitSquare) :
    A.kernel p z = ∑ i, A.layoutBlockKernel p i z := rfl

/-- Integral of one layout block before the regular-core row sum is used. -/
theorem integral_layoutBlockKernel_raw (p : ℝ) (i : Fin A.count) :
    ∫ z : UnitSquare, A.layoutBlockKernel p i z ∂unitSquareMeasure =
      (A.alpha i / (A.core i).order) ^ 2 *
        ∑ v : Fin (A.core i).order, ∑ w : Fin (A.core i).order,
          profileXiMatrix p (A.core i) v w := by
  simpa only [layoutBlockKernel, A.measureReal_blockCell_prod, Finset.mul_sum] using
    integral_doubleSum_cellIndicators (A.blockCell i) (A.blockCell i)
      (A.measurableSet_blockCell i) (A.measurableSet_blockCell i)
      (profileXiMatrix p (A.core i))

/-- Exact `L¹` mass of one profile block. -/
theorem integral_layoutBlockKernel (p : ℝ) (i : Fin A.count) :
    ∫ z : UnitSquare, A.layoutBlockKernel p i z ∂unitSquareMeasure =
      A.alpha i ^ 2 *
        (1 + ((k - 2 : ℕ) : ℝ) * p) / (A.core i).order := by
  rw [A.integral_layoutBlockKernel_raw p i, sum_profileXiMatrix]
  have hr : (((A.core i).order : ℝ)) ≠ 0 := by
    exact_mod_cast (A.core i).order_pos.ne'
  field_simp [hr]

/-! ## Literal finite prefixes -/

/-- Retain the first `N` blocks as a standalone packed layout. -/
def take (N : ℕ) (hN : N ≤ A.count) : FiniteProfileBlockLayout k where
  count := N
  alpha := fun i ↦ A.alpha (Fin.castLE hN i)
  core := fun i ↦ A.core (Fin.castLE hN i)
  alpha_nonneg := fun i ↦ A.alpha_nonneg (Fin.castLE hN i)
  sum_alpha_le_one := by
    calc
      ∑ i : Fin N, A.alpha (Fin.castLE hN i) =
          ∑ i : Fin N, A.alphaNat i := by
        apply Finset.sum_congr rfl
        intro i _
        exact (A.alphaNat_of_lt (i.isLt.trans_le hN)).symm
      _ = A.blockStart N := by
        rw [Fin.sum_univ_eq_sum_range]
        rfl
      _ ≤ A.blockStart A.count := A.blockStart_mono hN
      _ ≤ 1 := A.blockStart_count_le_one

@[simp] theorem take_count (N : ℕ) (hN : N ≤ A.count) :
    (A.take N hN).count = N := rfl

@[simp] theorem take_alpha (N : ℕ) (hN : N ≤ A.count) (i : Fin N) :
    (A.take N hN).alpha i = A.alpha (Fin.castLE hN i) := rfl

@[simp] theorem take_core (N : ℕ) (hN : N ≤ A.count) (i : Fin N) :
    (A.take N hN).core i = A.core (Fin.castLE hN i) := rfl

theorem take_blockStart (N : ℕ) (hN : N ≤ A.count)
    {i : ℕ} (hi : i ≤ N) :
    (A.take N hN).blockStart i = A.blockStart i := by
  unfold blockStart
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j < i := Finset.mem_range.mp hj
  have hjN : j < N := hji.trans_le hi
  rw [(A.take N hN).alphaNat_of_lt hjN,
    A.alphaNat_of_lt (hjN.trans_le hN)]
  rfl

theorem take_blockCell (N : ℕ) (hN : N ≤ A.count) (i : Fin N)
    (v : Fin (A.core (Fin.castLE hN i)).order) :
    (A.take N hN).blockCell i v =
      A.blockCell (Fin.castLE hN i) v := by
  have hs := A.take_blockStart N hN i.isLt.le
  have hs' : (A.take N hN).blockStart i =
      A.blockStart (Fin.castLE hN i) := by
    simpa only [Fin.val_castLE] using hs
  unfold blockCell cellLeftUI cellRightUI cellLeft cellRight
  simp only [take_alpha, take_core]
  congr 1 <;> apply Subtype.ext <;> simp only [hs']

theorem take_layoutBlockKernel (p : ℝ) (N : ℕ)
    (hN : N ≤ A.count) (i : Fin N) (z : UnitSquare) :
    (A.take N hN).layoutBlockKernel p i z =
      A.layoutBlockKernel p (Fin.castLE hN i) z := by
  classical
  unfold layoutBlockKernel
  simp only [take_core]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [A.take_blockCell N hN i v, A.take_blockCell N hN i w]

/-- Keep exactly the blocks of rank below `N`, in their existing packed
coordinates. -/
def prefixKernel (p : ℝ) (N : ℕ) (z : UnitSquare) : ℝ :=
  ∑ i : Fin A.count,
    if (i : ℕ) < N then A.layoutBlockKernel p i z else 0

theorem take_kernel_eq_prefixKernel (p : ℝ) (N : ℕ)
    (hN : N ≤ A.count) (z : UnitSquare) :
    (A.take N hN).kernel p z = A.prefixKernel p N z := by
  classical
  rw [(A.take N hN).kernel_eq_sum_layoutBlockKernel]
  unfold prefixKernel
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun i _ ↦ Fin.castLE hN i)
  · intro i _
    simp
  · intro i _ j _ hij
    exact Fin.castLE_injective hN hij
  · intro j hj
    have hjN : (j : ℕ) < N := by simpa using hj
    refine ⟨⟨j, hjN⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro i _
    exact A.take_layoutBlockKernel p N hN i z

/-- Kernel discarded when ranks `N,N+1,…` are deleted. -/
def omittedKernel (p : ℝ) (N : ℕ) (z : UnitSquare) : ℝ :=
  ∑ i : Fin A.count,
    if N ≤ (i : ℕ) then A.layoutBlockKernel p i z else 0

@[fun_prop] theorem measurable_prefixKernel (p : ℝ) (N : ℕ) :
    Measurable (A.prefixKernel p N) := by
  unfold prefixKernel
  apply Finset.measurable_sum
  intro i _
  by_cases hi : (i : ℕ) < N
  · simp [hi, A.measurable_layoutBlockKernel p i]
  · simp [hi]

theorem prefixKernel_nonneg {p : ℝ} (hp : 0 ≤ p) (N : ℕ)
    (z : UnitSquare) : 0 ≤ A.prefixKernel p N z := by
  classical
  unfold prefixKernel
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact A.layoutBlockKernel_nonneg hp i z
  · exact le_rfl

theorem prefixKernel_le_kernel {p : ℝ} (hp : 0 ≤ p) (N : ℕ)
    (z : UnitSquare) : A.prefixKernel p N z ≤ A.kernel p z := by
  rw [A.kernel_eq_sum_layoutBlockKernel]
  unfold prefixKernel
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact A.layoutBlockKernel_nonneg hp i z

theorem prefixKernel_le_one {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (N : ℕ) (z : UnitSquare) : A.prefixKernel p N z ≤ 1 :=
  (A.prefixKernel_le_kernel hp.1 N z).trans (A.kernel_le_one hp.2 z)

theorem prefixKernel_symm (p : ℝ) (N : ℕ) (z : UnitSquare) :
    A.prefixKernel p N (z.2, z.1) = A.prefixKernel p N z := by
  classical
  unfold prefixKernel layoutBlockKernel
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    rw [(profileXiMatrix_isSymm p (A.core i)).apply]
    simp [Set.indicator_apply, and_comm]
  · rfl

theorem integrable_prefixKernel {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (N : ℕ) : Integrable (A.prefixKernel p N) unitSquareMeasure := by
  apply Integrable.of_bound (A.measurable_prefixKernel p N).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (A.prefixKernel_nonneg hp.1 N z)]
  exact A.prefixKernel_le_one hp N z

/-- Canonical graphon after deleting all ranks at least `N`.  For `N=0`
this is the zero graphon. -/
def prefixGraphon (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (N : ℕ) : Graphon :=
  Graphon.ofFun (A.prefixKernel p N) (A.integrable_prefixKernel hp N)
    (ae_of_all _ (A.prefixKernel_nonneg hp.1 N))
    (ae_of_all _ (A.prefixKernel_le_one hp N))
    (A.prefixKernel_symm p N)

theorem prefixGraphon_ae_eq_prefixKernel
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    ∀ᵐ z ∂unitSquareMeasure,
      A.prefixGraphon p hp N z = A.prefixKernel p N z :=
  Graphon.coe_ofFun _ _ _ _ _

/-- The raw prefix graphon is exactly the graphon of the standalone prefix
layout. -/
theorem prefixGraphon_eq_graphon_take
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (N : ℕ)
    (hN : N ≤ A.count) :
    A.prefixGraphon p hp N = (A.take N hN).graphon p hp := by
  apply Graphon.ext
  filter_upwards [A.prefixGraphon_ae_eq_prefixKernel p hp N,
    (A.take N hN).graphon_ae_eq_kernel p hp] with z hzP hzT
  rw [hzP, hzT, A.take_kernel_eq_prefixKernel p N hN z]

theorem kernel_eq_prefixKernel_add_omittedKernel
    (p : ℝ) (N : ℕ) (z : UnitSquare) :
    A.kernel p z = A.prefixKernel p N z + A.omittedKernel p N z := by
  rw [A.kernel_eq_sum_layoutBlockKernel]
  unfold prefixKernel omittedKernel
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : (i : ℕ) < N
  · simp [hi, Nat.not_le_of_lt hi]
  · simp [hi, Nat.le_of_not_gt hi]

theorem omittedKernel_nonneg {p : ℝ} (hp : 0 ≤ p) (N : ℕ)
    (z : UnitSquare) : 0 ≤ A.omittedKernel p N z := by
  classical
  unfold omittedKernel
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact A.layoutBlockKernel_nonneg hp i z
  · exact le_rfl

/-- Exact fixed-coordinate `L¹` cost of deleting every block of rank at
least `N`. -/
theorem graphonL1Dist_prefixGraphon_eq_sum_omittedBlockMass
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    graphonL1Dist (A.graphon p hp) (A.prefixGraphon p hp N) =
      ∑ i : Fin A.count, if N ≤ (i : ℕ) then
        A.alpha i ^ 2 * (1 + ((k - 2 : ℕ) : ℝ) * p) /
          (A.core i).order else 0 := by
  rw [graphonL1Dist_eq_integral]
  calc
    (∫ z, |A.graphon p hp z - A.prefixGraphon p hp N z|
        ∂unitSquareMeasure) =
        ∫ z, A.omittedKernel p N z ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [A.graphon_ae_eq_kernel p hp,
        A.prefixGraphon_ae_eq_prefixKernel p hp N] with z hz hzp
      rw [hz, hzp, A.kernel_eq_prefixKernel_add_omittedKernel p N z]
      simp [abs_of_nonneg (A.omittedKernel_nonneg hp.1 N z)]
    _ = _ := by
      unfold omittedKernel
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i _
        split_ifs with hi
        · exact A.integral_layoutBlockKernel p i
        · simp
      · intro i _
        split_ifs
        · exact A.integrable_layoutBlockKernel p i
        · simpa using
            (integrable_zero (measure := unitSquareMeasure) ℝ)

/-- Coarse deletion bound independent of core orders and of the profile
value. -/
theorem graphonL1Dist_prefixGraphon_le_sum_omittedSquares
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    graphonL1Dist (A.graphon p hp) (A.prefixGraphon p hp N) ≤
      ∑ i : Fin A.count, if N ≤ (i : ℕ) then A.alpha i ^ 2 else 0 := by
  rw [A.graphonL1Dist_prefixGraphon_eq_sum_omittedBlockMass p hp N]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · have hnum : 1 + ((k - 2 : ℕ) : ℝ) * p ≤
        ((k - 1 : ℕ) : ℝ) := by
      have hd : 0 ≤ ((k - 2 : ℕ) : ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hp.2 hd
      calc
        1 + ((k - 2 : ℕ) : ℝ) * p ≤
            1 + ((k - 2 : ℕ) : ℝ) * 1 := by linarith
        _ = ((k - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (show 2 ≤ k by omega),
            Nat.cast_sub (show 1 ≤ k by omega)]
          ring
    have horder : ((k - 1 : ℕ) : ℝ) ≤ (A.core i).order := by
      exact_mod_cast RegularBlockCore.k_sub_one_le_order hk (A.core i)
    have hratio : (1 + ((k - 2 : ℕ) : ℝ) * p) /
        (A.core i).order ≤ 1 := by
      apply (div_le_one (by exact_mod_cast (A.core i).order_pos)).2
      exact hnum.trans horder
    have hratio0 : 0 ≤ (1 + ((k - 2 : ℕ) : ℝ) * p) /
        (A.core i).order := by
      exact div_nonneg (add_nonneg zero_le_one
        (mul_nonneg (by positivity) hp.1)) (by positivity)
    calc
      A.alpha i ^ 2 * (1 + ((k - 2 : ℕ) : ℝ) * p) /
          (A.core i).order = A.alpha i ^ 2 *
            ((1 + ((k - 2 : ℕ) : ℝ) * p) / (A.core i).order) := by ring
      _ ≤ A.alpha i ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ = A.alpha i ^ 2 := by ring
  · exact le_rfl

/-- A block whose core order is large has uniformly small `L¹` mass. -/
theorem omittedBlockMass_le_k_sub_one_div_order
    (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (i : Fin A.count) :
    A.alpha i ^ 2 * (1 + ((k - 2 : ℕ) : ℝ) * p) /
        (A.core i).order ≤
      ((k - 1 : ℕ) : ℝ) / (A.core i).order := by
  have ha : A.alpha i ^ 2 ≤ 1 := by
    have hai : A.alpha i ≤ 1 := by
      calc
        A.alpha i ≤ ∑ j, A.alpha j := by
          exact Finset.single_le_sum (fun j _ ↦ A.alpha_nonneg j) (Finset.mem_univ i)
        _ ≤ 1 := A.sum_alpha_le_one
    nlinarith [A.alpha_nonneg i]
  have hnum : 1 + ((k - 2 : ℕ) : ℝ) * p ≤
      ((k - 1 : ℕ) : ℝ) := by
    have hd : 0 ≤ ((k - 2 : ℕ) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hp.2 hd
    calc
      1 + ((k - 2 : ℕ) : ℝ) * p ≤
          1 + ((k - 2 : ℕ) : ℝ) * 1 := by linarith
      _ = ((k - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (show 2 ≤ k by omega),
          Nat.cast_sub (show 1 ≤ k by omega)]
        ring
  have hnum0 : 0 ≤ 1 + ((k - 2 : ℕ) : ℝ) * p :=
    add_nonneg zero_le_one (mul_nonneg (by positivity) hp.1)
  have hprod : A.alpha i ^ 2 *
      (1 + ((k - 2 : ℕ) : ℝ) * p) ≤ ((k - 1 : ℕ) : ℝ) := by
    calc
      A.alpha i ^ 2 * (1 + ((k - 2 : ℕ) : ℝ) * p) ≤
          1 * (1 + ((k - 2 : ℕ) : ℝ) * p) :=
        mul_le_mul_of_nonneg_right ha hnum0
      _ ≤ ((k - 1 : ℕ) : ℝ) := by simpa using hnum
  exact div_le_div_of_nonneg_right hprod (by positivity)

/-! ## Fixed-core continuity under moving block lengths -/

/-- Total movement of all cell endpoints for two length vectors carrying
the same literal core list. -/
def fixedCoreEndpointError {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) : ℝ :=
  ∑ i : Fin q, ∑ v : Fin (C i).order,
    (|(a.layout C).cellLeft i v - (b.layout C).cellLeft i v| +
      |(a.layout C).cellRight i v - (b.layout C).cellRight i v|)

/-- One-dimensional cells on which two fixed-core layouts disagree. -/
def fixedCoreCellDisagreement {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) : Set UnitInterval :=
  ⋃ i : Fin q, ⋃ v : Fin (C i).order,
    (a.layout C).blockCell i v ∆ (b.layout C).blockCell i v

@[measurability] theorem measurableSet_fixedCoreCellDisagreement {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) :
    MeasurableSet (fixedCoreCellDisagreement a b C) := by
  exact MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun v ↦
    ((a.layout C).measurableSet_blockCell i v).symmDiff
      ((b.layout C).measurableSet_blockCell i v)

theorem measureReal_fixedCoreCellDisagreement_le_endpointError {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) :
    volume.real (fixedCoreCellDisagreement a b C) ≤
      fixedCoreEndpointError a b C := by
  calc
    volume.real (fixedCoreCellDisagreement a b C) ≤
        ∑ i : Fin q, volume.real (⋃ v : Fin (C i).order,
          (a.layout C).blockCell i v ∆ (b.layout C).blockCell i v) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin q, ∑ v : Fin (C i).order,
          volume.real ((a.layout C).blockCell i v ∆
            (b.layout C).blockCell i v) := by
      exact Finset.sum_le_sum fun i _ ↦ measureReal_iUnion_fintype_le _
    _ ≤ ∑ i : Fin q, ∑ v : Fin (C i).order,
          (|(a.layout C).cellLeft i v - (b.layout C).cellLeft i v| +
            |(a.layout C).cellRight i v - (b.layout C).cellRight i v|) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro v _
      simpa only [blockCell, cellLeftUI, cellRightUI] using
        measureReal_Ico_symmDiff_le
          ((a.layout C).cellLeftUI i v) ((a.layout C).cellRightUI i v)
          ((b.layout C).cellLeftUI i v) ((b.layout C).cellRightUI i v)
    _ = fixedCoreEndpointError a b C := rfl

def fixedCoreDisagreementSquare {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) : Set UnitSquare :=
  (fixedCoreCellDisagreement a b C ×ˢ univ) ∪
    (univ ×ˢ fixedCoreCellDisagreement a b C)

@[measurability] theorem measurableSet_fixedCoreDisagreementSquare {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) :
    MeasurableSet (fixedCoreDisagreementSquare a b C) :=
  ((measurableSet_fixedCoreCellDisagreement a b C).prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod (measurableSet_fixedCoreCellDisagreement a b C))

theorem measureReal_fixedCoreDisagreementSquare_le {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) :
    unitSquareMeasure.real (fixedCoreDisagreementSquare a b C) ≤
      2 * fixedCoreEndpointError a b C := by
  calc
    unitSquareMeasure.real (fixedCoreDisagreementSquare a b C) ≤
        2 * volume.real (fixedCoreCellDisagreement a b C) := by
      unfold fixedCoreDisagreementSquare
      calc
        unitSquareMeasure.real
            ((fixedCoreCellDisagreement a b C ×ˢ univ) ∪
              (univ ×ˢ fixedCoreCellDisagreement a b C)) ≤
            unitSquareMeasure.real
                (fixedCoreCellDisagreement a b C ×ˢ univ) +
              unitSquareMeasure.real
                (univ ×ˢ fixedCoreCellDisagreement a b C) :=
          measureReal_union_le _ _
        _ = 2 * volume.real (fixedCoreCellDisagreement a b C) := by
          rw [measureReal_prod_prod, measureReal_prod_prod]
          simp [Measure.real]
          ring
    _ ≤ 2 * fixedCoreEndpointError a b C := by
      gcongr
      exact measureReal_fixedCoreCellDisagreement_le_endpointError a b C

theorem fixedCore_mem_blockCell_iff_of_not_mem_disagreement {q : ℕ}
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) (x : UnitInterval)
    (hx : x ∉ fixedCoreCellDisagreement a b C)
    (i : Fin q) (v : Fin (C i).order) :
    x ∈ (a.layout C).blockCell i v ↔
      x ∈ (b.layout C).blockCell i v := by
  have hnot : x ∉ (a.layout C).blockCell i v ∆
      (b.layout C).blockCell i v := by
    intro hv
    exact hx (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨v, hv⟩⟩)
  rw [Set.mem_symmDiff] at hnot
  tauto

theorem fixedCore_kernel_eq_of_not_mem_disagreement {q : ℕ}
    (p : ℝ) (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) (z : UnitSquare)
    (hx : z.1 ∉ fixedCoreCellDisagreement a b C)
    (hy : z.2 ∉ fixedCoreCellDisagreement a b C) :
    (a.layout C).kernel p z = (b.layout C).kernel p z := by
  classical
  unfold kernel
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  simp only [Set.indicator_apply, Set.mem_prod]
  rw [fixedCore_mem_blockCell_iff_of_not_mem_disagreement a b C z.1 hx i v,
    fixedCore_mem_blockCell_iff_of_not_mem_disagreement a b C z.2 hy i w]
  rfl

/-- Explicit `L¹` modulus for a fixed finite list of cores under changes
of the block lengths. -/
theorem graphonL1Dist_fixedCoreLayouts_le_endpointError {q : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (a b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k) :
    graphonL1Dist ((a.layout C).graphon p hp) ((b.layout C).graphon p hp) ≤
      2 * fixedCoreEndpointError a b C := by
  rw [graphonL1Dist_eq_integral]
  let D := fixedCoreDisagreementSquare a b C
  have hD : MeasurableSet D := measurableSet_fixedCoreDisagreementSquare a b C
  calc
    (∫ z, |(a.layout C).graphon p hp z - (b.layout C).graphon p hp z|
        ∂unitSquareMeasure) ≤
        ∫ z, D.indicator (fun _ ↦ (1 : ℝ)) z ∂unitSquareMeasure := by
      apply integral_mono_ae
      · exact ((a.layout C).graphon p hp).integrable.sub
          ((b.layout C).graphon p hp).integrable |>.abs
      · exact (integrable_const (1 : ℝ)).indicator hD
      filter_upwards [(a.layout C).graphon_ae_eq_kernel p hp,
        (b.layout C).graphon_ae_eq_kernel p hp,
        ((a.layout C).graphon p hp).ae_mem_Icc,
        ((b.layout C).graphon p hp).ae_mem_Icc]
        with z hza hzb hba hbb
      rcases hba with ⟨hba0, hba1⟩
      rcases hbb with ⟨hbb0, hbb1⟩
      by_cases hz : z ∈ D
      · rw [Set.indicator_of_mem hz]
        rw [abs_le]
        constructor <;> linarith
      · rw [Set.indicator_of_notMem hz]
        have hx : z.1 ∉ fixedCoreCellDisagreement a b C := by
          intro hx
          exact hz (Or.inl ⟨hx, Set.mem_univ _⟩)
        have hy : z.2 ∉ fixedCoreCellDisagreement a b C := by
          intro hy
          exact hz (Or.inr ⟨Set.mem_univ _, hy⟩)
        rw [hza, hzb, fixedCore_kernel_eq_of_not_mem_disagreement
          p a b C z hx hy]
        simp
    _ = unitSquareMeasure.real D := by
      rw [integral_indicator_const (1 : ℝ) hD]
      simp
    _ ≤ 2 * fixedCoreEndpointError a b C :=
      measureReal_fixedCoreDisagreementSquare_le a b C

theorem fixedCore_blockStart_tendsto {q : ℕ}
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i)))
    (i : Fin q) :
    Tendsto (fun n ↦ ((a n).layout C).blockStart i) atTop
      (nhds ((b.layout C).blockStart i)) := by
  unfold blockStart
  apply tendsto_finset_sum
  intro j hj
  have hjq : j < q := (Finset.mem_range.mp hj).trans i.isLt
  simpa [alphaNat, FiniteProfileBlockLengths.layout, hjq] using hα ⟨j, hjq⟩

theorem fixedCore_cellLeft_tendsto {q : ℕ}
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i)))
    (i : Fin q) (v : Fin (C i).order) :
    Tendsto (fun n ↦ ((a n).layout C).cellLeft i v) atTop
      (nhds ((b.layout C).cellLeft i v)) := by
  simpa [cellLeft] using
    (fixedCore_blockStart_tendsto a b C hα i).add
      ((hα i).mul_const ((v : ℝ) / (C i).order))

theorem fixedCore_cellRight_tendsto {q : ℕ}
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i)))
    (i : Fin q) (v : Fin (C i).order) :
    Tendsto (fun n ↦ ((a n).layout C).cellRight i v) atTop
      (nhds ((b.layout C).cellRight i v)) := by
  simpa [cellRight] using
    (fixedCore_blockStart_tendsto a b C hα i).add
      ((hα i).mul_const ((((v : ℕ) + 1 : ℝ) / (C i).order)))

theorem fixedCoreEndpointError_tendsto_zero {q : ℕ}
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i))) :
    Tendsto (fun n ↦ fixedCoreEndpointError (a n) b C) atTop (nhds 0) := by
  unfold fixedCoreEndpointError
  have hterm (i : Fin q) (v : Fin (C i).order) :
      Tendsto (fun n ↦
        |((a n).layout C).cellLeft i v - (b.layout C).cellLeft i v| +
          |((a n).layout C).cellRight i v - (b.layout C).cellRight i v|)
        atTop (nhds 0) := by
    have hleft := (fixedCore_cellLeft_tendsto a b C hα i v).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ (b.layout C).cellLeft i v) atTop
        (nhds ((b.layout C).cellLeft i v)))
    have hright := (fixedCore_cellRight_tendsto a b C hα i v).sub
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ ↦ (b.layout C).cellRight i v) atTop
        (nhds ((b.layout C).cellRight i v)))
    simpa using hleft.abs.add hright.abs
  have hrow (i : Fin q) :
      Tendsto (fun n ↦ ∑ v : Fin (C i).order,
        (|((a n).layout C).cellLeft i v - (b.layout C).cellLeft i v| +
          |((a n).layout C).cellRight i v - (b.layout C).cellRight i v|))
        atTop (nhds 0) := by
    simpa using tendsto_finset_sum Finset.univ (fun v _ ↦ hterm i v)
  simpa using tendsto_finset_sum Finset.univ (fun i _ ↦ hrow i)

/-- Fixed finite layouts with literally fixed cores are continuous in `L¹`
under coordinatewise convergence of their block lengths. -/
theorem graphonL1Dist_fixedCoreLayouts_tendsto_zero {q : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i))) :
    Tendsto (fun n ↦ graphonL1Dist ((a n).layout C |>.graphon p hp)
      ((b.layout C).graphon p hp)) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun n ↦ graphonL1Dist_nonneg _ _
  · exact fun n ↦ graphonL1Dist_fixedCoreLayouts_le_endpointError
      p hp (a n) b C
  · simpa using (tendsto_const_nhds.mul
      (fixedCoreEndpointError_tendsto_zero a b C hα) :
        Tendsto (fun n ↦ 2 * fixedCoreEndpointError (a n) b C)
          atTop (nhds (2 * 0)))

theorem cutDist_fixedCoreLayouts_tendsto_zero {q : ℕ}
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1)
    (a : ℕ → FiniteProfileBlockLengths q)
    (b : FiniteProfileBlockLengths q)
    (C : Fin q → RegularBlockCore k)
    (hα : ∀ i, Tendsto (fun n ↦ (a n).alpha i) atTop (nhds (b.alpha i))) :
    Tendsto (fun n ↦ cutDist ((a n).layout C |>.graphon p hp)
      ((b.layout C).graphon p hp)) atTop (nhds 0) := by
  apply squeeze_zero
  · exact fun n ↦ cutDist_nonneg _ _
  · exact fun n ↦ cutDist_le_graphonL1Dist _ _
  · exact graphonL1Dist_fixedCoreLayouts_tendsto_zero p hp a b C hα

/-! ## A first-block estimate against the full fixed-core graphon -/

/-- The one-dimensional set on which the cells of the first packed block
and the full equal-cell partition can disagree. -/
def firstBlockCellDisagreement (hcount : 0 < A.count) : Set UnitInterval :=
  ⋃ v : Fin (A.core ⟨0, hcount⟩).order,
    A.blockCell ⟨0, hcount⟩ v ∆ equalCell v

@[measurability] theorem measurableSet_firstBlockCellDisagreement
    (hcount : 0 < A.count) :
    MeasurableSet (A.firstBlockCellDisagreement hcount) := by
  exact MeasurableSet.iUnion fun v ↦
    (A.measurableSet_blockCell ⟨0, hcount⟩ v).symmDiff
      (measurableSet_equalCell v)

theorem measureReal_firstBlockCell_symmDiff_le
    (hcount : 0 < A.count) (v : Fin (A.core ⟨0, hcount⟩).order) :
    volume.real (A.blockCell ⟨0, hcount⟩ v ∆ equalCell v) ≤
      2 * (1 - A.alpha ⟨0, hcount⟩) := by
  let i : Fin A.count := ⟨0, hcount⟩
  have ha0 : 0 ≤ A.alpha i := A.alpha_nonneg i
  have ha1 : A.alpha i ≤ 1 := A.alpha_le_one i
  have hr : (0 : ℝ) < (A.core i).order := by
    exact_mod_cast (A.core i).order_pos
  have hv0 : 0 ≤ (v : ℝ) / (A.core i).order := by positivity
  have hv1 : (v : ℝ) / (A.core i).order ≤ 1 := by
    rw [div_le_one hr]
    exact_mod_cast v.isLt.le
  have hsv0 : 0 ≤ (((v : ℕ) + 1 : ℝ) / (A.core i).order) := by positivity
  have hsv1 : (((v : ℕ) + 1 : ℝ) / (A.core i).order) ≤ 1 := by
    rw [div_le_one hr]
    exact_mod_cast v.isLt
  rw [blockCell, equalCell]
  refine (measureReal_Ico_symmDiff_le _ _ _ _).trans ?_
  simp only [cellLeftUI, cellRightUI, cellLeft, cellRight, equalCellLeft,
    equalCellRight, i]
  rw [A.blockStart_zero]
  have hleftNonpos :
      A.alpha i * ((v : ℝ) / (A.core i).order) -
        (v : ℝ) / (A.core i).order ≤ 0 := by nlinarith
  have hrightNonpos :
      A.alpha i * (((v : ℕ) + 1 : ℝ) / (A.core i).order) -
        ((v : ℕ) + 1 : ℝ) / (A.core i).order ≤ 0 := by nlinarith
  have hleftNonpos' :
      0 + A.alpha ⟨0, hcount⟩ *
          ((v : ℝ) / (A.core ⟨0, hcount⟩).order) -
        (v : ℝ) / (A.core ⟨0, hcount⟩).order ≤ 0 := by
    simpa [i] using hleftNonpos
  have hrightNonpos' :
      0 + A.alpha ⟨0, hcount⟩ *
          (((v : ℕ) + 1 : ℝ) / (A.core ⟨0, hcount⟩).order) -
        ((v : ℕ) + 1 : ℝ) / (A.core ⟨0, hcount⟩).order ≤ 0 := by
    simpa [i] using hrightNonpos
  rw [abs_of_nonpos hleftNonpos', abs_of_nonpos hrightNonpos']
  nlinarith

/-- The total one-dimensional mismatch of the first block is controlled by
its missing length. -/
theorem measureReal_firstBlockCellDisagreement_le
    (hcount : 0 < A.count) :
    volume.real (A.firstBlockCellDisagreement hcount) ≤
      2 * ((A.core ⟨0, hcount⟩).order : ℝ) *
        (1 - A.alpha ⟨0, hcount⟩) := by
  calc
    volume.real (A.firstBlockCellDisagreement hcount) ≤
        ∑ v : Fin (A.core ⟨0, hcount⟩).order,
          volume.real (A.blockCell ⟨0, hcount⟩ v ∆ equalCell v) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _v : Fin (A.core ⟨0, hcount⟩).order,
          2 * (1 - A.alpha ⟨0, hcount⟩) := by
      exact Finset.sum_le_sum fun v _ ↦
        A.measureReal_firstBlockCell_symmDiff_le hcount v
    _ = 2 * ((A.core ⟨0, hcount⟩).order : ℝ) *
          (1 - A.alpha ⟨0, hcount⟩) := by
      simp
      ring

def firstBlockDisagreementSquare (hcount : 0 < A.count) : Set UnitSquare :=
  (A.firstBlockCellDisagreement hcount ×ˢ univ) ∪
    (univ ×ˢ A.firstBlockCellDisagreement hcount)

@[measurability] theorem measurableSet_firstBlockDisagreementSquare
    (hcount : 0 < A.count) :
    MeasurableSet (A.firstBlockDisagreementSquare hcount) :=
  ((A.measurableSet_firstBlockCellDisagreement hcount).prod MeasurableSet.univ).union
    (MeasurableSet.univ.prod
      (A.measurableSet_firstBlockCellDisagreement hcount))

theorem measureReal_firstBlockDisagreementSquare_le
    (hcount : 0 < A.count) :
    unitSquareMeasure.real (A.firstBlockDisagreementSquare hcount) ≤
      2 * volume.real (A.firstBlockCellDisagreement hcount) := by
  unfold firstBlockDisagreementSquare
  calc
    unitSquareMeasure.real
        ((A.firstBlockCellDisagreement hcount ×ˢ univ) ∪
          (univ ×ˢ A.firstBlockCellDisagreement hcount)) ≤
        unitSquareMeasure.real
            (A.firstBlockCellDisagreement hcount ×ˢ univ) +
          unitSquareMeasure.real
            (univ ×ˢ A.firstBlockCellDisagreement hcount) :=
      measureReal_union_le _ _
    _ = 2 * volume.real (A.firstBlockCellDisagreement hcount) := by
      rw [measureReal_prod_prod, measureReal_prod_prod]
      simp [Measure.real]
      ring

theorem mem_blockCell_iff_mem_equalCell_of_not_mem_firstDisagreement
    (hcount : 0 < A.count) (x : UnitInterval)
    (hx : x ∉ A.firstBlockCellDisagreement hcount)
    (v : Fin (A.core ⟨0, hcount⟩).order) :
    x ∈ A.blockCell ⟨0, hcount⟩ v ↔ x ∈ equalCell v := by
  have hnot : x ∉ A.blockCell ⟨0, hcount⟩ v ∆ equalCell v := by
    intro hv
    exact hx (Set.mem_iUnion.2 ⟨v, hv⟩)
  rw [Set.mem_symmDiff] at hnot
  tauto

theorem prefixKernel_one_eq_matrixKernel_of_not_mem_firstDisagreement
    (p : ℝ) (hcount : 0 < A.count) (z : UnitSquare)
    (hx : z.1 ∉ A.firstBlockCellDisagreement hcount)
    (hy : z.2 ∉ A.firstBlockCellDisagreement hcount) :
    A.prefixKernel p 1 z =
      matrixKernel (profileXiMatrix p (A.core ⟨0, hcount⟩)) z := by
  classical
  let i : Fin A.count := ⟨0, hcount⟩
  unfold prefixKernel
  rw [Finset.sum_eq_single i]
  · simp only [i, Fin.val_zero, Nat.zero_lt_one, if_true]
    unfold layoutBlockKernel matrixKernel
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    simp only [Set.indicator_apply, Set.mem_prod]
    rw [A.mem_blockCell_iff_mem_equalCell_of_not_mem_firstDisagreement
        hcount z.1 hx v,
      A.mem_blockCell_iff_mem_equalCell_of_not_mem_firstDisagreement
        hcount z.2 hy w]
  · intro j _ hji
    have hj : ¬(j : ℕ) < 1 := by
      intro hj
      apply hji
      apply Fin.ext
      change (j : ℕ) = 0
      omega
    simp [hj]
  · simp

/-- A first packed block of length `α` differs from its full fixed-core
equal-cell graphon by at most `4 r (1-α)` in fixed-coordinate `L¹`. -/
theorem graphonL1Dist_prefixGraphon_one_profileXiGraphon_le
    (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) (hcount : 0 < A.count) :
    graphonL1Dist (A.prefixGraphon p hp 1)
        (profileXiGraphon p (A.core ⟨0, hcount⟩) hp) ≤
      4 * ((A.core ⟨0, hcount⟩).order : ℝ) *
        (1 - A.alpha ⟨0, hcount⟩) := by
  rw [graphonL1Dist_eq_integral]
  let D := A.firstBlockDisagreementSquare hcount
  have hD : MeasurableSet D := A.measurableSet_firstBlockDisagreementSquare hcount
  have hmajor :
      (∫ z, |A.prefixGraphon p hp 1 z -
          profileXiGraphon p (A.core ⟨0, hcount⟩) hp z|
          ∂unitSquareMeasure) ≤ unitSquareMeasure.real D := by
    calc
      (∫ z, |A.prefixGraphon p hp 1 z -
          profileXiGraphon p (A.core ⟨0, hcount⟩) hp z|
          ∂unitSquareMeasure) ≤
          ∫ z, D.indicator (fun _ ↦ (1 : ℝ)) z ∂unitSquareMeasure := by
        apply integral_mono_ae
        · exact (A.prefixGraphon p hp 1).integrable.sub
            (profileXiGraphon p (A.core ⟨0, hcount⟩) hp).integrable |>.abs
        · exact (integrable_const (1 : ℝ)).indicator hD
        filter_upwards [A.prefixGraphon_ae_eq_prefixKernel p hp 1,
          matrixGraphon_ae_eq_kernel
            (profileXiMatrix p (A.core ⟨0, hcount⟩))
            (profileXiMatrix_isSymm p (A.core ⟨0, hcount⟩))
            (profileXiMatrix_nonneg hp.1 (A.core ⟨0, hcount⟩))
            (profileXiMatrix_le_one hp.2 (A.core ⟨0, hcount⟩)),
          (A.prefixGraphon p hp 1).ae_mem_Icc,
          (profileXiGraphon p (A.core ⟨0, hcount⟩) hp).ae_mem_Icc]
          with z hzA hzC hbA hbC
        have hzC' : profileXiGraphon p (A.core ⟨0, hcount⟩) hp z =
            matrixKernel (profileXiMatrix p (A.core ⟨0, hcount⟩)) z := by
          simpa only [profileXiGraphon] using hzC
        rcases hbA with ⟨hbA0, hbA1⟩
        rcases hbC with ⟨hbC0, hbC1⟩
        by_cases hz : z ∈ D
        · rw [Set.indicator_of_mem hz]
          rw [abs_le]
          constructor <;> linarith
        · rw [Set.indicator_of_notMem hz]
          have hx : z.1 ∉ A.firstBlockCellDisagreement hcount := by
            intro hx
            exact hz (Or.inl ⟨hx, Set.mem_univ _⟩)
          have hy : z.2 ∉ A.firstBlockCellDisagreement hcount := by
            intro hy
            exact hz (Or.inr ⟨Set.mem_univ _, hy⟩)
          rw [hzA, hzC',
            A.prefixKernel_one_eq_matrixKernel_of_not_mem_firstDisagreement
              p hcount z hx hy]
          simp
      _ = unitSquareMeasure.real D := by
        rw [integral_indicator_const (1 : ℝ) hD]
        simp
  calc
    (∫ z, |A.prefixGraphon p hp 1 z -
        profileXiGraphon p (A.core ⟨0, hcount⟩) hp z|
        ∂unitSquareMeasure) ≤ unitSquareMeasure.real D := hmajor
    _ ≤ 2 * volume.real (A.firstBlockCellDisagreement hcount) :=
      A.measureReal_firstBlockDisagreementSquare_le hcount
    _ ≤ 2 * (2 * ((A.core ⟨0, hcount⟩).order : ℝ) *
        (1 - A.alpha ⟨0, hcount⟩)) := by
      gcongr
      exact A.measureReal_firstBlockCellDisagreement_le hcount
    _ = 4 * ((A.core ⟨0, hcount⟩).order : ℝ) *
        (1 - A.alpha ⟨0, hcount⟩) := by ring

end FiniteProfileBlockLayout

end InducedStars
