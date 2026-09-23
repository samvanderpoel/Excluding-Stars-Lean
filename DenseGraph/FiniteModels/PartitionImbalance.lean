import DenseGraph.FiniteModels.BalancedAssignments
import Mathlib.Tactic

/-!
# Quantitative imbalance of finite multipartite size vectors

Reusable finite smoothing and lattice-shell bounds for ordered multipartite
size vectors.  These lemmas are graph-family independent.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace DenseGraph

/-! ## Quadratic capacity loss from an imbalanced size vector -/

/-- Maximum coordinate of a nonempty finite size vector. -/
def sizeVectorMax {r : ℕ} (hr : 0 < r) (a : Fin r → ℕ) : ℕ :=
  (Finset.univ.image a).max' (by
    refine ⟨a ⟨0, hr⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩)

/-- Minimum coordinate of a nonempty finite size vector. -/
def sizeVectorMin {r : ℕ} (hr : 0 < r) (a : Fin r → ℕ) : ℕ :=
  (Finset.univ.image a).min' (by
    refine ⟨a ⟨0, hr⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩)

/-- Range of the coordinates of a nonempty finite size vector. -/
def sizeVectorRange {r : ℕ} (hr : 0 < r) (a : Fin r → ℕ) : ℕ :=
  sizeVectorMax hr a - sizeVectorMin hr a

theorem exists_eq_sizeVectorMax {r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) : ∃ i, a i = sizeVectorMax hr a := by
  have hmem := Finset.max'_mem (Finset.univ.image a)
    (by
      refine ⟨a ⟨0, hr⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩)
  simpa [sizeVectorMax] using Finset.mem_image.mp hmem

theorem exists_eq_sizeVectorMin {r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) : ∃ i, a i = sizeVectorMin hr a := by
  have hmem := Finset.min'_mem (Finset.univ.image a)
    (by
      refine ⟨a ⟨0, hr⟩, ?_⟩
      exact Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, rfl⟩)
  simpa [sizeVectorMin] using Finset.mem_image.mp hmem

theorem sizeVectorMin_le {r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (i : Fin r) : sizeVectorMin hr a ≤ a i := by
  unfold sizeVectorMin
  apply Finset.min'_le
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem le_sizeVectorMax {r : ℕ} (hr : 0 < r)
    (a : Fin r → ℕ) (i : Fin r) : a i ≤ sizeVectorMax hr a := by
  unfold sizeVectorMax
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Bounding the max--min range of a nonempty natural-valued vector is
equivalent to bounding every pairwise absolute difference.  The bound is
stated in `ℝ` so it can be used directly with analytic cutoffs. -/
theorem sizeVectorRange_cast_le_iff_pairwise_abs_sub_le
    {r : ℕ} (hr : 0 < r) (a : Fin r → ℕ) (R : ℝ) :
    (sizeVectorRange hr a : ℝ) ≤ R ↔
      ∀ i j, |(a i : ℝ) - (a j : ℝ)| ≤ R := by
  have hminMax : sizeVectorMin hr a ≤ sizeVectorMax hr a :=
    (sizeVectorMin_le hr a ⟨0, hr⟩).trans
      (le_sizeVectorMax hr a ⟨0, hr⟩)
  have hRangeCast : (sizeVectorRange hr a : ℝ) =
      (sizeVectorMax hr a : ℝ) - (sizeVectorMin hr a : ℝ) := by
    rw [sizeVectorRange, Nat.cast_sub hminMax]
  constructor
  · intro hR i j
    have hminI : (sizeVectorMin hr a : ℝ) ≤ (a i : ℝ) := by
      exact_mod_cast sizeVectorMin_le hr a i
    have hminJ : (sizeVectorMin hr a : ℝ) ≤ (a j : ℝ) := by
      exact_mod_cast sizeVectorMin_le hr a j
    have hiMax : (a i : ℝ) ≤ (sizeVectorMax hr a : ℝ) := by
      exact_mod_cast le_sizeVectorMax hr a i
    have hjMax : (a j : ℝ) ≤ (sizeVectorMax hr a : ℝ) := by
      exact_mod_cast le_sizeVectorMax hr a j
    rw [abs_le]
    constructor <;> rw [hRangeCast] at hR <;> linarith
  · intro hPair
    obtain ⟨i, hi⟩ := exists_eq_sizeVectorMax hr a
    obtain ⟨j, hj⟩ := exists_eq_sizeVectorMin hr a
    have hij := hPair i j
    have hnonneg : 0 ≤ (a i : ℝ) - (a j : ℝ) := by
      rw [hi, hj]
      exact sub_nonneg.mpr (by exact_mod_cast hminMax)
    rw [abs_of_nonneg hnonneg] at hij
    rw [hRangeCast, ← hi, ← hj]
    exact hij

private theorem choose_two_pair_smoothing
    {lo hi x : ℕ} (hlo : lo ≤ hi) (hx : x ≤ hi - lo) :
    hi.choose 2 + lo.choose 2 =
      (hi - x).choose 2 + (lo + x).choose 2 + x * (hi - lo - x) := by
  let d := hi - lo
  let y := d - x
  have hd : hi = lo + d := by dsimp [d]; omega
  have hxy : d = x + y := by dsimp [y]; omega
  have hhix : hi - x = lo + y := by dsimp [d, y]; omega
  rw [hd, hxy]
  have hleft : lo + (x + y) - x = lo + y := by omega
  have hright : lo + (x + y) - lo - x = y := by omega
  rw [hleft, hright, choose_two_add, choose_two_add,
    choose_two_add, choose_two_add]
  dsimp [d, y]
  ring

private theorem sum_choose_pair_smoothing
    {r : ℕ} (a : Fin r → ℕ) {i j : Fin r} (hij : i ≠ j)
    {x : ℕ} (hijSize : a j ≤ a i) (hx : x ≤ a i - a j) :
    let a' := Function.update (Function.update a i (a i - x)) j (a j + x)
    (∑ z, (a z).choose 2) =
      (∑ z, (a' z).choose 2) + x * (a i - a j - x) := by
  dsimp only
  let R : Finset (Fin r) := Finset.univ.erase i |>.erase j
  let a' := Function.update (Function.update a i (a i - x)) j (a j + x)
  have hiMem : i ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ i
  have hjMem : j ∈ (Finset.univ.erase i : Finset (Fin r)) := by
    simp [Ne.symm hij]
  have hdecomp (f : Fin r → ℕ) :
      ∑ z, f z = f i + f j + ∑ z ∈ R, f z := by
    calc
      ∑ z, f z = (∑ z ∈ Finset.univ.erase i, f z) + f i :=
        (Finset.sum_erase_add Finset.univ f hiMem).symm
      _ = ((∑ z ∈ R, f z) + f j) + f i := by
        rw [← Finset.sum_erase_add (Finset.univ.erase i) f hjMem]
      _ = f i + f j + ∑ z ∈ R, f z := by omega
  have ha'ij : a' i = a i - x := by simp [a', hij]
  have ha'ji : a' j = a j + x := by simp [a']
  have ha'other : ∀ z ∈ R, a' z = a z := by
    intro z hz
    have hzi : z ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
    have hzj : z ≠ j := (Finset.mem_erase.mp hz).1
    simp [a', hzi, hzj]
  rw [hdecomp (fun z ↦ (a z).choose 2),
    hdecomp (fun z ↦ (a' z).choose 2), ha'ij, ha'ji]
  have hrest : (∑ z ∈ R, (a' z).choose 2) =
      ∑ z ∈ R, (a z).choose 2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [ha'other z hz]
  rw [hrest, choose_two_pair_smoothing hijSize hx]
  omega

/-- If a size vector has range `d`, its multipartite cross capacity loses
at least `floor(d²/4)` from the balanced maximum.  The proof smooths the
largest and smallest coordinates while preserving their sum. -/
theorem range_mul_sub_half_le_balancedCross_sub_multipartite
    {r q : ℕ} (hr : 0 < r) (a : Fin r → ℕ)
    (hsum : ∑ i, a i = q) :
    let d := sizeVectorRange hr a
    (d / 2) * (d - d / 2) ≤
      balancedMultipartiteCrossCapacity r q - multipartiteCrossCapacity a := by
  dsimp only
  let hi := sizeVectorMax hr a
  let lo := sizeVectorMin hr a
  let d := hi - lo
  let x := d / 2
  obtain ⟨i, hiEq⟩ := exists_eq_sizeVectorMax hr a
  obtain ⟨j, hjEq⟩ := exists_eq_sizeVectorMin hr a
  have hlohi : lo ≤ hi := by
    dsimp [lo, hi]
    exact (sizeVectorMin_le hr a i).trans (le_sizeVectorMax hr a i)
  by_cases hd0 : d = 0
  · simp [sizeVectorRange, d, hi, lo, hd0]
  have hij : i ≠ j := by
    intro hij
    subst j
    apply hd0
    change sizeVectorMax hr a - sizeVectorMin hr a = 0
    rw [← hiEq, ← hjEq]
    simp
  have hx : x ≤ a i - a j := by
    rw [hiEq, hjEq]
    exact Nat.div_le_self d 2
  let a' := Function.update (Function.update a i (a i - x)) j (a j + x)
  have hsum' : ∑ z, a' z = q := by
    have hdecomp (f : Fin r → ℕ) :
        ∑ z, f z = f i + f j +
          ∑ z ∈ ((Finset.univ.erase i).erase j), f z := by
      calc
        ∑ z, f z =
            (∑ z ∈ Finset.univ.erase i, f z) + f i :=
          (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)).symm
        _ = ((∑ z ∈ (Finset.univ.erase i).erase j, f z) + f j) +
            f i := by
          rw [← Finset.sum_erase_add (Finset.univ.erase i) f
            (a := j) (by simp [Ne.symm hij])]
        _ = f i + f j +
            ∑ z ∈ ((Finset.univ.erase i).erase j), f z := by omega
    have hai : a i = a j + d := by rw [hiEq, hjEq]; dsimp [d]; omega
    have hother : ∀ z ∈ ((Finset.univ.erase i).erase j), a' z = a z := by
      intro z hz
      have hzi : z ≠ i := (Finset.mem_erase.mp
        (Finset.mem_erase.mp hz).2).1
      have hzj : z ≠ j := (Finset.mem_erase.mp hz).1
      simp [a', hzi, hzj]
    have hrest : (∑ z ∈ ((Finset.univ.erase i).erase j), a' z) =
        ∑ z ∈ ((Finset.univ.erase i).erase j), a z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hother z hz]
    calc
      ∑ z, a' z = a' i + a' j +
          ∑ z ∈ ((Finset.univ.erase i).erase j), a' z := hdecomp a'
      _ = a i + a j +
          ∑ z ∈ ((Finset.univ.erase i).erase j), a z := by
        rw [hrest]
        simp [a', hij]
        omega
      _ = ∑ z, a z := (hdecomp a).symm
      _ = q := hsum
  have hsmooth := sum_choose_pair_smoothing a hij
    (by rw [hiEq, hjEq]; exact hlohi) hx
  change (∑ z, (a z).choose 2) =
      (∑ z, (a' z).choose 2) + x * (a i - a j - x) at hsmooth
  have hdai : a i - a j = d := by
    rw [hiEq, hjEq]
  rw [hdai] at hsmooth
  have hparts := multipartiteCrossPairSum_add_sum_choose a
  have hparts' := multipartiteCrossPairSum_add_sum_choose a'
  rw [hsum] at hparts
  rw [hsum'] at hparts'
  have hcapEq : multipartiteCrossCapacity a' =
      multipartiteCrossCapacity a + x * (d - x) := by
    rw [multipartiteCrossCapacity_eq_pairSum,
      multipartiteCrossCapacity_eq_pairSum]
    have hpairTotal :
        multipartiteCrossPairSum a + (∑ z, (a z).choose 2) =
          multipartiteCrossPairSum a' + (∑ z, (a' z).choose 2) :=
      hparts.trans hparts'.symm
    omega
  have hmax := balancedMultipartiteCrossCapacity_max a' hsum'
  rw [hcapEq] at hmax
  change x * (d - x) ≤
    balancedMultipartiteCrossCapacity r q - multipartiteCrossCapacity a
  omega

/-- A convenient quadratic form of the preceding integer smoothing bound. -/
theorem sizeVectorRange_sq_le_nine_mul_balancedCross_gap
    {r q : ℕ} (hr : 0 < r) (a : Fin r → ℕ)
    (hsum : ∑ i, a i = q) (hrange : 2 ≤ sizeVectorRange hr a) :
    (sizeVectorRange hr a) ^ 2 ≤
      9 * (balancedMultipartiteCrossCapacity r q -
        multipartiteCrossCapacity a) := by
  let d := sizeVectorRange hr a
  let x := d / 2
  have hxpos : 1 ≤ x := by
    dsimp [x]
    omega
  have htwox : 2 * x ≤ d := by
    dsimp [x]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self d 2
  have hmod : d % 2 < 2 := Nat.mod_lt d (by omega)
  have hdecomp := Nat.mod_add_div d 2
  have hdle : d ≤ 3 * x := by omega
  have hxle : x ≤ d - x := by omega
  have hxx : x ^ 2 ≤ x * (d - x) := by
    simpa [pow_two] using Nat.mul_le_mul_left x hxle
  have hgap := range_mul_sub_half_le_balancedCross_sub_multipartite
    hr a hsum
  change x * (d - x) ≤
      balancedMultipartiteCrossCapacity r q -
        multipartiteCrossCapacity a at hgap
  have hdsq : d ^ 2 ≤ 9 * x ^ 2 := by
    calc
      d ^ 2 ≤ (3 * x) ^ 2 := Nat.pow_le_pow_left hdle 2
      _ = 9 * x ^ 2 := by ring
  dsimp [d] at hdsq ⊢
  exact hdsq.trans <| (Nat.mul_le_mul_left 9 hxx).trans
    (Nat.mul_le_mul_left 9 hgap)

/-! ## Counting fixed-range size vectors -/

/-- Weak compositions with prescribed total and prescribed coordinate
range. -/
def sizeVectorsWithSumAndRange (r q : ℕ) (hr : 0 < r) (d : ℕ) :
    Finset (Fin r → ℕ) :=
  (Finset.piAntidiag (Finset.univ : Finset (Fin r)) q).filter
    fun a ↦ sizeVectorRange hr a = d

@[simp] theorem mem_sizeVectorsWithSumAndRange
    {r q d : ℕ} {hr : 0 < r} {a : Fin r → ℕ} :
    a ∈ sizeVectorsWithSumAndRange r q hr d ↔
      (∑ i, a i = q) ∧ sizeVectorRange hr a = d := by
  simp [sizeVectorsWithSumAndRange]

/-- At fixed total, subtracting the minimum coordinate injects a range-`d`
size vector into the `(d+1)^r` box.  Thus the number of range shells is
polynomial in the range itself, with no ambient-`q` loss. -/
theorem card_sizeVectorsWithSumAndRange_le
    (r q : ℕ) (hr : 0 < r) (d : ℕ) :
    (sizeVectorsWithSumAndRange r q hr d).card ≤ (d + 1) ^ r := by
  classical
  let shell := sizeVectorsWithSumAndRange r q hr d
  let offsetCode : (↑shell) → (Fin r → Fin (d + 1)) := fun a i ↦
    ⟨a.1 i - sizeVectorMin hr a.1, by
      have hai := le_sizeVectorMax hr a.1 i
      have hmin := sizeVectorMin_le hr a.1 i
      have hrange := (mem_sizeVectorsWithSumAndRange.mp a.2).2
      have : a.1 i - sizeVectorMin hr a.1 ≤
          sizeVectorMax hr a.1 - sizeVectorMin hr a.1 := by omega
      rw [← sizeVectorRange, hrange] at this
      omega⟩
  have hinj : Function.Injective offsetCode := by
    intro a b hab
    have haMem := mem_sizeVectorsWithSumAndRange.mp a.2
    have hbMem := mem_sizeVectorsWithSumAndRange.mp b.2
    let amin := sizeVectorMin hr a.1
    let bmin := sizeVectorMin hr b.1
    have hoff : (fun i ↦ a.1 i - amin) = (fun i ↦ b.1 i - bmin) := by
      funext i
      exact congrArg Fin.val (congrFun hab i)
    have haDecomp : ∑ i, a.1 i =
        (∑ i, (a.1 i - amin)) + r * amin := by
      calc
        ∑ i, a.1 i = ∑ i, ((a.1 i - amin) + amin) := by
          apply Finset.sum_congr rfl
          intro i _hi
          have := sizeVectorMin_le hr a.1 i
          omega
        _ = (∑ i, (a.1 i - amin)) + ∑ _i : Fin r, amin := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i, (a.1 i - amin)) + r * amin := by simp
    have hbDecomp : ∑ i, b.1 i =
        (∑ i, (b.1 i - bmin)) + r * bmin := by
      calc
        ∑ i, b.1 i = ∑ i, ((b.1 i - bmin) + bmin) := by
          apply Finset.sum_congr rfl
          intro i _hi
          have := sizeVectorMin_le hr b.1 i
          omega
        _ = (∑ i, (b.1 i - bmin)) + ∑ _i : Fin r, bmin := by
          rw [Finset.sum_add_distrib]
        _ = (∑ i, (b.1 i - bmin)) + r * bmin := by simp
    have hsumoff := congrArg (fun f : Fin r → ℕ ↦ ∑ i, f i) hoff
    have hmul : r * amin = r * bmin := by
      rw [haMem.1] at haDecomp
      rw [hbMem.1] at hbDecomp
      omega
    have hminEq : amin = bmin := Nat.eq_of_mul_eq_mul_left hr hmul
    apply Subtype.ext
    funext i
    have hi := congrFun hoff i
    have hamin := sizeVectorMin_le hr a.1 i
    have hbmin := sizeVectorMin_le hr b.1 i
    dsimp [amin, bmin] at hi hminEq hamin hbmin
    omega
  have hcard := Fintype.card_le_of_injective offsetCode hinj
  simpa [shell, Fintype.card_fun] using hcard

end DenseGraph
