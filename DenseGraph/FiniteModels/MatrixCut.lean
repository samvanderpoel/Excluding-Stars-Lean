import InducedStars.Graphon.Metric
import InducedStars.Graphon.Step
import Mathlib.Tactic

/-!
# Finite matrix cut estimates

The results here are the assumption-free analytic bridge from rectangle sums
of finite matrices to the cut norm of their equal-cell graphons.  They live in
the reusable `DenseGraph` layer and import no compactness or prior-literature
instances.
-/

noncomputable section

open Finset Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace DenseGraph

open InducedStars

/-- A linear form on a finite cube attains its largest absolute value at a
`0/1` vertex. -/
theorem abs_sum_mul_le_of_abs_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c a : ι → ℝ) (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1)
    {B : ℝ} (hB : ∀ s : Finset ι, |∑ i ∈ s, c i| ≤ B) :
    |∑ i, a i * c i| ≤ B := by
  classical
  let P : Finset ι := Finset.univ.filter fun i ↦ 0 ≤ c i
  let N : Finset ι := Finset.univ.filter fun i ↦ ¬0 ≤ c i
  have hsplit (f : ι → ℝ) : ∑ i, f i = ∑ i ∈ P, f i + ∑ i ∈ N, f i := by
    simp only [P, N]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i ↦ 0 ≤ c i) f]
  have hupper : (∑ i, a i * c i) ≤ ∑ i ∈ P, c i := by
    rw [hsplit]
    calc
      (∑ i ∈ P, a i * c i) + ∑ i ∈ N, a i * c i ≤
          (∑ i ∈ P, c i) + 0 := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro i hi
          have hci : 0 ≤ c i := (Finset.mem_filter.mp hi).2
          nlinarith [ha₁ i]
        · simpa only [Finset.sum_const_zero] using
            Finset.sum_nonpos (s := N) (f := fun i ↦ a i * c i) (by
              intro i hi
              have hci : c i ≤ 0 := le_of_not_ge (Finset.mem_filter.mp hi).2
              exact mul_nonpos_of_nonneg_of_nonpos (ha₀ i) hci)
      _ = _ := add_zero _
  have hlower : (∑ i ∈ N, c i) ≤ ∑ i, a i * c i := by
    rw [hsplit]
    calc
      (∑ i ∈ N, c i) ≤ 0 + ∑ i ∈ N, a i * c i := by
        simpa only [zero_add] using Finset.sum_le_sum (s := N) (f := c)
          (g := fun i ↦ a i * c i) (by
            intro i hi
            have hci : c i ≤ 0 := le_of_not_ge (Finset.mem_filter.mp hi).2
            nlinarith [ha₁ i])
      _ ≤ (∑ i ∈ P, a i * c i) + ∑ i ∈ N, a i * c i := by
        have hp : 0 ≤ ∑ i ∈ P, a i * c i :=
          Finset.sum_nonneg (s := P) (f := fun i ↦ a i * c i) fun i hi ↦
            mul_nonneg (ha₀ i) (Finset.mem_filter.mp hi).2
        linarith
  rw [abs_le]
  constructor
  · calc
      -B ≤ -|∑ i ∈ N, c i| := neg_le_neg (hB N)
      _ ≤ ∑ i ∈ N, c i := neg_abs_le _
      _ ≤ ∑ i, a i * c i := hlower
  · calc
      (∑ i, a i * c i) ≤ ∑ i ∈ P, c i := hupper
      _ ≤ |∑ i ∈ P, c i| := le_abs_self _
      _ ≤ B := hB P

/-- Bilinear finite-cube estimate: fractional weights in both coordinates do
not enlarge a rectangle-cut bound. -/
theorem abs_sum_mul_mul_le_of_abs_rect_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (D : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1)
    (hb₀ : ∀ j, 0 ≤ b j) (hb₁ : ∀ j, b j ≤ 1)
    {B : ℝ}
    (hB : ∀ s : Finset ι, ∀ t : Finset κ,
      |∑ i ∈ s, ∑ j ∈ t, D i j| ≤ B) :
    |∑ i, ∑ j, a i * b j * D i j| ≤ B := by
  classical
  have hinner (s : Finset ι) :
      |∑ j, b j * (∑ i ∈ s, D i j)| ≤ B := by
    apply abs_sum_mul_le_of_abs_sum_le
      (c := fun j ↦ ∑ i ∈ s, D i j) (a := b) hb₀ hb₁
    intro t
    convert hB s t using 1
    rw [Finset.sum_comm]
  have houter :
      |∑ i, a i * (∑ j, b j * D i j)| ≤ B := by
    apply abs_sum_mul_le_of_abs_sum_le
      (c := fun i ↦ ∑ j, b j * D i j) (a := a) ha₀ ha₁
    intro s
    convert hinner s using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  convert houter using 1
  apply congrArg abs
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Fraction of an equal cell selected by a measurable set. -/
def cutCellWeight {q : ℕ} (S : Set UnitInterval) (i : Fin q) : ℝ :=
  (q : ℝ) * (volume (S ∩ equalCell i)).toReal

theorem cutCellWeight_nonneg {q : ℕ} (S : Set UnitInterval) (i : Fin q) :
    0 ≤ cutCellWeight S i := by
  exact mul_nonneg (by positivity) ENNReal.toReal_nonneg

theorem cutCellWeight_le_one {q : ℕ} (hq : 0 < q)
    (S : Set UnitInterval) (i : Fin q) :
    cutCellWeight S i ≤ 1 := by
  have hmeasure : volume (S ∩ equalCell i) ≤ volume (equalCell i) :=
    measure_mono inter_subset_right
  have hfinite : volume (equalCell i) ≠ ∞ := by
    rw [volume_equalCell]
    exact ENNReal.ofReal_ne_top
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [volume_equalCell, ENNReal.toReal_ofReal (by positivity)] at hreal
  unfold cutCellWeight
  calc
    (q : ℝ) * (volume (S ∩ equalCell i)).toReal ≤
        (q : ℝ) * (1 / (q : ℝ)) := by gcongr
    _ = 1 := by field_simp

/-- Exact finite-cell formula for a cut integral of matrix graphons. -/
theorem cutIntegral_matrixGraphon_sub_eq_sum {q : ℕ}
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1)
    (C : MeasurableCut) :
    cutIntegral
        ((matrixGraphon M hM hM₀ hM₁).toL1 -
          (matrixGraphon N hN hN₀ hN₁).toL1) C =
      ∑ i, ∑ j,
        (volume (C.left ∩ equalCell i)).toReal *
          (volume (C.right ∩ equalCell j)).toReal * (M i j - N i j) := by
  classical
  let WM := matrixGraphon M hM hM₀ hM₁
  let WN := matrixGraphon N hN hN₀ hN₁
  have hae : ∀ᵐ z ∂unitSquareMeasure,
      (WM.toL1 - WN.toL1) z =
        ∑ i : Fin q, ∑ j : Fin q,
          (equalCell i ×ˢ equalCell j).indicator
            (fun _ ↦ M i j - N i j) z := by
    filter_upwards [Lp.coeFn_sub WM.toL1 WN.toL1,
      matrixGraphon_ae_eq_kernel M hM hM₀ hM₁,
      matrixGraphon_ae_eq_kernel N hN hN₀ hN₁] with z hzsub hzM hzN
    rw [hzsub]
    change WM z - WN z = _
    rw [hzM, hzN]
    rw [matrixKernel, matrixKernel, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hz : z ∈ equalCell i ×ˢ equalCell j <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hz]
  rw [cutIntegral]
  calc
    (∫ z in C.rectangle, (WM.toL1 - WN.toL1) z ∂unitSquareMeasure) =
        ∫ z in C.rectangle, ∑ i : Fin q, ∑ j : Fin q,
          (equalCell i ×ˢ equalCell j).indicator
            (fun _ ↦ M i j - N i j) z ∂unitSquareMeasure := by
      exact integral_congr_ae (ae_restrict_of_ae hae)
    _ = ∑ i : Fin q, ∑ j : Fin q,
        ∫ z in C.rectangle, (equalCell i ×ˢ equalCell j).indicator
          (fun _ ↦ M i j - N i j) z ∂unitSquareMeasure := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact ((integrable_const (M i j - N i j)).indicator
          ((measurableSet_equalCell i).prod (measurableSet_equalCell j))).integrableOn
      · intro i hi
        exact integrable_finsetSum _ fun j hj ↦
          ((integrable_const (M i j - N i j)).indicator
            ((measurableSet_equalCell i).prod (measurableSet_equalCell j))).integrableOn
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [setIntegral_indicator
        ((measurableSet_equalCell i).prod (measurableSet_equalCell j))]
      rw [setIntegral_const, smul_eq_mul]
      change unitSquareMeasure.real
          ((C.left ×ˢ C.right) ∩ (equalCell i ×ˢ equalCell j)) *
            (M i j - N i j) = _
      rw [Set.prod_inter_prod, measureReal_prod_prod]
      rfl

/-- A rectangle-sum estimate controls the cut norm of equal-cell matrix
graphons. -/
theorem cutNorm_matrixGraphon_sub_le_of_rect_sum {q : ℕ} (hq : 0 < q)
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hrect : ∀ s t : Finset (Fin q),
      |∑ i ∈ s, ∑ j ∈ t, (M i j - N i j)| ≤ B * (q : ℝ) ^ 2) :
    cutNorm
        ((matrixGraphon M hM hM₀ hM₁).toL1 -
          (matrixGraphon N hN hN₀ hN₁).toL1) ≤ B := by
  classical
  unfold cutNorm
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨C, rfl⟩
  change |cutIntegral
    ((matrixGraphon M hM hM₀ hM₁).toL1 -
      (matrixGraphon N hN hN₀ hN₁).toL1) C| ≤ B
  rw [cutIntegral_matrixGraphon_sub_eq_sum M N hM hN hM₀ hM₁ hN₀ hN₁ C]
  let a : Fin q → ℝ := fun i ↦ cutCellWeight C.left i
  let b : Fin q → ℝ := fun j ↦ cutCellWeight C.right j
  have hweighted :
      |∑ i, ∑ j, a i * b j * (M i j - N i j)| ≤ B * (q : ℝ) ^ 2 :=
    abs_sum_mul_mul_le_of_abs_rect_sum_le
      (D := fun i j ↦ M i j - N i j) a b
      (fun i ↦ cutCellWeight_nonneg C.left i)
      (fun i ↦ cutCellWeight_le_one hq C.left i)
      (fun j ↦ cutCellWeight_nonneg C.right j)
      (fun j ↦ cutCellWeight_le_one hq C.right j) hrect
  have hrewrite :
      (∑ i, ∑ j,
        (volume (C.left ∩ equalCell i)).toReal *
          (volume (C.right ∩ equalCell j)).toReal * (M i j - N i j)) =
        (1 / (q : ℝ) ^ 2) *
          ∑ i, ∑ j, a i * b j * (M i j - N i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [a, b, cutCellWeight]
    field_simp
  rw [hrewrite, abs_mul]
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (q : ℝ) ^ 2)]
  calc
    (1 / (q : ℝ) ^ 2) *
        |∑ i, ∑ j, a i * b j * (M i j - N i j)| ≤
        (1 / (q : ℝ) ^ 2) * (B * (q : ℝ) ^ 2) := by
      gcongr
    _ = B := by field_simp

end DenseGraph

