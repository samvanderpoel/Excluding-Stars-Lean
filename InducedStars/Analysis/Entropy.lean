import InducedStars.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Scalar binary entropy

This file fixes the logarithm convention used by the paper.  Mathlib's
`Real.log` and `Real.binEntropy` use natural logarithms, so the paper's
base-two entropy is obtained by dividing by `Real.log 2`.
-/

namespace InducedStars

open Set

/-- The base-two logarithm used by the paper. -/
noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

lemma realLogTwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma realLogTwo_ne_zero : Real.log 2 ≠ 0 := realLogTwo_pos.ne'

@[simp] lemma log2_zero : log2 0 = 0 := by simp [log2]

@[simp] lemma log2_one : log2 1 = 0 := by simp [log2]

@[simp] lemma log2_two : log2 2 = 1 := by
  exact div_self realLogTwo_ne_zero

lemma log2_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x * y) = log2 x + log2 y := by
  rw [log2, Real.log_mul hx hy]
  simp only [log2]
  ring

lemma log2_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    log2 (x / y) = log2 x - log2 y := by
  rw [log2, Real.log_div hx hy]
  simp only [log2]
  ring

lemma log2_pow (x : ℝ) (n : ℕ) : log2 (x ^ n) = (n : ℝ) * log2 x := by
  rw [log2, Real.log_pow]
  simp only [log2]
  ring

lemma log2_inv (x : ℝ) : log2 x⁻¹ = -log2 x := by
  rw [log2, Real.log_inv]
  simp only [log2]
  ring

lemma log2_pos {x : ℝ} (hx : 1 < x) : 0 < log2 x := by
  exact div_pos (Real.log_pos hx) realLogTwo_pos

lemma log2_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ log2 x := by
  exact div_nonneg (Real.log_nonneg hx) realLogTwo_pos.le

/-- The paper's binary entropy, measured in bits rather than nats. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  Real.binEntropy p / Real.log 2

lemma binaryEntropy_eq_formula (p : ℝ) :
    binaryEntropy p = -p * log2 p - (1 - p) * log2 (1 - p) := by
  simp only [binaryEntropy, Real.binEntropy, log2, Real.log_inv]
  ring

@[simp] lemma binaryEntropy_zero : binaryEntropy 0 = 0 := by
  simp [binaryEntropy]

@[simp] lemma binaryEntropy_one : binaryEntropy 1 = 0 := by
  simp [binaryEntropy]

@[simp] lemma binaryEntropy_one_sub (p : ℝ) :
    binaryEntropy (1 - p) = binaryEntropy p := by
  simp [binaryEntropy]

lemma binaryEntropy_nonneg {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ binaryEntropy p := by
  exact div_nonneg (Real.binEntropy_nonneg hp₀ hp₁) realLogTwo_pos.le

lemma binaryEntropy_pos {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    0 < binaryEntropy p := by
  exact div_pos (Real.binEntropy_pos hp₀ hp₁) realLogTwo_pos

lemma binaryEntropy_eq_zero {p : ℝ} :
    binaryEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  constructor
  · intro h
    rcases (div_eq_zero_iff.mp h) with h | h
    · exact Real.binEntropy_eq_zero.mp h
    · exact (realLogTwo_ne_zero h).elim
  · intro h
    rw [binaryEntropy, Real.binEntropy_eq_zero.mpr h, zero_div]

lemma binaryEntropy_continuous : Continuous binaryEntropy := by
  exact Real.binEntropy_continuous.div_const _

lemma binaryEntropy_continuousOn : ContinuousOn binaryEntropy (Icc 0 1) :=
  binaryEntropy_continuous.continuousOn

lemma binaryEntropy_differentiableAt {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    DifferentiableAt ℝ binaryEntropy p := by
  exact (Real.differentiableAt_binEntropy hp₀.ne' (by linarith)).div_const _

/-- Derivative of binary entropy in the paper's base-two convention. -/
lemma hasDerivAt_binaryEntropy {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasDerivAt binaryEntropy (log2 ((1 - p) / p)) p := by
  have h := (Real.hasDerivAt_binEntropy hp₀.ne' (by linarith)).div_const (Real.log 2)
  have hOneSub : 1 - p ≠ 0 := by linarith
  change HasDerivAt (fun q : ℝ => Real.binEntropy q / Real.log 2)
    (log2 ((1 - p) / p)) p
  simpa only [log2, Real.log_div hOneSub hp₀.ne'] using h

lemma deriv_binaryEntropy {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    deriv binaryEntropy p = log2 ((1 - p) / p) :=
  (hasDerivAt_binaryEntropy hp₀ hp₁).deriv

/-- Base-two binary entropy is strictly concave on the full probability interval. -/
lemma binaryEntropy_strictConcaveOn :
    StrictConcaveOn ℝ (Icc (0 : ℝ) 1) binaryEntropy := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := Real.strictConcave_binEntropy.2 hx hy hxy ha hb hab
  change
    a * (Real.binEntropy x / Real.log 2) + b * (Real.binEntropy y / Real.log 2) <
      Real.binEntropy (a * x + b * y) / Real.log 2
  calc
    a * (Real.binEntropy x / Real.log 2) + b * (Real.binEntropy y / Real.log 2) =
        (a * Real.binEntropy x + b * Real.binEntropy y) / Real.log 2 := by ring
    _ < Real.binEntropy (a * x + b * y) / Real.log 2 :=
      (div_lt_div_iff_of_pos_right realLogTwo_pos).2 h

lemma binaryEntropy_strictConcaveOn_Ioo :
    StrictConcaveOn ℝ (Ioo (0 : ℝ) 1) binaryEntropy :=
  binaryEntropy_strictConcaveOn.subset Ioo_subset_Icc_self (convex_Ioo 0 1)

lemma hasDerivAt_log2 {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt log2 (x⁻¹ / Real.log 2) x := by
  exact (Real.hasDerivAt_log hx).div_const (Real.log 2)

/-- Algebraic identity controlling monotonicity of the entropy perspective. -/
lemma binaryEntropy_sub_mul_log2_div {p : ℝ} (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    binaryEntropy p - p * log2 ((1 - p) / p) = -log2 (1 - p) := by
  rw [binaryEntropy_eq_formula, log2_div (sub_ne_zero.mpr hp₁.symm) hp₀]
  ring

/-- Companion identity for the boundary `y = 1-x`. -/
lemma binaryEntropy_add_one_sub_mul_log2_div {p : ℝ} (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    binaryEntropy p + (1 - p) * log2 ((1 - p) / p) = -log2 p := by
  rw [binaryEntropy_eq_formula, log2_div (sub_ne_zero.mpr hp₁.symm) hp₀]
  ring

/-- The homogeneous perspective `y H(a/y)` of binary entropy. -/
noncomputable def entropyPerspective (a y : ℝ) : ℝ :=
  y * binaryEntropy (a / y)

lemma entropyPerspective_strictMono {a y₁ y₂ : ℝ}
    (ha : 0 < a) (hy₁ : 0 < y₁) (hay₁ : a ≤ y₁) (hy₁y₂ : y₁ < y₂) :
    entropyPerspective a y₁ < entropyPerspective a y₂ := by
  have hy₂ : 0 < y₂ := hy₁.trans hy₁y₂
  have hq₁ : a / y₁ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ha.le hy₁.le, (div_le_one hy₁).2 hay₁⟩
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.2 zero_le_one
  have hq₁_ne : a / y₁ ≠ 0 := div_ne_zero ha.ne' hy₁.ne'
  have hweight_pos : 0 < y₁ / y₂ := div_pos hy₁ hy₂
  have hcomplement_pos : 0 < 1 - y₁ / y₂ :=
    sub_pos.2 ((div_lt_one hy₂).2 hy₁y₂)
  have hweights : y₁ / y₂ + (1 - y₁ / y₂) = 1 := by ring
  have hconcave := binaryEntropy_strictConcaveOn.2 hq₁ hzero hq₁_ne
    hweight_pos hcomplement_pos hweights
  simp only [smul_eq_mul, binaryEntropy_zero, mul_zero, add_zero] at hconcave
  have hcombo : y₁ / y₂ * (a / y₁) = a / y₂ := by
    field_simp [hy₁.ne', hy₂.ne']
  rw [hcombo] at hconcave
  rw [entropyPerspective, entropyPerspective]
  calc
    y₁ * binaryEntropy (a / y₁) =
        y₂ * (y₁ / y₂ * binaryEntropy (a / y₁)) := by field_simp [hy₂.ne']
    _ < y₂ * binaryEntropy (a / y₂) := mul_lt_mul_of_pos_left hconcave hy₂

/-- The perspective is nondecreasing in scale, with one exact degenerate case. -/
lemma entropyPerspective_mono {a y₁ y₂ : ℝ}
    (ha : 0 ≤ a) (hy₁ : 0 < y₁) (hay₁ : a ≤ y₁) (hy₁y₂ : y₁ ≤ y₂) :
    entropyPerspective a y₁ ≤ entropyPerspective a y₂ := by
  rcases hy₁y₂.eq_or_lt with rfl | hy₁y₂
  · exact le_rfl
  rcases ha.eq_or_lt with rfl | ha
  · simp [entropyPerspective]
  · exact (entropyPerspective_strictMono ha hy₁ hay₁ hy₁y₂).le

@[simp] lemma entropyPerspective_zero (y : ℝ) : entropyPerspective 0 y = 0 := by
  simp [entropyPerspective]

lemma entropyPerspective_eq_iff {a y₁ y₂ : ℝ}
    (ha : 0 ≤ a) (hy₁ : 0 < y₁) (hay₁ : a ≤ y₁) (hy₁y₂ : y₁ ≤ y₂) :
    entropyPerspective a y₁ = entropyPerspective a y₂ ↔ a = 0 ∨ y₁ = y₂ := by
  constructor
  · intro heq
    rcases ha.eq_or_lt with ha | ha
    · exact Or.inl ha.symm
    rcases hy₁y₂.eq_or_lt with hy | hy
    · exact Or.inr hy
    · exact ((entropyPerspective_strictMono ha hy₁ hay₁ hy).ne heq).elim
  · rintro (rfl | rfl)
    · simp [entropyPerspective]
    · rfl

end InducedStars
