import InducedStars.C4.ScalarBasic

/-!
# Exact derivatives of split-model entropy

All formulas use natural logarithms.  Their common domain is the interior
of the feasible density interval; the more general lemmas expose just the
nonvanishing and strict-density hypotheses used by differentiation.
-/

namespace InducedStars

open Filter Set
open scoped Topology

/-- The first derivative of the natural-log split entropy. -/
noncomputable def c4SplitEntropyNatDerivative (γ x : ℝ) : ℝ :=
  x * Real.log (c4SplitCrossDensity γ x) -
    (1 - x) * Real.log (1 - c4SplitCrossDensity γ x)

/-- The second derivative, in a form displaying strict negativity. -/
noncomputable def c4SplitEntropyNatSecondDerivative (γ x : ℝ) : ℝ :=
  Real.log (c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x)) -
    (x + c4SplitCrossDensity γ x * (1 - 2 * x)) ^ 2 /
      (x * (1 - x) * c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x))

lemma hasDerivAt_c4SplitCrossDensity (γ : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    HasDerivAt (c4SplitCrossDensity γ)
      (-(x + c4SplitCrossDensity γ x * (1 - 2 * x)) / (x * (1 - x))) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  have hd := ((hasDerivAt_const x γ).sub ((hasDerivAt_id x).pow 2)).div
    (((hasDerivAt_id x).const_mul 2).mul ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))
    (show 2 * x * (1 - x) ≠ 0 by positivity)
  convert hd using 1 <;> try rfl
  dsimp [c4SplitCrossDensity]
  field_simp [hx0, hx1]
  ring

lemma hasDerivAt_c4SplitEntropyNat_of_density {γ x : ℝ}
    (hx : x ∈ Ioo 0 1) (hq : c4SplitCrossDensity γ x ∈ Ioo 0 1) :
    HasDerivAt (c4SplitEntropyNat γ) (c4SplitEntropyNatDerivative γ x) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  have hq1 : c4SplitCrossDensity γ x ≠ 1 := hq.2.ne
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_const x 1).sub (hasDerivAt_id x))).mul
    ((Real.hasDerivAt_binEntropy hq.1.ne' hq1).comp x (hasDerivAt_c4SplitCrossDensity γ hx))
  convert hd using 1 <;> try rfl
  dsimp [c4SplitEntropyNatDerivative]
  simp only [Real.binEntropy, Real.log_inv]
  field_simp [hx0, hx1]
  ring

lemma hasDerivAt_c4SplitEntropyNat {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    HasDerivAt (c4SplitEntropyNat γ) (c4SplitEntropyNatDerivative γ x) x :=
  hasDerivAt_c4SplitEntropyNat_of_density (c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩)
    (c4SplitCrossDensity_mem_Ioo hγ hx)

lemma deriv_c4SplitEntropyNat {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    deriv (c4SplitEntropyNat γ) x = c4SplitEntropyNatDerivative γ x :=
  (hasDerivAt_c4SplitEntropyNat hγ hx).deriv

lemma hasDerivAt_c4SplitEntropyNatDerivative_of_density {γ x : ℝ}
    (hx : x ∈ Ioo 0 1) (hq : c4SplitCrossDensity γ x ∈ Ioo 0 1) :
    HasDerivAt (c4SplitEntropyNatDerivative γ) (c4SplitEntropyNatSecondDerivative γ x) x := by
  have hx0 : x ≠ 0 := hx.1.ne'
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  have hq0 : c4SplitCrossDensity γ x ≠ 0 := hq.1.ne'
  have hq1 : 1 - c4SplitCrossDensity γ x ≠ 0 := sub_ne_zero.mpr hq.2.ne'
  have hdq := hasDerivAt_c4SplitCrossDensity γ hx
  have hd := ((hasDerivAt_id x).mul (hdq.log hq0)).sub
    (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul
      (((hasDerivAt_const x 1).sub hdq).log hq1))
  convert hd using 1 <;> try rfl
  dsimp [c4SplitEntropyNatSecondDerivative]
  rw [Real.log_mul hq0 hq1]
  field_simp [hx0, hx1, hq0, hq1]
  ring

lemma hasDerivAt_c4SplitEntropyNatDerivative {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    HasDerivAt (c4SplitEntropyNatDerivative γ) (c4SplitEntropyNatSecondDerivative γ x) x :=
  hasDerivAt_c4SplitEntropyNatDerivative_of_density
    (c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩) (c4SplitCrossDensity_mem_Ioo hγ hx)

lemma hasDerivAt_deriv_c4SplitEntropyNat {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    HasDerivAt (deriv (c4SplitEntropyNat γ)) (c4SplitEntropyNatSecondDerivative γ x) x := by
  apply (hasDerivAt_c4SplitEntropyNatDerivative hγ hx).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact deriv_c4SplitEntropyNat hγ hy

lemma deriv_deriv_c4SplitEntropyNat {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    deriv (deriv (c4SplitEntropyNat γ)) x = c4SplitEntropyNatSecondDerivative γ x :=
  (hasDerivAt_deriv_c4SplitEntropyNat hγ hx).deriv

lemma c4SplitEntropyNatSecondDerivative_neg_of_density {γ x : ℝ}
    (hx : x ∈ Ioo 0 1) (hq : c4SplitCrossDensity γ x ∈ Ioo 0 1) :
    c4SplitEntropyNatSecondDerivative γ x < 0 := by
  have hprod : 0 < c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x) := by
    exact mul_pos hq.1 (sub_pos.mpr hq.2)
  have hprod1 : c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x) < 1 := by
    nlinarith [sq_nonneg (c4SplitCrossDensity γ x - 1 / 2)]
  have hlog := Real.log_neg hprod hprod1
  have hden : 0 < x * (1 - x) * c4SplitCrossDensity γ x *
      (1 - c4SplitCrossDensity γ x) :=
    mul_pos (mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) hq.1) (sub_pos.mpr hq.2)
  have hquot := div_nonneg
    (sq_nonneg (x + c4SplitCrossDensity γ x * (1 - 2 * x))) hden.le
  unfold c4SplitEntropyNatSecondDerivative
  linarith

lemma deriv_deriv_c4SplitEntropyNat_neg {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    deriv (deriv (c4SplitEntropyNat γ)) x < 0 := by
  rw [deriv_deriv_c4SplitEntropyNat hγ hx]
  exact c4SplitEntropyNatSecondDerivative_neg_of_density
    (c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩) (c4SplitCrossDensity_mem_Ioo hγ hx)

/-- The exact negative second derivative gives strict concavity on the full
closed feasible interval, including the two zero-entropy endpoints. -/
lemma strictConcaveOn_c4SplitEntropyNat {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    StrictConcaveOn ℝ (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ))
      (c4SplitEntropyNat γ) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    (continuousOn_c4SplitEntropyNat hγ)
  intro x hx
  rw [interior_Icc] at hx
  exact deriv_deriv_c4SplitEntropyNat_neg hγ hx

end InducedStars
