import InducedStars.C4.ScalarOptimizer
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A stationary-point parametrization by cross density

Solving the stationary equation for the clique proportion produces an
analytic strictly increasing parametrization of the total density.  It is
used to prove analyticity of the optimizer by the one-variable inverse
function theorem.
-/

namespace InducedStars

open Set

/-- Clique proportion solving the entropy stationary equation at cross density `q`. -/
noncomputable def c4StationaryCliqueProportion (q : ℝ) : ℝ :=
  Real.log (1 - q) / (Real.log q + Real.log (1 - q))

noncomputable def c4StationaryCliqueDerivative (q : ℝ) : ℝ :=
  (-Real.log q / (1 - q) - Real.log (1 - q) / q) /
    (Real.log q + Real.log (1 - q)) ^ 2

/-- Total density corresponding to the stationary split model with cross density `q`. -/
noncomputable def c4StationaryTotalDensity (q : ℝ) : ℝ :=
  c4StationaryCliqueProportion q ^ 2 +
    2 * c4StationaryCliqueProportion q * (1 - c4StationaryCliqueProportion q) * q

noncomputable def c4StationaryTotalDensityDerivative (q : ℝ) : ℝ :=
  2 * c4StationaryCliqueDerivative q *
      (c4StationaryCliqueProportion q + q * (1 - 2 * c4StationaryCliqueProportion q)) +
    2 * c4StationaryCliqueProportion q * (1 - c4StationaryCliqueProportion q)

lemma c4Stationary_log_sum_neg {q : ℝ} (hq : q ∈ Ioo 0 1) :
    Real.log q + Real.log (1 - q) < 0 := by
  exact add_neg (Real.log_neg hq.1 hq.2)
    (Real.log_neg (sub_pos.mpr hq.2) (by linarith [hq.1]))

lemma c4StationaryCliqueProportion_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 1) :
    c4StationaryCliqueProportion q ∈ Ioo 0 1 := by
  have hA := Real.log_neg hq.1 hq.2
  have hB := Real.log_neg (sub_pos.mpr hq.2) (show 1 - q < 1 by linarith [hq.1])
  have hsum := c4Stationary_log_sum_neg hq
  exact ⟨div_pos_of_neg_of_neg hB hsum, (div_lt_one_of_neg hsum).mpr (by linarith)⟩

lemma analyticAt_c4StationaryCliqueProportion {q : ℝ} (hq : q ∈ Ioo 0 1) :
    AnalyticAt ℝ c4StationaryCliqueProportion q := by
  have hA : AnalyticAt ℝ Real.log q := analyticAt_log hq.1
  have hB : AnalyticAt ℝ (fun y : ℝ => Real.log (1 - y)) q :=
    (analyticAt_const.sub analyticAt_id).log (sub_pos.mpr hq.2)
  exact hB.div (hA.add hB) (c4Stationary_log_sum_neg hq).ne

lemma hasDerivAt_c4StationaryCliqueProportion {q : ℝ} (hq : q ∈ Ioo 0 1) :
    HasDerivAt c4StationaryCliqueProportion (c4StationaryCliqueDerivative q) q := by
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1 - q ≠ 0 := sub_ne_zero.mpr hq.2.ne'
  have hsum : Real.log q + Real.log (1 - q) ≠ 0 := (c4Stationary_log_sum_neg hq).ne
  have hA := Real.hasDerivAt_log hq0
  have hB := ((hasDerivAt_const q 1).sub (hasDerivAt_id q)).log hq1
  have hd := hB.div (hA.add hB) hsum
  convert hd using 1 <;> try rfl
  dsimp [c4StationaryCliqueDerivative]
  field_simp [hq0, hq1, hsum]
  ring

lemma c4StationaryCliqueDerivative_pos {q : ℝ} (hq : q ∈ Ioo 0 1) :
    0 < c4StationaryCliqueDerivative q := by
  have hA := Real.log_neg hq.1 hq.2
  have hB := Real.log_neg (sub_pos.mpr hq.2) (show 1 - q < 1 by linarith [hq.1])
  have hnum : 0 < -Real.log q / (1 - q) - Real.log (1 - q) / q := by
    have hpos := div_pos (neg_pos.mpr hA) (sub_pos.mpr hq.2)
    have hneg := div_neg_of_neg_of_pos hB hq.1
    linarith
  exact div_pos hnum (sq_pos_of_ne_zero (c4Stationary_log_sum_neg hq).ne)

lemma analyticAt_c4StationaryTotalDensity {q : ℝ} (hq : q ∈ Ioo 0 1) :
    AnalyticAt ℝ c4StationaryTotalDensity q := by
  have hx := analyticAt_c4StationaryCliqueProportion hq
  exact (hx.pow 2).add (((analyticAt_const.mul hx).mul (analyticAt_const.sub hx)).mul analyticAt_id)

lemma hasDerivAt_c4StationaryTotalDensity {q : ℝ} (hq : q ∈ Ioo 0 1) :
    HasDerivAt c4StationaryTotalDensity (c4StationaryTotalDensityDerivative q) q := by
  have hx := hasDerivAt_c4StationaryCliqueProportion hq
  have hd := (hx.pow 2).add
    ((((hx.const_mul 2).mul ((hasDerivAt_const q 1).sub hx)).mul (hasDerivAt_id q)))
  convert hd using 1 <;> try rfl
  dsimp [c4StationaryTotalDensityDerivative]
  ring

lemma c4StationaryTotalDensityDerivative_pos {q : ℝ} (hq : q ∈ Ioo 0 1) :
    0 < c4StationaryTotalDensityDerivative q := by
  have hx := c4StationaryCliqueProportion_mem_Ioo hq
  have ha : 0 < c4StationaryCliqueProportion q + q * (1 - 2 * c4StationaryCliqueProportion q) := by
    nlinarith [mul_pos hx.1 (sub_pos.mpr hq.2), mul_pos hq.1 (sub_pos.mpr hx.2)]
  exact add_pos (mul_pos (mul_pos (by norm_num) (c4StationaryCliqueDerivative_pos hq)) ha)
    (mul_pos (mul_pos (by norm_num) hx.1) (sub_pos.mpr hx.2))

lemma deriv_c4StationaryTotalDensity_pos {q : ℝ} (hq : q ∈ Ioo 0 1) :
    0 < deriv c4StationaryTotalDensity q := by
  rw [(hasDerivAt_c4StationaryTotalDensity hq).deriv]
  exact c4StationaryTotalDensityDerivative_pos hq

lemma strictMonoOn_c4StationaryTotalDensity :
    StrictMonoOn c4StationaryTotalDensity (Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    (fun q hq => (analyticAt_c4StationaryTotalDensity hq).continuousAt.continuousWithinAt)
  intro q hq
  exact deriv_c4StationaryTotalDensity_pos (interior_subset hq)

lemma c4StationaryTotalDensity_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 1) :
    c4StationaryTotalDensity q ∈ Ioo 0 1 := by
  have hx := c4StationaryCliqueProportion_mem_Ioo hq
  have hc : 0 < 2 * c4StationaryCliqueProportion q * (1 - c4StationaryCliqueProportion q) :=
    mul_pos (mul_pos (by norm_num) hx.1) (sub_pos.mpr hx.2)
  have hcross := mul_lt_mul_of_pos_left hq.2 hc
  have hcross0 := mul_pos hc hq.1
  unfold c4StationaryTotalDensity
  constructor
  · nlinarith [sq_nonneg (c4StationaryCliqueProportion q)]
  · nlinarith [sq_pos_of_pos (sub_pos.mpr hx.2)]

lemma c4StationaryCliqueProportion_at_optimizer {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4StationaryCliqueProportion (c4SplitCrossDensity γ (c4Lambda γ)) = c4Lambda γ := by
  have hq := c4SplitCrossDensity_c4Lambda_mem_Ioo hγ
  have hsum := (c4Stationary_log_sum_neg hq).ne
  have hstat := c4SplitEntropyNatDerivative_c4Lambda_eq_zero hγ
  unfold c4SplitEntropyNatDerivative at hstat
  unfold c4StationaryCliqueProportion
  apply (div_eq_iff hsum).mpr
  nlinarith

lemma c4StationaryTotalDensity_at_optimizer {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4StationaryTotalDensity (c4SplitCrossDensity γ (c4Lambda γ)) = γ := by
  have hx := c4Lambda_mem_Ioo hγ
  have hx0 : c4Lambda γ ≠ 0 := hx.1.ne'
  have hx1 : 1 - c4Lambda γ ≠ 0 := sub_ne_zero.mpr hx.2.ne'
  unfold c4StationaryTotalDensity
  rw [c4StationaryCliqueProportion_at_optimizer hγ]
  unfold c4SplitCrossDensity
  field_simp [hx0, hx1]
  ring

end InducedStars
