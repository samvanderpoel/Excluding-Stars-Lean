import InducedStars.Analysis.Entropy
import Mathlib.Analysis.Real.Sqrt

/-!
# Feasible split-graph entropy

The clique proportion is `x`; the other part is independent.  The density
constraint determines the cross-edge density.  The entropy in this file is
in natural units, with an explicit conversion to the paper's base-two units.
-/

namespace InducedStars

open Set

/-- The cross-edge density forced by total density `γ` and clique proportion `x`. -/
noncomputable def c4SplitCrossDensity (γ x : ℝ) : ℝ :=
  (γ - x ^ 2) / (2 * x * (1 - x))

/-- Natural-log entropy of the split model. -/
noncomputable def c4SplitEntropyNat (γ x : ℝ) : ℝ :=
  x * (1 - x) * Real.binEntropy (c4SplitCrossDensity γ x)

/-- The split-model entropy in the paper's base-two convention. -/
noncomputable def c4SplitEntropy (γ x : ℝ) : ℝ :=
  x * (1 - x) * binaryEntropy (c4SplitCrossDensity γ x)

lemma c4SplitEntropy_eq_nat_div_log_two (γ x : ℝ) :
    c4SplitEntropy γ x = c4SplitEntropyNat γ x / Real.log 2 := by
  simp only [c4SplitEntropy, c4SplitEntropyNat, binaryEntropy]
  ring

/-- Both endpoints of the feasible interval lie strictly between zero and one. -/
lemma c4Split_feasible_endpoints {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    0 < 1 - Real.sqrt (1 - γ) ∧
      1 - Real.sqrt (1 - γ) < Real.sqrt γ ∧ Real.sqrt γ < 1 := by
  have hsγ := Real.sq_sqrt hγ.1.le
  have hs₁ := Real.sq_sqrt (show 0 ≤ 1 - γ by linarith [hγ.2])
  have hpγ := Real.sqrt_pos.mpr hγ.1
  have hp₁ := Real.sqrt_pos.mpr (show 0 < 1 - γ by linarith [hγ.2])
  have hl : Real.sqrt (1 - γ) < 1 := by nlinarith [hγ.1]
  have hr : Real.sqrt γ < 1 := by nlinarith [hγ.2]
  refine ⟨by linarith, ?_, hr⟩
  nlinarith [mul_pos hpγ hp₁]

lemma c4Split_mem_unitInterval {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    x ∈ Ioo 0 1 := by
  obtain ⟨hl, _, hr⟩ := c4Split_feasible_endpoints hγ
  exact ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩

lemma c4SplitCrossDensity_mem_Icc {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    c4SplitCrossDensity γ x ∈ Icc 0 1 := by
  obtain ⟨hx0, hx1⟩ := c4Split_mem_unitInterval hγ hx
  have hd : 0 < 2 * x * (1 - x) := by positivity
  have hsγ := Real.sq_sqrt hγ.1.le
  have hs₁ := Real.sq_sqrt (show 0 ≤ 1 - γ by linarith [hγ.2])
  have hnum : 0 ≤ γ - x ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2)
      (show 0 ≤ Real.sqrt γ + x by positivity)]
  have hupper : γ - x ^ 2 ≤ 2 * x * (1 - x) := by
    nlinarith [mul_nonneg (show 0 ≤ Real.sqrt (1 - γ) - (1 - x) by linarith [hx.1])
      (show 0 ≤ Real.sqrt (1 - γ) + (1 - x) by positivity)]
  exact ⟨div_nonneg hnum hd.le, (div_le_one hd).mpr hupper⟩

lemma c4SplitCrossDensity_mem_Ioo {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    c4SplitCrossDensity γ x ∈ Ioo 0 1 := by
  obtain ⟨hx0, hx1⟩ := c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩
  have hd : 0 < 2 * x * (1 - x) := by positivity
  have hsγ := Real.sq_sqrt hγ.1.le
  have hs₁ := Real.sq_sqrt (show 0 ≤ 1 - γ by linarith [hγ.2])
  have hnum : 0 < γ - x ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx.2)
      (show 0 < Real.sqrt γ + x by positivity)]
  have hupper : γ - x ^ 2 < 2 * x * (1 - x) := by
    nlinarith [mul_pos (show 0 < Real.sqrt (1 - γ) - (1 - x) by linarith [hx.1])
      (show 0 < Real.sqrt (1 - γ) + (1 - x) by positivity)]
  exact ⟨div_pos hnum hd, (div_lt_one hd).mpr hupper⟩

lemma c4SplitCrossDensity_lowerEndpoint {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitCrossDensity γ (1 - Real.sqrt (1 - γ)) = 1 := by
  have hx := c4Split_mem_unitInterval hγ
    (show 1 - Real.sqrt (1 - γ) ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)
      from ⟨le_rfl, (c4Split_feasible_endpoints hγ).2.1.le⟩)
  rcases hx with ⟨hx0, hx1⟩
  have hd : 2 * (1 - Real.sqrt (1 - γ)) * (1 - (1 - Real.sqrt (1 - γ))) ≠ 0 := by
    exact ne_of_gt (by positivity)
  rw [c4SplitCrossDensity, div_eq_one_iff_eq hd]
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 - γ by linarith [hγ.2])]

lemma c4SplitCrossDensity_upperEndpoint {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitCrossDensity γ (Real.sqrt γ) = 0 := by
  simp [c4SplitCrossDensity, Real.sq_sqrt hγ.1.le]

lemma continuousAt_c4SplitCrossDensity (γ : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    ContinuousAt (c4SplitCrossDensity γ) x := by
  rcases hx with ⟨hx0, hx1⟩
  unfold c4SplitCrossDensity
  exact (continuousAt_const.sub (continuousAt_id.pow 2)).div
    ((continuousAt_const.mul continuousAt_id).mul
      (continuousAt_const.sub continuousAt_id)) (ne_of_gt (by positivity))

lemma continuousAt_c4SplitEntropyNat (γ : ℝ) {x : ℝ} (hx : x ∈ Ioo 0 1) :
    ContinuousAt (c4SplitEntropyNat γ) x := by
  exact (continuousAt_id.mul (continuousAt_const.sub continuousAt_id)).mul
    (Real.binEntropy_continuous.continuousAt.comp
      (continuousAt_c4SplitCrossDensity γ hx))

/-- Entropy remains continuous at the feasible endpoints, where the cross density
is respectively one and zero. -/
lemma continuousOn_c4SplitEntropyNat {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ContinuousOn (c4SplitEntropyNat γ)
      (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) := by
  intro x hx
  exact (continuousAt_c4SplitEntropyNat γ (c4Split_mem_unitInterval hγ hx)).continuousWithinAt

lemma continuousOn_c4SplitEntropy {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ContinuousOn (c4SplitEntropy γ)
      (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) := by
  have heq : c4SplitEntropy γ = fun x => c4SplitEntropyNat γ x / Real.log 2 := by
    funext x
    exact c4SplitEntropy_eq_nat_div_log_two γ x
  rw [heq]
  exact (continuousOn_c4SplitEntropyNat hγ).div_const (Real.log 2)

lemma c4SplitEntropyNat_lowerEndpoint {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitEntropyNat γ (1 - Real.sqrt (1 - γ)) = 0 := by
  simp [c4SplitEntropyNat, c4SplitCrossDensity_lowerEndpoint hγ]

lemma c4SplitEntropyNat_upperEndpoint {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitEntropyNat γ (Real.sqrt γ) = 0 := by
  simp [c4SplitEntropyNat, c4SplitCrossDensity_upperEndpoint hγ]

lemma c4SplitEntropyNat_pos {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    0 < c4SplitEntropyNat γ x := by
  obtain ⟨hx0, hx1⟩ := c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩
  have hq := c4SplitCrossDensity_mem_Ioo hγ hx
  exact mul_pos (mul_pos hx0 (sub_pos.mpr hx1)) (Real.binEntropy_pos hq.1 hq.2)

end InducedStars
