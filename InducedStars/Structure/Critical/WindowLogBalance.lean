import InducedStars.Structure.Critical.WindowReference
import InducedStars.Structure.Critical.WindowSlope

/-!
# Signed logarithmic balance along the critical window
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The first-order logarithmic cancellation drifts at the signed window
speed; the quadratic logarithm remainder vanishes after this normalization. -/
theorem criticalWindowLogBalance_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (fun n ↦
      (((k - 1 : ℕ) : ℝ) * Real.log (1 - criticalWindowReferenceDensity k a n) -
        Real.log (criticalWindowReferenceDensity k a n)) *
          (n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (-(criticalWindowLogSlope k * ((k - 1 : ℕ) : ℝ) * a /
        (k - 2 : ℕ)))) := by
  let q := criticalWindowReferenceDensity k a
  have hq := criticalWindowReferenceDensity_tendsto hk a
  have hshift := criticalWindowReferenceDensity_displacement_tendsto hk a
  have hd : Tendsto (fun n ↦ q n - pK k) atTop (𝓝 0) := by
    simpa only [sub_self] using hq.sub_const (pK k)
  have he : Tendsto (fun n ↦
      (2 * ((k - 1 : ℕ) : ℝ) / (1 - pK k) ^ 2 + 2 / (pK k) ^ 2) *
        ((q n - pK k) * n / Real.log (n : ℝ)) * (q n - pK k)) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (hshift.const_mul
        (2 * ((k - 1 : ℕ) : ℝ) / (1 - pK k) ^ 2 + 2 / (pK k) ^ 2)).mul hd
  have had := hd.abs
  simp only [abs_zero] at had
  have hnear0 : ∀ᶠ n : ℕ in atTop, |q n - pK k| ≤ pK k / 2 := by
    have h := had.eventually (Iio_mem_nhds (half_pos (pK_pos (k := k) (by omega))))
    simpa only [abs_zero] using h.mono (fun _ hn ↦ hn.le)
  have hnear1 : ∀ᶠ n : ℕ in atTop, |q n - pK k| ≤ (1 - pK k) / 2 := by
    have h := had.eventually
      (Iio_mem_nhds (half_pos (sub_pos.mpr (pK_lt_one (k := k) (by omega)))))
    simpa only [abs_zero] using h.mono (fun _ hn ↦ hn.le)
  have herr : Tendsto (fun n ↦
      ((((k - 1 : ℕ) : ℝ) * Real.log (1 - q n) - Real.log (q n)) +
        criticalWindowLogSlope k * (q n - pK k)) *
          (n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ he
    have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hnear0, hnear1, hlog] with n h0 h1 hl
    have h := mul_le_mul_of_nonneg_right (abs_criticalWindowLogBalance_add_slope_le hk h0 h1)
      (div_nonneg (Nat.cast_nonneg n) hl.le)
    change 0 < Real.log (n : ℝ) at hl
    simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), abs_of_pos hl]
    convert h using 1 <;> first | rfl | (dsimp only [q, Function.comp_apply]; ring)
  have h := herr.sub (hshift.const_mul (criticalWindowLogSlope k))
  convert h using 1
  · ext n
    dsimp only [q]
    ring
  · ring

end InducedStars
