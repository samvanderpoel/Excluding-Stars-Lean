import InducedStars.Structure.Critical.WindowCompletionGuards
import InducedStars.Structure.Critical.WindowLogBalance

/-!
# The signed first-order completion exponent
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The first-order entropy term, arranged to expose the critical
cancellation and its signed drift. -/
def criticalWindowFirstOrder (k : ℕ) (a : ℝ) (n s t : ℕ) : ℝ :=
  (criticalWindowCapacityLoss k n s -
      ((k - 2 : ℕ) : ℝ) * criticalWindowSelectedIncrease k n s t) *
    Real.log (1 - criticalWindowReferenceDensity k a n) +
  criticalWindowSelectedIncrease k n s t *
    (((k - 1 : ℕ) : ℝ) * Real.log (1 - criticalWindowReferenceDensity k a n) -
      Real.log (criticalWindowReferenceDensity k a n))

/-- The cancellation term has only the remainder edge count on the
squared-logarithm scale. -/
theorem criticalWindowCancellation_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦
      (criticalWindowCapacityLoss k n (s n) -
        ((k - 2 : ℕ) : ℝ) * criticalWindowSelectedIncrease k n (s n) (t n)) /
          Real.log (n : ℝ) ^ 2) atTop (𝓝 (((k - 2 : ℕ) : ℝ) * y)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hsmall := hs.mul (tendsto_const_nhds.div_atTop hlog :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
  simp only [mul_zero] at hsmall
  have h := (((hsmall.div_const 2).add ht).const_mul ((k - 2 : ℕ) : ℝ)).add
    (((hres (fun n ↦ n - s n)).sub (hres id)).const_mul ((k - 1 : ℕ) : ℝ))
  simp only [zero_div, zero_add, sub_self, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowLogarithmicSize_le_order hs] with n hn
  rw [criticalWindowCapacityLoss_sub_mul_selectedIncrease hk hn]
  dsimp only [id_eq, Function.comp_apply]
  ring

/-- The first-order completion exponent retains the exact signed coefficient
of the critical-window parameter. -/
theorem criticalWindowFirstOrder_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ criticalWindowFirstOrder k a n (s n) (t n) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 (y * Real.log (pK k / (1 - pK k)) - a / criticalWindowThreshold k * x)) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hlog := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (criticalWindowReferenceDensity_tendsto hk a)).log hq.ne'
  have h := ((criticalWindowCancellation_scale_tendsto hk hs ht).mul hlog).add
    ((criticalWindowSelectedIncrease_scale_tendsto hk hs ht).mul
      (criticalWindowLogBalance_scale_tendsto hk a))
  have heq : ((k - 2 : ℕ) : ℝ) * y * Real.log (1 - pK k) +
      (x / (k - 1 : ℕ)) *
        (-(criticalWindowLogSlope k * ((k - 1 : ℕ) : ℝ) * a / (k - 2 : ℕ))) =
      y * Real.log (pK k / (1 - pK k)) - a / criticalWindowThreshold k * x := by
    rw [Real.log_div hp.ne' hq.ne', log_pK_eq]
    have hr : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
    have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 2 ≠ 0 by omega)
    have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
    rw [← criticalWindowLogSlope_mul_window_scale hk a]
    field_simp
    rw [hrel]
    ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold criticalWindowFirstOrder
  field_simp <;> ring

end InducedStars
