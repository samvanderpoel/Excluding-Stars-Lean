import InducedStars.Structure.Critical.WindowPositivePerturbations
import InducedStars.Structure.Critical.WindowFirstOrder

/-!
# Signed linear drift for every positive remainder size
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowPositiveCancellation_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦
      (criticalWindowCapacityLoss k n (s n) -
        ((k - 2 : ℕ) : ℝ) * criticalWindowSelectedIncrease k n (s n) (t n)) /
          ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (((k - 2 : ℕ) : ℝ) * z)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden := criticalWindowPositiveScale_tendsto_atTop hspos
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hsmall : Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have h := (((hsmall.div_const 2).add ht).const_mul ((k - 2 : ℕ) : ℝ)).add
    (((hres (fun n ↦ n - s n)).sub (hres id)).const_mul ((k - 1 : ℕ) : ℝ))
  simp only [zero_div, zero_add, sub_self, mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [hspos, eventually_criticalWindowLogarithmicSize_le_order hs] with n hp hn
  have hsR : (s n : ℝ) ≠ 0 := by exact_mod_cast (show s n ≠ 0 by omega)
  rw [criticalWindowCapacityLoss_sub_mul_selectedIncrease hk hn]
  dsimp only [id_eq]
  field_simp <;> ring

theorem criticalWindowPositiveFirstOrder_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦ criticalWindowFirstOrder k a n (s n) (t n) /
      ((s n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (z * Real.log (pK k / (1 - pK k)) - a / criticalWindowThreshold k)) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hlog := ((tendsto_const_nhds (x := (1 : ℝ))).sub
    (criticalWindowReferenceDensity_tendsto hk a)).log hq.ne'
  have h := ((criticalWindowPositiveCancellation_scale_tendsto hk hspos hs ht).mul hlog).add
    ((criticalWindowPositiveSelectedIncrease_scale_tendsto hk hspos hs ht).mul
      (criticalWindowLogBalance_scale_tendsto hk a))
  have heq : ((k - 2 : ℕ) : ℝ) * z * Real.log (1 - pK k) +
      (1 / ((k - 1 : ℕ) : ℝ)) *
        (-(criticalWindowLogSlope k * ((k - 1 : ℕ) : ℝ) * a / (k - 2 : ℕ))) =
      z * Real.log (pK k / (1 - pK k)) - a / criticalWindowThreshold k := by
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
