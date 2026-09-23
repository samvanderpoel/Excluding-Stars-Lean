import InducedStars.Structure.Critical.WindowPositiveScales
import InducedStars.Structure.Critical.WindowPerturbationLimits

/-!
# Capacity perturbations per positive remainder vertex
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowPositiveCapacityLoss_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s : ℕ → ℕ} {x : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ criticalWindowCapacityLoss k n (s n) / ((s n : ℝ) * n))
      atTop (𝓝 (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ))) := by
  have hden := criticalWindowPositiveSize_order_tendsto_atTop hspos
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hsmall := criticalWindowLogarithmicSize_div_order_tendsto_zero hs
  have h := (((tendsto_const_nhds (x := ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ))).sub
    (hsmall.const_mul (((k - 2 : ℕ) : ℝ) / (2 * (k - 1 : ℕ))))).add
      (hres (fun n ↦ n - s n))).sub (hres id)
  simp only [mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [hspos, eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_ge_atTop 1] with n hsp hsn hn
  have hsR : (s n : ℝ) ≠ 0 := by exact_mod_cast (show s n ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [criticalWindowCapacityLoss_eq hk hsn]
  dsimp only [id_eq]
  field_simp <;> ring

theorem criticalWindowPositiveSelectedIncrease_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦ criticalWindowSelectedIncrease k n (s n) (t n) / ((s n : ℝ) * n))
      atTop (𝓝 (1 / ((k - 1 : ℕ) : ℝ))) := by
  have hden := criticalWindowPositiveSize_order_tendsto_atTop hspos
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hsmall := criticalWindowLogarithmicSize_div_order_tendsto_zero hs
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have htiny := ht.mul hlog
  have hninv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (((((tendsto_const_nhds (x := 1 / ((k - 1 : ℕ) : ℝ))).sub
    (hsmall.div_const (2 * ((k - 1 : ℕ) : ℝ)))).sub (hninv.div_const 2)).sub htiny).add
      (hres id)).sub (hres (fun n ↦ n - s n))
  simp only [zero_div, mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  have hlogpos := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hspos, eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_ge_atTop 1, hlogpos] with n hsp hsn hn hl
  have hsR : (s n : ℝ) ≠ 0 := by exact_mod_cast (show s n ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change 0 < Real.log (n : ℝ) at hl
  rw [criticalWindowSelectedIncrease_eq hk hsn]
  dsimp only [id_eq]
  field_simp <;> ring

end InducedStars
