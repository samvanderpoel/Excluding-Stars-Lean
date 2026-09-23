import InducedStars.Structure.Critical.WindowReference
import InducedStars.Structure.Critical.WindowScales

/-!
# Moving logarithmic remainder sizes

These limits hold along every sequence of remainder sizes on the logarithmic
scale and every sequence of remainder edge counts on the squared-logarithm
scale.  The signed capacity and selected-count shifts retain their exact
finite definitions.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowLogarithmicSize_div_order_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (s n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h := hs.mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  have hlogpos := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hlogpos] with n hn
  change 0 < Real.log (n : ℝ) at hn
  field_simp

theorem eventually_criticalWindowLogarithmicSize_le_order
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n : ℕ in atTop, s n ≤ n := by
  have h := (criticalWindowLogarithmicSize_div_order_tendsto_zero hs).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact_mod_cast ((div_lt_one hnR).mp hn).le

/-- The capacity loss has its expected first-order logarithmic scale. -/
theorem criticalWindowCapacityLoss_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ criticalWindowCapacityLoss k n (s n) /
      ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) * x)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden := tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlog
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hquad := hs.mul (criticalWindowLogarithmicSize_div_order_tendsto_zero hs)
  simp only [mul_zero] at hquad
  have h := (((hs.const_mul (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ))).sub
    (hquad.const_mul (((k - 2 : ℕ) : ℝ) / (2 * (k - 1 : ℕ))))).add
      (hres (fun n ↦ n - s n))).sub (hres id)
  simp only [mul_zero, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_ge_atTop 1] with n hsn hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [criticalWindowCapacityLoss_eq hk hsn]
  dsimp only [id_eq, Function.comp_apply]
  field_simp <;> ring

/-- The selected-count shift is signed, and its leading scale is independent
of the quadratically smaller number of prescribed remainder edges. -/
theorem criticalWindowSelectedIncrease_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ criticalWindowSelectedIncrease k n (s n) (t n) /
      ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (x / (k - 1 : ℕ))) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden := tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlog
  have hres (v : ℕ → ℕ) := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := v n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := v n) hk) hden
  have hquad := hs.mul (criticalWindowLogarithmicSize_div_order_tendsto_zero hs)
  have hsmall := hs.mul (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0))
  have htiny := ht.mul
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop)
  simp only [mul_zero] at hquad hsmall htiny
  have h := (((((hs.div_const ((k - 1 : ℕ) : ℝ)).sub
      (hquad.div_const (2 * ((k - 1 : ℕ) : ℝ)))).sub
        (hsmall.div_const 2)).sub htiny).add (hres id)).sub (hres (fun n ↦ n - s n))
  simp only [zero_div, sub_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_ge_atTop 1, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hsn hn hl
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [criticalWindowSelectedIncrease_eq hk hsn]
  dsimp only [id_eq, Function.comp_apply]
  field_simp <;> ring

end InducedStars
