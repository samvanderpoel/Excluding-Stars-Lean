import InducedStars.Structure.Critical.WindowBinomial

/-!
# Reference density in the logarithmic critical window

The full equitable reference remains in the interior of the cross-edge
slice.  Its displacement from the critical probability is of order
`log n / n`, with the signed coefficient retained.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Cross density of the full equitable reference slice. -/
def criticalWindowReferenceDensity (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (criticalWindowReferenceSelected k a n : ℝ) / criticalWindowCoreCapacity k n 0

theorem eventually_criticalWindowReference_feasible
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      criticalWindowCoreInternal k n 0 ≤ criticalWindowEdgeCount k a n := by
  have h := eventually_balancedDivision_internal_le_of_density_gt
    k hk (gammaK k) (one_div_parts_lt_gammaK hk)
      (criticalWindowEdgeCount k a) (criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk a)
  filter_upwards [h, eventually_ge_atTop (k - 1)] with n hn hn'
  simpa only [criticalWindowCoreInternal, Nat.sub_zero,
    supercriticalBalancedDivision_internalCapacity_eq hk hn'] using hn hn'

theorem criticalWindowEdgeCount_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (fun n ↦ (criticalWindowEdgeCount k a n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (gammaK k / 2)) := by
  have h := (hasAsymptoticEdgeDensity_orderedSquare
    (criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk a)).div_const 2
  convert h using 1
  ext n
  ring

theorem criticalWindowReferenceSelected_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (fun n ↦ (criticalWindowReferenceSelected k a n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (pK k * criticalReferenceCapacityScale k)) := by
  have hC := (criticalBalancedInternalCapacity_orderedSquare_tendsto k hk).div_const 2
  have heq : gammaK k / 2 - (1 / ((k - 1 : ℕ) : ℝ)) / 2 =
      pK k * criticalReferenceCapacityScale k := by
    have hr : ((k - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
    unfold gammaK criticalReferenceCapacityScale
    field_simp <;> ring
  rw [← heq]
  apply ((criticalWindowEdgeCount_scale_tendsto hk a).sub hC).congr'
  filter_upwards [eventually_criticalWindowReference_feasible hk a] with n hn
  rw [criticalWindowReferenceSelected, Nat.cast_sub hn]
  simp only [criticalWindowCoreInternal, Nat.sub_zero]
  ring

theorem criticalWindowReferenceDensity_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (criticalWindowReferenceDensity k a) atTop (𝓝 (pK k)) := by
  have hc : criticalReferenceCapacityScale k ≠ 0 := by
    unfold criticalReferenceCapacityScale
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
    positivity
  have h := (criticalWindowReferenceSelected_scale_tendsto hk a).div
    (criticalTargetCapacity_scale_tendsto k hk) hc
  simp only [mul_div_cancel_right₀ _ hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  unfold criticalWindowReferenceDensity criticalWindowCoreCapacity criticalTargetCapacity
  simp only [Nat.sub_zero, Pi.div_apply]
  field_simp

theorem eventually_criticalWindowReference_interior
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < criticalWindowReferenceSelected k a n ∧
      criticalWindowReferenceSelected k a n < criticalWindowCoreCapacity k n 0 := by
  have hd := (criticalWindowReferenceDensity_tendsto hk a).eventually
    (Ioo_mem_nhds (pK_pos (by omega)) (pK_lt_one (by omega)))
  filter_upwards [hd] with n hn
  have hN : (0 : ℝ) < criticalWindowCoreCapacity k n 0 := by
    by_contra h
    have hz : criticalWindowCoreCapacity k n 0 = 0 := by
      exact_mod_cast (le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _))
    simp [criticalWindowReferenceDensity, hz] at hn
  constructor
  · have hm : (0 : ℝ) < criticalWindowReferenceSelected k a n :=
      (div_pos_iff_of_pos_right hN).mp hn.1
    exact_mod_cast hm
  · have hm : (criticalWindowReferenceSelected k a n : ℝ) <
        criticalWindowCoreCapacity k n 0 := (div_lt_one hN).mp hn.2
    exact_mod_cast hm

/-- The selected-count displacement from the critical cross density has
its signed logarithmic-window coefficient. -/
theorem criticalWindowReferenceDisplacement_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (fun n ↦
      ((criticalWindowReferenceSelected k a n : ℝ) -
        pK k * criticalWindowCoreCapacity k n 0) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (a / 2)) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden := tendsto_natCast_atTop_atTop.atTop_mul_atTop₀ hlog
  have hf := tendsto_bdd_div_atTop_nhds_zero
    ((eventually_criticalWindowFloorError_mem_Ico hk a).mono fun _ h ↦ h.1)
    ((eventually_criticalWindowFloorError_mem_Ico hk a).mono fun _ h ↦ h.2.le) hden
  have hr := tendsto_bdd_div_atTop_nhds_zero
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_nonneg (n := n) hk)
    (Eventually.of_forall fun n ↦ criticalBalancedResidueError_le (n := n) hk) hden
  have hn : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlin : Tendsto (fun n : ℕ ↦ ((1 - gammaK k) / 2) / Real.log (n : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have hmain := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hn).const_mul (a / 2)).add hlin).sub hf
  have hmain' := hmain.sub (hr.const_mul (1 - pK k))
  simp only [sub_zero, mul_one, add_zero, mul_zero] at hmain'
  apply hmain'.congr'
  filter_upwards [eventually_criticalWindowReference_feasible hk a,
    eventually_ge_atTop 1, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hfeas hn hl
  have hn' : 0 < n := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn'.ne'
  rw [criticalWindowReferenceSelected_sub_p_mul_capacity_eq hk hn' hfeas]
  field_simp <;> ring

/-- The normalized signed shift of the cross density. -/
theorem criticalWindowReferenceDensity_displacement_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    Tendsto (fun n ↦ (criticalWindowReferenceDensity k a n - pK k) *
      (n : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 (((k - 1 : ℕ) : ℝ) * a / (k - 2 : ℕ))) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hc : criticalReferenceCapacityScale k ≠ 0 := by
    unfold criticalReferenceCapacityScale
    positivity
  have h := (criticalWindowReferenceDisplacement_scale_tendsto hk a).div
    (criticalTargetCapacity_scale_tendsto k hk) hc
  have heq : (a / 2) / criticalReferenceCapacityScale k =
      ((k - 1 : ℕ) : ℝ) * a / (k - 2 : ℕ) := by
    unfold criticalReferenceCapacityScale
    field_simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowReference_interior hk a,
    eventually_ge_atTop 1] with n hinter hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hN : (criticalWindowCoreCapacity k n 0 : ℝ) ≠ 0 := by
    exact_mod_cast (lt_trans hinter.1 hinter.2).ne'
  unfold criticalWindowReferenceDensity
  change ((_ - _ * (criticalWindowCoreCapacity k n 0 : ℝ)) / _) /
    ((criticalWindowCoreCapacity k n 0 : ℝ) / _) = _
  field_simp <;> ring

end InducedStars
