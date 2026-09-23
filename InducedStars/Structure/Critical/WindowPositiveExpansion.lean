import InducedStars.Structure.Critical.WindowPositiveFirstOrder
import InducedStars.Structure.Critical.WindowPositiveQuadratic
import InducedStars.Structure.Critical.WindowCompletionExpansion

/-!
# Sharp completion expansion for every positive remainder size
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The two-sided completion estimate on the finer `s log n` scale.
This includes every positive bounded or sublogarithmic remainder sequence. -/
theorem criticalWindowPositiveCompletion_log_ratio_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦
      (Real.log (criticalWindowCompletionCount k a n (s n) (t n) : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) /
          ((s n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (-(gammaK k / criticalWindowThreshold k) * x -
        a / criticalWindowThreshold k + z * Real.log (pK k / (1 - pK k)))) := by
  have hc : 0 < criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
    positivity
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := pK_lt_one (show 2 ≤ k by omega)
  have hpc := mul_pos hp hc
  have hqc : 0 < criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k := by nlinarith
  have hN : Tendsto (fun n ↦ (criticalWindowCoreCapacity k n 0 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (criticalReferenceCapacityScale k)) := criticalTargetCapacity_scale_tendsto k hk
  have hM := criticalWindowReferenceSelected_scale_tendsto hk a
  have hK := criticalWindowPositiveCapacityLoss_scale_tendsto hk hspos hs
  have hL := criticalWindowPositiveSelectedIncrease_scale_tendsto hk hspos hs ht
  have hNM : Tendsto (fun n ↦
      ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) / (n : ℝ) ^ 2)
      atTop (𝓝 (criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k)) := by
    simpa only [sub_div] using hN.sub hM
  have hKL : Tendsto (fun n ↦
      (criticalWindowCapacityLoss k n (s n) + criticalWindowSelectedIncrease k n (s n) (t n)) /
        ((s n : ℝ) * n))
      atTop (𝓝 (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) + 1 / ((k - 1 : ℕ) : ℝ))) := by
    simpa only [add_div] using hK.add hL
  have he1 := criticalWindowPositiveCubicTerm_tendsto_zero hc.ne' hspos hs hN hK
  have he2 := criticalWindowPositiveCubicTerm_tendsto_zero hpc.ne' hspos hs hM hL
  have he3 := criticalWindowPositiveCubicTerm_tendsto_zero hqc.ne' hspos hs hNM hKL
  have he4 := (criticalWindowPositiveScale_inv_tendsto_zero hspos).const_mul 4
  have herrbound : Tendsto (fun n ↦
      (4 * (|criticalWindowCapacityLoss k n (s n)| ^ 3 / (criticalWindowCoreCapacity k n 0 : ℝ) ^ 2 +
        |criticalWindowSelectedIncrease k n (s n) (t n)| ^ 3 / (criticalWindowReferenceSelected k a n : ℝ) ^ 2 +
        |criticalWindowCapacityLoss k n (s n) + criticalWindowSelectedIncrease k n (s n) (t n)| ^ 3 /
          ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) ^ 2) + 4) /
          ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
    convert (((he1.add he2).add he3).const_mul 4).add he4 using 1
    · ext n
      ring
    · norm_num
  have ht' := criticalWindowPositiveEdgeCount_logSq_tendsto hspos hs ht
  have hguard := eventually_criticalWindowCompletion_binomial_guards hk a hs ht'
  have herr : Tendsto (fun n ↦
      (Real.log (Nat.choose (criticalWindowCoreCapacity k n (s n))
          (criticalWindowCompletionSelected k a n (s n) (t n)) : ℝ) -
        Real.log (Nat.choose (criticalWindowCoreCapacity k n 0)
          (criticalWindowReferenceSelected k a n) : ℝ) -
        DenseGraph.binomialSecondOrderMain
          (criticalWindowCoreCapacity k n 0) (criticalWindowReferenceSelected k a n)
          (criticalWindowCapacityLoss k n (s n)) (criticalWindowSelectedIncrease k n (s n) (t n))) /
            ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ herrbound
    have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_gt_atTop (0 : ℝ))
    filter_upwards [hspos, hlog, hguard,
      eventually_criticalWindowCompletionSelected_cast hk a hs ht'] with n hsp hl hn heq
    rcases hn with ⟨hM0, hMN, hM'0, hM'N', hK', hL', hKL'⟩
    have hLid : (criticalWindowCompletionSelected k a n (s n) (t n) : ℝ) -
        criticalWindowReferenceSelected k a n = criticalWindowSelectedIncrease k n (s n) (t n) := by
      rw [heq, add_sub_cancel_left]
    have hh := DenseGraph.abs_log_choose_signed_secondOrder_le hM0 hMN hM'0 hM'N'
      hK' (by simpa only [hLid] using hL') (by simpa only [hLid, criticalWindowCapacityLoss] using hKL')
    rw [hLid] at hh
    change 0 < Real.log (n : ℝ) at hl
    have hden : 0 < (s n : ℝ) * Real.log (n : ℝ) := by
      have hsR : (0 : ℝ) < s n := by exact_mod_cast (show 0 < s n by omega)
      positivity
    rw [abs_div, abs_of_pos hden]
    exact div_le_div_of_nonneg_right hh hden.le
  have hmain := (criticalWindowPositiveFirstOrder_scale_tendsto hk a hspos hs ht).add
    (criticalWindowPositiveQuadratic_scale_tendsto hk a hspos hs ht)
  have h := herr.add hmain
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [hguard, eventually_criticalWindowCompletion_feasible hk a hs ht',
    eventually_criticalWindowReference_feasible hk a] with n hn hfeas hbase
  rw [criticalWindowBinomialMain_eq hk hn.1 hn.2.1]
  unfold criticalWindowCompletionCount criticalWindowCompletionSelected criticalWindowReferenceSelected
  rw [if_pos hfeas.le, if_pos (by simpa using hbase)]
  simp only [Nat.add_zero]
  ring

end InducedStars
