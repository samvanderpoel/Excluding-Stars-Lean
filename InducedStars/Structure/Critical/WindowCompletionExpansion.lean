import InducedStars.Structure.Critical.WindowFirstOrder
import InducedStars.Structure.Critical.WindowQuadratic
import InducedStars.Structure.Critical.WindowTaylorLimits

/-!
# The sharp two-sided critical-window completion expansion
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Finite decomposition of the entropy Taylor polynomial into its signed
first-order term and its quadratic penalty. -/
theorem criticalWindowBinomialMain_eq
    {k n s t : ℕ} {a : ℝ} (hk : 3 ≤ k)
    (hM : 0 < criticalWindowReferenceSelected k a n)
    (hMN : criticalWindowReferenceSelected k a n < criticalWindowCoreCapacity k n 0) :
    DenseGraph.binomialSecondOrderMain
      (criticalWindowCoreCapacity k n 0) (criticalWindowReferenceSelected k a n)
      (criticalWindowCapacityLoss k n s) (criticalWindowSelectedIncrease k n s t) =
        criticalWindowFirstOrder k a n s t + criticalWindowQuadratic k a n s t := by
  have hMr : (0 : ℝ) < criticalWindowReferenceSelected k a n := by exact_mod_cast hM
  have hNr : (0 : ℝ) < criticalWindowCoreCapacity k n 0 := by exact_mod_cast (lt_trans hM hMN)
  have hgap : (0 : ℝ) < (criticalWindowCoreCapacity k n 0 : ℝ) -
      criticalWindowReferenceSelected k a n := by exact_mod_cast (sub_pos.mpr (show
        (criticalWindowReferenceSelected k a n : ℝ) < criticalWindowCoreCapacity k n 0 by exact_mod_cast hMN))
  have hq : 0 < criticalWindowReferenceDensity k a n := div_pos hMr hNr
  have hq' : criticalWindowReferenceDensity k a n < 1 := (div_lt_one hNr).mpr (by exact_mod_cast hMN)
  have h1 : ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) /
      criticalWindowCoreCapacity k n 0 = 1 - criticalWindowReferenceDensity k a n := by
    unfold criticalWindowReferenceDensity
    field_simp
  have h2 : ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) /
      criticalWindowReferenceSelected k a n =
      (1 - criticalWindowReferenceDensity k a n) / criticalWindowReferenceDensity k a n := by
    unfold criticalWindowReferenceDensity
    field_simp <;> ring
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
  unfold DenseGraph.binomialSecondOrderMain
  rw [h1, h2, Real.log_div (sub_pos.mpr hq').ne' hq.ne']
  unfold criticalWindowFirstOrder criticalWindowQuadratic
  rw [hrel]
  ring

/-- Every moving natural-log-scale completion sequence has the exact
squared-logarithm expansion.  The exact floors use the natural-log window
parameter, the capacity perturbations are signed, and both sides are controlled. -/
theorem criticalWindowCompletion_log_ratio_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦
      (Real.log (criticalWindowCompletionCount k a n (s n) (t n) : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 (-(gammaK k / criticalWindowThreshold k) * x ^ 2 -
        a / criticalWindowThreshold k * x + y * Real.log (pK k / (1 - pK k)))) := by
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
  have hK := criticalWindowCapacityLoss_scale_tendsto hk hs
  have hL : Tendsto (fun n ↦
      ((criticalWindowCompletionSelected k a n (s n) (t n) : ℝ) - criticalWindowReferenceSelected k a n) /
        ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 (x / (k - 1 : ℕ))) := by
    apply (criticalWindowSelectedIncrease_scale_tendsto hk hs ht).congr'
    filter_upwards [eventually_criticalWindowCompletionSelected_cast hk a hs ht] with n hn
    rw [hn, add_sub_cancel_left]
  have hguard := eventually_criticalWindowCompletion_binomial_guards hk a hs ht
  have herr := criticalWindowSignedBinomial_remainder_tendsto_zero hc.ne' hpc.ne' hqc.ne'
    hN hM hK hL (by
      filter_upwards [hguard, eventually_criticalWindowCompletionSelected_cast hk a hs ht] with n hn heq
      simpa only [criticalWindowCapacityLoss, heq, add_sub_cancel_left] using hn)
  have hmain := (criticalWindowFirstOrder_scale_tendsto hk a hs ht).add
    (criticalWindowQuadratic_scale_tendsto hk a hs ht)
  have h := herr.add hmain
  convert h.congr' ?_ using 1
  · ring
  filter_upwards [hguard, eventually_criticalWindowCompletionSelected_cast hk a hs ht,
    eventually_criticalWindowCompletion_feasible hk a hs ht,
    eventually_criticalWindowReference_feasible hk a] with n hn heq hfeas hbase
  simp only [heq, add_sub_cancel_left]
  change (Real.log (Nat.choose _ _ : ℝ) - Real.log (Nat.choose _ _ : ℝ) -
      DenseGraph.binomialSecondOrderMain _ _ (criticalWindowCapacityLoss k n (s n))
        (criticalWindowSelectedIncrease k n (s n) (t n))) / _ + _ = _
  rw [criticalWindowBinomialMain_eq hk hn.1 hn.2.1]
  unfold criticalWindowCompletionCount criticalWindowCompletionSelected criticalWindowReferenceSelected
  rw [if_pos hfeas.le, if_pos (by simpa using hbase)]
  simp only [Nat.add_zero]
  ring

end InducedStars
