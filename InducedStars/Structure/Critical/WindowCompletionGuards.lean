import InducedStars.Structure.Critical.WindowPerturbationLimits

/-!
# Feasibility of the moving completion slices
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The selected cross count in a prescribed remainder completion. -/
def criticalWindowCompletionSelected (k : ℕ) (a : ℝ) (n s t : ℕ) : ℕ :=
  criticalWindowEdgeCount k a n - (criticalWindowCoreInternal k n s + t)

/-- All completion slices in a moving logarithmic-size sequence are
feasible; this establishes the natural-subtraction guard rather than
assuming it in the entropy comparison. -/
theorem eventually_criticalWindowCompletion_feasible
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    ∀ᶠ n : ℕ in atTop,
      criticalWindowCoreInternal k n (s n) + t n < criticalWindowEdgeCount k a n := by
  have hc : 0 < pK k * criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
    exact mul_pos (pK_pos (k := k) (by omega)) (by positivity)
  have h := (criticalWindowReferenceSelected_scale_tendsto hk a).add
    (criticalWindowPerturbation_div_sq_tendsto_zero
      (criticalWindowSelectedIncrease_scale_tendsto hk hs ht))
  simp only [add_zero] at h
  have hraw : Tendsto (fun n ↦
      ((criticalWindowEdgeCount k a n : ℝ) - criticalWindowCoreInternal k n (s n) - t n) /
        (n : ℝ) ^ 2) atTop (𝓝 (pK k * criticalReferenceCapacityScale k)) := by
    apply h.congr'
    filter_upwards [eventually_criticalWindowReference_feasible hk a] with n hn
    rw [criticalWindowReferenceSelected, Nat.cast_sub hn]
    unfold criticalWindowSelectedIncrease
    ring
  filter_upwards [eventually_pos_of_criticalWindowQuadraticScale hc hraw] with n hn
  have hlt : (criticalWindowCoreInternal k n (s n) : ℝ) + t n <
      criticalWindowEdgeCount k a n := by linarith
  exact_mod_cast hlt

theorem eventually_criticalWindowCompletionSelected_cast
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    ∀ᶠ n : ℕ in atTop,
      (criticalWindowCompletionSelected k a n (s n) (t n) : ℝ) =
        criticalWindowReferenceSelected k a n + criticalWindowSelectedIncrease k n (s n) (t n) := by
  filter_upwards [eventually_criticalWindowCompletion_feasible hk a hs ht,
    eventually_criticalWindowReference_feasible hk a] with n hn hn'
  rw [criticalWindowCompletionSelected, criticalWindowReferenceSelected,
    Nat.cast_sub hn.le, Nat.cast_sub hn', Nat.cast_add]
  unfold criticalWindowSelectedIncrease
  ring

/-- The actual, signed natural-count differences satisfy every guard in the
constant-error two-sided binomial expansion. -/
theorem eventually_criticalWindowCompletion_binomial_guards
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    ∀ᶠ n : ℕ in atTop,
      0 < criticalWindowReferenceSelected k a n ∧
      criticalWindowReferenceSelected k a n < criticalWindowCoreCapacity k n 0 ∧
      0 < criticalWindowCompletionSelected k a n (s n) (t n) ∧
      criticalWindowCompletionSelected k a n (s n) (t n) < criticalWindowCoreCapacity k n (s n) ∧
      |criticalWindowCapacityLoss k n (s n)| ≤ (criticalWindowCoreCapacity k n 0 : ℝ) / 2 ∧
      |criticalWindowSelectedIncrease k n (s n) (t n)| ≤
        (criticalWindowReferenceSelected k a n : ℝ) / 2 ∧
      |criticalWindowCapacityLoss k n (s n) + criticalWindowSelectedIncrease k n (s n) (t n)| ≤
        ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) / 2 := by
  have hc : 0 < criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
    positivity
  have hpc := mul_pos (pK_pos (k := k) (by omega)) hc
  have hqc : 0 < criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k := by
    nlinarith [pK_lt_one (show 2 ≤ k by omega)]
  have hN : Tendsto (fun n ↦ (criticalWindowCoreCapacity k n 0 : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (criticalReferenceCapacityScale k)) := criticalTargetCapacity_scale_tendsto k hk
  have hM := criticalWindowReferenceSelected_scale_tendsto hk a
  have hK := criticalWindowCapacityLoss_scale_tendsto hk hs
  have hL := criticalWindowSelectedIncrease_scale_tendsto hk hs ht
  have hNM : Tendsto (fun n ↦
      ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n) / (n : ℝ) ^ 2)
      atTop (𝓝 (criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k)) := by
    simpa only [sub_div] using hN.sub hM
  have hKL : Tendsto (fun n ↦
      (criticalWindowCapacityLoss k n (s n) + criticalWindowSelectedIncrease k n (s n) (t n)) /
        ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) * x + x / (k - 1 : ℕ))) := by
    simpa only [add_div] using hK.add hL
  have hgap := hNM.sub (criticalWindowPerturbation_div_sq_tendsto_zero hKL)
  simp only [sub_zero] at hgap
  have hgap' : Tendsto (fun n ↦
      ((criticalWindowCoreCapacity k n (s n) : ℝ) -
        criticalWindowCompletionSelected k a n (s n) (t n)) / (n : ℝ) ^ 2)
      atTop (𝓝 (criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k)) := by
    apply hgap.congr'
    filter_upwards [eventually_criticalWindowCompletionSelected_cast hk a hs ht] with n hn
    rw [hn]
    unfold criticalWindowCapacityLoss
    ring
  filter_upwards [eventually_criticalWindowReference_interior hk a,
    eventually_criticalWindowCompletion_feasible hk a hs ht,
    eventually_pos_of_criticalWindowQuadraticScale hqc hgap',
    eventually_abs_le_half_of_criticalWindowScales hc hN hK,
    eventually_abs_le_half_of_criticalWindowScales hpc hM hL,
    eventually_abs_le_half_of_criticalWindowScales hqc hNM hKL]
    with n hbase hfeas hgap hK' hL' hKL'
  refine ⟨hbase.1, hbase.2, Nat.sub_pos_of_lt hfeas, ?_, hK', hL', hKL'⟩
  exact_mod_cast (sub_pos.mp hgap)

end InducedStars
