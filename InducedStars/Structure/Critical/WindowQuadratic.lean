import InducedStars.Structure.Critical.WindowCompletionGuards

/-!
# The sharp quadratic completion penalty
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The quadratic part of the signed entropy expansion. -/
def criticalWindowQuadratic (k : ℕ) (a : ℝ) (n s t : ℕ) : ℝ :=
  -(criticalWindowCapacityLoss k n s + criticalWindowSelectedIncrease k n s t) ^ 2 /
      (2 * ((criticalWindowCoreCapacity k n 0 : ℝ) - criticalWindowReferenceSelected k a n)) +
    (criticalWindowCapacityLoss k n s) ^ 2 / (2 * criticalWindowCoreCapacity k n 0) -
    (criticalWindowSelectedIncrease k n s t) ^ 2 / (2 * criticalWindowReferenceSelected k a n)

/-- The quadratic Taylor term has the natural-log completion coefficient,
independently of the remainder edge-count profile. -/
theorem criticalWindowQuadratic_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ criticalWindowQuadratic k a n (s n) (t n) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 (-(gammaK k / criticalWindowThreshold k) * x ^ 2)) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hc : 0 < criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    positivity
  have hpc := mul_pos hp hc
  have hqc : 0 < criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k := by
    nlinarith
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
  have h := (((criticalWindowQuadraticTerm_tendsto hqc.ne' hNM hKL).neg).add
    (criticalWindowQuadraticTerm_tendsto hc.ne' hN hK)).sub
      (criticalWindowQuadraticTerm_tendsto hpc.ne' hM hL)
  have heq : -((((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) * x + x / (k - 1 : ℕ)) ^ 2 /
        (2 * (criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k))) +
      (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) * x) ^ 2 / (2 * criticalReferenceCapacityScale k) -
      (x / (k - 1 : ℕ)) ^ 2 / (2 * (pK k * criticalReferenceCapacityScale k)) =
      -(gammaK k / criticalWindowThreshold k) * x ^ 2 := by
    rw [← criticalQuadraticCoefficient_eq_gamma_div_threshold hk]
    have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
    unfold criticalReferenceCapacityScale criticalQuadraticCoefficient
    have hden : ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) / (2 : ℝ) -
        pK k * (((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) / 2) =
        ((k - 2 : ℕ) : ℝ) / (2 * (k - 1 : ℕ)) * (1 - pK k) := by ring
    rw [hden]
    field_simp
    rw [hrel]
    ring
  rw [heq] at h
  convert h using 1
  ext n
  unfold criticalWindowQuadratic
  ring

end InducedStars
