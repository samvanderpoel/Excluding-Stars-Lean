import InducedStars.Structure.Critical.WindowPositivePerturbations
import InducedStars.Structure.Critical.WindowQuadratic

/-!
# Quadratic penalty on the positive-remainder normalization
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowPositiveQuadratic_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦ criticalWindowQuadratic k a n (s n) (t n) /
      ((s n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (-(gammaK k / criticalWindowThreshold k) * x)) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hc : 0 < criticalReferenceCapacityScale k := by
    unfold criticalReferenceCapacityScale
    positivity
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
  have h := (((criticalWindowPositiveQuadraticTerm_tendsto hqc.ne' hspos hs hNM hKL).neg).add
    (criticalWindowPositiveQuadraticTerm_tendsto hc.ne' hspos hs hN hK)).sub
      (criticalWindowPositiveQuadraticTerm_tendsto hpc.ne' hspos hs hM hL)
  have heq : -((((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) + 1 / ((k - 1 : ℕ) : ℝ)) ^ 2 /
        (2 * (criticalReferenceCapacityScale k - pK k * criticalReferenceCapacityScale k)) * x) +
      ((((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ)) ^ 2 / (2 * criticalReferenceCapacityScale k)) * x -
      ((1 / ((k - 1 : ℕ) : ℝ)) ^ 2 / (2 * (pK k * criticalReferenceCapacityScale k))) * x =
      -(gammaK k / criticalWindowThreshold k) * x := by
    rw [← criticalQuadraticCoefficient_eq_gamma_div_threshold hk]
    have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
    unfold criticalReferenceCapacityScale criticalQuadraticCoefficient
    have hden : ((k - 2 : ℕ) : ℝ) / (k - 1 : ℕ) / 2 -
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
