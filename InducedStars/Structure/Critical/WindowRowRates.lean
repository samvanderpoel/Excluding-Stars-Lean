import InducedStars.Structure.Critical.WindowPrefactors
import InducedStars.Structure.Critical.WindowPartition
import InducedStars.Structure.Critical.WindowUniformExpansion
import InducedStars.Structure.Critical.WindowVariational

/-!
# Scalar assembly weights and their sharp rates
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The upper assembly weight relative to the full equitable reference. -/
def criticalWindowAssemblyEnvelope (k : ℕ) (a : ℝ) (n s : ℕ) : ℝ :=
  (Nat.choose n s : ℝ) *
    ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) /
      criticalWindowBalancedMultinomial (k - 1) n) *
    criticalRemainderPartitionFunction k s *
    Real.exp (criticalWindowCompletionExponent k a n s 0)

/-- The empty-remainder assembly lower weight, including its exact
multiplicity bound, relative to the full equitable reference. -/
def criticalWindowEmptyAssemblyRatio (k : ℕ) (a : ℝ) (n s : ℕ) : ℝ :=
  (Nat.choose n s : ℝ) *
    ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) /
      criticalWindowBalancedMultinomial (k - 1) n) *
    ((criticalWindowCompletionCount k a n s 0 : ℝ) /
      criticalWindowCompletionCount k a n 0 0) /
    Nat.choose (s + (k - 1)) (k - 1)

theorem eventually_criticalWindowEmptyCompletion_pos
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n : ℕ in atTop, 0 < criticalWindowCompletionCount k a n (s n) 0 := by
  filter_upwards [eventually_criticalWindowCompletion_pos_uniform hk a (x + 1) 0,
    hs.eventually (Iio_mem_nhds (by linarith : x < x + 1))] with n hn hsn
  exact hn (s n) 0 hsn.le (by simp)

theorem criticalWindowAssemblyEnvelope_log_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log (criticalWindowAssemblyEnvelope k a n (s n)) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 (criticalWindowRate k a x)) := by
  have hr : 0 < k - 1 := by omega
  have h := ((((criticalWindowChoose_log_tendsto hs).add
    (criticalWindowBalancedMultinomialRatio_log_tendsto hr hs)).add
      (criticalRemainderPartitionFunction_log_logSq_tendsto_zero hk hs)).add
        ((hs.pow 2).const_mul (-(gammaK k / criticalWindowThreshold k)))).sub
          (hs.const_mul (a / criticalWindowThreshold k))
  have htarget : x + 0 + 0 + -(gammaK k / criticalWindowThreshold k) * x ^ 2 -
      a / criticalWindowThreshold k * x = criticalWindowRate k a x := by
    unfold criticalWindowRate
    ring
  rw [htarget] at h
  apply h.congr'
  filter_upwards [eventually_criticalWindowLogarithmicSize_le_order hs,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hsn hl
  have hc : (0 : ℝ) < Nat.choose n (s n) := by exact_mod_cast Nat.choose_pos hsn
  have hm : (0 : ℝ) < (criticalWindowBalancedMultinomial (k - 1) (n - s n) : ℝ) /
      criticalWindowBalancedMultinomial (k - 1) n := div_pos
    (by exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) (n - s n))
    (by exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n)
  have hz := criticalRemainderPartitionFunction_pos hk (s n)
  unfold criticalWindowAssemblyEnvelope
  rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_mul (by positivity) hz.ne', Real.log_mul hc.ne' hm.ne', Real.log_exp]
  unfold criticalWindowCompletionExponent
  simp only [Nat.cast_zero, zero_mul, add_zero]
  field_simp <;> ring

theorem criticalWindowEmptyAssemblyRatio_log_scale_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log (criticalWindowEmptyAssemblyRatio k a n (s n)) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 (criticalWindowRate k a x)) := by
  have hr : 0 < k - 1 := by omega
  have ht : Tendsto (fun n : ℕ ↦ ((0 : ℕ) : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Nat.cast_zero, zero_div] using (tendsto_const_nhds (x := (0 : ℝ)))
  have h := (((criticalWindowChoose_log_tendsto hs).add
    (criticalWindowBalancedMultinomialRatio_log_tendsto hr hs)).add
      (criticalWindowCompletion_log_ratio_scale_tendsto hk a hs ht)).sub
        (criticalWindowAssemblyMultiplicity_log_tendsto (k - 1) hs)
  have htarget : x + 0 + (-(gammaK k / criticalWindowThreshold k) * x ^ 2 -
      a / criticalWindowThreshold k * x + 0 * Real.log (pK k / (1 - pK k))) - 0 =
      criticalWindowRate k a x := by unfold criticalWindowRate; ring
  rw [htarget] at h
  apply h.congr'
  have hs0 : Tendsto (fun n : ℕ ↦ ((0 : ℕ) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_zero, zero_div] using (tendsto_const_nhds (x := (0 : ℝ)))
  filter_upwards [eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_criticalWindowEmptyCompletion_pos hk a hs,
    eventually_criticalWindowEmptyCompletion_pos hk a hs0] with n hsn hBs hB0
  have hc : (0 : ℝ) < Nat.choose n (s n) := by exact_mod_cast Nat.choose_pos hsn
  have hm : (0 : ℝ) < (criticalWindowBalancedMultinomial (k - 1) (n - s n) : ℝ) /
      criticalWindowBalancedMultinomial (k - 1) n := div_pos
    (by exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) (n - s n))
    (by exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n)
  have hbs : (0 : ℝ) < criticalWindowCompletionCount k a n (s n) 0 := by exact_mod_cast hBs
  have hb0 : (0 : ℝ) < criticalWindowCompletionCount k a n 0 0 := by exact_mod_cast hB0
  have hmultip : (0 : ℝ) < Nat.choose (s n + (k - 1)) (k - 1) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_left (k - 1) (s n))
  unfold criticalWindowEmptyAssemblyRatio
  rw [Real.log_div (by positivity) hmultip.ne', Real.log_mul (by positivity) (div_pos hbs hb0).ne',
    Real.log_mul hc.ne' hm.ne', Real.log_div hbs.ne' hb0.ne']
  ring

end InducedStars
