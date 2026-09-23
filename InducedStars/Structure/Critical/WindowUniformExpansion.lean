import InducedStars.Structure.Critical.WindowCompletionExpansion
import DenseGraph.Combinatorics.CompactSequenceUniformity

/-!
# Uniform sharp completion expansion in a bounded logarithmic window
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The unnormalized sharp completion exponent. -/
def criticalWindowCompletionExponent (k : ℕ) (a : ℝ) (n s t : ℕ) : ℝ :=
  -(gammaK k / criticalWindowThreshold k) * (s : ℝ) ^ 2 -
    a / criticalWindowThreshold k * s * Real.log (n : ℝ) +
      t * Real.log (pK k / (1 - pK k))

/-- Completion counts are uniformly positive in each bounded logarithmic
parameter rectangle. -/
theorem eventually_criticalWindowCompletion_pos_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L T : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ,
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      (t : ℝ) / Real.log (n : ℝ) ^ 2 ≤ T →
      0 < criticalWindowCompletionCount k a n s t := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply DenseGraph.eventually_uniform_of_normalizedSequences_eventually hlog
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog) ?_ L T
  intro s t x y _hx _hy hs ht
  filter_upwards [eventually_criticalWindowCompletion_binomial_guards hk a hs ht,
    eventually_criticalWindowCompletion_feasible hk a hs ht] with n hn hf
  unfold criticalWindowCompletionCount
  rw [if_pos hf.le]
  exact Nat.choose_pos hn.2.2.2.1.le

/-- The two-sided error is uniformly `o(log² n)` over every bounded
logarithmic remainder-size and squared-logarithmic edge-count range. -/
theorem eventually_criticalWindowCompletion_log_error_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ,
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      (t : ℝ) / Real.log (n : ℝ) ^ 2 ≤ T →
      |Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
          criticalWindowCompletionExponent k a n s t| ≤ epsilon * Real.log (n : ℝ) ^ 2 := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := DenseGraph.eventually_uniform_of_normalizedSequences_tendsto_zero hlog
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog)
    (F := fun n s t ↦
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) / Real.log (n : ℝ) ^ 2 -
        (-(gammaK k / criticalWindowThreshold k) * ((s : ℝ) / Real.log (n : ℝ)) ^ 2 -
          a / criticalWindowThreshold k * ((s : ℝ) / Real.log (n : ℝ)) +
          ((t : ℝ) / Real.log (n : ℝ) ^ 2) * Real.log (pK k / (1 - pK k))))
    (fun s t x y _hx _hy hs ht ↦ by
      have hpoly := (((hs.pow 2).const_mul (-(gammaK k / criticalWindowThreshold k))).sub
        (hs.const_mul (a / criticalWindowThreshold k))).add
          (ht.mul_const (Real.log (pK k / (1 - pK k))))
      have hdiff := (criticalWindowCompletion_log_ratio_scale_tendsto hk a hs ht).sub hpoly
      simp only [sub_self] at hdiff
      convert hdiff using 1
      ext n
      rfl)
    L T hepsilon
  filter_upwards [hu, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hln
  intro s t hs ht
  have h := hn s t hs ht
  have heq :
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) / Real.log (n : ℝ) ^ 2 -
        (-(gammaK k / criticalWindowThreshold k) * ((s : ℝ) / Real.log (n : ℝ)) ^ 2 -
          a / criticalWindowThreshold k * ((s : ℝ) / Real.log (n : ℝ)) +
          ((t : ℝ) / Real.log (n : ℝ) ^ 2) * Real.log (pK k / (1 - pK k))) =
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
          criticalWindowCompletionExponent k a n s t) / Real.log (n : ℝ) ^ 2 := by
    unfold criticalWindowCompletionExponent
    field_simp <;> ring
  rw [heq, abs_div, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ)))] at h
  exact (div_le_iff₀ (sq_pos_of_pos hln)).mp h

end InducedStars
