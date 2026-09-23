import InducedStars.Structure.Critical.WindowPositiveExpansion
import InducedStars.Structure.Critical.WindowUniformExpansion
import DenseGraph.Combinatorics.PositiveSequenceUniformity

/-!
# Uniform expansion down to one exceptional vertex
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The sharp signed completion error is uniformly `o(s log n)` for every
positive remainder size in a bounded logarithmic range. -/
theorem eventually_criticalWindowCompletion_log_error_positive_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L T : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ, 1 ≤ s →
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      (t : ℝ) / ((s : ℝ) * Real.log (n : ℝ)) ≤ T →
      |Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
          criticalWindowCompletionExponent k a n s t| ≤ epsilon * s * Real.log (n : ℝ) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu := DenseGraph.eventually_uniform_of_positiveNormalizedSequences_tendsto_zero hlog
    (F := fun n s t ↦
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) / ((s : ℝ) * Real.log (n : ℝ)) -
        (-(gammaK k / criticalWindowThreshold k) * ((s : ℝ) / Real.log (n : ℝ)) -
          a / criticalWindowThreshold k +
          ((t : ℝ) / ((s : ℝ) * Real.log (n : ℝ))) * Real.log (pK k / (1 - pK k))))
    (fun s t x z _hx _hz hspos hs ht ↦ by
      have hpoly := ((hs.const_mul (-(gammaK k / criticalWindowThreshold k))).sub_const
        (a / criticalWindowThreshold k)).add
          (ht.mul_const (Real.log (pK k / (1 - pK k))))
      have hdiff := (criticalWindowPositiveCompletion_log_ratio_scale_tendsto hk a hspos hs ht).sub hpoly
      simp only [sub_self] at hdiff
      convert hdiff using 1)
    L T hepsilon
  filter_upwards [hu, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hln
  intro s t hsp hs ht
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have h := hn s t hsp hs ht
  have heq :
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ)) / ((s : ℝ) * Real.log (n : ℝ)) -
        (-(gammaK k / criticalWindowThreshold k) * ((s : ℝ) / Real.log (n : ℝ)) -
          a / criticalWindowThreshold k +
          ((t : ℝ) / ((s : ℝ) * Real.log (n : ℝ))) * Real.log (pK k / (1 - pK k))) =
      (Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
          Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
          criticalWindowCompletionExponent k a n s t) / ((s : ℝ) * Real.log (n : ℝ)) := by
    unfold criticalWindowCompletionExponent
    field_simp <;> ring
  rw [heq, abs_div, abs_of_pos (mul_pos hsR hln)] at h
  have h' := (div_le_iff₀ (mul_pos hsR hln)).mp h
  simpa only [mul_assoc] using h'

end InducedStars
