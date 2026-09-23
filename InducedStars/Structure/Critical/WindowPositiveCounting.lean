import InducedStars.Structure.Critical.WindowCounting
import InducedStars.Structure.Critical.WindowPositiveUniformExpansion

/-!
# Positive-size assembly bounds on the finer logarithmic scale

The remainder partition function is uniformly negligible relative to
`s log n` for `1≤s=O(log n)`.  This includes bounded positive remainders,
which are needed for the exactly co-partite conclusion above the transition.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A global subquadratic envelope is uniform on every bounded positive
logarithmic range, including sizes that remain bounded. -/
theorem eventually_subquadratic_positive_logarithmic_uniform
    {f : ℕ → ℝ}
    (hf : Tendsto (fun s ↦ f s / (s : ℝ) ^ 2) atTop (𝓝 0))
    (L : ℝ) (hL : 0 ≤ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      |f s| ≤ epsilon * (s : ℝ) * Real.log (n : ℝ) := by
  let delta := epsilon / (2 * (L + 1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨C, _hC, hbound⟩ := exists_global_subquadratic_envelope hf hd
  have hsmall : ∀ᶠ n : ℕ in atTop, C / Real.log (n : ℝ) < epsilon / 2 :=
    (tendsto_const_nhds.div_atTop criticalWindowLog_nat_tendsto_atTop).eventually
      (Iio_mem_nhds (half_pos hepsilon))
  have hdL : delta * L ≤ epsilon / 2 := by
    have hden : 0 < 2 * (L + 1) := by positivity
    have heq : delta * L = epsilon * L / (2 * (L + 1)) := by dsimp [delta]; ring
    rw [heq]
    apply (div_le_iff₀ hden).mpr
    nlinarith
  filter_upwards [hsmall, criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn hl
  intro s hs hsL
  change 0 < Real.log (n : ℝ) at hl
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsbound : (s : ℝ) ≤ L * Real.log (n : ℝ) := (div_le_iff₀ hl).mp hsL
  have hquad : delta * (s : ℝ) ^ 2 ≤ epsilon / 2 * ((s : ℝ) * Real.log (n : ℝ)) := by
    calc
      delta * (s : ℝ) ^ 2 = (delta * (s : ℝ)) * (s : ℝ) := by ring
      _ ≤ (delta * (s : ℝ)) * (L * Real.log (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsbound (mul_nonneg hd.le (Nat.cast_nonneg _))
      _ = (delta * L) * ((s : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hdL
        (mul_nonneg (Nat.cast_nonneg _) hl.le)
  have hconst : C ≤ epsilon / 2 * ((s : ℝ) * Real.log (n : ℝ)) := by
    calc
      C ≤ epsilon / 2 * Real.log (n : ℝ) := ((div_lt_iff₀ hl).mp hn).le
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by nlinarith : Real.log (n : ℝ) ≤ (s : ℝ) * Real.log (n : ℝ))
        (half_pos hepsilon).le
  nlinarith [hbound s]

theorem eventually_criticalRemainderPartitionFunction_log_positive_uniform
    {k : ℕ} (hk : 3 ≤ k) (L : ℝ) (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      |Real.log (criticalRemainderPartitionFunction k s)| ≤
        epsilon * (s : ℝ) * Real.log (n : ℝ) :=
  eventually_subquadratic_positive_logarithmic_uniform
    (criticalRemainderPartitionFunction_log_sq_tendsto_zero hk) L hL hepsilon

/-- Sequential form of the positive-size partition-function estimate. -/
theorem criticalRemainderPartitionFunction_log_positiveScale_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n) :
    Tendsto (fun n ↦ Real.log (criticalRemainderPartitionFunction k (s n)) /
      ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hL : (0 : ℝ) ≤ |x| + 1 := by positivity
  have hbound := eventually_criticalRemainderPartitionFunction_log_positive_uniform
    hk (|x| + 1) hL (half_pos hepsilon)
  have hseq := hs.eventually
    (Iio_mem_nhds (by linarith [le_abs_self x] : x < |x| + 1))
  filter_upwards [hbound, hseq, hspos,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hb hsL hsp hl
  change 0 < Real.log (n : ℝ) at hl
  have hsR : (0 : ℝ) < s n := by exact_mod_cast (show 0 < s n by omega)
  simp only [Real.dist_eq, sub_zero, abs_div, abs_of_pos (mul_pos hsR hl)]
  have h := div_le_div_of_nonneg_right (hb (s n) hsp hsL.le) (mul_pos hsR hl).le
  have heq : (epsilon / 2 * (s n : ℝ) * Real.log (n : ℝ)) /
      ((s n : ℝ) * Real.log (n : ℝ)) = epsilon / 2 := by field_simp
  rw [heq] at h
  exact h.trans_lt (half_lt_self hepsilon)

theorem criticalWindowRemainderEdges_positiveNormalized_le
    {n s t : ℕ} {L : ℝ} (hlog : 0 < Real.log (n : ℝ)) (hspos : 1 ≤ s)
    (hs : (s : ℝ) / Real.log (n : ℝ) ≤ L)
    (ht : t ≤ completeEdgeCount s) :
    (t : ℝ) / ((s : ℝ) * Real.log (n : ℝ)) ≤ L := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have htR : (t : ℝ) ≤ (s : ℝ) ^ 2 := by
    have hcap := completeEdgeCount_cast_le_half_square s
    have ht' : (t : ℝ) ≤ completeEdgeCount s := by exact_mod_cast ht
    nlinarith [sq_nonneg (s : ℝ)]
  calc
    (t : ℝ) / ((s : ℝ) * Real.log (n : ℝ)) ≤
        (s : ℝ) ^ 2 / ((s : ℝ) * Real.log (n : ℝ)) :=
      div_le_div_of_nonneg_right htR (mul_pos hsR hlog).le
    _ = (s : ℝ) / Real.log (n : ℝ) := by field_simp
    _ ≤ L := hs

/-- Uniform positive-size row bound with the partition function absorbed
into the arbitrarily small `s log n` error. -/
theorem exists_criticalWindowAssembly_positive_row_upper
    {k : ℕ} (hk : 3 ≤ k) (a L : ℝ) (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
        C * (n.choose s : ℝ) *
          (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
          (criticalWindowCompletionCount k a n 0 0 : ℝ) *
          Real.exp (criticalWindowCompletionExponent k a n s 0 +
            epsilon * (s : ℝ) * Real.log (n : ℝ)) := by
  obtain ⟨C, hC, hcomp⟩ := exists_criticalWindowCoPartite_comparison_uniform hk a L (L ^ 2)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcomp, eventually_criticalWindowCompletion_pos_uniform hk a L (L ^ 2),
    eventually_criticalWindowCompletion_log_error_positive_uniform hk a L L (half_pos hepsilon),
    eventually_criticalRemainderPartitionFunction_log_positive_uniform hk L hL (half_pos hepsilon),
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hc hp he hz hl
  intro s hspos hs
  have hzero : ((0 : ℕ) : ℝ) / Real.log (n : ℝ) ^ 2 ≤ L ^ 2 := by simpa using sq_nonneg L
  have hrow := criticalWindowAssembly_row_upper_of_comparison hk a C
    (epsilon / 2 * (s : ℝ) * Real.log (n : ℝ)) hC.le n s
    (fun t ht ↦ (hc s t hs (criticalWindowRemainderEdges_normalized_le hl hs ht)).2.2)
    (fun t ht ↦ hp s t hs (criticalWindowRemainderEdges_normalized_le hl hs ht))
    (hp 0 0 (by simpa using hL) hzero)
    (fun t ht ↦ he s t hspos hs (criticalWindowRemainderEdges_positiveNormalized_le hl hspos hs ht))
  have hZ : criticalRemainderPartitionFunction k s ≤
      Real.exp (epsilon / 2 * (s : ℝ) * Real.log (n : ℝ)) := by
    have h := Real.exp_le_exp.mpr (abs_le.mp (hz s hspos hs)).2
    rwa [Real.exp_log (criticalRemainderPartitionFunction_pos hk s)] at h
  apply hrow.trans
  calc
    C * (n.choose s : ℝ) *
        (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          epsilon / 2 * (s : ℝ) * Real.log (n : ℝ)) *
        criticalRemainderPartitionFunction k s ≤
      C * (n.choose s : ℝ) *
        (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          epsilon / 2 * (s : ℝ) * Real.log (n : ℝ)) *
        Real.exp (epsilon / 2 * (s : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      congr 1
      ring

end InducedStars
