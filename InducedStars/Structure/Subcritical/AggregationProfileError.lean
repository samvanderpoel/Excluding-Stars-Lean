import InducedStars.Structure.Subcritical.AggregationParameters

/-!
# Absorbing the unchanged profile error

The original coefficient `1000 (k+1)^4 (R₀+1)`, binary entropy, and base-two
logarithm are unchanged. A root-free profile has identically zero error.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InducedStars

theorem subcriticalProfileErrorConstant_pos (k R₀ : ℕ) :
    0 < subcriticalProfileErrorConstant k R₀ := by
  unfold subcriticalProfileErrorConstant
  positivity

@[simp] theorem subcriticalProfileErrorBudget_eq_zero_of_roots_empty
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}
    (alpha delta epsilon : ℝ) (p : SubcriticalProfile D eta R₀ theta)
    (hp : p.roots = ∅) : subcriticalProfileErrorBudget alpha delta epsilon p = 0 := by
  simp [subcriticalProfileErrorBudget, hp]

/-- Uniform finite error absorption, including the empty-root case, without
any lower bound on the graph count or the clean partition function. -/
theorem SubcriticalAggregationParameters.profile_error_le
    {k R₀ n : ℕ} {gamma eta theta alpha delta epsilon : ℝ}
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    {D : SubcriticalDivision k (Fin n)} (p : SubcriticalProfile D eta R₀ theta) :
    subcriticalProfileErrorBudget alpha delta epsilon p ≤
      subcriticalAggregationRootRate k eta R₀ / 4 * n * p.roots.card := by
  have hb := mul_le_mul_of_nonneg_right P.profile_error_base (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hc := P.profile_error_log
  have h : subcriticalProfileErrorConstant k R₀ *
      (binaryEntropy (5 * alpha) * n + theta * n + delta * n +
        subcriticalProfileRootFraction alpha theta epsilon * n + log2 (n + 1)) ≤
      subcriticalAggregationRootRate k eta R₀ / 4 * n := by
    nlinarith only [hb, hc]
  have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg p.roots.card : (0 : ℝ) ≤ _)
  simpa only [subcriticalProfileErrorBudget, Fintype.card_fin, mul_assoc, mul_left_comm,
    mul_comm] using hh

/-- A uniform small closed interval for the binary-entropy contribution. -/
theorem exists_subcriticalProfileEntropyRadius {a : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ ∀ alpha ∈ Icc (0 : ℝ) r, binaryEntropy (5 * alpha) ≤ a := by
  have hcont : Continuous (fun alpha : ℝ ↦ binaryEntropy (5 * alpha)) :=
    binaryEntropy_continuous.comp (continuous_const.mul continuous_id)
  have ht : Tendsto (fun alpha : ℝ ↦ binaryEntropy (5 * alpha)) (𝓝 0) (𝓝 0) := by
    simpa using (hcont.continuousAt (x := (0 : ℝ))).tendsto
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp (ht.eventually (Iio_mem_nhds ha))
  refine ⟨r / 2, by positivity, ?_⟩
  intro alpha halpha
  apply le_of_lt (he ?_)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg halpha.1]
  linarith [halpha.2]

theorem subcriticalProfile_logOrder_tendsto_zero :
    Tendsto (fun n : ℕ ↦ log2 ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  convert subcriticalResidual_logOrder_tendsto_zero.div_const (Real.log 2) using 1
  · funext n
    unfold log2
    ring
  · simp

/-- Any fixed logarithmic overhead is eventually smaller than any prescribed
positive linear reserve. This also supplies polynomial absorption thresholds. -/
theorem eventually_subcritical_log_overhead_le (C a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, C * log2 ((n : ℝ) + 1) ≤ a * n := by
  have ht : Tendsto (fun n : ℕ ↦ C * (log2 ((n : ℝ) + 1) / n)) atTop (𝓝 0) := by
    simpa using subcriticalProfile_logOrder_tendsto_zero.const_mul C
  filter_upwards [ht.eventually (Iio_mem_nhds ha), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnpos).mp (show C * log2 ((n : ℝ) + 1) / n < a by
    simpa only [mul_div_assoc] using hn)
  exact hh.le

/-- The natural-log version used when absorbing a polynomial into `exp`.
Its constant is fixed before the final graph-order threshold. -/
theorem eventually_subcritical_natural_log_overhead_le (C a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, C * Real.log ((n : ℝ) + 1) ≤ a * n := by
  have ht : Tendsto (fun n : ℕ ↦ C * (Real.log ((n : ℝ) + 1) / n)) atTop (𝓝 0) := by
    simpa using subcriticalResidual_logOrder_tendsto_zero.const_mul C
  filter_upwards [ht.eventually (Iio_mem_nhds ha), eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hh := (div_lt_iff₀ hnpos).mp (show C * Real.log ((n : ℝ) + 1) / n < a by
    simpa only [mul_div_assoc] using hn)
  exact hh.le

end InducedStars
