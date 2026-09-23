import InducedStars.Structure.Critical.CombinedSlice
import InducedStars.Structure.Critical.BinomialUniformBounds
import InducedStars.Structure.Critical.SliceFeasibility

/-!
# Uniform critical binomial comparisons

All thresholds here are selected before the sparse size or a graph division.
The exact floor critical edge count is used throughout.  The fourfold
Gaussian reserve is kept until the final logarithmic-cutoff estimate.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Strong error-retaining critical exponent, before the sparse cutoff. -/
def criticalCombinedSliceExponent (k n s : ℕ) : ℝ :=
  -(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
    criticalCombinedSliceErrorConstant k * s +
    criticalCombinedSliceErrorConstant k * Real.log ((n + 1 : ℕ) : ℝ)

/-- Uniform critical comparison for every positive sparse size in the
Taylor range.  In particular, none of its thresholds depends on a division,
profile, or sparse size. -/
theorem eventually_criticalPositiveCombinedSlice_le_referenceFiber_with_errors
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      (Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalCombinedSliceExponent k n s) := by
  have hmargin : ∀ᶠ n : ℕ in atTop,
      8 / (n : ℝ) ≤ criticalDensityMargin k :=
    ((tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ))).2
      _ (criticalDensityMargin_pos hk)).mono fun _ hn ↦ hn.le
  filter_upwards [eventually_criticalBinomialSecondOrderGuards k hk,
    eventually_criticalQuadraticExponent_le k hk,
    eventually_criticalSecondOrderCubicError_le k hk,
    hmargin, eventually_ge_atTop (4 * (k - 1) ^ 2)] with
      n hguards hquadratic hcubic hmarginN hn
  intro s hs hsmall
  have G := hguards s hs hsmall
  have hdelta := (criticalCombinedSliceDelta_le_taylor k).trans
    (criticalTaylorDeltaBound_le_one_sixteenth k)
  have hsmallR := hsmall.trans
    (mul_le_mul_of_nonneg_right hdelta (Nat.cast_nonneg (α := ℝ) n))
  have hsmallN : 16 * s ≤ n := by
    have h : (16 : ℝ) * s ≤ n := by linarith
    exact_mod_cast h
  have hsn : s ≤ n := by omega
  have hnFour : 4 * (k - 1) ≤ n :=
    (Nat.mul_le_mul_left 4
      (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (k - 1))).trans hn
  exact criticalCombinedSlice_le_reference_with_errors_of_bounds hk hs hsn hnFour
    G.balancedInternal_le_edge hmarginN
    (criticalMaximumCombinedCapacity_le_target hk hs hsmallN hn)
    (criticalBalancedInternalCapacity_mono_sparse hk hs hsmallN hn)
    G.selected_pos G.selected_lt_capacity G.capacity_loss_half
    G.selected_increase_half G.remaining_half
    (hquadratic s hs hsmall) (hcubic s hs hsmall)

/-- Error-retaining comparison uniform also at sparse size zero. -/
theorem eventually_criticalCleanCombinedSlice_le_referenceFiber_with_errors
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      (Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalCombinedSliceExponent k n s) := by
  filter_upwards [eventually_criticalPositiveCombinedSlice_le_referenceFiber_with_errors k hk,
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_criticalTargetSelectedCount_le_capacity k hk] with n hpositive href hselected
  intro s hsmall
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · rw [criticalMaximumCombinedCapacity_zero_sparse,
      criticalMaximumCombinedSelectedCount_zero_sparse href hselected,
      ← criticalReferenceFiberCard_eq_choose_of_feasible href]
    have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
    have herror := mul_nonneg (criticalCombinedSliceErrorConstant_nonneg k) hlog
    have hexp := Real.one_le_exp_iff.mpr herror
    simpa [criticalCombinedSliceExponent] using
      (le_mul_of_one_le_right (by positivity : (0 : ℝ) ≤ criticalReferenceFiberCard k n) hexp)
  · exact hpositive s hs hsmall

/-- The scalar binomial penalty above a logarithmic sparse cutoff.

This is the clean numerical estimate at the exact floor critical edge count;
it is independent of graphon inputs and uses only the foundational axioms. -/
theorem criticalCleanCombinedSlice_le_referenceFiber
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
        L * Real.log ((n + 1 : ℕ) : ℝ) ≤ s →
        (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
        (Nat.choose (criticalMaximumCombinedCapacity k n s)
          (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
          (criticalReferenceFiberCard k n : ℝ) *
            Real.exp (-criticalSparsePenaltyConstant k * (s : ℝ) ^ 2) := by
  let c := criticalSparsePenaltyConstant k
  let C := criticalCombinedSliceErrorConstant k
  let L := max 1 (2 * C / c)
  have hc : 0 < c := criticalSparsePenaltyConstant_pos hk
  have hC : 0 ≤ C := criticalCombinedSliceErrorConstant_nonneg k
  have hL : 1 ≤ L := le_max_left _ _
  have hCL : 2 * C ≤ c * L := by
    have h := (div_le_iff₀ hc).mp (le_max_right 1 (2 * C / c))
    simpa [L, mul_comm] using h
  have hlog : ∀ᶠ n : ℕ in atTop,
      1 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    have hN : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact (Real.tendsto_log_atTop.comp hN).eventually (eventually_ge_atTop 1)
  refine ⟨L, lt_of_lt_of_le (by norm_num) hL, ?_⟩
  filter_upwards [eventually_criticalCleanCombinedSlice_le_referenceFiber_with_errors k hk,
    hlog] with n hslice hlogN
  intro s hcutoff hsmall
  apply (hslice s hsmall).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have herr := criticalSparseErrors_le_of_logarithmic_cutoff hc hC hL hCL hlogN hcutoff
  have hcs := mul_nonneg hc.le (sq_nonneg (s : ℝ))
  change -(4 * c) * (s : ℝ) ^ 2 + C * s +
      C * Real.log ((n + 1 : ℕ) : ℝ) ≤ -c * (s : ℝ) ^ 2
  nlinarith only [herr, hcs]

/-- Feasibility and the fixed compact density band needed to transport any
actual division into the maximal combined slice. -/
structure CriticalCombinedSliceFeasibility (k n s : ℕ) : Prop where
  edge_upper : criticalEdgeCount k n ≤ Nat.choose (n - s) 2 + Nat.choose s 2
  missing_le : criticalCombinedMissingCount k n s ≤ criticalMaximumCombinedCapacity k n s
  selected_lower : criticalDensityMargin k * (criticalMaximumCombinedCapacity k n s : ℝ) ≤
    (criticalMaximumCombinedSelectedCount k n s : ℝ)
  selected_upper : (criticalMaximumCombinedSelectedCount k n s : ℝ) ≤
    (1 - criticalDensityMargin k) * (criticalMaximumCombinedCapacity k n s : ℝ)

/-- The combined slice remains feasible in the same compact band uniformly
throughout the critical sparse range, including sparse size zero. -/
theorem eventually_criticalCombinedSliceFeasibility
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      CriticalCombinedSliceFeasibility k n s := by
  have hOne : ∀ᶠ n : ℕ in atTop,
      (1 : ℝ) ≤ criticalCombinedSliceDelta k * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop
      (criticalCombinedSliceDelta_pos hk)).eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_criticalBinomialSecondOrderGuards k hk,
    hOne, eventually_ge_atTop (4 * (k - 1) ^ 2)] with n hguards hOneN hn
  intro s hsmall
  have G₁ := hguards 1 (by norm_num) (by simpa only [Nat.cast_one] using hOneN)
  have hcapacity : criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · have hδ := (criticalCombinedSliceDelta_le_taylor k).trans
        (criticalTaylorDeltaBound_le_one_sixteenth k)
      have h := hsmall.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) n))
      have h16 : 16 * s ≤ n := by exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith)
      exact criticalMaximumCombinedCapacity_le_target hk hs h16 hn
  have hinternal : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp
    · have hδ := (criticalCombinedSliceDelta_le_taylor k).trans
        (criticalTaylorDeltaBound_le_one_sixteenth k)
      have h := hsmall.trans (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (α := ℝ) n))
      have h16 : 16 * s ≤ n := by exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith)
      exact criticalBalancedInternalCapacity_mono_sparse hk hs h16 hn
  have hperturb : 2 * ((criticalCapacityLoss k n s + criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
      criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [criticalCapacityLoss, criticalSelectedIncrease,
        criticalMaximumCombinedCapacity_zero_sparse, Nat.sub_self, Nat.sub_zero,
        Nat.zero_add, Nat.cast_zero, mul_zero]
      exact mul_nonneg (criticalDensityMargin_pos hk).le (by positivity)
    · exact (hguards s hs hsmall).twice_sum_le_margin
  have hshift : criticalTargetSelectedCount k n + criticalSelectedIncrease k n s ≤
      criticalMaximumCombinedCapacity k n s := by
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simpa [criticalSelectedIncrease] using G₁.selected_lt_capacity.le
    · have G := hguards s hs hsmall
      have h := G.remaining_half
      have hMN := G.selected_lt_capacity
      have hEq := criticalTargetCapacity_sub_loss hcapacity
      omega
  have hfeasible := criticalCombinedSlice_missing_feasibility
    G₁.balancedInternal_le_edge hinternal hshift
  have hband := criticalMaximumCombinedSelectedCount_mem_compact_of_triple_margin
    ⟨criticalDensityMargin_pos hk, criticalDensityMargin_lt_half hk⟩ hcapacity
    hfeasible.2.2 G₁.triple_compact_selected G₁.triple_compact_remaining hperturb
  exact ⟨hfeasible.1, hfeasible.2.1, hband.1, hband.2⟩

/-- Uniform comparison for any signed shift of the combined selected count. -/
theorem criticalShiftedCombinedSlice_le_referenceFiber
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      ∀ (x : ℕ) (u : ℤ),
        Nat.dist x (criticalMaximumCombinedSelectedCount k n s) = u.natAbs →
        (Nat.choose (criticalMaximumCombinedCapacity k n s) x : ℝ) ≤
          (criticalReferenceFiberCard k n : ℝ) *
            Real.exp (criticalCombinedSliceExponent k n s +
              criticalShiftErrorConstant k * (u.natAbs : ℝ)) := by
  filter_upwards [eventually_criticalCleanCombinedSlice_le_referenceFiber_with_errors k hk,
    eventually_criticalCombinedSliceFeasibility k hk] with n hslice hfeasible
  intro s hsmall x u hdist
  have H := hfeasible s hsmall
  exact criticalShiftedCombinedSlice_le_of_center_bound hk (hslice s hsmall)
    H.selected_lower H.selected_upper hdist

end InducedStars
