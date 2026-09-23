import InducedStars.Structure.Critical.BinomialExpansion

/-!
# The critical combined binomial slice

This module applies the locally proved second-order binomial inequality to
the exact critical capacities.  Selected and missing counts remain distinct,
and all exponential coefficients use natural logarithms.
The canonical fine-balance result is proved separately in `FineBalanceMain`;
the combined-coordinate arithmetic does not replace that result.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Under the actual finite perturbation guards, the old selected count is
exactly `M+L`.  This statement does not assume existence of a graph fiber. -/
theorem criticalTargetSelectedCount_add_increase_eq_maximum
    {k n s : ℕ}
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n)
    (hinternal : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n)
    (hreference : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      criticalEdgeCount k n)
    (hshift : criticalTargetSelectedCount k n + criticalSelectedIncrease k n s ≤
      criticalTargetCapacity k n - criticalCapacityLoss k n s) :
    criticalTargetSelectedCount k n + criticalSelectedIncrease k n s =
      criticalMaximumCombinedSelectedCount k n s := by
  rw [criticalTargetCapacity_sub_loss hcapacity] at hshift
  have htotal := criticalMaximumCombinedCapacity_add_balancedInternal k n s
  unfold criticalTargetSelectedCount criticalSelectedIncrease
    criticalMaximumCombinedSelectedCount criticalCombinedMissingCount at *
  omega

/-- The first-order expression in the generic binomial theorem agrees with
the signed-capacity critical expression, including the exact target density. -/
theorem criticalBinomialFirstOrder_eq
    {k n s : ℕ}
    (hM : 0 < criticalTargetSelectedCount k n)
    (hMN : criticalTargetSelectedCount k n < criticalTargetCapacity k n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n)
    (hinternal : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    (criticalCapacityLoss k n s : ℝ) *
        Real.log (((criticalTargetCapacity k n - criticalTargetSelectedCount k n : ℕ) : ℝ) /
          (criticalTargetCapacity k n : ℝ)) +
      (criticalSelectedIncrease k n s : ℝ) *
        Real.log (((criticalTargetCapacity k n - criticalTargetSelectedCount k n : ℕ) : ℝ) /
          (criticalTargetSelectedCount k n : ℝ)) =
      criticalFirstOrderAtDensityExponent k n s (criticalBalancedSelectedDensity k n) := by
  have hN : (criticalTargetCapacity k n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hM.trans hMN))
  have hMR : (criticalTargetSelectedCount k n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  have hfirst :
      ((criticalTargetCapacity k n - criticalTargetSelectedCount k n : ℕ) : ℝ) /
        (criticalTargetCapacity k n : ℝ) = 1 - criticalBalancedSelectedDensity k n := by
    rw [Nat.cast_sub hMN.le]
    unfold criticalBalancedSelectedDensity
    field_simp
  have hsecond :
      ((criticalTargetCapacity k n - criticalTargetSelectedCount k n : ℕ) : ℝ) /
        (criticalTargetSelectedCount k n : ℝ) =
      (1 - criticalBalancedSelectedDensity k n) / criticalBalancedSelectedDensity k n := by
    rw [Nat.cast_sub hMN.le]
    unfold criticalBalancedSelectedDensity
    field_simp
  rw [hfirst, hsecond, criticalCapacityLoss_cast_eq_signed hcapacity,
    criticalSelectedIncrease_cast_eq_signed hinternal]
  rfl

/-- The entropy-sandwich error is at most twice the logarithm of the graph
order plus one. -/
theorem log_criticalTargetCapacity_succ_le (k n : ℕ) :
    Real.log ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) ≤
      2 * Real.log ((n + 1 : ℕ) : ℝ) := by
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) n
  have hN : criticalTargetCapacity k n ≤ n ^ 2 := by
    apply le_trans (show criticalTargetCapacity k n ≤ n.choose 2 by
      unfold criticalTargetCapacity
      omega)
    exact Nat.choose_le_pow n 2
  have hNR : (criticalTargetCapacity k n : ℝ) ≤ (n : ℝ) ^ 2 := by
    exact_mod_cast hN
  have h := Real.log_le_log
    (show (0 : ℝ) < ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) by positivity)
    (show ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) ^ 2) by
        push_cast
        nlinarith [Nat.cast_nonneg (α := ℝ) n])
  simpa [Real.log_pow] using h

/-- Finite critical binomial comparison before absorbing the linear and
logarithmic errors.  A factor-four reserve in the Gaussian coefficient is
kept for the later logarithmic sparse cutoff. -/
theorem criticalCombinedSlice_le_reference_with_errors_of_bounds
    {k n s : ℕ} (hk : 3 ≤ k) (hs : 1 ≤ s) (hsn : s ≤ n)
    (hn : 4 * (k - 1) ≤ n)
    (hreference : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      criticalEdgeCount k n)
    (hmargin : 8 / (n : ℝ) ≤ criticalDensityMargin k)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n)
    (hinternal : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n)
    (hM : 0 < criticalTargetSelectedCount k n)
    (hMN : criticalTargetSelectedCount k n < criticalTargetCapacity k n)
    (hKhalf : 2 * criticalCapacityLoss k n s ≤ criticalTargetCapacity k n)
    (hLhalf : 2 * criticalSelectedIncrease k n s ≤ criticalTargetSelectedCount k n)
    (hdhalf : 2 * (criticalCapacityLoss k n s + criticalSelectedIncrease k n s) ≤
      criticalTargetCapacity k n - criticalTargetSelectedCount k n)
    (hquad : criticalQuadraticExponent k n s ≤
      (-criticalQuadraticCoefficient k + criticalSparseQuadraticGap k / 16) * (s : ℝ) ^ 2)
    (hcubic : DenseGraph.binomialSecondOrderCubicError
      (criticalTargetCapacity k n) (criticalTargetSelectedCount k n)
      (criticalCapacityLoss k n s) (criticalSelectedIncrease k n s) ≤
        criticalSparseQuadraticGap k / 8 * (s : ℝ) ^ 2) :
    (Nat.choose (criticalMaximumCombinedCapacity k n s)
      (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
      (criticalReferenceFiberCard k n : ℝ) * Real.exp
        (-(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
          criticalCombinedSliceErrorConstant k * s +
          criticalCombinedSliceErrorConstant k * Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hshift : criticalTargetSelectedCount k n + criticalSelectedIncrease k n s ≤
      criticalTargetCapacity k n - criticalCapacityLoss k n s := by omega
  have hselected := criticalTargetSelectedCount_add_increase_eq_maximum
    hcapacity hinternal hreference hshift
  have hbin := DenseGraph.choose_sub_capacity_add_selected_secondOrder_le
    hM hMN hKhalf hLhalf hdhalf
  rw [criticalTargetCapacity_sub_loss hcapacity, hselected,
    ← criticalReferenceFiberCard_eq_choose_of_feasible hreference] at hbin
  apply hbin.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hfirst := criticalFirstOrderAtTargetDensity_le hk hsn hn hreference hmargin
    (by rw [← criticalCapacityLoss_cast_eq_signed hcapacity]; positivity)
    (by rw [← criticalSelectedIncrease_cast_eq_signed hinternal]; positivity)
  have hfirstEq := criticalBinomialFirstOrder_eq hM hMN hcapacity hinternal
  have hlog := log_criticalTargetCapacity_succ_le k n
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hgap := criticalSparseQuadraticGap_pos hk
  have habs := le_abs_self (criticalFirstOrderResidueBound k)
  have hres := mul_le_mul_of_nonneg_left hsR
    (abs_nonneg (criticalFirstOrderResidueBound k))
  have hC : 2 ≤ criticalCombinedSliceErrorConstant k := by
    unfold criticalCombinedSliceErrorConstant
    have hdiv : 0 ≤ 16 / criticalDensityMargin k :=
      div_nonneg (by norm_num) (criticalDensityMargin_pos hk).le
    linarith [abs_nonneg (criticalFirstOrderResidueBound k)]
  have hCLog := mul_le_mul_of_nonneg_right hC hlog0
  have hgapSq := mul_nonneg hgap.le (sq_nonneg (s : ℝ))
  rw [← hfirstEq] at hfirst
  unfold criticalQuadraticExponent at hquad
  simp only [neg_div] at hquad
  unfold criticalSparsePenaltyConstant criticalSparseQuadraticGap at *
  unfold criticalCombinedSliceErrorConstant at *
  nlinarith only [hfirst, hquad, hcubic, hlog, habs, hres, hCLog, hgapSq, hsR]

/-- Both signs of the integer profile shift are controlled by the same
compact-band adjacent-binomial estimate.  Counts outside the capacity give
the zero binomial coefficient, without any extra feasibility assumption. -/
theorem criticalShiftedCombinedSlice_le_of_center_bound
    {k n s x : ℕ} (hk : 3 ≤ k) {u : ℤ} {E : ℝ}
    (hcenter : (Nat.choose (criticalMaximumCombinedCapacity k n s)
      (criticalMaximumCombinedSelectedCount k n s) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) * Real.exp E)
    (hlower : criticalDensityMargin k * (criticalMaximumCombinedCapacity k n s : ℝ) ≤
      (criticalMaximumCombinedSelectedCount k n s : ℝ))
    (hupper : (criticalMaximumCombinedSelectedCount k n s : ℝ) ≤
      (1 - criticalDensityMargin k) * (criticalMaximumCombinedCapacity k n s : ℝ))
    (hdist : Nat.dist x (criticalMaximumCombinedSelectedCount k n s) = u.natAbs) :
    (Nat.choose (criticalMaximumCombinedCapacity k n s) x : ℝ) ≤
      (criticalReferenceFiberCard k n : ℝ) *
        Real.exp (E + criticalShiftErrorConstant k * (u.natAbs : ℝ)) := by
  by_cases hx : x ≤ criticalMaximumCombinedCapacity k n s
  · have hy : criticalMaximumCombinedSelectedCount k n s ≤
        criticalMaximumCombinedCapacity k n s := by
      unfold criticalMaximumCombinedSelectedCount
      exact Nat.sub_le _ _
    have hshift := DenseGraph.choose_le_choose_mul_exp_abs_shift_of_compact_band
      hx hy (criticalDensityMargin_pos hk) (criticalDensityMargin_lt_half hk)
      hlower hupper
    rw [hdist] at hshift
    calc
      (Nat.choose (criticalMaximumCombinedCapacity k n s) x : ℝ) ≤
          (Nat.choose (criticalMaximumCombinedCapacity k n s)
            (criticalMaximumCombinedSelectedCount k n s) : ℝ) *
              Real.exp (criticalShiftErrorConstant k * (u.natAbs : ℝ)) := hshift
      _ ≤ ((criticalReferenceFiberCard k n : ℝ) * Real.exp E) *
          Real.exp (criticalShiftErrorConstant k * (u.natAbs : ℝ)) :=
        mul_le_mul_of_nonneg_right hcenter (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hx), Nat.cast_zero]
    positivity

/-- Elementary absorption of the linear and logarithmic errors above a
fixed logarithmic sparse cutoff. -/
theorem criticalSparseErrors_le_of_logarithmic_cutoff
    {c C L x s : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hL : 1 ≤ L) (hCL : 2 * C ≤ c * L)
    (hx : 1 ≤ x) (hs : L * x ≤ s) :
    C * s + C * x ≤ c * s ^ 2 := by
  have hxs : x ≤ s := (le_mul_of_one_le_left (by linarith : 0 ≤ x) hL).trans hs
  have hLs : L ≤ s := (le_mul_of_one_le_right (by linarith : 0 ≤ L) hx).trans hs
  have hs0 : 0 ≤ s := by linarith
  have hCs := mul_le_mul_of_nonneg_left hxs hC
  have hcLs := mul_le_mul_of_nonneg_left hLs hc.le
  have hscale := mul_le_mul_of_nonneg_right (hCL.trans hcLs) hs0
  nlinarith only [hCs, hscale]

end InducedStars
