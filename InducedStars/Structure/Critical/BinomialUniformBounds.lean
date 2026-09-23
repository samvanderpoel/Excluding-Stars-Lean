import InducedStars.Structure.Critical.BinomialExpansion

/-!
# Uniform finite bounds for the critical binomial expansion

This file packages the estimates needed to apply the reusable second-order
binomial comparison simultaneously for every positive sparse size in the
critical small-sparse range.  The reference slice is independent of the
sparse size; all perturbation variables are the exact natural-valued loss and
increase from `Critical.BinomialExpansion`.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The exact hypotheses needed by the natural-number second-order binomial
comparison, together with the stronger common margin estimate from which the
three half-range hypotheses follow. -/
structure CriticalBinomialSecondOrderGuards (k n s : ℕ) : Prop where
  balancedInternal_le_edge :
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      criticalEdgeCount k n
  selected_pos : 0 < criticalTargetSelectedCount k n
  selected_lt_capacity :
    criticalTargetSelectedCount k n < criticalTargetCapacity k n
  compact_lower :
    criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetSelectedCount k n : ℝ)
  compact_upper :
    (criticalTargetSelectedCount k n : ℝ) ≤
      (1 - criticalDensityMargin k) * (criticalTargetCapacity k n : ℝ)
  triple_compact_selected :
    3 * criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetSelectedCount k n : ℝ)
  triple_compact_remaining :
    3 * criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetCapacity k n : ℝ) -
        (criticalTargetSelectedCount k n : ℝ)
  loss_add_increase_eq :
    criticalCapacityLoss k n s + criticalSelectedIncrease k n s =
      s * (n - s)
  twice_sum_le_margin :
    2 * ((criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
      criticalDensityMargin k * (criticalTargetCapacity k n : ℝ)
  capacity_loss_half :
    2 * criticalCapacityLoss k n s ≤ criticalTargetCapacity k n
  selected_increase_half :
    2 * criticalSelectedIncrease k n s ≤ criticalTargetSelectedCount k n
  remaining_half :
    2 * (criticalCapacityLoss k n s +
      criticalSelectedIncrease k n s) ≤
        criticalTargetCapacity k n - criticalTargetSelectedCount k n

/-- The critical reference capacity is eventually at least `n²/8`.  This is
the common denominator bound used by both the half-range and cubic estimates. -/
theorem eventually_criticalTargetCapacity_quadratic_lower
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ 2 / 8 ≤ (criticalTargetCapacity k n : ℝ) := by
  filter_upwards [eventually_ge_atTop (4 * (k - 1))] with n hn
  exact criticalTargetCapacity_quadratic_lower hk hn

/-- Uniform finite feasibility and half-range guards for the reusable
second-order binomial theorem. -/
theorem eventually_criticalBinomialSecondOrderGuards
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
      CriticalBinomialSecondOrderGuards k n s := by
  have hlambda : 0 < criticalDensityMargin k :=
    criticalDensityMargin_pos hk
  have hEightOver : Tendsto (fun n : ℕ ↦ (8 : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat 8
  have hmargin : ∀ᶠ n : ℕ in atTop,
      8 / (n : ℝ) ≤ criticalDensityMargin k :=
    ((tendsto_order.1 hEightOver).2 _ hlambda).mono fun _ hn ↦ hn.le
  filter_upwards [
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_criticalTargetSelectedCount_mem_Ioo k hk,
    eventually_criticalTargetCapacity_quadratic_lower k hk,
    hmargin,
    eventually_ge_atTop (4 * (k - 1) ^ 2)] with
      n hfeasible hselected hcapacityLower hmarginN hnLarge
  intro s hs hsSmall
  have hnPos : 0 < n := by
    have hrPos : 0 < k - 1 := by omega
    exact (Nat.mul_pos (by norm_num) (pow_pos hrPos 2)).trans_le hnLarge
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hlambda0 : 0 ≤ criticalDensityMargin k := hlambda.le
  have hdeltaTaylor :
      criticalCombinedSliceDelta k ≤ criticalTaylorDeltaBound k :=
    criticalCombinedSliceDelta_le_taylor k
  have hdeltaSixteenth :
      criticalCombinedSliceDelta k ≤ (1 / 16 : ℝ) :=
    hdeltaTaylor.trans (criticalTaylorDeltaBound_le_one_sixteenth k)
  have hsmallR : (16 : ℝ) * (s : ℝ) ≤ (n : ℝ) := by
    calc
      (16 : ℝ) * (s : ℝ) ≤
          16 * (criticalCombinedSliceDelta k * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsSmall (by norm_num)
      _ ≤ 16 * ((1 / 16 : ℝ) * (n : ℝ)) := by
        gcongr
      _ = (n : ℝ) := by ring
  have hsmall : 16 * s ≤ n := by exact_mod_cast hsmallR
  have hsle : s ≤ n := by omega
  have hsnlt : s < n := by omega
  have hcapacity := criticalMaximumCombinedCapacity_le_target
    hk hs hsmall hnLarge
  have hinternal := criticalBalancedInternalCapacity_mono_sparse
    hk hs hsmall hnLarge
  have hsum := criticalCapacityLoss_add_selectedIncrease
    hk hsle hcapacity hinternal
  have hnFour : 4 * (k - 1) ≤ n := by
    exact (Nat.mul_le_mul_left 4
      (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) (k - 1))).trans hnLarge
  have hband := criticalBalancedSelectedDensity_mem_compact
    hk hnFour hfeasible hmarginN
  have herr := criticalBalancedSelectedDensity_error_le
    hk hnFour hfeasible
  rw [abs_le] at herr
  have hmarginP := criticalDensityMargin_le_pK_div_four k
  have hmarginQ := criticalDensityMargin_le_one_sub_pK_div_four k
  have hTripleBandLower : 3 * criticalDensityMargin k ≤
      criticalBalancedSelectedDensity k n := by
    nlinarith
  have hTripleBandUpper : criticalBalancedSelectedDensity k n ≤
      1 - 3 * criticalDensityMargin k := by
    nlinarith
  have hNpos : (0 : ℝ) < criticalTargetCapacity k n := by
    exact_mod_cast hselected.1.trans hselected.2
  have hLower : criticalDensityMargin k *
      (criticalTargetCapacity k n : ℝ) ≤
        (criticalTargetSelectedCount k n : ℝ) := by
    apply (le_div_iff₀ hNpos).mp
    simpa [criticalBalancedSelectedDensity] using hband.1
  have hUpper : (criticalTargetSelectedCount k n : ℝ) ≤
      (1 - criticalDensityMargin k) *
        (criticalTargetCapacity k n : ℝ) := by
    apply (div_le_iff₀ hNpos).mp
    simpa [criticalBalancedSelectedDensity] using hband.2
  have hTripleSelected : 3 * criticalDensityMargin k *
      (criticalTargetCapacity k n : ℝ) ≤
        (criticalTargetSelectedCount k n : ℝ) := by
    apply (le_div_iff₀ hNpos).mp
    simpa [criticalBalancedSelectedDensity, mul_assoc] using hTripleBandLower
  have hTripleSelectedUpper : (criticalTargetSelectedCount k n : ℝ) ≤
      (1 - 3 * criticalDensityMargin k) *
        (criticalTargetCapacity k n : ℝ) := by
    apply (div_le_iff₀ hNpos).mp
    simpa [criticalBalancedSelectedDensity] using hTripleBandUpper
  have hTripleRemaining : 3 * criticalDensityMargin k *
      (criticalTargetCapacity k n : ℝ) ≤
        (criticalTargetCapacity k n : ℝ) -
          (criticalTargetSelectedCount k n : ℝ) := by
    nlinarith
  have hdeltaMargin : criticalCombinedSliceDelta k ≤
      criticalDensityMargin k / 16 :=
    hdeltaTaylor.trans (criticalTaylorDeltaBound_le_densityMargin_div k)
  have hnsCast : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hsumCast :
      ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) =
          (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hsumLe :
      ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
          (s : ℝ) * (n : ℝ) := by
    rw [hsumCast]
    exact mul_le_mul_of_nonneg_left hnsCast hsR.le
  have hdeltaScale :
      criticalCombinedSliceDelta k * (n : ℝ) ^ 2 ≤
        criticalDensityMargin k * ((n : ℝ) ^ 2 / 16) := by
    have := mul_le_mul_of_nonneg_right hdeltaMargin
      (sq_nonneg (n : ℝ))
    nlinarith
  have hsumSmall :
      2 * ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
          criticalDensityMargin k * ((n : ℝ) ^ 2 / 8) := by
    have hsN : (s : ℝ) * (n : ℝ) ≤
        criticalCombinedSliceDelta k * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hsSmall hnR.le
      nlinarith
    nlinarith
  have hcapacityScaled : criticalDensityMargin k *
      ((n : ℝ) ^ 2 / 8) ≤
        criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) :=
    mul_le_mul_of_nonneg_left hcapacityLower hlambda0
  have hsumMargin :
      2 * ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ≤
          criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) :=
    hsumSmall.trans hcapacityScaled
  have hlambdaHalf := criticalDensityMargin_lt_half hk
  have hmarginCapacity : criticalDensityMargin k *
      (criticalTargetCapacity k n : ℝ) ≤
        (criticalTargetCapacity k n : ℝ) := by
    have hN0 : (0 : ℝ) ≤ criticalTargetCapacity k n := hNpos.le
    nlinarith
  have hsumHalfCapacity :
      2 * (criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s) ≤ criticalTargetCapacity k n := by
    exact_mod_cast hsumMargin.trans hmarginCapacity
  have hsumHalfSelected :
      2 * (criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s) ≤
        criticalTargetSelectedCount k n := by
    exact_mod_cast hsumMargin.trans hLower
  have hKhalfR :
      (2 * criticalCapacityLoss k n s : ℕ) ≤
        criticalTargetCapacity k n := by omega
  have hLhalfR :
      (2 * criticalSelectedIncrease k n s : ℕ) ≤
        criticalTargetSelectedCount k n := by omega
  have hremainingR :
      2 * (criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s) ≤
        criticalTargetCapacity k n - criticalTargetSelectedCount k n := by
    have hRemainingReal : criticalDensityMargin k *
        (criticalTargetCapacity k n : ℝ) ≤
          (criticalTargetCapacity k n : ℝ) -
            (criticalTargetSelectedCount k n : ℝ) := by
      rw [show criticalDensityMargin k *
          (criticalTargetCapacity k n : ℝ) =
        (criticalTargetCapacity k n : ℝ) -
          (1 - criticalDensityMargin k) *
            (criticalTargetCapacity k n : ℝ) by ring]
      exact sub_le_sub_left hUpper _
    have hremainingReal :
        ((2 * (criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s) : ℕ) : ℝ) ≤
          ((criticalTargetCapacity k n -
            criticalTargetSelectedCount k n : ℕ) : ℝ) := by
      push_cast
      rw [Nat.cast_sub hselected.2.le]
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        hsumMargin.trans hRemainingReal
    exact_mod_cast hremainingReal
  exact {
    balancedInternal_le_edge := hfeasible
    selected_pos := hselected.1
    selected_lt_capacity := hselected.2
    compact_lower := hLower
    compact_upper := hUpper
    triple_compact_selected := hTripleSelected
    triple_compact_remaining := hTripleRemaining
    loss_add_increase_eq := hsum
    twice_sum_le_margin := hsumMargin
    capacity_loss_half := hKhalfR
    selected_increase_half := hLhalfR
    remaining_half := hremainingR }

/-- Uniform continuity estimate for the exact finite quadratic exponent. -/
theorem eventually_criticalQuadraticExponent_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
      criticalQuadraticExponent k n s ≤
        (-criticalQuadraticCoefficient k +
          criticalSparseQuadraticGap k / 16) * (s : ℝ) ^ 2 := by
  let epsilon := criticalQuadraticContinuityRadius k
  have hepsilon : 0 < epsilon := criticalQuadraticContinuityRadius_pos hk
  have hcapacityClose : ∀ᶠ n : ℕ in atTop,
      |(criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2 -
          criticalReferenceCapacityScale k| < epsilon := by
    have h := (criticalTargetCapacity_scale_tendsto k hk).eventually
      (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [h] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have hdensityClose : ∀ᶠ n : ℕ in atTop,
      |criticalBalancedSelectedDensity k n - pK k| < epsilon := by
    have h := (criticalBalancedSelectedDensity_tendsto k hk).eventually
      (Metric.ball_mem_nhds _ hepsilon)
    filter_upwards [h] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have hconstantLimit : Tendsto
      (fun n : ℕ ↦
        ((2 * (k - 1) + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact tendsto_const_div_atTop_nhds_zero_nat _
  have hconstantSmall : ∀ᶠ n : ℕ in atTop,
      ((2 * (k - 1) + 1 : ℕ) : ℝ) / (n : ℝ) <
        15 * epsilon / 16 :=
    (tendsto_order.1 hconstantLimit).2 _ (by positivity)
  filter_upwards [eventually_criticalBinomialSecondOrderGuards k hk,
    hcapacityClose, hdensityClose, hconstantSmall,
    eventually_ge_atTop 1,
    eventually_ge_atTop (4 * (k - 1) ^ 2)] with
      n hguards hcapacityCloseN hdensityCloseN hconstantSmallN hnPos hnLarge
  intro s hs hsSmall
  have hG := hguards s hs hsSmall
  have hnNat : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hdeltaEpsilon : criticalCombinedSliceDelta k ≤ epsilon / 16 :=
    criticalCombinedSliceDelta_le_continuity k
  have hsle : s ≤ n := by
    have hdeltaOne : criticalCombinedSliceDelta k ≤ (1 : ℝ) :=
      (criticalCombinedSliceDelta_le_taylor k).trans
        (criticalTaylorDeltaBound_le_one_sixteenth k) |>.trans (by norm_num)
    have hsReal : (s : ℝ) ≤ n :=
      hsSmall.trans (by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hdeltaOne
            (show (0 : ℝ) ≤ n by positivity))
    exact_mod_cast hsReal
  have hsnlt : s < n := by
    have hsmall : (s : ℝ) ≤ (1 / 16 : ℝ) * n :=
      hsSmall.trans (mul_le_mul_of_nonneg_right
        ((criticalCombinedSliceDelta_le_taylor k).trans
          (criticalTaylorDeltaBound_le_one_sixteenth k)) (by positivity))
    have hsPos : (0 : ℝ) < s := by exact_mod_cast hs
    exact_mod_cast (show (s : ℝ) < n by nlinarith)
  have ha : |(criticalQuadraticCoordinates k n s).1.1 -
      criticalReferenceCapacityScale k| < epsilon := by
    simpa [criticalQuadraticCoordinates] using hcapacityCloseN
  have hd : |(criticalQuadraticCoordinates k n s).1.2 - pK k| <
      epsilon := by
    simpa [criticalQuadraticCoordinates, criticalBalancedSelectedDensity]
      using hdensityCloseN
  have hsmallR : (16 : ℝ) * (s : ℝ) ≤ (n : ℝ) := by
    calc
      (16 : ℝ) * (s : ℝ) ≤
          16 * (criticalCombinedSliceDelta k * (n : ℝ)) := by gcongr
      _ ≤ 16 * ((1 / 16 : ℝ) * n) := by
        gcongr
        exact (criticalCombinedSliceDelta_le_taylor k).trans
          (criticalTaylorDeltaBound_le_one_sixteenth k)
      _ = n := by ring
  have hsmall : 16 * s ≤ n := by exact_mod_cast hsmallR
  have hxBound := abs_criticalCapacityLossRatio_sub_reference_le
    hk hs (by omega : 2 * s ≤ n)
      (criticalMaximumCombinedCapacity_le_target hk hs
        hsmall hnLarge)
      (criticalBalancedInternalCapacity_mono_sparse hk hs
        hsmall hnLarge)
  have hsDiv : (s : ℝ) / (n : ℝ) ≤
      criticalCombinedSliceDelta k := by
    exact (div_le_iff₀ hnR).2 hsSmall
  have hconstantCast :
      (((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / (n : ℝ)) =
        (s : ℝ) / n +
          ((2 * (k - 1) + 1 : ℕ) : ℝ) / n := by
    push_cast
    ring
  have hx : |(criticalQuadraticCoordinates k n s).2.1 -
      criticalReferenceLossFraction k| < epsilon := by
    apply hxBound.trans_lt
    rw [hconstantCast]
    have hsEpsilon : (s : ℝ) / n ≤ epsilon / 16 :=
      hsDiv.trans hdeltaEpsilon
    linarith
  have hy : |(criticalQuadraticCoordinates k n s).2.2 - 1| <
      epsilon := by
    rw [criticalQuadraticCoordinates,
      abs_criticalRemainingVertexRatio_sub_one hnNat hsle]
    exact hsDiv.trans_lt (hdeltaEpsilon.trans_lt (by linarith))
  exact criticalQuadraticExponent_le_of_close hk hnNat (by omega) hsnlt
    hG.selected_pos hG.selected_lt_capacity hG.loss_add_increase_eq
    (criticalQuadraticContinuityRadius_spec hk) ha hd hx hy

/-- The compact-band cubic Taylor error is uniformly at most one eighth of
the positive critical gap throughout the critical small-sparse range. -/
theorem eventually_criticalSecondOrderCubicError_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
      DenseGraph.binomialSecondOrderCubicError
          (criticalTargetCapacity k n) (criticalTargetSelectedCount k n)
          (criticalCapacityLoss k n s) (criticalSelectedIncrease k n s) ≤
        criticalSparseQuadraticGap k / 8 * (s : ℝ) ^ 2 := by
  filter_upwards [eventually_criticalBinomialSecondOrderGuards k hk,
    eventually_criticalTargetCapacity_quadratic_lower k hk,
    eventually_ge_atTop 1] with n hguards hcapacityLower hnPos
  intro s hs hsSmall
  have hG := hguards s hs hsSmall
  let N := criticalTargetCapacity k n
  let M := criticalTargetSelectedCount k n
  let K := criticalCapacityLoss k n s
  let L := criticalSelectedIncrease k n s
  let C := criticalSecondOrderCubicConstant k
  have hcubic :=
    DenseGraph.binomialSecondOrderCubicError_le_of_compact_band
      (criticalDensityMargin_pos hk) hG.selected_pos hG.selected_lt_capacity
        hG.compact_lower hG.compact_upper hG.capacity_loss_half
          hG.selected_increase_half hG.remaining_half
  change DenseGraph.binomialSecondOrderCubicError N M K L ≤ _ at hcubic
  change DenseGraph.binomialSecondOrderCubicError N M K L ≤
    C * (((K + L : ℕ) : ℝ) ^ 3) / (N : ℝ) ^ 2 at hcubic
  have hnR : (0 : ℝ) < n := by positivity
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast (hG.selected_pos.trans hG.selected_lt_capacity)
  have hC : 0 < C := criticalSecondOrderCubicConstant_pos hk
  have hsumCast : (((K + L : ℕ) : ℝ)) =
      (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    exact_mod_cast hG.loss_add_increase_eq
  have hremaining : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hsumLe : ((K + L : ℕ) : ℝ) ≤ (s : ℝ) * (n : ℝ) := by
    rw [hsumCast]
    exact mul_le_mul_of_nonneg_left hremaining (by positivity)
  have hsumCube : (((K + L : ℕ) : ℝ) ^ 3) ≤
      ((s : ℝ) * (n : ℝ)) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hsumLe 3
  have hcapacitySquare : ((n : ℝ) ^ 2 / 8) ^ 2 ≤ (N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by simpa [N] using hcapacityLower) 2
  have hcubicSimple : C * (((K + L : ℕ) : ℝ) ^ 3) / (N : ℝ) ^ 2 ≤
      64 * C * (s : ℝ) ^ 3 / (n : ℝ) := by
    calc
      C * (((K + L : ℕ) : ℝ) ^ 3) / (N : ℝ) ^ 2 ≤
          C * (((s : ℝ) * (n : ℝ)) ^ 3) / (N : ℝ) ^ 2 := by
        gcongr
      _ ≤ C * (((s : ℝ) * (n : ℝ)) ^ 3) /
          (((n : ℝ) ^ 2 / 8) ^ 2) := by
        gcongr
      _ = 64 * C * (s : ℝ) ^ 3 / (n : ℝ) := by
        field_simp
        ring
  have hdeltaControl : 512 * C * criticalCombinedSliceDelta k ≤
      criticalSparseQuadraticGap k := by
    have hscale : 0 ≤ 512 * C := by positivity
    have hdelta := mul_le_mul_of_nonneg_left
      (criticalCombinedSliceDelta_le_taylor k) hscale
    exact hdelta.trans (by
      simpa [C] using criticalTaylorDeltaBound_cubic_control hk)
  have hsDiv : (s : ℝ) / (n : ℝ) ≤
      criticalCombinedSliceDelta k := (div_le_iff₀ hnR).2 hsSmall
  have hfinal : 64 * C * (s : ℝ) ^ 3 / (n : ℝ) ≤
      criticalSparseQuadraticGap k / 8 * (s : ℝ) ^ 2 := by
    have hcoeff : 64 * C * ((s : ℝ) / n) ≤
        criticalSparseQuadraticGap k / 8 := by
      have hscaled := mul_le_mul_of_nonneg_left hsDiv (by positivity :
        0 ≤ 64 * C)
      nlinarith
    have hsSq : 0 ≤ (s : ℝ) ^ 2 := sq_nonneg _
    have := mul_le_mul_of_nonneg_right hcoeff hsSq
    calc
      64 * C * (s : ℝ) ^ 3 / (n : ℝ) =
          (64 * C * ((s : ℝ) / n)) * (s : ℝ) ^ 2 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ criticalSparseQuadraticGap k / 8 * (s : ℝ) ^ 2 := this
  exact hcubic.trans (hcubicSimple.trans hfinal)

end InducedStars
