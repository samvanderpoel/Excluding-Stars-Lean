import InducedStars.Structure.Critical.BinomialUniformBounds
import InducedStars.Structure.Critical.CombinedSlice
import InducedStars.Structure.Critical.WindowReference

/-!
# A coarse Gaussian binomial envelope in the critical window

The equitable reference uses the exact logarithmic-window edge count.
Capacity geometry is unchanged; density drift contributes an explicit
constant times s log(n+1), while the same quadratic gap remains positive.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

structure CriticalWindowCoarseGuards (k : ℕ) (a : ℝ) (n s : ℕ) : Prop where
  balancedInternal_le_edge :
    DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
      criticalWindowEdgeCount k a n
  selected_pos : 0 < criticalWindowReferenceSelected k a n
  selected_lt_capacity :
    criticalWindowReferenceSelected k a n < criticalTargetCapacity k n
  compact_lower :
    criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalWindowReferenceSelected k a n : ℝ)
  compact_upper :
    (criticalWindowReferenceSelected k a n : ℝ) ≤
      (1 - criticalDensityMargin k) * (criticalTargetCapacity k n : ℝ)
  triple_compact_selected :
    3 * criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalWindowReferenceSelected k a n : ℝ)
  triple_compact_remaining :
    3 * criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetCapacity k n : ℝ) -
        (criticalWindowReferenceSelected k a n : ℝ)
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
    2 * criticalSelectedIncrease k n s ≤ criticalWindowReferenceSelected k a n
  remaining_half :
    2 * (criticalCapacityLoss k n s +
      criticalSelectedIncrease k n s) ≤
        criticalTargetCapacity k n - criticalWindowReferenceSelected k a n


/-- Transfer the capacity guards to the moving window density. -/
theorem eventually_criticalWindowCoarseGuards
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      CriticalWindowCoarseGuards k a n s := by
  have hlambda := criticalDensityMargin_pos hk
  have hp := criticalDensityMargin_le_pK_div_four k
  have hq := criticalDensityMargin_le_one_sub_pK_div_four k
  have hband := (criticalWindowReferenceDensity_tendsto hk a).eventually
    (Ioo_mem_nhds (show 3 * criticalDensityMargin k < pK k by linarith)
      (show pK k < 1 - 3 * criticalDensityMargin k by linarith))
  filter_upwards [eventually_criticalBinomialSecondOrderGuards k hk,
    eventually_criticalWindowReference_feasible hk a,
    eventually_criticalWindowReference_interior hk a, hband] with
      n hgeom hfeas hinter hband
  intro s hs hsmall
  have hG := hgeom s hs hsmall
  have hM : 0 < criticalWindowReferenceSelected k a n := hinter.1
  have hMN : criticalWindowReferenceSelected k a n < criticalTargetCapacity k n := by
    simpa only [criticalWindowCoreCapacity, Nat.sub_zero, criticalTargetCapacity] using hinter.2
  have hN : (0 : ℝ) < criticalTargetCapacity k n := by exact_mod_cast hM.trans hMN
  change 3 * criticalDensityMargin k <
      (criticalWindowReferenceSelected k a n : ℝ) / criticalTargetCapacity k n ∧
    (criticalWindowReferenceSelected k a n : ℝ) / criticalTargetCapacity k n <
      1 - 3 * criticalDensityMargin k at hband
  have hlo3 := (lt_div_iff₀ hN).mp hband.1
  have hhi3 := (div_lt_iff₀ hN).mp hband.2
  have hlN := mul_pos hlambda hN
  have hlo : criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      criticalWindowReferenceSelected k a n := by nlinarith only [hlo3, hlN]
  have hhi : (criticalWindowReferenceSelected k a n : ℝ) ≤
      (1 - criticalDensityMargin k) * criticalTargetCapacity k n := by
    nlinarith only [hhi3, hlN]
  have hremaining : criticalDensityMargin k * (criticalTargetCapacity k n : ℝ) ≤
      (criticalTargetCapacity k n : ℝ) - criticalWindowReferenceSelected k a n := by
    nlinarith only [hhi]
  have hselectedHalf : 2 * (criticalCapacityLoss k n s + criticalSelectedIncrease k n s) ≤
      criticalWindowReferenceSelected k a n := by
    exact_mod_cast hG.twice_sum_le_margin.trans hlo
  have hremainingHalf : 2 * (criticalCapacityLoss k n s + criticalSelectedIncrease k n s) ≤
      criticalTargetCapacity k n - criticalWindowReferenceSelected k a n := by
    have hh := hG.twice_sum_le_margin.trans hremaining
    rw [← Nat.cast_sub hMN.le] at hh
    exact_mod_cast hh
  exact {
    balancedInternal_le_edge := by simpa [criticalWindowCoreInternal] using hfeas
    selected_pos := hM
    selected_lt_capacity := hMN
    compact_lower := hlo
    compact_upper := hhi
    triple_compact_selected := by nlinarith only [hlo3]
    triple_compact_remaining := by nlinarith only [hhi3]
    loss_add_increase_eq := hG.loss_add_increase_eq
    twice_sum_le_margin := hG.twice_sum_le_margin
    capacity_loss_half := hG.capacity_loss_half
    selected_increase_half := by omega
    remaining_half := hremainingHalf }

/-- Quadratic part of the reusable second-order binomial comparison at the
critical reference slice. -/
def criticalWindowCoarseQuadraticExponent (k : ℕ) (a : ℝ) (n s : ℕ) : ℝ :=
  -((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) ^ 2 /
      (2 * ((criticalTargetCapacity k n -
        criticalWindowReferenceSelected k a n : ℕ) : ℝ)) +
    (criticalCapacityLoss k n s : ℝ) ^ 2 /
      (2 * (criticalTargetCapacity k n : ℝ)) -
    (criticalSelectedIncrease k n s : ℝ) ^ 2 /
      (2 * (criticalWindowReferenceSelected k a n : ℝ))

/-- The four dimensionless coordinates which turn the finite quadratic term
into `s²` times `criticalNormalizedQuadratic`. -/
def criticalWindowCoarseQuadraticCoordinates (k : ℕ) (a : ℝ) (n s : ℕ) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  (((criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2,
      (criticalWindowReferenceSelected k a n : ℝ) /
        (criticalTargetCapacity k n : ℝ)),
    ((criticalCapacityLoss k n s : ℝ) /
        ((criticalCapacityLoss k n s +
          criticalSelectedIncrease k n s : ℕ) : ℝ),
      ((n - s : ℕ) : ℝ) / (n : ℝ)))

/-- Exact normalization identity for the finite quadratic expression. -/
theorem criticalWindowCoarseQuadraticExponent_eq_normalized
    {k n s : ℕ} {a : ℝ} (hn : 0 < n) (hs : 0 < s) (hsn : s < n)
    (hM : 0 < criticalWindowReferenceSelected k a n)
    (hMN : criticalWindowReferenceSelected k a n < criticalTargetCapacity k n)
    (hsum : criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s = s * (n - s)) :
    criticalWindowCoarseQuadraticExponent k a n s =
      (s : ℝ) ^ 2 *
        criticalNormalizedQuadratic (criticalWindowCoarseQuadraticCoordinates k a n s) := by
  have hN : (0 : ℝ) < criticalTargetCapacity k n := by
    exact_mod_cast hM.trans hMN
  have hMR : (0 : ℝ) < criticalWindowReferenceSelected k a n := by
    exact_mod_cast hM
  have hA : (0 : ℝ) < (criticalTargetCapacity k n : ℝ) -
      (criticalWindowReferenceSelected k a n : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hMN)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hnsR : (0 : ℝ) < (n : ℝ) - (s : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hsn)
  have hsumPos : 0 < criticalCapacityLoss k n s +
      criticalSelectedIncrease k n s := by
    rw [hsum]
    exact Nat.mul_pos hs (Nat.sub_pos_of_lt hsn)
  have hsumR : (0 : ℝ) <
      ((criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s : ℕ) : ℝ) := by
    exact_mod_cast hsumPos
  have hsumCast :
      (criticalCapacityLoss k n s : ℝ) +
          (criticalSelectedIncrease k n s : ℝ) =
        (s : ℝ) * ((n - s : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hLcast : (criticalSelectedIncrease k n s : ℝ) =
      (s : ℝ) * ((n - s : ℕ) : ℝ) -
        (criticalCapacityLoss k n s : ℝ) := by
    linarith
  unfold criticalWindowCoarseQuadraticExponent criticalWindowCoarseQuadraticCoordinates
    criticalNormalizedQuadratic
  rw [hsum, Nat.cast_mul, Nat.cast_sub hsn.le,
    Nat.cast_sub hMN.le]
  rw [hLcast, Nat.cast_sub hsn.le]
  field_simp [hN.ne', hMR.ne', hA.ne', hnR.ne', hsR.ne', hnsR.ne',
    hsumR.ne']

/-- Continuity turns coordinatewise finite control into the desired
quadratic penalty. -/
theorem criticalWindowCoarseQuadraticExponent_le_of_close
    {k n s : ℕ} {a : ℝ} (hk : 3 ≤ k) (hn : 0 < n) (hs : 0 < s) (hsn : s < n)
    (hM : 0 < criticalWindowReferenceSelected k a n)
    (hMN : criticalWindowReferenceSelected k a n < criticalTargetCapacity k n)
    (hsum : criticalCapacityLoss k n s +
        criticalSelectedIncrease k n s = s * (n - s))
    {epsilon : ℝ}
    (hclose : ∀ {a d x y : ℝ},
      |a - criticalReferenceCapacityScale k| < epsilon →
      |d - pK k| < epsilon →
      |x - criticalReferenceLossFraction k| < epsilon →
      |y - 1| < epsilon →
      criticalNormalizedQuadratic ((a, d), (x, y)) ≤
        -criticalQuadraticCoefficient k +
          criticalSparseQuadraticGap k / 16)
    (ha : |(criticalWindowCoarseQuadraticCoordinates k a n s).1.1 -
        criticalReferenceCapacityScale k| < epsilon)
    (hd : |(criticalWindowCoarseQuadraticCoordinates k a n s).1.2 - pK k| < epsilon)
    (hx : |(criticalWindowCoarseQuadraticCoordinates k a n s).2.1 -
        criticalReferenceLossFraction k| < epsilon)
    (hy : |(criticalWindowCoarseQuadraticCoordinates k a n s).2.2 - 1| < epsilon) :
    criticalWindowCoarseQuadraticExponent k a n s ≤
      (-criticalQuadraticCoefficient k +
        criticalSparseQuadraticGap k / 16) * (s : ℝ) ^ 2 := by
  rw [criticalWindowCoarseQuadraticExponent_eq_normalized hn hs hsn hM hMN hsum]
  have hnorm := hclose ha hd hx hy
  nlinarith [sq_nonneg (s : ℝ)]

/-- Uniform continuity estimate for the exact finite quadratic exponent. -/
theorem eventually_criticalWindowCoarseQuadraticExponent_le
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
      criticalWindowCoarseQuadraticExponent k a n s ≤
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
      |criticalWindowReferenceDensity k a n - pK k| < epsilon := by
    have h := (criticalWindowReferenceDensity_tendsto hk a).eventually
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
  filter_upwards [eventually_criticalWindowCoarseGuards k hk a,
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
  have ha : |(criticalWindowCoarseQuadraticCoordinates k a n s).1.1 -
      criticalReferenceCapacityScale k| < epsilon := by
    simpa [criticalWindowCoarseQuadraticCoordinates] using hcapacityCloseN
  have hd : |(criticalWindowCoarseQuadraticCoordinates k a n s).1.2 - pK k| <
      epsilon := by
    simpa [criticalWindowCoarseQuadraticCoordinates, criticalWindowReferenceDensity, criticalWindowCoreCapacity, criticalTargetCapacity, Nat.sub_zero]
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
  have hx : |(criticalWindowCoarseQuadraticCoordinates k a n s).2.1 -
      criticalReferenceLossFraction k| < epsilon := by
    apply hxBound.trans_lt
    rw [hconstantCast]
    have hsEpsilon : (s : ℝ) / n ≤ epsilon / 16 :=
      hsDiv.trans hdeltaEpsilon
    linarith
  have hy : |(criticalWindowCoarseQuadraticCoordinates k a n s).2.2 - 1| <
      epsilon := by
    rw [criticalWindowCoarseQuadraticCoordinates,
      abs_criticalRemainingVertexRatio_sub_one hnNat hsle]
    exact hsDiv.trans_lt (hdeltaEpsilon.trans_lt (by linarith))
  exact criticalWindowCoarseQuadraticExponent_le_of_close hk hnNat (by omega) hsnlt
    hG.selected_pos hG.selected_lt_capacity hG.loss_add_increase_eq
    (criticalQuadraticContinuityRadius_spec hk) ha hd hx hy

/-- The compact-band cubic Taylor error is uniformly at most one eighth of
the positive critical gap throughout the critical small-sparse range. -/
theorem eventually_criticalWindowCoarseCubicError_le
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * (n : ℝ) →
      DenseGraph.binomialSecondOrderCubicError
          (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n)
          (criticalCapacityLoss k n s) (criticalSelectedIncrease k n s) ≤
        criticalSparseQuadraticGap k / 8 * (s : ℝ) ^ 2 := by
  filter_upwards [eventually_criticalWindowCoarseGuards k hk a,
    eventually_criticalTargetCapacity_quadratic_lower k hk,
    eventually_ge_atTop 1] with n hguards hcapacityLower hnPos
  intro s hs hsSmall
  have hG := hguards s hs hsSmall
  let N := criticalTargetCapacity k n
  let M := criticalWindowReferenceSelected k a n
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

/-- The first-order expression in the generic binomial theorem agrees with
the signed-capacity critical expression, including the exact target density. -/
theorem criticalWindowCoarseBinomialFirstOrder_eq
    {k n s : ℕ} {a : ℝ}
    (hM : 0 < criticalWindowReferenceSelected k a n)
    (hMN : criticalWindowReferenceSelected k a n < criticalTargetCapacity k n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤ criticalTargetCapacity k n)
    (hinternal : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    (criticalCapacityLoss k n s : ℝ) *
        Real.log (((criticalTargetCapacity k n - criticalWindowReferenceSelected k a n : ℕ) : ℝ) /
          (criticalTargetCapacity k n : ℝ)) +
      (criticalSelectedIncrease k n s : ℝ) *
        Real.log (((criticalTargetCapacity k n - criticalWindowReferenceSelected k a n : ℕ) : ℝ) /
          (criticalWindowReferenceSelected k a n : ℝ)) =
      criticalFirstOrderAtDensityExponent k n s (criticalWindowReferenceDensity k a n) := by
  have hN : (criticalTargetCapacity k n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hM.trans hMN))
  have hMR : (criticalWindowReferenceSelected k a n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hM)
  have hfirst :
      ((criticalTargetCapacity k n - criticalWindowReferenceSelected k a n : ℕ) : ℝ) /
        (criticalTargetCapacity k n : ℝ) = 1 - criticalWindowReferenceDensity k a n := by
    rw [Nat.cast_sub hMN.le]
    unfold criticalTargetCapacity at hN ⊢
    unfold criticalWindowReferenceDensity criticalWindowCoreCapacity
    simp only [Nat.sub_zero]
    field_simp
  have hsecond :
      ((criticalTargetCapacity k n - criticalWindowReferenceSelected k a n : ℕ) : ℝ) /
        (criticalWindowReferenceSelected k a n : ℝ) =
      (1 - criticalWindowReferenceDensity k a n) / criticalWindowReferenceDensity k a n := by
    rw [Nat.cast_sub hMN.le]
    unfold criticalTargetCapacity at hN ⊢
    unfold criticalWindowReferenceDensity criticalWindowCoreCapacity
    simp only [Nat.sub_zero]
    field_simp
  rw [hfirst, hsecond, criticalCapacityLoss_cast_eq_signed hcapacity,
    criticalSelectedIncrease_cast_eq_signed hinternal]
  rfl


/-- The density displacement costs at most a fixed multiple of log(n+1)
after multiplication by n. -/
theorem exists_criticalWindowReferenceDensity_drift_bound
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n : ℕ in atTop,
      |criticalWindowReferenceDensity k a n - pK k| * n ≤
        D * Real.log ((n + 1 : ℕ) : ℝ) := by
  let b := ((k - 1 : ℕ) : ℝ) * a / (k - 2 : ℕ)
  refine ⟨|b| + 1, by positivity, ?_⟩
  have hh := (criticalWindowReferenceDensity_displacement_tendsto hk a).abs.eventually
    (Iio_mem_nhds (show |b| < |b| + 1 by linarith))
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hh, hlog, eventually_ge_atTop 1] with n hn hl hnPos
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change 0 < Real.log (n : ℝ) at hl
  simp only [abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
    abs_of_pos hl] at hn
  have hb := (div_lt_iff₀ hl).mp hn
  have hlogs : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hnR (by exact_mod_cast (Nat.le_succ n))
  exact hb.le.trans (mul_le_mul_of_nonneg_left hlogs (by positivity))

/-- The summed equitable slice has a Gaussian penalty throughout the fixed
small-sparse range. Window drift contributes only s log(n+1). -/
theorem eventually_criticalWindowCombinedSlice_le_reference
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      (Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalWindowReferenceSelected k a n + criticalSelectedIncrease k n s) : ℝ) ≤
      (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) *
        Real.exp (-(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
          C * s * Real.log ((n + 1 : ℕ) : ℝ) +
          C * Real.log ((n + 1 : ℕ) : ℝ)) := by
  obtain ⟨D, hD, hdrift⟩ := exists_criticalWindowReferenceDensity_drift_bound hk a
  let F := 2 * D / criticalDensityMargin k
  let C := F + |criticalFirstOrderResidueBound k| + 3
  have hF : 0 < F := by dsimp [F]; positivity [criticalDensityMargin_pos hk]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_criticalWindowCoarseGuards k hk a,
    eventually_criticalWindowCoarseQuadraticExponent_le k hk a,
    eventually_criticalWindowCoarseCubicError_le k hk a, hdrift, hlog,
    eventually_ge_atTop (4 * (k - 1) ^ 2), eventually_ge_atTop 1] with
      n hguards hquad hcubic hdriftN hlogN hnLarge hnPos
  intro s hsSmall
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogs : Real.log (n : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_le_log hnR (by exact_mod_cast (Nat.le_succ n))
  have hlogOne : 1 ≤ Real.log ((n + 1 : ℕ) : ℝ) := hlogN.trans hlogs
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by linarith only [hlogOne]
  by_cases hs0 : s = 0
  · subst s
    simp only [criticalMaximumCombinedCapacity, Nat.sub_zero,
      Nat.choose_eq_zero_of_lt (by norm_num : (0 : ℕ) < 2), add_zero,
      criticalSelectedIncrease, Nat.sub_self, Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, zero_add]
    apply le_mul_of_one_le_right (Nat.cast_nonneg _)
    exact Real.one_le_exp_iff.mpr (mul_nonneg hC.le hlog0)
  have hs : 1 ≤ s := by omega
  have hG := hguards s hs hsSmall
  have hquadN := hquad s hs hsSmall
  have hcubicN := hcubic s hs hsSmall
  have hsmall : 16 * s ≤ n := by
    have hd := (criticalCombinedSliceDelta_le_taylor k).trans
      (criticalTaylorDeltaBound_le_one_sixteenth k)
    have hh := hsSmall.trans (mul_le_mul_of_nonneg_right hd hnR.le)
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith only [hh])
  have hsle : s ≤ n := by omega
  have hcapacity := criticalMaximumCombinedCapacity_le_target hk hs hsmall hnLarge
  have hinternal := criticalBalancedInternalCapacity_mono_sparse hk hs hsmall hnLarge
  have hNpos : (0 : ℝ) < criticalTargetCapacity k n := by
    exact_mod_cast hG.selected_pos.trans hG.selected_lt_capacity
  have hband : criticalWindowReferenceDensity k a n ∈
      Icc (criticalDensityMargin k) (1 - criticalDensityMargin k) := by
    change criticalDensityMargin k ≤
        (criticalWindowReferenceSelected k a n : ℝ) / criticalTargetCapacity k n ∧
      (criticalWindowReferenceSelected k a n : ℝ) / criticalTargetCapacity k n ≤
        1 - criticalDensityMargin k
    exact ⟨(le_div_iff₀ hNpos).mpr hG.compact_lower,
      (div_le_iff₀ hNpos).mpr hG.compact_upper⟩
  have hfirst := criticalFirstOrderAtDensityExponent_le hk hsle
    (by rw [← criticalCapacityLoss_cast_eq_signed hcapacity]; positivity)
    (by rw [← criticalSelectedIncrease_cast_eq_signed hinternal]; positivity) hband
  have hns : ((n - s : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n s
  have hnsDrift : ((n - s : ℕ) : ℝ) *
      |criticalWindowReferenceDensity k a n - pK k| ≤
      D * Real.log ((n + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ (n : ℝ) * |criticalWindowReferenceDensity k a n - pK k| :=
        mul_le_mul_of_nonneg_right hns (abs_nonneg _)
      _ ≤ _ := by simpa only [mul_comm] using hdriftN
  have hpert : (2 * (s : ℝ) * ((n - s : ℕ) : ℝ)) *
      |criticalWindowReferenceDensity k a n - pK k| / criticalDensityMargin k ≤
      F * s * Real.log ((n + 1 : ℕ) : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hnsDrift
      (show 0 ≤ 2 * (s : ℝ) / criticalDensityMargin k by
        positivity [criticalDensityMargin_pos hk])
    dsimp [F]
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  have hbin := DenseGraph.choose_sub_capacity_add_selected_secondOrder_le
    hG.selected_pos hG.selected_lt_capacity hG.capacity_loss_half
      hG.selected_increase_half hG.remaining_half
  rw [criticalTargetCapacity_sub_loss hcapacity] at hbin
  apply hbin.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  have hfirstEq := criticalWindowCoarseBinomialFirstOrder_eq
    hG.selected_pos hG.selected_lt_capacity hcapacity hinternal
  rw [← hfirstEq] at hfirst
  have hlogcap := log_criticalTargetCapacity_succ_le k n
  have hres := (le_abs_self (criticalFirstOrderResidueBound k)).trans
    (le_mul_of_one_le_right (abs_nonneg _) hlogOne)
  have hCF : F ≤ C := by
    dsimp [C]
    linarith only [abs_nonneg (criticalFirstOrderResidueBound k)]
  have hCR : |criticalFirstOrderResidueBound k| + 2 ≤ C := by
    dsimp [C]; linarith only [hF]
  have hCs := mul_le_mul_of_nonneg_right hCF
    (mul_nonneg (Nat.cast_nonneg s) hlog0)
  have hClog := mul_le_mul_of_nonneg_right hCR hlog0
  have hgapSq := mul_nonneg (criticalSparseQuadraticGap_pos hk).le (sq_nonneg (s : ℝ))
  unfold criticalWindowCoarseQuadraticExponent at hquadN
  simp only [neg_div] at hquadN
  unfold criticalSparsePenaltyConstant criticalSparseQuadraticGap at *
  nlinarith only [hfirst, hquadN, hcubicN, hpert, hlogcap, hres, hCs, hClog, hgapSq]

end InducedStars
