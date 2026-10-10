import InducedStars.Structure.Critical.BinomialExpansion
import InducedStars.Structure.Critical.BinomialTail

/-!
# The critical Gaussian binomial bound

At the exact critical edge count, the binomial likelihood ratio contributes
one half of log(1/(1-p)) times the square of the remainder size. The upper-tail
Chernoff bound contributes at least p times that square. Their positive gap
gives the uniform Gaussian envelope used to sum the paper's Q_s.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

/-- The Chernoff rate divided by the square of the remainder size.
Coordinates are capacity/n², selected density, relative capacity loss, and s/n. -/
def criticalNormalizedChernoff (z : (ℝ × ℝ) × (ℝ × ℝ)) : ℝ :=
  (1 - z.2.2) ^ 2 * (1 - (1 - z.1.2) * z.2.1) ^ 2 /
    (2 * (z.1.1 * z.1.2 + z.2.2 * (1 - z.2.2) * (1 - z.2.1)))

theorem criticalReferenceLossFraction_mem_Ioo {k : ℕ} (hk : 3 ≤ k) :
    criticalReferenceLossFraction k ∈ Set.Ioo (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  constructor
  · exact div_pos hd hr
  · apply (div_lt_one hr).2
    exact_mod_cast (show k - 2 < k - 1 by omega)

theorem criticalNormalizedChernoff_at_limit_gt {k : ℕ} (hk : 3 ≤ k) :
    pK k < criticalNormalizedChernoff
      ((criticalReferenceCapacityScale k, pK k), (criticalReferenceLossFraction k, 0)) := by
  have hx := criticalReferenceLossFraction_mem_Ioo hk
  have hx0 := hx.1
  have hp := pK_pos (k := k) (by omega)
  have hp1 := pK_lt_one (k := k) (by omega)
  have hu : pK k < 1 - (1 - pK k) * criticalReferenceLossFraction k := by
    nlinarith [mul_pos (sub_pos.mpr hp1) (sub_pos.mpr hx.2)]
  have hscale : criticalReferenceCapacityScale k = criticalReferenceLossFraction k / 2 := rfl
  simp only [criticalNormalizedChernoff, hscale, sub_zero, one_pow, one_mul,
    zero_mul, add_zero]
  have hden : 0 < 2 * (criticalReferenceLossFraction k / 2 * pK k) := by positivity
  apply (lt_div_iff₀ hden).2
  have hsquare : (pK k) ^ 2 < (1 - (1 - pK k) * criticalReferenceLossFraction k) ^ 2 := by
    nlinarith
  have hsmall := mul_le_mul_of_nonneg_right hx.2.le (sq_nonneg (pK k))
  nlinarith

theorem continuousAt_criticalNormalizedChernoff_limit {k : ℕ} (hk : 3 ≤ k) :
    ContinuousAt criticalNormalizedChernoff
      ((criticalReferenceCapacityScale k, pK k), (criticalReferenceLossFraction k, 0)) := by
  have hx := criticalReferenceLossFraction_mem_Ioo hk
  have hx0 := hx.1
  have hp := pK_pos (k := k) (by omega)
  have ha : 0 < criticalReferenceCapacityScale k := by
    change 0 < criticalReferenceLossFraction k / 2
    positivity
  unfold criticalNormalizedChernoff
  apply ContinuousAt.div (by fun_prop) (by fun_prop)
  simpa using (mul_pos (show (0 : ℝ) < 2 by norm_num) (mul_pos ha hp)).ne'

theorem exists_criticalChernoffContinuityRadius {k : ℕ} (hk : 3 ≤ k) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ {a d x z : ℝ},
      |a - criticalReferenceCapacityScale k| < epsilon →
      |d - pK k| < epsilon →
      |x - criticalReferenceLossFraction k| < epsilon →
      |z| < epsilon →
      pK k ≤ criticalNormalizedChernoff ((a, d), (x, z)) := by
  let v := criticalNormalizedChernoff
    ((criticalReferenceCapacityScale k, pK k), (criticalReferenceLossFraction k, 0))
  have hgap : 0 < v - pK k := sub_pos.mpr (criticalNormalizedChernoff_at_limit_gt hk)
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp (continuousAt_criticalNormalizedChernoff_limit hk))
      (v - pK k) hgap
  refine ⟨epsilon, hepsilon, ?_⟩
  intro a d x z ha hd hx hz
  have hdist : dist ((a, d), (x, z))
      ((criticalReferenceCapacityScale k, pK k), (criticalReferenceLossFraction k, 0)) <
        epsilon := by
    simpa only [Prod.dist_eq, Real.dist_eq, max_lt_iff, sub_zero] using
      ⟨⟨ha, hd⟩, hx, hz⟩
  have hclose := hcontrol hdist
  rw [Real.dist_eq] at hclose
  have := (abs_lt.mp hclose).1
  dsimp [v] at *
  linarith

noncomputable def criticalChernoffContinuityRadius (k : ℕ) : ℝ :=
  if hk : 3 ≤ k then Classical.choose (exists_criticalChernoffContinuityRadius hk) else 1

theorem criticalChernoffContinuityRadius_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalChernoffContinuityRadius k := by
  rw [criticalChernoffContinuityRadius, dite_eq_left hk]
  exact (Classical.choose_spec (exists_criticalChernoffContinuityRadius hk)).1

theorem criticalChernoffContinuityRadius_spec {k : ℕ} (hk : 3 ≤ k) :
    ∀ {a d x z : ℝ},
      |a - criticalReferenceCapacityScale k| < criticalChernoffContinuityRadius k →
      |d - pK k| < criticalChernoffContinuityRadius k →
      |x - criticalReferenceLossFraction k| < criticalChernoffContinuityRadius k →
      |z| < criticalChernoffContinuityRadius k →
      pK k ≤ criticalNormalizedChernoff ((a, d), (x, z)) := by
  rw [criticalChernoffContinuityRadius, dite_eq_left hk]
  exact (Classical.choose_spec (exists_criticalChernoffContinuityRadius hk)).2

/-- A common small remainder radius for balanced capacity positivity and the
uniform Chernoff estimate. -/
noncomputable def criticalCombinedSliceDelta (k : ℕ) : ℝ :=
  min (1 / 16 : ℝ) (criticalChernoffContinuityRadius k / 16)

theorem criticalCombinedSliceDelta_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalCombinedSliceDelta k := by
  unfold criticalCombinedSliceDelta
  exact lt_min (by norm_num) (div_pos (criticalChernoffContinuityRadius_pos hk) (by norm_num))

theorem criticalCombinedSliceDelta_le_one_sixteenth (k : ℕ) :
    criticalCombinedSliceDelta k ≤ (1 / 16 : ℝ) := min_le_left _ _

theorem criticalCombinedSliceDelta_le_continuity (k : ℕ) :
    criticalCombinedSliceDelta k ≤ criticalChernoffContinuityRadius k / 16 := min_le_right _ _

def criticalChernoffCoordinates (k n s : ℕ) : (ℝ × ℝ) × (ℝ × ℝ) :=
  (((criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2,
    criticalBalancedSelectedDensity k n),
    ((criticalCapacityLoss k n s : ℝ) /
      ((criticalCapacityLoss k n s + criticalSelectedIncrease k n s : ℕ) : ℝ),
      (s : ℝ) / n))

/-- Uniform finite lower bound for the normalized Chernoff rate. -/
theorem eventually_criticalNormalizedChernoff_ge
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s →
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      pK k ≤ criticalNormalizedChernoff (criticalChernoffCoordinates k n s) := by
  let epsilon := criticalChernoffContinuityRadius k
  have hepsilon := criticalChernoffContinuityRadius_pos hk
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
      (fun n : ℕ => ((2 * (k - 1) + 1 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hconstantSmall : ∀ᶠ n : ℕ in atTop,
      ((2 * (k - 1) + 1 : ℕ) : ℝ) / (n : ℝ) < 15 * epsilon / 16 :=
    (tendsto_order.1 hconstantLimit).2 _ (by positivity)
  filter_upwards [hcapacityClose, hdensityClose, hconstantSmall,
    eventually_ge_atTop 1, eventually_ge_atTop (4 * (k - 1) ^ 2)] with
      n ha hd hconst hnPos hnLarge
  intro s hs hsmall
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsDiv : (s : ℝ) / n ≤ criticalCombinedSliceDelta k := (div_le_iff₀ hn).2 hsmall
  have hsmall16 : 16 * s ≤ n := by
    have h := hsDiv.trans (criticalCombinedSliceDelta_le_one_sixteenth k)
    have hh := (div_le_iff₀ hn).1 h
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith)
  have hxBound := abs_criticalCapacityLossRatio_sub_reference_le hk hs (by omega)
    (criticalMaximumCombinedCapacity_le_target hk hs hsmall16 hnLarge)
    (criticalBalancedInternalCapacity_mono_sparse hk hs hsmall16 hnLarge)
  have hconstantCast :
      ((s : ℝ) + 2 * ((k - 1 : ℕ) : ℝ) + 1) / n =
      (s : ℝ) / n + ((2 * (k - 1) + 1 : ℕ) : ℝ) / n := by
    push_cast
    ring
  have hx : |(criticalCapacityLoss k n s : ℝ) /
      ((criticalCapacityLoss k n s + criticalSelectedIncrease k n s : ℕ) : ℝ) -
      criticalReferenceLossFraction k| < epsilon := by
    apply hxBound.trans_lt
    rw [hconstantCast]
    have h := hsDiv.trans (criticalCombinedSliceDelta_le_continuity k)
    linarith
  have hz : |(s : ℝ) / n| < epsilon := by
    rw [abs_of_nonneg (by positivity)]
    exact hsDiv.trans_lt ((criticalCombinedSliceDelta_le_continuity k).trans_lt (by linarith))
  exact criticalChernoffContinuityRadius_spec hk ha hd hx hz

/-- Exact algebraic normalization of the upper-tail exponent. -/
theorem criticalChernoffExponent_eq_normalized
    {k n s : ℕ} (hn : 0 < n) (hs : 0 < s) (hsn : s < n)
    (hM : 0 < criticalTargetSelectedCount k n)
    (hN : 0 < criticalTargetCapacity k n)
    (hsum : criticalCapacityLoss k n s + criticalSelectedIncrease k n s = s * (n - s)) :
    ((criticalSelectedIncrease k n s : ℝ) + criticalBalancedSelectedDensity k n *
        criticalCapacityLoss k n s) ^ 2 /
        (2 * ((criticalTargetSelectedCount k n : ℝ) + criticalSelectedIncrease k n s)) =
      (s : ℝ) ^ 2 * criticalNormalizedChernoff (criticalChernoffCoordinates k n s) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hnsR : ((n : ℝ) - s) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hsn.ne')
  have hNR : (criticalTargetCapacity k n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hML : (criticalTargetSelectedCount k n : ℝ) + criticalSelectedIncrease k n s ≠ 0 := by
    have hMR : (0 : ℝ) < criticalTargetSelectedCount k n := by exact_mod_cast hM
    positivity
  have hL : (criticalSelectedIncrease k n s : ℝ) =
      (s : ℝ) * ((n : ℝ) - s) - criticalCapacityLoss k n s := by
    have hh := congrArg (fun t : ℕ => (t : ℝ)) hsum
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hsn.le] at hh
    linarith
  unfold criticalNormalizedChernoff criticalChernoffCoordinates criticalBalancedSelectedDensity
  rw [hsum, Nat.cast_mul, Nat.cast_sub hsn.le]
  rw [hL] at *
  field_simp
  ring

/-- The entropy mode bound costs at most two natural logarithms of n+1. -/
theorem log_criticalTargetCapacity_succ_le (k n : ℕ) :
    Real.log ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) ≤
      2 * Real.log ((n + 1 : ℕ) : ℝ) := by
  have htotal := DenseGraph.balancedCross_add_internal (k - 1) n
  have hN : criticalTargetCapacity k n ≤ n ^ 2 := by
    apply le_trans (show criticalTargetCapacity k n ≤ n.choose 2 by
      unfold criticalTargetCapacity
      omega)
    exact Nat.choose_le_pow n 2
  have hNR : (criticalTargetCapacity k n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hN
  have h := Real.log_le_log
    (show (0 : ℝ) < ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) by positivity)
    (show ((criticalTargetCapacity k n + 1 : ℕ) : ℝ) ≤ (((n + 1 : ℕ) : ℝ) ^ 2) by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n])
  simpa [Real.log_pow] using h

/-- The combined balanced coefficient has a uniform Gaussian envelope for
all sufficiently small remainders at the exact critical density. -/
theorem eventually_criticalCombinedSlice_le_reference
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) ≤ criticalCombinedSliceDelta k * n →
      (Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalTargetSelectedCount k n + criticalSelectedIncrease k n s) : ℝ) ≤
      (criticalReferenceFiberCard k n : ℝ) *
        Real.exp (-(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
          C * s * Real.log ((n + 1 : ℕ) : ℝ) +
          C * Real.log ((n + 1 : ℕ) : ℝ)) := by
  let F := 16 / criticalDensityMargin k
  let C := F + |criticalFirstOrderResidueBound k| + 3
  have hF : 0 < F := by dsimp [F]; positivity [criticalDensityMargin_pos hk]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hmargin : ∀ᶠ n : ℕ in atTop, 8 / (n : ℝ) ≤ criticalDensityMargin k :=
    ((tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (8 : ℝ))).2 _
      (criticalDensityMargin_pos hk)).mono fun _ h => h.le
  filter_upwards [eventually_criticalNormalizedChernoff_ge k hk,
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_criticalTargetSelectedCount_mem_Ioo k hk, hlog, hmargin,
    eventually_ge_atTop (4 * (k - 1) ^ 2), eventually_ge_atTop 1] with
      n hrate hreference hselected hlogN hmarginN hnLarge hnPos
  intro s hsmall
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog1 : 1 ≤ Real.log ((n + 1 : ℕ) : ℝ) := hlogN.trans
    (Real.log_le_log hnR (by exact_mod_cast (Nat.le_succ n)))
  have href := criticalReferenceFiberCard_eq_choose_of_feasible hreference
  by_cases hs0 : s = 0
  · subst s
    simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul,
      zero_add, add_zero, criticalSelectedIncrease, Nat.sub_zero, Nat.sub_self,
      criticalMaximumCombinedCapacity, Nat.choose_eq_zero_of_lt
        (by norm_num : 0 < 2), add_zero]
    rw [href]
    change (Nat.choose (criticalTargetCapacity k n) (criticalTargetSelectedCount k n) : ℝ) ≤ _
    exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_exp_iff.mpr (mul_nonneg hC.le
        (show 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) by linarith)))
  have hs : 1 ≤ s := by omega
  have hsmall16 : 16 * s ≤ n := by
    have hh := hsmall.trans (mul_le_mul_of_nonneg_right
      (criticalCombinedSliceDelta_le_one_sixteenth k) hnR.le)
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith)
  have hsn : s < n := by omega
  have hcapacity := criticalMaximumCombinedCapacity_le_target hk hs hsmall16 hnLarge
  have hinternal := criticalBalancedInternalCapacity_mono_sparse hk hs hsmall16 hnLarge
  have hsum := criticalCapacityLoss_add_selectedIncrease hk hsn.le hcapacity hinternal
  let N := criticalTargetCapacity k n
  let M := criticalTargetSelectedCount k n
  let K := criticalCapacityLoss k n s
  let L := criticalSelectedIncrease k n s
  let A := criticalMaximumCombinedCapacity k n s
  let q := criticalBalancedSelectedDensity k n
  have hN : 0 < N := hselected.1.trans hselected.2
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hselected.1
  have hq : 0 < q := by exact div_pos hMR hNR
  have hq1 : q < 1 := (div_lt_one hNR).2 (by exact_mod_cast hselected.2)
  have hNq : (N : ℝ) * q = M := by
    change (N : ℝ) * ((M : ℝ) / N) = M
    field_simp
  have hK : (K : ℝ) = (N : ℝ) - A := by
    dsimp [K, criticalCapacityLoss, N, A]
    rw [Nat.cast_sub hcapacity]
  have hdeviation : ((M + L : ℕ) : ℝ) - q * A = (L : ℝ) + q * K := by
    push_cast
    rw [hK]
    nlinarith [hNq]
  have hmean : q * (A : ℝ) ≤ (M + L : ℕ) := by
    have hz : 0 ≤ (L : ℝ) + q * K := by positivity
    linarith [hdeviation]
  by_cases hfeasible : M + L ≤ A
  · have hbin := choose_le_choose_mul_chernoff hN hq hq1 hNq
      (show 0 < M + L from lt_of_lt_of_le hselected.1 (Nat.le_add_right M L)) hfeasible hmean
    have htail : pK k * (s : ℝ) ^ 2 ≤
        ((L : ℝ) + q * K) ^ 2 / (2 * ((M : ℝ) + L)) := by
      rw [criticalChernoffExponent_eq_normalized
        (by omega) (by omega) hsn hselected.1 hN hsum]
      nlinarith [mul_le_mul_of_nonneg_right (hrate s hs hsmall) (sq_nonneg (s : ℝ))]
    have hfirstEq :
        ((N : ℝ) - A) * Real.log (1 - q) +
          ((M : ℝ) - (M + L : ℕ)) * Real.log (q / (1 - q)) =
        criticalFirstOrderAtDensityExponent k n s q := by
      have hlogInv : Real.log (q / (1 - q)) = -Real.log ((1 - q) / q) := by
        rw [Real.log_div hq.ne' (sub_pos.mpr hq1).ne',
          Real.log_div (sub_pos.mpr hq1).ne' hq.ne']
        ring
      rw [← hK, Nat.cast_add, hlogInv]
      dsimp [criticalFirstOrderAtDensityExponent]
      rw [← criticalCapacityLoss_cast_eq_signed hcapacity,
        ← criticalSelectedIncrease_cast_eq_signed hinternal]
      dsimp [K, L]
      ring
    have hfirst := criticalFirstOrderAtTargetDensity_le hk hsn.le
      (show 4 * (k - 1) ≤ n by
        exact (Nat.mul_le_mul_left 4 (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) _)).trans hnLarge)
      hreference hmarginN
      (by rw [← criticalCapacityLoss_cast_eq_signed hcapacity]; positivity)
      (by rw [← criticalSelectedIncrease_cast_eq_signed hinternal]; positivity)
    rw [hfirstEq, hdeviation, Nat.cast_add] at hbin
    have hprefactor : (Nat.choose N M : ℝ) * ((N : ℝ) + 1) *
        Real.exp (criticalFirstOrderAtDensityExponent k n s q -
          ((L : ℝ) + q * K) ^ 2 / (2 * ((M : ℝ) + L))) =
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalFirstOrderAtDensityExponent k n s q -
            ((L : ℝ) + q * K) ^ 2 / (2 * ((M : ℝ) + L)) +
              Real.log ((N + 1 : ℕ) : ℝ)) := by
      rw [href, Real.exp_add, Real.exp_log (by positivity)]
      push_cast
      ring
    rw [hprefactor] at hbin
    exact hbin.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have hlogcap := log_criticalTargetCapacity_succ_le k n
      have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
      have hres := le_abs_self (criticalFirstOrderResidueBound k)
      have hClog := mul_le_mul_of_nonneg_left hlog1 hC.le
      have hCs := mul_le_mul_of_nonneg_left hClog (by positivity : (0 : ℝ) ≤ s)
      have hCtwo : 2 ≤ C := by
        dsimp [C]
        linarith [abs_nonneg (criticalFirstOrderResidueBound k)]
      have hlogpay := mul_le_mul_of_nonneg_right hCtwo
        (show 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) by linarith)
      have hgapSq := mul_nonneg (criticalSparseQuadraticGap_pos hk).le (sq_nonneg (s : ℝ))
      have hresS := mul_le_mul_of_nonneg_left hsR (abs_nonneg (criticalFirstOrderResidueBound k))
      change _ ≤ _ at hfirst
      dsimp [C, F, criticalSparsePenaltyConstant, criticalSparseQuadraticGap] at *
      nlinarith only [hfirst, htail, hlogcap, hres, hresS, hCs, hlogpay, hgapSq,
        hlog1, hsR])) (by positivity))
  · rw [Nat.choose_eq_zero_of_lt (lt_of_not_ge hfeasible), Nat.cast_zero]
    positivity

end InducedStars
