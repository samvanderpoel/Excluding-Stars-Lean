import InducedStars.Structure.Critical.WindowCompletionGuards
import InducedStars.Structure.Critical.DivisionCounting
import InducedStars.Structure.Critical.WindowPrefactors
import DenseGraph.Combinatorics.CompactSequenceUniformity

/-!
# Uniform co-partite counts in the critical window

These bounds compare actual labeled co-partite graphs with the guarded
balanced completion count.  The comparison constants are independent of
the remainder size and its prescribed edge count throughout a bounded
logarithmic parameter rectangle.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowCoreOrder_scale_tendsto
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ ((n - s n : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (criticalWindowSize_div_nat_tendsto_zero hs)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [criticalWindow_eventually_size_le_nat hs,
    eventually_ge_atTop 1] with n hn hn1
  rw [Nat.cast_sub hn]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem criticalWindowCoreOrder_tendsto_atTop
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ n - s n) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have h := (criticalWindowCoreOrder_scale_tendsto hs).pos_mul_atTop
    (by norm_num : (0 : ℝ) < 1) tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [div_mul_cancel₀ _ hnR]

theorem criticalWindowRemainderEdges_div_sq_tendsto_zero
    {t : ℕ → ℕ} {y : ℝ}
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ (t n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h := ht.mul (hl.pow 2)
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
  apply h.congr'
  filter_upwards [criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn
  change 0 < Real.log (n : ℝ) at hn
  field_simp

theorem criticalWindowCoreCompleteEdges_scale_tendsto
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (completeEdgeCount (n - s n) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2)) := by
  have h := ((completeEdgeCount_orderedSquareFactor_tendsto_one.comp
    (criticalWindowCoreOrder_tendsto_atTop hs)).mul
      ((criticalWindowCoreOrder_scale_tendsto hs).pow 2)).div_const 2
  norm_num only [one_pow, one_mul] at h
  apply h.congr'
  filter_upwards [(criticalWindowCoreOrder_tendsto_atTop hs).eventually
    (eventually_ge_atTop 1), eventually_ge_atTop 1] with n hv hn
  have hvR : ((n - s n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - s n ≠ 0 by omega)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Function.comp_apply]
  field_simp

theorem criticalWindowCoreEdgeDensity_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ ((criticalWindowEdgeCount k a n - t n : ℕ) : ℝ) /
      completeEdgeCount (n - s n)) atTop (𝓝 (gammaK k)) := by
  have hm : Tendsto (fun n ↦ ((criticalWindowEdgeCount k a n - t n : ℕ) : ℝ) /
      (n : ℝ) ^ 2) atTop (𝓝 (gammaK k / 2)) := by
    have h := (criticalWindowEdgeCount_scale_tendsto hk a).sub
      (criticalWindowRemainderEdges_div_sq_tendsto_zero ht)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [eventually_criticalWindowCompletion_feasible hk a hs ht] with n hn
    rw [Nat.cast_sub (by omega : t n ≤ criticalWindowEdgeCount k a n)]
    ring
  have h := hm.div (criticalWindowCoreCompleteEdges_scale_tendsto hs)
    (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have heq : (gammaK k / 2) / (1 / 2) = gammaK k := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Pi.div_apply]
  field_simp

theorem criticalWindowCompletionDensity_tendsto
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s t : ℕ → ℕ} {x y : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 y)) :
    Tendsto (fun n ↦ (criticalWindowCompletionSelected k a n (s n) (t n) : ℝ) /
      criticalWindowCoreCapacity k n (s n)) atTop (𝓝 (pK k)) := by
  have hc : criticalReferenceCapacityScale k ≠ 0 := by
    unfold criticalReferenceCapacityScale
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
    positivity
  have hA : Tendsto (fun n ↦ (criticalWindowCoreCapacity k n (s n) : ℝ) /
      (n : ℝ) ^ 2) atTop (𝓝 (criticalReferenceCapacityScale k)) := by
    have h := (criticalTargetCapacity_scale_tendsto k hk).sub
      (criticalWindowPerturbation_div_sq_tendsto_zero
        (criticalWindowCapacityLoss_scale_tendsto hk hs))
    simp only [sub_zero] at h
    convert h using 1
    ext n
    unfold criticalWindowCapacityLoss criticalTargetCapacity criticalWindowCoreCapacity
    simp only [Nat.sub_zero]
    ring
  have hM : Tendsto (fun n ↦ (criticalWindowCompletionSelected k a n (s n) (t n) : ℝ) /
      (n : ℝ) ^ 2) atTop (𝓝 (pK k * criticalReferenceCapacityScale k)) := by
    have h := (criticalWindowReferenceSelected_scale_tendsto hk a).add
      (criticalWindowPerturbation_div_sq_tendsto_zero
        (criticalWindowSelectedIncrease_scale_tendsto hk hs ht))
    simp only [add_zero] at h
    apply h.congr'
    filter_upwards [eventually_criticalWindowCompletionSelected_cast hk a hs ht] with n hn
    rw [hn]
    ring
  have h := hM.div hA hc
  rw [mul_div_cancel_right₀ _ hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Pi.div_apply]
  field_simp

/-- The guarded completion definition is exactly the balanced reference
mass for the complementary core. -/
theorem coPartiteBalancedReferenceMass_eq_windowCompletion
    {k n s t : ℕ} {a : ℝ}
    (hfeas : criticalWindowCoreInternal k n s + t ≤ criticalWindowEdgeCount k a n) :
    coPartiteBalancedReferenceMass k (n - s) (criticalWindowEdgeCount k a n - t) =
      (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n s t : ℝ) := by
  unfold coPartiteBalancedReferenceMass criticalWindowBalancedMultinomial
    criticalWindowCompletionCount
  rw [ite_eq_left hfeas]
  simp only [criticalWindowCoreCapacity, criticalWindowCoreInternal, Nat.sub_sub, Nat.add_comm]

/-- Actual co-partite core counts have uniform constant-factor comparison
with the balanced completion reference throughout each bounded window. -/
theorem exists_criticalWindowCoPartite_comparison_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s t : ℕ,
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      (t : ℝ) / Real.log (n : ℝ) ^ 2 ≤ T →
      criticalWindowCoreInternal k n s + t ≤ criticalWindowEdgeCount k a n ∧
      C⁻¹ * ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
          (criticalWindowCompletionCount k a n s t : ℝ)) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
          (criticalWindowEdgeCount k a n - t) : ℝ) ∧
      (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
          (criticalWindowEdgeCount k a n - t) : ℝ) ≤
        C * ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
          (criticalWindowCompletionCount k a n s t : ℝ)) := by
  let eta := (1 - pK k) / 2
  have heta : 0 < eta := half_pos (sub_pos.mpr (pK_lt_one (by omega)))
  obtain ⟨C, hC, hcomparison⟩ := exists_coPartiteBalancedComparison k hk eta heta
  refine ⟨C, hC, ?_⟩
  apply DenseGraph.eventually_uniform_of_normalizedSequences_eventually
    criticalWindowLog_nat_tendsto_atTop
    ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      criticalWindowLog_nat_tendsto_atTop) ?_ L T
  intro s t x y _hx _hy hs ht
  have hselected := (criticalWindowCompletionDensity_tendsto hk a hs ht).eventually
    (Iio_mem_nhds (by dsimp [eta]; linarith [pK_lt_one (show 2 ≤ k by omega)] :
      pK k < 1 - eta))
  have htotal := (((criticalWindowCoreEdgeDensity_tendsto hk a hs ht).sub_const
    (criticalCoverComparisonDensity k)).abs).eventually
      (Iio_mem_nhds (criticalDensity_mem_coverComparison_window hk))
  filter_upwards [(criticalWindowCoreOrder_tendsto_atTop hs) hcomparison,
    eventually_criticalWindowCompletion_feasible hk a hs ht,
    eventually_criticalWindowCompletion_binomial_guards hk a hs ht,
    hselected, htotal] with n hcomp hfeas hguards hsel htotal
  have hselEq :
      criticalWindowEdgeCount k a n - t n -
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s n) =
      criticalWindowCompletionSelected k a n (s n) (t n) := by
    unfold criticalWindowCompletionSelected criticalWindowCoreInternal
    omega
  have h := hcomp (criticalWindowEdgeCount k a n - t n)
    (lt_trans hguards.2.2.1 hguards.2.2.2.1)
    (by
      change DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s n) ≤
        criticalWindowEdgeCount k a n - t n
      unfold criticalWindowCoreInternal at hfeas
      omega)
    (by rw [hselEq]; exact hsel.le)
    htotal
  rw [coPartiteBalancedReferenceMass_eq_windowCompletion hfeas.le] at h
  exact ⟨hfeas.le, h⟩

/-- The full window reference absorbs the assignment factor with the same
explicit polynomial and ordered-cover losses as at the critical density. -/
theorem eventually_windowReference_mul_pow_le_coPartiteCount_mul_poly
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      ((k - 1 : ℕ) : ℝ) ^ n *
          (Nat.choose (criticalTargetCapacity k n)
            (criticalWindowReferenceSelected k a n) : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) * (2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) := by
  have hd := (((criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk a).sub_const
    (criticalCoverComparisonDensity k)).abs).eventually
      (Iio_mem_nhds (criticalDensity_mem_coverComparison_window hk))
  filter_upwards [eventually_coPartiteBalancedReferenceMass_le_count k hk,
    eventually_criticalWindowReference_feasible hk a, hd] with n hcomp hf hd
  have href := hcomp (criticalWindowEdgeCount k a n)
    (by simpa only [criticalWindowCoreInternal, Nat.sub_zero] using hf) hd
  have hpow :
      ((k - 1 : ℕ) : ℝ) ^ n ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        (criticalWindowBalancedMultinomial (k - 1) n : ℝ) := by
    exact_mod_cast DenseGraph.pow_le_succ_pow_mul_multinomial_balancedPartSize
      (r := k - 1) (q := n) (by omega)
  change
    (criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
      (Nat.choose (criticalTargetCapacity k n)
        (criticalWindowReferenceSelected k a n) : ℝ) ≤
      (2 * (k - 1).factorial : ℕ) *
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ)
    at href
  calc
    ((k - 1 : ℕ) : ℝ) ^ n *
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
          (criticalWindowBalancedMultinomial (k - 1) n : ℝ)) *
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ = ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        ((criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
          (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ)) := by ring
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        ((2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ)) :=
      mul_le_mul_of_nonneg_left href (by positivity)
    _ = _ := by ring

/-- Division counting against the exact moving reference, with every loss
displayed explicitly. -/
theorem eventually_card_supercriticalDivisionsWithSparseCard_mul_windowReference_le
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ s ≤ n,
      ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
          (Nat.choose (criticalTargetCapacity k n)
            (criticalWindowReferenceSelected k a n) : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (k - 1) * (2 * (k - 1).factorial : ℕ) *
          (Nat.choose n s : ℝ) *
            (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) := by
  filter_upwards [eventually_windowReference_mul_pow_le_coPartiteCount_mul_poly k hk a]
    with n href
  intro s _hs
  have hr : 0 < k - 1 := by omega
  have hdiv : (supercriticalDivisionsWithSparseCard k n s).card ≤
      Nat.choose n s * (k - 1) ^ n :=
    (card_supercriticalDivisionsWithSparseCard_le k n s).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hr (Nat.sub_le n s)))
  have hdivR : ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) ≤
      (Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ) ^ n := by exact_mod_cast hdiv
  calc
    ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) ≤
      ((Nat.choose n s : ℝ) * ((k - 1 : ℕ) : ℝ) ^ n) *
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) :=
      mul_le_mul_of_nonneg_right hdivR (Nat.cast_nonneg _)
    _ = (Nat.choose n s : ℝ) * (((k - 1 : ℕ) : ℝ) ^ n *
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ)) := by ring
    _ ≤ (Nat.choose n s : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
        (2 * (k - 1).factorial : ℕ) *
          (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ)) :=
      mul_le_mul_of_nonneg_left href (Nat.cast_nonneg _)
    _ = _ := by ring


end InducedStars
