import InducedStars.Structure.Critical.WindowPositiveCounting
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The empty remainder above the critical-window transition

Positive exceptional sizes are summed geometrically.  This avoids a factor
of the ambient order and therefore treats every fixed parameter strictly
above the transition, however small its separation from the threshold.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

/-- Positive exceptional sizes in a bounded logarithmic range. -/
def criticalWindowPositiveSizes (n : ℕ) (L : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (n + 1)).filter fun s ↦
    1 ≤ s ∧ (s : ℝ) / Real.log (n : ℝ) ≤ L

@[simp] theorem mem_criticalWindowPositiveSizes {n s : ℕ} {L : ℝ} :
    s ∈ criticalWindowPositiveSizes n L ↔
      s ≤ n ∧ 1 ≤ s ∧ (s : ℝ) / Real.log (n : ℝ) ≤ L := by
  simp only [criticalWindowPositiveSizes, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hn, hp, hl⟩
    exact ⟨by omega, hp, hl⟩
  · rintro ⟨hn, hp, hl⟩
    exact ⟨by omega, hp, hl⟩

/-- The actual graphs admitting a positive-size clean remainder in the
specified logarithmic range. -/
def criticalWindowPositiveAssemblyFinset (k n : ℕ) (a L : ℝ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (criticalWindowPositiveSizes n L).biUnion fun s ↦
    exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s

/-- Uniform geometric domination of each actual positive-size row by the
full induced-free family. -/
theorem exists_criticalWindowAbove_row_geometric
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) (ha : criticalWindowThreshold k < a)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K delta : ℝ, 0 < K ∧ 0 < delta ∧ ∀ᶠ n : ℕ in atTop,
      0 < inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) ∧
      ∀ s : ℕ, s ∈ criticalWindowPositiveSizes n L →
        ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
          K * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) *
            (Real.exp (-delta * Real.log (n : ℝ))) ^ s := by
  let delta := (a / criticalWindowThreshold k - 1) / 2
  have hd : 0 < delta := half_pos (sub_pos.mpr
    ((one_lt_div (criticalWindowThreshold_pos hk)).mpr ha))
  have hdelta : a / criticalWindowThreshold k = 1 + 2 * delta := by dsimp [delta]; ring
  obtain ⟨C, hC, hrow⟩ := exists_criticalWindowAssembly_positive_row_upper hk a L hL hd
  obtain ⟨D, hD, hbase⟩ := exists_criticalWindowCoPartite_comparison_uniform hk a 0 0
  refine ⟨C * D, delta, mul_pos hC hD, hd, ?_⟩
  filter_upwards [hrow, hbase, eventually_criticalWindowCompletion_pos_uniform hk a 0 0,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 1] with n hr hb hp hl hn
  have hb0 := (hb 0 0 (by simp) (by simp)).2.1
  simp only [Nat.sub_zero] at hb0
  have hB : (0 : ℝ) < criticalWindowCompletionCount k a n 0 0 := by
    exact_mod_cast hp 0 0 (by simp) (by simp)
  have hM : (0 : ℝ) < criticalWindowBalancedMultinomial (k - 1) n := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n
  have hco : (coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) : ℝ) ≤
      (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) := by
    exact_mod_cast Finset.card_le_card
      (coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree (by omega : 1 ≤ k)
        (n := n) (m := criticalWindowEdgeCount k a n))
  have htotal : (0 : ℝ) < inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) :=
    (mul_pos (inv_pos.mpr hD) (mul_pos hM hB)).trans_le (hb0.trans hco)
  have hmass : (criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) ≤
      D * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (hb0.trans hco) hD.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] using h
  refine ⟨by exact_mod_cast htotal, ?_⟩
  intro s hs
  obtain ⟨hsn, hspos, hsL⟩ := mem_criticalWindowPositiveSizes.mp hs
  have hMs : (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) ≤
      criticalWindowBalancedMultinomial (k - 1) n := by
    have h := (criticalWindowBalancedMultinomial_add_bounds (by omega : 0 < k - 1) (n - s) s).1
    rw [Nat.sub_add_cancel hsn] at h
    exact_mod_cast h
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hchoose : (n.choose s : ℝ) ≤ Real.exp ((s : ℝ) * Real.log (n : ℝ)) := by
    rw [Real.exp_nat_mul, Real.exp_log hnR]
    exact_mod_cast Nat.choose_le_pow n s
  have hexp :
      Real.exp ((s : ℝ) * Real.log (n : ℝ)) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          delta * (s : ℝ) * Real.log (n : ℝ)) ≤
        Real.exp (-delta * (s : ℝ) * Real.log (n : ℝ)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold criticalWindowCompletionExponent
    simp only [Nat.cast_zero, zero_mul, add_zero]
    rw [hdelta]
    have hbeta : 0 ≤ gammaK k / criticalWindowThreshold k :=
      (div_pos (gammaK_pos hk) (criticalWindowThreshold_pos hk)).le
    nlinarith [mul_nonneg hbeta (sq_nonneg (s : ℝ))]
  calc
    ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
      C * (n.choose s : ℝ) *
        (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          delta * (s : ℝ) * Real.log (n : ℝ)) := hr s hspos hsL
    _ ≤ C * Real.exp ((s : ℝ) * Real.log (n : ℝ)) *
        (criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          delta * (s : ℝ) * Real.log (n : ℝ)) := by
      gcongr
    _ = (C * ((criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ))) *
      (Real.exp ((s : ℝ) * Real.log (n : ℝ)) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 +
          delta * (s : ℝ) * Real.log (n : ℝ))) := by ring
    _ ≤ (C * ((criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ))) *
          Real.exp (-delta * (s : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ (C * (D * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ))) *
          Real.exp (-delta * (s : ℝ) * Real.log (n : ℝ)) := by
      gcongr
    _ = (C * D) * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) *
        (Real.exp (-delta * Real.log (n : ℝ))) ^ s := by
      rw [← Real.exp_nat_mul]
      congr 1
      · ring
      · congr 1
        ring

/-- A finite sum over positive powers is bounded by the geometric tail. -/
theorem sum_positive_powers_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (S : Finset ℕ) (hS : 0 ∉ S) :
    ∑ s ∈ S, q ^ s ≤ q / (1 - q) := by
  have h := (summable_geometric_of_lt_one hq0 hq1).sum_le_tsum
    (insert 0 S) (fun s _ ↦ pow_nonneg hq0 s)
  rw [tsum_geometric_of_lt_one hq0 hq1, Finset.sum_insert hS, pow_zero] at h
  have hid : (1 - q)⁻¹ = 1 + q / (1 - q) := by
    have hne : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
    field_simp
    ring
  linarith

/-- Above the transition, the sum of the actual positive-size row counts is
negligible relative to the full exact-edge family. -/
theorem criticalWindowAbove_positive_row_sum_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) (ha : criticalWindowThreshold k < a)
    (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun n ↦
      (∑ s ∈ criticalWindowPositiveSizes n L,
        ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ)) /
      (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨K, delta, hK, hd, hrow⟩ := exists_criticalWindowAbove_row_geometric hk a ha L hL
  let q : ℕ → ℝ := fun n ↦ Real.exp (-delta * Real.log (n : ℝ))
  have hq : Tendsto q atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (criticalWindowLog_nat_tendsto_atTop.const_mul_atTop hd) using 1
    ext n
    simp only [q, Function.comp_apply]
    congr 1
    ring
  have hlimit : Tendsto (fun n ↦ K * (q n / (1 - q n))) atTop (𝓝 0) := by
    have h := (hq.div ((tendsto_const_nhds (x := (1 : ℝ))).sub hq) (by norm_num)).const_mul K
    simpa only [sub_zero, zero_div, mul_zero, Pi.div_apply] using h
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ div_nonneg
      (Finset.sum_nonneg fun s _ ↦ Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ hlimit
  filter_upwards [hrow, criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn hl
  have hN : (0 : ℝ) < inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) := by
    exact_mod_cast hn.1
  have hq0 : 0 ≤ q n := (Real.exp_pos _).le
  have hq1 : q n < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have : 0 < delta * Real.log (n : ℝ) := mul_pos hd hl
    nlinarith
  have hzero : 0 ∉ criticalWindowPositiveSizes n L := by simp
  have hgeom := sum_positive_powers_le hq0 hq1 (criticalWindowPositiveSizes n L) hzero
  have hsum :
      (∑ s ∈ criticalWindowPositiveSizes n L,
        ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ)) ≤
      (K * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ)) *
        (q n / (1 - q n)) := by
    calc
      _ ≤ ∑ s ∈ criticalWindowPositiveSizes n L,
          K * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ) *
            (q n) ^ s := Finset.sum_le_sum fun s hs ↦ hn.2 s hs
      _ = (K * (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ)) *
          ∑ s ∈ criticalWindowPositiveSizes n L, (q n) ^ s := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (mul_pos hK hN).le
  apply (div_le_iff₀ hN).mpr
  nlinarith only [hsum]

/-- The same vanishing bound for the actual union of all positive-size rows. -/
theorem criticalWindowAbove_positive_assembly_probability_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) (ha : criticalWindowThreshold k < a)
    (L : ℝ) (hL : 0 ≤ L) :
    Tendsto (fun n ↦
      ((criticalWindowPositiveAssemblyFinset k n a L).card : ℝ) /
        (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ))
      atTop (𝓝 0) := by
  classical
  apply squeeze_zero'
    (Eventually.of_forall fun _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (Eventually.of_forall fun n ↦ ?_)
    (criticalWindowAbove_positive_row_sum_tendsto_zero hk a ha L hL)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have h := Finset.card_biUnion_le
    (s := criticalWindowPositiveSizes n L)
    (t := fun s ↦ exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s)
  exact_mod_cast h

end InducedStars
