import InducedStars.Structure.Critical.WindowAssemblies
import InducedStars.Structure.Critical.WindowCoPartite
import InducedStars.Structure.Critical.WindowUniformExpansion
import InducedStars.Structure.Critical.WindowPartition

/-!
# Counting exact-size clean assemblies in the critical window

The finite convolution is bounded by the critical remainder partition
function.  The displayed statements concern actual labeled graphs and
retain the exact floor edge count.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

theorem inducedStarFreeGraphCountWithEdges_eq_zero_of_completeEdgeCount_lt
    (k : ℕ) {n m : ℕ} (hm : completeEdgeCount n < m) :
    inducedStarFreeGraphCountWithEdges k n m = 0 := by
  classical
  change (inducedStarFreeGraphFinsetWithEdges k n m).card = 0
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro G hG
  have hcard := (mem_inducedStarFreeGraphFinsetWithEdges.mp hG).2
  have hmax := card_edgeFinset_le_completeEdgeCount G
  omega

/-- The exact assembly convolution may be truncated at the maximum possible
number of remainder edges, even when the total edge count is smaller. -/
theorem card_exactCriticalAssemblyFinset_le_remainder_range
    (k n m s : ℕ) :
    (exactCriticalAssemblyFinset k n m s).card ≤
      n.choose s * ∑ t ∈ Finset.range (completeEdgeCount s + 1),
        coMultipartiteGraphCountWithEdges (k - 1) (n - s) (m - t) *
          inducedStarFreeGraphCountWithEdges k s t := by
  apply (card_exactCriticalAssemblyFinset_le k n m s).trans
  apply Nat.mul_le_mul_left
  by_cases hsm : completeEdgeCount s ≤ m
  · have heq :
        (∑ t ∈ Finset.range (completeEdgeCount s + 1),
          coMultipartiteGraphCountWithEdges (k - 1) (n - s) (m - t) *
            inducedStarFreeGraphCountWithEdges k s t) =
        ∑ t ∈ Finset.range (m + 1),
          coMultipartiteGraphCountWithEdges (k - 1) (n - s) (m - t) *
            inducedStarFreeGraphCountWithEdges k s t := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro t ht hnot
      have hsmall : completeEdgeCount s < t := by
        have : ¬t < completeEdgeCount s + 1 := by simpa only [Finset.mem_range] using hnot
        omega
      rw [inducedStarFreeGraphCountWithEdges_eq_zero_of_completeEdgeCount_lt k hsmall,
        mul_zero]
    exact heq.ge
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (by omega)) (by intros; omega)

/-- Exponentiating the completion log comparison preserves both sides. -/
theorem criticalWindowCompletion_bounds_of_log_error
    {k n s t : ℕ} {a error : ℝ}
    (hB : 0 < criticalWindowCompletionCount k a n s t)
    (hB0 : 0 < criticalWindowCompletionCount k a n 0 0)
    (herror : |Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
        criticalWindowCompletionExponent k a n s t| ≤ error) :
    (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s t - error) ≤
      (criticalWindowCompletionCount k a n s t : ℝ) ∧
    (criticalWindowCompletionCount k a n s t : ℝ) ≤
      (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s t + error) := by
  have hBR : (0 : ℝ) < criticalWindowCompletionCount k a n s t := by exact_mod_cast hB
  have hB0R : (0 : ℝ) < criticalWindowCompletionCount k a n 0 0 := by exact_mod_cast hB0
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  constructor
  · have h := Real.exp_le_exp.mpr (show
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) +
          (criticalWindowCompletionExponent k a n s t - error) ≤
        Real.log (criticalWindowCompletionCount k a n s t : ℝ) by linarith)
    simpa only [Real.exp_add, Real.exp_log hBR, Real.exp_log hB0R] using h
  · have h := Real.exp_le_exp.mpr (show
        Real.log (criticalWindowCompletionCount k a n s t : ℝ) ≤
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) +
          (criticalWindowCompletionExponent k a n s t + error) by linarith)
    simpa only [Real.exp_add, Real.exp_log hBR, Real.exp_log hB0R] using h

theorem criticalWindowCompletionExponent_exp_factor
    {k : ℕ} (hk : 3 ≤ k) (a error : ℝ) (n s t : ℕ) :
    Real.exp (criticalWindowCompletionExponent k a n s t + error) =
      Real.exp (criticalWindowCompletionExponent k a n s 0 + error) *
        (pK k / (1 - pK k)) ^ t := by
  have hp : 0 < pK k / (1 - pK k) :=
    div_pos (pK_pos (by omega)) (sub_pos.mpr (pK_lt_one (by omega)))
  have heq : criticalWindowCompletionExponent k a n s t + error =
      (criticalWindowCompletionExponent k a n s 0 + error) +
        (t : ℝ) * Real.log (pK k / (1 - pK k)) := by
    unfold criticalWindowCompletionExponent
    push_cast
    ring
  rw [heq, Real.exp_add, Real.exp_nat_mul, Real.exp_log hp]

/-- Finite exact-row upper bound.  The error is an arbitrary real number,
so this lemma applies both to `epsilon log² n` and to `epsilon s log n`. -/
theorem criticalWindowAssembly_row_upper_of_comparison
    {k : ℕ} (hk : 3 ≤ k) (a C error : ℝ) (hC : 0 ≤ C) (n s : ℕ)
    (hcompare : ∀ t ≤ completeEdgeCount s,
      (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
        (criticalWindowEdgeCount k a n - t) : ℝ) ≤
      C * ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n s t : ℝ)))
    (hpos : ∀ t ≤ completeEdgeCount s, 0 < criticalWindowCompletionCount k a n s t)
    (hbase : 0 < criticalWindowCompletionCount k a n 0 0)
    (herror : ∀ t ≤ completeEdgeCount s,
      |Real.log (criticalWindowCompletionCount k a n s t : ℝ) -
        Real.log (criticalWindowCompletionCount k a n 0 0 : ℝ) -
        criticalWindowCompletionExponent k a n s t| ≤ error) :
    ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
      C * (n.choose s : ℝ) * (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n 0 0 : ℝ) *
        Real.exp (criticalWindowCompletionExponent k a n s 0 + error) *
        criticalRemainderPartitionFunction k s := by
  have hrow : ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
      (n.choose s : ℝ) *
        ∑ t ∈ Finset.range (completeEdgeCount s + 1),
          (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
            (criticalWindowEdgeCount k a n - t) : ℝ) *
          (inducedStarFreeGraphCountWithEdges k s t : ℝ) := by
    exact_mod_cast card_exactCriticalAssemblyFinset_le_remainder_range
      k n (criticalWindowEdgeCount k a n) s
  apply hrow.trans
  calc
    (n.choose s : ℝ) *
        ∑ t ∈ Finset.range (completeEdgeCount s + 1),
          (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
            (criticalWindowEdgeCount k a n - t) : ℝ) *
          (inducedStarFreeGraphCountWithEdges k s t : ℝ) ≤
      (n.choose s : ℝ) *
        ∑ t ∈ Finset.range (completeEdgeCount s + 1),
          (C * ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
            ((criticalWindowCompletionCount k a n 0 0 : ℝ) *
              Real.exp (criticalWindowCompletionExponent k a n s 0 + error) *
                (pK k / (1 - pK k)) ^ t))) *
          (inducedStarFreeGraphCountWithEdges k s t : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro t ht
      have ht' : t ≤ completeEdgeCount s := by have := Finset.mem_range.mp ht; omega
      have hB := (criticalWindowCompletion_bounds_of_log_error
        (hpos t ht') hbase (herror t ht')).2
      rw [criticalWindowCompletionExponent_exp_factor hk] at hB
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      apply (hcompare t ht').trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      simpa only [mul_assoc] using hB
    _ = _ := by
      unfold criticalRemainderPartitionFunction
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- Empty remainder graphs give the matching finite lower reference.
The only decomposition loss is polynomial in `s`, with degree `k-1`. -/
theorem criticalWindowAssembly_row_lower_of_comparison
    {k : ℕ} (hk : 3 ≤ k) (a C : ℝ) (n s : ℕ)
    (hcompare :
      C⁻¹ * ((criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n s 0 : ℝ)) ≤
      (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
        (criticalWindowEdgeCount k a n) : ℝ)) :
    C⁻¹ * (n.choose s : ℝ) * (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        (criticalWindowCompletionCount k a n s 0 : ℝ) /
          ((s + (k - 1)).choose (k - 1) : ℝ) ≤
      ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) := by
  have hmulti : (0 : ℝ) < (s + (k - 1)).choose (k - 1) := by
    exact_mod_cast Nat.choose_pos (by omega : k - 1 ≤ s + (k - 1))
  apply (div_le_iff₀ hmulti).mpr
  have hfinite :
      (n.choose s : ℝ) * (coMultipartiteGraphCountWithEdges (k - 1) (n - s)
        (criticalWindowEdgeCount k a n) : ℝ) ≤
      ((s + (k - 1)).choose (k - 1) : ℝ) *
        ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) := by
    exact_mod_cast choose_mul_coPartiteCount_le_card_exactCriticalAssembly_mul
      (by omega : 1 ≤ k) n (criticalWindowEdgeCount k a n) s
  have h := (mul_le_mul_of_nonneg_left hcompare (Nat.cast_nonneg (α := ℝ) (n.choose s))).trans hfinite
  nlinarith only [h]

/-- The remainder edge range lies in a bounded squared-logarithmic rectangle. -/
theorem criticalWindowRemainderEdges_normalized_le
    {n s t : ℕ} {L : ℝ} (hlog : 0 < Real.log (n : ℝ))
    (hs : (s : ℝ) / Real.log (n : ℝ) ≤ L)
    (ht : t ≤ completeEdgeCount s) :
    (t : ℝ) / Real.log (n : ℝ) ^ 2 ≤ L ^ 2 := by
  have hs0 : 0 ≤ (s : ℝ) / Real.log (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hlog.le
  have hsquare : ((s : ℝ) / Real.log (n : ℝ)) ^ 2 ≤ L ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have htR : (t : ℝ) ≤ (s : ℝ) ^ 2 := by
    have hcap := completeEdgeCount_cast_le_half_square s
    have ht' : (t : ℝ) ≤ completeEdgeCount s := by exact_mod_cast ht
    nlinarith [sq_nonneg (s : ℝ)]
  calc
    (t : ℝ) / Real.log (n : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 / Real.log (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right htR (sq_nonneg _)
    _ = ((s : ℝ) / Real.log (n : ℝ)) ^ 2 := by rw [div_pow]
    _ ≤ L ^ 2 := hsquare

/-- Uniform squared-logarithmic row bounds, ready to sum over remainder sizes. -/
theorem exists_criticalWindowAssembly_row_bounds_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L : ℝ) (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      (s : ℝ) / Real.log (n : ℝ) ≤ L →
      C⁻¹ * (n.choose s : ℝ) *
          (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
          (criticalWindowCompletionCount k a n s 0 : ℝ) /
            ((s + (k - 1)).choose (k - 1) : ℝ) ≤
        ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ∧
      ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
        C * (n.choose s : ℝ) *
          (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
          (criticalWindowCompletionCount k a n 0 0 : ℝ) *
          Real.exp (criticalWindowCompletionExponent k a n s 0 +
            epsilon * Real.log (n : ℝ) ^ 2) *
          criticalRemainderPartitionFunction k s := by
  obtain ⟨C, hC, hcomp⟩ := exists_criticalWindowCoPartite_comparison_uniform hk a L (L ^ 2)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcomp, eventually_criticalWindowCompletion_pos_uniform hk a L (L ^ 2),
    eventually_criticalWindowCompletion_log_error_uniform hk a L (L ^ 2) hepsilon,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hc hp he hl
  intro s hs
  have hzero : ((0 : ℕ) : ℝ) / Real.log (n : ℝ) ^ 2 ≤ L ^ 2 := by simpa using sq_nonneg L
  constructor
  · apply criticalWindowAssembly_row_lower_of_comparison hk a C n s
    simpa only [Nat.sub_zero] using (hc s 0 hs hzero).2.1
  · apply criticalWindowAssembly_row_upper_of_comparison hk a C
      (epsilon * Real.log (n : ℝ) ^ 2) hC.le n s
    · intro t ht
      exact (hc s t hs (criticalWindowRemainderEdges_normalized_le hl hs ht)).2.2
    · intro t ht
      exact hp s t hs (criticalWindowRemainderEdges_normalized_le hl hs ht)
    · exact hp 0 0 (by simpa using hL) hzero
    · intro t ht
      exact he s t hs (criticalWindowRemainderEdges_normalized_le hl hs ht)

end InducedStars
