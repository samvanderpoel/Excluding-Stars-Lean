import InducedStars.Structure.Critical.CompletionCounting
import InducedStars.Structure.Critical.ChernoffSlice

/-!
# Uniform division bounds at the exact critical density

Empty canonical fibers are handled explicitly. Every nonempty fiber inherits
the small-sparse conclusion of close structure, so the coarse Gaussian
estimate applies uniformly before summation over divisions.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Topology Classical
namespace InducedStars

/-- The common coarse exponent before choosing sparse vertices. -/
def criticalRemainderExponent (k : ℕ) (C : ℝ) (n s : ℕ) : ℝ :=
  -(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
    C * s * Real.log ((n + 1 : ℕ) : ℝ) +
      C * Real.log ((n + 1 : ℕ) : ℝ)

/-- The balanced guarded selected count agrees with the exact reference plus
the equitable internal-capacity decrease throughout the small-sparse range. -/
theorem critical_balanced_reference_eq
    {k n s : ℕ} (hk : 3 ≤ k)
    (hn : 4 * (k - 1) ^ 2 ≤ n)
    (hs : (s : ℝ) ≤ criticalCombinedSliceDelta k * n)
    (hfeas : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤ criticalEdgeCount k n) :
    (if DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤ criticalEdgeCount k n then
      Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalEdgeCount k n - DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s)) else 0) =
      Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalTargetSelectedCount k n + criticalSelectedIncrease k n s) := by
  have hsmall : 16 * s ≤ n := by
    have hd := criticalCombinedSliceDelta_le_one_sixteenth k
    have hh := hs.trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n))
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith only [hh])
  have hmono : DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤ DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n := by
    by_cases hz : s = 0
    · simp [hz]
    · exact criticalBalancedInternalCapacity_mono_sparse hk (by omega) hsmall hn
  rw [ite_eq_left (hmono.trans hfeas)]
  congr 1
  unfold criticalTargetSelectedCount criticalSelectedIncrease at *
  omega

/-- Clean and nonclean canonical division fibers share the same coarse
Gaussian envelope; the latter retain an additional linear exponential loss. -/
theorem eventually_criticalDivisionBounds
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (hdelta : P.delta < criticalCombinedSliceDelta k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)),
      let B : ℝ := criticalReferenceFiberCard k n
      let E := Real.exp (criticalRemainderExponent k C n D.sparse.card)
      ((supercriticalCleanDivisionGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n)
          n P.tau hn D).card : ℝ) ≤ B * E ∧
      ((supercriticalDivisionDefectGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n)
          n P.tau hn D).card : ℝ) ≤ B * E * Real.exp (-(P.cMat / 4) * n) := by
  obtain ⟨C, hC, hslice⟩ := eventually_criticalCombinedSlice_le_reference k hk
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hslice,
    eventually_criticalDivisionDefect_le_combined_reference k hk P,
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_ge_atTop (4 * (k - 1) ^ 2),
    eventually_ge_atTop nClose] with n hsliceN hdefN hfeas hnLarge hnClose
  intro hn D
  dsimp only
  have getSmall (G : SimpleGraph (Fin n))
      (hG : G ∈ supercriticalCloseGraphFinset k hk (gammaK k) hgamma
        (criticalEdgeCount k n) n P.tau)
      (hD : canonicalSupercriticalDivision G (by simpa using hn) = D) :
      (D.sparse.card : ℝ) ≤ criticalCombinedSliceDelta k * n := by
    have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n
        (criticalEdgeCount k n) \
      supercriticalFarGraphFinset k hk (gammaK k) hgamma
        (criticalEdgeCount k n) n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hG
    obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k) hgamma
      P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
        P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
          (criticalEdgeCount k n) hnClose G (by simpa [P.tau_eq] using hfamily)
    have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
      simpa only [hD] using R.sparse_card_le
    have hd := mul_le_mul_of_nonneg_right hdelta.le (Nat.cast_nonneg (α := ℝ) n)
    have hpos := mul_nonneg P.delta_pos.le (Nat.cast_nonneg (α := ℝ) n)
    linarith
  by_cases hs : (D.sparse.card : ℝ) ≤ criticalCombinedSliceDelta k * n
  · have hbalanced := criticalCombined_reference_le_balanced (m := criticalEdgeCount k n) D
    rw [critical_balanced_reference_eq hk hnLarge hs hfeas] at hbalanced
    have hbalancedR :
        (if divisionInternalCliqueCapacity D ≤ criticalEdgeCount k n then
          (Nat.choose (criticalCombinedVariableCapacity D)
            (criticalEdgeCount k n - divisionInternalCliqueCapacity D) : ℝ) else 0) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalRemainderExponent k C n D.sparse.card) := by
      exact (show _ ≤ (Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalTargetSelectedCount k n + criticalSelectedIncrease k n D.sparse.card) : ℝ)
        by exact_mod_cast hbalanced).trans (hsliceN D.sparse.card hs)
    constructor
    · exact (show _ ≤
        (if divisionInternalCliqueCapacity D ≤ criticalEdgeCount k n then
          (Nat.choose (criticalCombinedVariableCapacity D)
            (criticalEdgeCount k n - divisionInternalCliqueCapacity D) : ℝ) else 0)
        by exact_mod_cast (card_supercriticalCleanDivisionGraphFinset_le_guarded_combined
          (hk := hk) (hgamma := hgamma) (tau := P.tau) (hn := hn)
            (m := criticalEdgeCount k n) D)).trans hbalancedR
    · exact (hdefN (criticalEdgeCount k n) hn D).trans
        (mul_le_mul_of_nonneg_right hbalancedR (Real.exp_pos _).le)
  · have hclean : supercriticalCleanDivisionGraphFinset k hk (gammaK k) hgamma
        (criticalEdgeCount k n) n P.tau hn D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have h := mem_supercriticalCleanDivisionGraphFinset.mp hG
      exact hs (getSmall G h.1 h.2.1)
    have hdef : supercriticalDivisionDefectGraphFinset k hk (gammaK k) hgamma
        (criticalEdgeCount k n) n P.tau hn D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have h := mem_supercriticalDivisionDefectGraphFinset.mp hG
      exact hs (getSmall G h.1 h.2.1)
    rw [hclean, hdef]
    simp only [Finset.card_empty, Nat.cast_zero]
    constructor <;> positivity

end InducedStars
