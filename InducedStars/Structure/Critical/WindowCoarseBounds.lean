import InducedStars.Structure.Critical.WindowCoarseCounting
import InducedStars.Structure.Critical.WindowCoarseBinomial
import InducedStars.Structure.Critical.WindowCoPartite

/-!
# Uniform division bounds in the logarithmic critical window

Empty canonical fibers are handled explicitly. Every nonempty fiber inherits
the small-sparse conclusion of close structure, so the coarse Gaussian
estimate applies uniformly before summation over divisions.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Topology Classical
namespace InducedStars

/-- The common coarse exponent before choosing sparse vertices. -/
def criticalWindowCoarseExponent (k : ℕ) (C : ℝ) (n s : ℕ) : ℝ :=
  -(4 * criticalSparsePenaltyConstant k) * (s : ℝ) ^ 2 +
    C * s * Real.log ((n + 1 : ℕ) : ℝ) +
      C * Real.log ((n + 1 : ℕ) : ℝ)

/-- The balanced guarded selected count agrees with the exact reference plus
the equitable internal-capacity decrease throughout the small-sparse range. -/
theorem criticalWindow_balanced_reference_eq
    {k n s : ℕ} {a : ℝ} (hk : 3 ≤ k)
    (hn : 4 * (k - 1) ^ 2 ≤ n)
    (hs : (s : ℝ) ≤ criticalCombinedSliceDelta k * n)
    (hfeas : criticalWindowCoreInternal k n 0 ≤ criticalWindowEdgeCount k a n) :
    (if criticalWindowCoreInternal k n s ≤ criticalWindowEdgeCount k a n then
      Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalWindowEdgeCount k a n - criticalWindowCoreInternal k n s) else 0) =
      Nat.choose (criticalMaximumCombinedCapacity k n s)
        (criticalWindowReferenceSelected k a n + criticalSelectedIncrease k n s) := by
  have hsmall : 16 * s ≤ n := by
    have hd := (criticalCombinedSliceDelta_le_taylor k).trans
      (criticalTaylorDeltaBound_le_one_sixteenth k)
    have hh := hs.trans (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n))
    exact_mod_cast (show (16 : ℝ) * s ≤ n by linarith only [hh])
  have hmono : criticalWindowCoreInternal k n s ≤ criticalWindowCoreInternal k n 0 := by
    by_cases hz : s = 0
    · simp [hz]
    · exact criticalBalancedInternalCapacity_mono_sparse hk (by omega) hsmall hn
  rw [ite_eq_left (hmono.trans hfeas)]
  congr 1
  unfold criticalWindowReferenceSelected criticalSelectedIncrease
    criticalWindowCoreInternal at *
  simp only [Nat.sub_zero] at *
  omega

/-- Clean and nonclean canonical division fibers share the same coarse
Gaussian envelope; the latter retain an additional linear exponential loss. -/
theorem eventually_criticalWindowDivisionBounds
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) (P : CriticalAggregationParameters k) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)),
      let B : ℝ := Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n)
      let E := Real.exp (criticalWindowCoarseExponent k C n D.sparse.card)
      ((supercriticalCleanDivisionGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) (criticalWindowEdgeCount k a n)
          n P.tau hn D).card : ℝ) ≤ B * E ∧
      ((supercriticalDivisionDefectGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) (criticalWindowEdgeCount k a n)
          n P.tau hn D).card : ℝ) ≤ B * E * Real.exp (-(P.cMat / 4) * n) := by
  obtain ⟨C, hC, hslice⟩ := eventually_criticalWindowCombinedSlice_le_reference k hk a
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
  refine ⟨C, hC, ?_⟩
  filter_upwards [hslice,
    eventually_criticalDivisionDefect_le_combined_reference k hk P,
    eventually_criticalWindowReference_feasible hk a,
    eventually_ge_atTop (4 * (k - 1) ^ 2),
    eventually_ge_atTop nClose] with n hsliceN hdefN hfeas hnLarge hnClose
  intro hn D
  dsimp only
  have getSmall (G : SimpleGraph (Fin n))
      (hG : G ∈ supercriticalCloseGraphFinset k hk (gammaK k) hgamma
        (criticalWindowEdgeCount k a n) n P.tau)
      (hD : canonicalSupercriticalDivision G (by simpa using hn) = D) :
      (D.sparse.card : ℝ) ≤ criticalCombinedSliceDelta k * n := by
    have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n
        (criticalWindowEdgeCount k a n) \
      supercriticalFarGraphFinset k hk (gammaK k) hgamma
        (criticalWindowEdgeCount k a n) n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hG
    obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k) hgamma
      P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
        P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
          (criticalWindowEdgeCount k a n) hnClose G (by simpa [P.tau_eq] using hfamily)
    have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
      simpa only [hD] using R.sparse_card_le
    have hd := mul_le_mul_of_nonneg_right P.critical_slice_delta.le (Nat.cast_nonneg (α := ℝ) n)
    have hpos := mul_nonneg P.delta_pos.le (Nat.cast_nonneg (α := ℝ) n)
    linarith
  by_cases hs : (D.sparse.card : ℝ) ≤ criticalCombinedSliceDelta k * n
  · have hbalanced := criticalCombined_reference_le_balanced (m := criticalWindowEdgeCount k a n) D
    rw [criticalWindow_balanced_reference_eq hk hnLarge hs hfeas] at hbalanced
    have hbalancedR :
        (if divisionInternalCliqueCapacity D ≤ criticalWindowEdgeCount k a n then
          (Nat.choose (criticalCombinedVariableCapacity D)
            (criticalWindowEdgeCount k a n - divisionInternalCliqueCapacity D) : ℝ) else 0) ≤
        (Nat.choose (criticalTargetCapacity k n) (criticalWindowReferenceSelected k a n) : ℝ) *
          Real.exp (criticalWindowCoarseExponent k C n D.sparse.card) := by
      exact (show _ ≤ (Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (criticalWindowReferenceSelected k a n + criticalSelectedIncrease k n D.sparse.card) : ℝ)
        by exact_mod_cast hbalanced).trans (hsliceN D.sparse.card hs)
    constructor
    · exact (show _ ≤
        (if divisionInternalCliqueCapacity D ≤ criticalWindowEdgeCount k a n then
          (Nat.choose (criticalCombinedVariableCapacity D)
            (criticalWindowEdgeCount k a n - divisionInternalCliqueCapacity D) : ℝ) else 0)
        by exact_mod_cast (card_supercriticalCleanDivisionGraphFinset_le_guarded_combined
          (hk := hk) (hgamma := hgamma) (tau := P.tau) (hn := hn)
            (m := criticalWindowEdgeCount k a n) D)).trans hbalancedR
    · exact (hdefN (criticalWindowEdgeCount k a n) hn D).trans
        (mul_le_mul_of_nonneg_right hbalancedR (Real.exp_pos _).le)
  · have hclean : supercriticalCleanDivisionGraphFinset k hk (gammaK k) hgamma
        (criticalWindowEdgeCount k a n) n P.tau hn D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have h := mem_supercriticalCleanDivisionGraphFinset.mp hG
      exact hs (getSmall G h.1 h.2.1)
    have hdef : supercriticalDivisionDefectGraphFinset k hk (gammaK k) hgamma
        (criticalWindowEdgeCount k a n) n P.tau hn D = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      have h := mem_supercriticalDivisionDefectGraphFinset.mp hG
      exact hs (getSmall G h.1 h.2.1)
    rw [hclean, hdef]
    simp only [Finset.card_empty, Nat.cast_zero]
    constructor <;> positivity

end InducedStars
