import InducedStars.Structure.Gnp.WeightedPartition
import InducedStars.Structure.Gnp.WeightedMatching
import InducedStars.Structure.Gnp.GroupedFinite

/-!
# Weighted cut-ball bounds from the finite grouped profile estimates

The exact edge-count sum is performed with the common ambient binomial-model
factor. Separation from zero makes the small edge levels empty before the
finite profile bounds are applied. Every outer summand is an actual
retained key, never a decoration of its complementary sparse set.
-/

noncomputable section
open Finset Set
open scoped Classical BigOperators
namespace InducedStars

/-- The actual weighted cut ball is bounded by the weighted retained-key sum.
Only feasible levels above the positive-density threshold require the finite
grouped estimate; all other levels are empty. The parameter-selection theorem
supplies these uniform finite estimates separately. -/
theorem gnpInducedStarCutBallMass_le_weightedRetainedSum
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (L : AdmissibleBlockSequence k) (R₀ : ℕ)
    (eta delta tau c : ℝ) {gamma p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hgamma : 0 ≤ gamma)
    (hseparated : gamma ≤ cutDist (WLambda hk L) zeroGraphon)
    (htau : tau ≤ gamma / 2)
    (hcount : ∀ m : ℕ, m ≤ completeEdgeCount n →
      gamma / 8 * (n : ℝ)^2 ≤ m →
      SubcriticalGroupedCandidateUpperBounds hk hn L R₀ m eta delta tau c) :
    gnpInducedStarCutBallMass k n p (WLambda hk L) tau ≤
      (1 + Real.exp (-c * n)) *
        ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          retainedKeyWeightedCleanPartitionFunction K eta delta p := by
  let keys := compatibleRetainedKeys k n L eta delta R₀
  let ms := range (completeEdgeCount n + 1)
  let w (m : ℕ) := (1 - p) ^ completeEdgeCount n * (p / (1 - p)) ^ m
  let fac := 1 + Real.exp (-c * n)
  have hw (m : ℕ) : 0 ≤ w m := by
    exact mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.le) _)
      (pow_nonneg (div_nonneg hp.1.le (sub_nonneg.mpr hp.2.le)) _)
  have hfac : 0 ≤ fac := by dsimp [fac]; positivity
  have hlevel (m : ℕ) (hm : m ∈ ms) :
      ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
        fac * ∑ K ∈ keys, (retainedKeyCleanPartitionFunction K eta m delta : ℝ) := by
    by_cases hdensity : gamma / 8 * (n : ℝ)^2 ≤ m
    · exact (hcount m (Nat.le_of_lt_succ (mem_range.mp hm)) hdensity).cutBall
    · have hsmall : (m : ℝ) < gamma / 4 * (n : ℝ)^2 := by
        have hprod := mul_nonneg hgamma (sq_nonneg (n : ℝ))
        linarith [lt_of_not_ge hdensity]
      rw [subcriticalCandidateCutBall_eq_empty_of_edgeCount_lt
        (by omega) (WLambda hk L) hgamma hseparated htau hsmall,
        Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hfac (sum_nonneg fun _ _ ↦ Nat.cast_nonneg _)
  have hmass : gnpInducedStarCutBallMass k n p (WLambda hk L) tau =
      ∑ m ∈ ms, w m *
        ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) := by
    rw [gnpInducedStarCutBallMass, gnpGraphEventProbability_eq_sum_graphFamilySliceWeights]
    apply sum_congr rfl
    intro m hm
    rw [gnpGraphFamilySliceWeight, graphFamilyEdgeSlice_gnpInducedStarCutBall]
    dsimp [w]
    rw [gnpCommonWeight_eq_of_le (Nat.le_of_lt_succ (mem_range.mp hm)) hp.2]
    ring
  rw [hmass]
  calc
    _ ≤ ∑ m ∈ ms, w m *
        (fac * ∑ K ∈ keys, (retainedKeyCleanPartitionFunction K eta m delta : ℝ)) :=
      sum_le_sum fun m hm ↦ mul_le_mul_of_nonneg_left (hlevel m hm) (hw m)
    _ = fac * ∑ K ∈ keys, ∑ m ∈ ms,
        w m * (retainedKeyCleanPartitionFunction K eta m delta : ℝ) := by
      simp only [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro K _
      apply sum_congr rfl
      intro m _
      ring
    _ ≤ fac * ∑ K ∈ keys, retainedKeyWeightedCleanPartitionFunction K eta delta p := by
      apply mul_le_mul_of_nonneg_left _ hfac
      apply sum_le_sum
      intro K _
      exact sum_retainedKeyCleanPartitionFunction_weight_le K eta delta ms ⟨hp.1.le, hp.2.le⟩

/-- Paper: `eqn:critical-weighted-upper-K1k` followed by
`eqn:critical-clean-sparse-side-K1k`. Regularity of each actual retained core
cancels its quadratic weight, leaving an explicit linear exponential loss. -/
theorem gnpCriticalCutBallMass_le_weightedSparseSum
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (L : AdmissibleBlockSequence k) (R₀ : ℕ)
    (eta delta tau c : ℝ) {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (hseparated : gamma ≤ cutDist (WLambda hk L) zeroGraphon)
    (htau : tau ≤ gamma / 2)
    (hcount : ∀ m : ℕ, m ≤ completeEdgeCount n →
      gamma / 8 * (n : ℝ)^2 ≤ m →
      SubcriticalGroupedCandidateUpperBounds hk hn L R₀ m eta delta tau c) :
    gnpInducedStarCutBallMass k n (pK k) (WLambda hk L) tau ≤
      (1 + Real.exp (-c * n)) * Real.exp (criticalRetainedWeightConstant k * n) *
        ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          retainedKeyWeightedSparseSum K eta (pK k) := by
  apply (gnpInducedStarCutBallMass_le_weightedRetainedSum hk hn L R₀ eta delta tau c
    (pK_mem_Ioo (by omega)) hgamma hseparated htau hcount).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [mul_sum]
  exact sum_le_sum fun K _ ↦ retainedKeyWeightedCleanPartitionFunction_le_sparse K hk eta delta

end InducedStars
