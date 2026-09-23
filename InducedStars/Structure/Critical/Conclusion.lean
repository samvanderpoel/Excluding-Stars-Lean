import InducedStars.Structure.Critical.AggregationFamilies
import InducedStars.Structure.Critical.DefectAggregation
import InducedStars.Structure.Critical.AlmostAllLimits

/-!
# Assembly of the critical exceptional-family estimate

The deterministic four-way decomposition is combined here with its three
co-partite-relative estimates and the graphon-far estimate.  No probability
ratio is formed before eventual nonemptiness of the exact critical family.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The four exact critical contributions give the global unstructured-family
bound.  The three finite counting estimates are explicit inputs to this
composition lemma and are discharged in the paper-facing theorem. -/
theorem criticalExceptionalBound_of_totals
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {L : ℝ} {cleanError : ℕ → ℝ} {cDefect : ℝ}
    (hclean : ∀ᶠ n : ℕ in atTop,
      (criticalCleanLargeSparseTotal k hk n P.tau L : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          cleanError n)
    (hmedium : ∀ᶠ n : ℕ in atTop,
      (criticalMediumTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)))
    (hfixed : ∀ᶠ n : ℕ in atTop,
      (criticalFixedDefectTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          Real.exp (-(cDefect * (n : ℝ)))) :
    ∃ cFar : ℝ, 0 < cFar ∧
      CriticalExceptionalBound k (criticalLogarithmicSparseCutoff L)
        (criticalAggregationError cleanError cDefect P.mediumRate) cFar := by
  obtain ⟨cFar, hcFar, hfar⟩ := eventually_criticalFarTotal_le k hk P.tau P.tau_pos
  refine ⟨cFar, hcFar, ?_⟩
  filter_upwards [hclean, hmedium, hfixed, hfar, eventually_ge_atTop (k - 1)]
    with n hcleanN hmediumN hfixedN hfarN hn
  have hmasterNat := card_criticalUnstructuredGraphFinset_le_aggregationTotals
    k hk P.alpha n P.tau L hn
  have hmaster :
      ((criticalUnstructuredGraphFinset k n
        (criticalLogarithmicSparseCutoff L n)).card : ℝ) ≤
      ((criticalFarGraphFinset k hk n P.tau).card : ℝ) +
        (criticalCleanLargeSparseTotal k hk n P.tau L : ℝ) +
        (criticalMediumTotal k hk P n : ℝ) +
        (criticalFixedDefectTotal k hk P n : ℝ) := by
    exact_mod_cast hmasterNat
  unfold criticalAggregationError
  nlinarith only [hmaster, hcleanN, hmediumN, hfixedN, hfarN]

/-- A vanishing clean-to-co-partite ratio supplies a nonnegative vanishing
error sequence in the cardinal form needed by the global union bound. -/
theorem criticalCleanTotal_le_count_mul_ratio
    {k n : ℕ} (hk : 3 ≤ k) (tau L : ℝ)
    (hcount : 0 < coMultipartiteGraphCountWithEdges (k - 1) n
      (criticalEdgeCount k n)) :
    (criticalCleanLargeSparseTotal k hk n tau L : ℝ) ≤
      (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
        ((criticalCleanLargeSparseTotal k hk n tau L : ℝ) /
          (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ)) := by
  have hnonzero : (coMultipartiteGraphCountWithEdges (k - 1) n
      (criticalEdgeCount k n) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcount)
  rw [mul_div_cancel₀ _ hnonzero]

/-- Eventual positivity of the exact critical co-partite denominator, proved
from the nonempty reference fiber. -/
theorem eventually_criticalCoMultipartiteGraphCount_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) := by
  filter_upwards [eventually_criticalReferenceFiber_nonempty k hk] with n hreference
  obtain ⟨G, hG⟩ := hreference
  exact Finset.card_pos.mpr ⟨G, criticalReferenceFiber_subset_coMultipartite k hk n hG⟩

/-- The three global counting bounds imply the structured probability limit.
This is an assembly theorem, not an assumption about the critical graph family. -/
theorem criticalStructuredProbability_tendsto_one_of_total_estimates
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {L cDefect : ℝ}
    (hclean : Tendsto (fun n : ℕ ↦
      (criticalCleanLargeSparseTotal k hk n P.tau L : ℝ) /
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ))
      atTop (nhds 0))
    (hmedium : ∀ᶠ n : ℕ in atTop,
      (criticalMediumTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)))
    (hfixed : ∀ᶠ n : ℕ in atTop,
      (criticalFixedDefectTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          Real.exp (-(cDefect * (n : ℝ))))
    (hcDefect : 0 < cDefect) :
    Tendsto (fun n ↦ criticalStructuredProbability k n (criticalLogarithmicSparseCutoff L n))
      atTop (nhds 1) := by
  let cleanError : ℕ → ℝ := fun n ↦
    (criticalCleanLargeSparseTotal k hk n P.tau L : ℝ) /
      (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ)
  have hcleanNonnegative : ∀ᶠ n : ℕ in atTop, 0 ≤ cleanError n :=
    Eventually.of_forall fun _ ↦ by dsimp [cleanError]; positivity
  have hcleanCard : ∀ᶠ n : ℕ in atTop,
      (criticalCleanLargeSparseTotal k hk n P.tau L : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ) *
          cleanError n := by
    filter_upwards [eventually_criticalCoMultipartiteGraphCount_pos k hk] with n hn
    exact criticalCleanTotal_le_count_mul_ratio hk P.tau L hn
  obtain ⟨cFar, hcFar, hbound⟩ := criticalExceptionalBound_of_totals k hk P
    hcleanCard hmedium hfixed
  exact criticalStructuredProbability_tendsto_one_of_bound hk
    (criticalAggregationError_eventually_nonneg hcleanNonnegative)
    (criticalAggregationError_tendsto_zero hclean hcDefect P.mediumRate_pos)
    hcFar hbound

end InducedStars
