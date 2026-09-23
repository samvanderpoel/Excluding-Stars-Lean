import InducedStars.Structure.Critical.Reference
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Limit algebra for the critical aggregation

This file isolates the final analytic step of the critical argument.  The
combinatorial layer supplies a vanishing error relative to the exact-edge
co-multipartite family and a quadratic error relative to the entire
induced-star-free family.  The results below turn that estimate into the
unstructured- and structured-probability limits without dividing before the
conditioning family is known to be nonempty.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Abstract output of the critical finite aggregation.  The first error is
measured relative to the exact-edge co-multipartite family and may have any
nonnegative rate tending to zero; the graphon-far contribution retains its
quadratic exponential decay relative to the whole conditioning family. -/
def CriticalExceptionalBound
    (k : ℕ) (exceptionalBound : ℕ → ℕ)
    (error : ℕ → ℝ) (cFar : ℝ) : Prop :=
  ∀ᶠ n in atTop,
    ((criticalUnstructuredGraphFinset
        k n (exceptionalBound n)).card : ℝ) ≤
      (coMultipartiteGraphCountWithEdges
          (k - 1) n (criticalEdgeCount k n) : ℝ) * error n +
        (criticalInducedStarFreeGraphCount k n : ℝ) *
          Real.exp (-cFar * (n : ℝ) ^ 2)

/-- Every exact-critical-edge co-multipartite graph belongs to the critical
induced-star-free sample space. -/
theorem coMultipartiteGraphCountWithCriticalEdges_le
    {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    coMultipartiteGraphCountWithEdges
        (k - 1) n (criticalEdgeCount k n) ≤
      criticalInducedStarFreeGraphCount k n := by
  unfold criticalInducedStarFreeGraphCount criticalInducedStarFreeGraphFinset
  exact Finset.card_le_card
    (coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree
      (k := k) (n := n) (m := criticalEdgeCount k n) hk)

/-- The exact critical conditioning family is eventually nonempty. -/
theorem eventually_criticalInducedStarFreeGraphFinset_nonempty
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ n in atTop,
      (criticalInducedStarFreeGraphFinset k n).Nonempty := by
  filter_upwards [eventually_criticalReferenceFiber_nonempty k hk] with n href
  obtain ⟨G, hG⟩ := href
  refine ⟨G, ?_⟩
  unfold criticalInducedStarFreeGraphFinset
  exact coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree
    (k := k) (n := n) (m := criticalEdgeCount k n) (by omega)
      (criticalReferenceFiber_subset_coMultipartite k hk n hG)

/-- A critical exceptional-family bound with a vanishing nonnegative first
error forces the unstructured proportion to vanish. -/
theorem criticalUnstructuredProbability_tendsto_zero_of_bound
    {k : ℕ} (hk : 3 ≤ k) {exceptionalBound : ℕ → ℕ}
    {error : ℕ → ℝ} {cFar : ℝ}
    (herrorNonneg : ∀ᶠ n in atTop, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hcFar : 0 < cFar)
    (hbound : CriticalExceptionalBound
      k exceptionalBound error cFar) :
    Tendsto
      (fun n ↦ criticalUnstructuredProbability
        k n (exceptionalBound n))
      atTop (nhds 0) := by
  have hnonempty :=
    eventually_criticalInducedStarFreeGraphFinset_nonempty hk
  have hupper : ∀ᶠ n in atTop,
      criticalUnstructuredProbability k n (exceptionalBound n) ≤
        error n + Real.exp (-cFar * (n : ℝ) ^ 2) := by
    filter_upwards [hbound, hnonempty, herrorNonneg] with n hn hne herr
    let total : ℝ := criticalInducedStarFreeGraphCount k n
    let good : ℝ := coMultipartiteGraphCountWithEdges
      (k - 1) n (criticalEdgeCount k n)
    have htotal : 0 < total := by
      dsimp [total, criticalInducedStarFreeGraphCount]
      exact_mod_cast Finset.card_pos.mpr hne
    have hgood : good ≤ total := by
      dsimp [good, total]
      exact_mod_cast coMultipartiteGraphCountWithCriticalEdges_le
        (k := k) (by omega) n
    have hscaled :
        good * error n + total * Real.exp (-cFar * (n : ℝ) ^ 2) ≤
          total * (error n + Real.exp (-cFar * (n : ℝ) ^ 2)) := by
      have hmul : good * error n ≤ total * error n :=
        mul_le_mul_of_nonneg_right hgood herr
      calc
        good * error n + total * Real.exp (-cFar * (n : ℝ) ^ 2) ≤
            total * error n + total * Real.exp (-cFar * (n : ℝ) ^ 2) :=
          add_le_add hmul le_rfl
        _ = total * (error n + Real.exp (-cFar * (n : ℝ) ^ 2)) := by
          ring
    rw [criticalUnstructuredProbability_eq_card_ratio]
    change ((criticalUnstructuredGraphFinset
      k n (exceptionalBound n)).card : ℝ) / total ≤ _
    apply (div_le_iff₀ htotal).2
    simpa [good, total, mul_comm] using hn.trans hscaled
  apply squeeze_zero'
  · exact Eventually.of_forall fun n ↦ by
      rw [criticalUnstructuredProbability_eq_card_ratio]
      positivity
  · exact hupper
  · simpa using herror.add
      (tendsto_exp_neg_mul_natCast_sq_zero hcFar)

/-- Vanishing of the unstructured side forces the complementary structured
probability to tend to one. -/
theorem criticalStructuredProbability_tendsto_one_of_bad
    {k : ℕ} (hk : 3 ≤ k) {exceptionalBound : ℕ → ℕ}
    (hbad : Tendsto
      (fun n ↦ criticalUnstructuredProbability
        k n (exceptionalBound n))
      atTop (nhds 0)) :
    Tendsto
      (fun n ↦ criticalStructuredProbability
        k n (exceptionalBound n))
      atTop (nhds 1) := by
  have hnonempty :=
    eventually_criticalInducedStarFreeGraphFinset_nonempty hk
  have heq : ∀ᶠ n in atTop,
      criticalStructuredProbability k n (exceptionalBound n) =
        1 - criticalUnstructuredProbability k n (exceptionalBound n) := by
    filter_upwards [hnonempty] with n hne
    linarith [criticalStructuredProbability_add_unstructuredProbability
      (k := k) (n := n) (exceptionalBound := exceptionalBound n) hne]
  have hlimit : Tendsto
      (fun n ↦ 1 - criticalUnstructuredProbability
        k n (exceptionalBound n))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hbad :
      Tendsto
        (fun n ↦ (1 : ℝ) -
          criticalUnstructuredProbability k n (exceptionalBound n))
        atTop (nhds (1 - 0)))
  exact hlimit.congr' (heq.mono fun _ hn ↦ hn.symm)

/-- Direct structured-probability form of the abstract critical aggregation
principle. -/
theorem criticalStructuredProbability_tendsto_one_of_bound
    {k : ℕ} (hk : 3 ≤ k) {exceptionalBound : ℕ → ℕ}
    {error : ℕ → ℝ} {cFar : ℝ}
    (herrorNonneg : ∀ᶠ n in atTop, 0 ≤ error n)
    (herror : Tendsto error atTop (nhds 0))
    (hcFar : 0 < cFar)
    (hbound : CriticalExceptionalBound
      k exceptionalBound error cFar) :
    Tendsto
      (fun n ↦ criticalStructuredProbability
        k n (exceptionalBound n))
      atTop (nhds 1) :=
  criticalStructuredProbability_tendsto_one_of_bad hk
    (criticalUnstructuredProbability_tendsto_zero_of_bound
      hk herrorNonneg herror hcFar hbound)

/-! ## A standard three-scale vanishing error -/

/-- The error shape produced by the clean, fixed-defect, and medium-degree
critical aggregations. -/
def criticalAggregationError
    (cleanError : ℕ → ℝ) (cDefect cMedium : ℝ) (n : ℕ) : ℝ :=
  cleanError n + Real.exp (-(cDefect * (n : ℝ))) +
    Real.exp (-(cMedium * (n : ℝ) ^ 2))

theorem criticalAggregationError_eventually_nonneg
    {cleanError : ℕ → ℝ} {cDefect cMedium : ℝ}
    (hclean : ∀ᶠ n in atTop, 0 ≤ cleanError n) :
    ∀ᶠ n in atTop,
      0 ≤ criticalAggregationError cleanError cDefect cMedium n := by
  filter_upwards [hclean] with n hn
  unfold criticalAggregationError
  positivity

theorem criticalAggregationError_tendsto_zero
    {cleanError : ℕ → ℝ} {cDefect cMedium : ℝ}
    (hclean : Tendsto cleanError atTop (nhds 0))
    (hcDefect : 0 < cDefect) (hcMedium : 0 < cMedium) :
    Tendsto
      (criticalAggregationError cleanError cDefect cMedium)
      atTop (nhds 0) := by
  change Tendsto
    (fun n ↦ criticalAggregationError cleanError cDefect cMedium n)
    atTop (nhds 0)
  simpa [criticalAggregationError] using
    (hclean.add (tendsto_exp_neg_mul_natCast_zero hcDefect)).add
      (tendsto_exp_neg_mul_natCast_sq_zero hcMedium)

end InducedStars
