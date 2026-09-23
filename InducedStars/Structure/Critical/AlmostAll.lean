import InducedStars.Structure.Critical.CleanCleanup
import InducedStars.Structure.Critical.MediumGlobalAggregation
import InducedStars.Structure.Critical.FixedDefectGlobalAggregation
import InducedStars.Structure.Critical.Conclusion

/-!
# Almost-all fine structure at the critical density

The sample space has exactly `criticalEdgeCount k n` edges.  All parameters
are chosen from `k` alone, before the graph order.  The final witness is a
literal disjoint union on complementary vertex sets, not a cut-distance or
edit-distance approximation.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The three-scale critical counting error for one synchronized parameter
package: a vanishing clean ratio, a linear defect penalty, and a quadratic
medium-degree penalty. -/
def criticalGlobalCountingError
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) : ℕ → ℝ :=
  criticalAggregationError (fun n ↦
    (criticalCleanLargeSparseTotal k hk n P.tau P.sparseCutoffConstant : ℝ) /
      (coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) : ℝ))
    (P.cMat / 8) P.mediumRate

theorem criticalGlobalCountingError_nonneg
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) (n : ℕ) :
    0 ≤ criticalGlobalCountingError k hk P n := by
  unfold criticalGlobalCountingError criticalAggregationError
  positivity

theorem criticalGlobalCountingError_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    Tendsto (criticalGlobalCountingError k hk P) atTop (nhds 0) := by
  exact criticalAggregationError_tendsto_zero
    (criticalCleanLargeSparseTotal_ratio_tendsto_zero k hk P)
    (div_pos P.cMat_pos (by norm_num)) P.mediumRate_pos

/-- Exact global unstructured-family bound at the floor critical edge count.
The co-partite-relative error tends to zero; the far error is exponentially
quadratic relative to the entire critical induced-star-free family. -/
theorem eventually_criticalUnstructuredGraphFinset_le
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∃ cFar : ℝ, 0 < cFar ∧
      CriticalExceptionalBound k
        (criticalLogarithmicSparseCutoff P.sparseCutoffConstant)
        (criticalGlobalCountingError k hk P) cFar := by
  apply criticalExceptionalBound_of_totals k hk P
  · filter_upwards [eventually_criticalCoMultipartiteGraphCount_pos k hk] with n hn
    exact criticalCleanTotal_le_count_mul_ratio hk P.tau P.sparseCutoffConstant hn
  · exact eventually_criticalMediumTotal_le k hk P
  · exact eventually_criticalFixedDefectTotal_le k hk P

/-- The critical unstructured proportion tends to zero, with the
conditioning denominator eventually positive. -/
theorem criticalUnstructuredProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    Tendsto (fun n ↦ criticalUnstructuredProbability k n
      (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n))
      atTop (nhds 0) := by
  obtain ⟨cFar, hcFar, hbound⟩ := eventually_criticalUnstructuredGraphFinset_le k hk P
  exact criticalUnstructuredProbability_tendsto_zero_of_bound hk
    (Eventually.of_forall (criticalGlobalCountingError_nonneg k hk P))
    (criticalGlobalCountingError_tendsto_zero k hk P) hcFar hbound

/-- The complementary structured critical proportion tends to one. -/
theorem criticalStructuredProbability_tendsto_one
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    Tendsto (fun n ↦ criticalStructuredProbability k n
      (criticalLogarithmicSparseCutoff P.sparseCutoffConstant n))
      atTop (nhds 1) :=
  criticalStructuredProbability_tendsto_one_of_bad hk
    (criticalUnstructuredProbability_tendsto_zero k hk P)

/-- Logarithmic exceptional-set bound for the exact critical density.

For the exact edge count `floor (gammaK k * choose n 2)`, almost every
induced-`K_{1,k}`-free labeled graph is the disjoint union of a co-`(k-1)`-
partite graph and an arbitrary graph on at most `ceil (L * log (n+1))`
vertices.  The constant `L` depends only on `k`.  The sharper signed-window
statement is `inducedStarCriticalWindowAlmostAll`. -/
theorem inducedStarCriticalAlmostAll
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))))
        atTop (nhds 1) := by
  let P : CriticalAggregationParameters k :=
    Classical.choice (exists_criticalAggregationParameters k hk)
  exact ⟨P.sparseCutoffConstant, P.sparseCutoffConstant_pos,
    criticalStructuredProbability_tendsto_one k hk P⟩

open Classical in
/-- Literal vertex-partition form of `inducedStarCriticalAlmostAll`:
with probability tending to one, the small vertex set has no edges to its
complement and the complement-induced graph is co-`(k-1)`-partite.
By `graph_eq_complement_induce_sup_induce_of_noCross` this is the exact
disjoint-union conclusion, including the arbitrary induced graph on the
small set. -/
theorem inducedStarCriticalAlmostAll_disjointUnion
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalUniformProbability k n
        ((criticalInducedStarFreeGraphFinset k n).filter fun G ↦
          ∃ S : Finset (Fin n),
            S.card ≤ Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ)) ∧
              (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
              DenseGraph.IsCoMultipartite
                (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1)))
        atTop (nhds 1) := by
  classical
  obtain ⟨L, hL, hlimit⟩ := inducedStarCriticalAlmostAll k hk
  refine ⟨L, hL, ?_⟩
  have heq (n : ℕ) :
      ((criticalInducedStarFreeGraphFinset k n).filter fun G ↦
        ∃ S : Finset (Fin n),
          S.card ≤ Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ)) ∧
            (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
            DenseGraph.IsCoMultipartite
              (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1)) =
      criticalStructuredGraphFinset k n
        (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))) := by
    ext G
    simp only [Finset.mem_filter, mem_criticalStructuredGraphFinset_iff_vertexSet,
      HasCriticalVertexSetStructure]
  simpa only [heq, criticalStructuredProbability] using hlimit

end InducedStars
