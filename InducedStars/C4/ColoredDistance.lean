import InducedStars.C4.SplitColorings
import DenseGraph.Regularity.ColoredEdit

/-!
# Split-template edit distance and colored stability

Paper: Definition `dfn:Jgamma-stable`, with a complete-template entropy
benchmark and arbitrary nearly complete partial templates as inputs.
-/

noncomputable section
open InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem c4SplitColoring_inconsistency_eq_defect (G : SimpleGraph V) (D : C4Division V) :
    DenseGraph.coloredInconsistency G (c4SplitColoring D) = c4DefectCost G D := by
  unfold DenseGraph.coloredInconsistency c4DefectCost
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [DenseGraph.mem_coloredInconsistencyFinset,
      DenseGraph.coloredPairStatus_mk, c4SplitColoring_complete, SimpleGraph.mem_edgeSet,
      SimpleGraph.top_adj, c4SplitColoring_edgeColor,
      mk_mem_finiteGraphEdges, c4DefectGraph_adj, C4Division.mem_cliquePart]
    by_cases heq : x = y
    · subst y; simp
    · by_cases hx : x ∈ D.independentPart <;> by_cases hy : y ∈ D.independentPart <;>
        simp [c4SplitColoring, RegularityColoredGraph.getEdgeColor,
          SimpleGraph.EdgeLabeling.get_mk, hx, hy, heq, and_comm]

/-- The transfer to genuine uncolored split edit distance keeps realization
errors and template edits separate. -/
theorem c4DefectCost_le_inconsistency_add_coloredEdit (G : SimpleGraph V)
    (J : RegularityColoredGraph V) (D : C4Division V) :
    c4DefectCost G D ≤ DenseGraph.coloredInconsistency G J +
      DenseGraph.coloredEditDistance J (c4SplitColoring D) := by
  rw [← c4SplitColoring_inconsistency_eq_defect]
  exact DenseGraph.coloredInconsistency_le_add_edit G J (c4SplitColoring D)

/-- Paper: Definition `dfn:Jgamma-stable` for the split family.
Completeness is required of the benchmark templates; the inputs may be partial.
Vertex recoloring costs zero; every missing or differently colored pair
costs one unordered edge edit. -/
def C4ColoredStable (gamma : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ delta eta : ℝ,
    0 < delta ∧ 0 < eta ∧ ∃ n0 : ℕ, ∀ n ≥ n0,
      ∀ J : RegularityColoredGraph (Fin n),
      ¬ColoredHomExists inducedC4 J →
      ((finiteGraphEdges J.graphᶜ).card : ℝ) ≤ eta*(n : ℝ)^2 →
      ∀ h : C4ColoredEntropyFeasible J gamma,
      c4CompleteEntropyBenchmark n gamma - delta*(n : ℝ)^2 ≤ c4ColoredEntropy J gamma h →
      ∃ D : C4Division (Fin n),
        (DenseGraph.coloredEditDistance J (c4SplitColoring D) : ℝ) ≤ epsilon*(n : ℝ)^2

end InducedStars
