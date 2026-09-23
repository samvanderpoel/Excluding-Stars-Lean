import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.FiniteModels.GraphonLimits

/-!
# Exact-edge and adjacency-graphon density normalizations

The unordered-edge density and the ordered-square density differ by at most
`1/n`. All denominators below are explicitly positive.
-/

noncomputable section

namespace DenseGraph
open InducedStars

noncomputable local instance densityNormalizationEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  graphFamiliesEdgeSetFintype G

theorem abs_edgeDensity_sub_orderedDensity_le {n m : ℕ}
    (hn : 2 ≤ n) (hm : m ≤ completeEdgeCount n) :
    |(m : ℝ) / completeEdgeCount n - 2 * (m : ℝ) / (n : ℝ)^2| ≤
      1 / (n : ℝ) := by
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnsub : (n : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hn1.ne'
  have hN : (completeEdgeCount n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [completeEdgeCount, Nat.cast_choose_two]
  have hNpos : (0 : ℝ) < completeEdgeCount n := by
    rw [hN]
    positivity
  have hid : (m : ℝ) / completeEdgeCount n - 2 * (m : ℝ) / (n : ℝ)^2 =
      ((m : ℝ) / completeEdgeCount n) / (n : ℝ) := by
    rw [hN]
    field_simp [hn0, hnsub]
    <;> ring
  rw [hid, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (div_le_one hNpos).mpr (by exact_mod_cast hm)

theorem abs_edgeDensity_sub_graphGraphonDensity_le {n : ℕ}
    (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    |((finiteGraphEdges G).card : ℝ) / completeEdgeCount n -
      graphonEdgeDensity (graphGraphon G)| ≤ 1 / (n : ℝ) := by
  classical
  rw [graphonEdgeDensity_graphGraphon (by omega)]
  apply abs_edgeDensity_sub_orderedDensity_le hn
  have hedge : finiteGraphEdges G = G.edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [hedge]
  exact card_edgeFinset_le_completeEdgeCount G

end DenseGraph
