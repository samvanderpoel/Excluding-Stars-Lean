import InducedStars.Graphon.Counting
import InducedStars.Graphon.SetDistance

/-!
# Distance from a nonnegative graphon to zero

Both the cut distance and the L¹ distance to zero equal the edge density.
This is an exact normalization statement, including for finite adjacency
graphons; it uses no graph-limit input.
-/

noncomputable section

open MeasureTheory Filter Set

namespace DenseGraph

open InducedStars

theorem graphonL1Dist_zeroGraphon (W : Graphon) :
    graphonL1Dist W zeroGraphon = graphonEdgeDensity W := by
  rw [graphonL1Dist_eq_integral, graphonEdgeDensity_eq_integral]
  apply integral_congr_ae
  filter_upwards [zeroGraphon_ae_eq, W.ae_nonneg] with z hz hW
  simp [hz, abs_of_nonneg hW]

theorem cutDist_zeroGraphon (W : Graphon) :
    cutDist W zeroGraphon = graphonEdgeDensity W := by
  apply le_antisymm
  · exact (cutDist_le_graphonL1Dist W zeroGraphon).trans_eq
      (graphonL1Dist_zeroGraphon W)
  · have hzero : graphonEdgeDensity zeroGraphon = 0 := by
      rw [graphonEdgeDensity_eq_integral]
      exact integral_eq_zero_of_ae zeroGraphon_ae_eq
    have hnonneg : 0 ≤ graphonEdgeDensity W := by
      rw [graphonEdgeDensity_eq_integral]
      exact integral_nonneg_of_ae W.ae_nonneg
    simpa [hzero, abs_of_nonneg hnonneg]
      using abs_graphonEdgeDensity_sub_le_cutDist_via_relabeling W zeroGraphon

theorem cutDist_graphGraphon_zeroGraphon {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    cutDist (graphGraphon G) zeroGraphon =
      2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 := by
  rw [cutDist_zeroGraphon, graphonEdgeDensity_graphGraphon hn]

/-- Taking distance to a cut-equivalence class agrees with taking distance
to its representative. No infimum-attainment claim is needed. -/
theorem cutDistToSet_eq_of_equivalent_representative
    (W U : Graphon) {S : Set Graphon} (hU : U ∈ S)
    (hS : ∀ V ∈ S, cutDist V U = 0) :
    cutDistToSet W S = cutDist W U := by
  apply le_antisymm (cutDistToSet_le W hU)
  rw [le_cutDistToSet_iff ⟨U, hU⟩]
  intro V hV
  simpa [hS V hV] using cutDist_triangle W V U

end DenseGraph
