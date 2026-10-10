import DenseGraph.Graphon.ZeroDistance
import InducedStars.Main.VariationalConsequences
import InducedStars.Graphon.SetDistance

/-!
# Edge mass and the noncritical conditioned optimizer sets

The strict low-probability optimizer is zero. At high probability every
optimizer has the same explicitly determined edge density. These statements
are about the existing cut-saturated optimizer sets, not chosen labels.
-/

noncomputable section

open Set

namespace InducedStars

/-- The paper's two equivalent formulas for the supercritical density. -/
theorem gammaFromProbability_eq_add (k : ℕ) (hk : 3 ≤ k) (p : ℝ) :
    gammaFromProbability k p = p + (1 - p) / (k - 1 : ℕ) := by
  have hr : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  have hcast : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    norm_cast
    omega
  unfold gammaFromProbability
  field_simp
  rw [hcast]
  ring

theorem gnpOptimizer_eq_zero_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsub : p < pK k) {W : Graphon}
    (hW : W ∈ gnpGraphonOptimizers k p) : W = zeroGraphon := by
  apply (graphonEdgeDensity_eq_zero_iff W).mp
  simpa only [hsub, ↓reduceIte] using
    gnpOptimizer_edgeDensity_classification k hk p hp hW

theorem cutDistToSet_gnpGraphonOptimizers_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsub : p < pK k) (W : Graphon) :
    cutDistToSet W (gnpGraphonOptimizers k p) = graphonEdgeDensity W := by
  have hzero : zeroGraphon ∈ gnpGraphonOptimizers k p := by
    apply gnpCandidate_mem_optimizer k hk p hp
    rw [gnpCandidateFamily_of_lt_pK hsub]
    exact mem_singleton _
  rw [DenseGraph.cutDistToSet_eq_of_equivalent_representative W zeroGraphon hzero]
  · exact DenseGraph.cutDist_zeroGraphon W
  · intro V hV
    rw [gnpOptimizer_eq_zero_of_lt_pK k hk p hp hsub hV, cutDist_self]

theorem abs_edgeDensity_sub_gammaFromProbability_le_optimizerDistance
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) (W : Graphon) :
    |graphonEdgeDensity W - gammaFromProbability k p| ≤
      cutDistToSet W (gnpGraphonOptimizers k p) := by
  rw [le_cutDistToSet_iff (gnpGraphonOptimizers_nonempty k hk p hp)]
  intro V hV
  have hden : graphonEdgeDensity V = gammaFromProbability k p := by
    simpa only [hsuper.not_gt, hsuper.ne', ↓reduceIte] using
      gnpOptimizer_edgeDensity_classification k hk p hp hV
  simpa only [hden] using
    abs_graphonEdgeDensity_sub_le_cutDist_via_relabeling W V

end InducedStars
