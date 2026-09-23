import InducedStars.Structure.Gnp.OptimizerGeometry
import InducedStars.FiniteModels.GnpConditioned
import DenseGraph.FiniteModels.EdgeDensityNormalization
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Probability consequences of conditioned rough structure

The finite laws here are the actual weighted induced-star-free conditional
laws. The low-probability assertion is sparse edge mass, not literal
emptiness. The high-probability assertion uses unordered-edge normalization.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

attribute [local instance] Classical.propDecidable

theorem gnpConditionedOptimizerFarProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ gnpConditionedOptimizerFarProbability k n p ε)
      atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ := inducedStarGnpConditionedRoughStructure k hk p hp ε hε
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ gnpConditionedOptimizerFarProbability_nonneg hk hp)
    hbound (tendsto_exp_neg_mul_natCast_sq_zero hc)

/-- Any events eventually contained in a fixed optimizer-far event have
vanishing conditional probability. Only containment inside the conditioning
family is required. -/
theorem gnpConditionedEvent_tendsto_zero_of_optimizerFar
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (Q : ∀ n, Finset (SimpleGraph (Fin n))) (ε : ℝ) (hε : 0 < ε)
    (hQ : ∀ᶠ n in atTop,
      inducedFreeGraphFinset (inducedStar k) n ∩ Q n ⊆
        gnpOptimizerFarInducedStarFinset k p ε n) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p (Q n))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦
      gnpConditionedInducedStarProbability_nonneg k n ⟨hp.1.le, hp.2.le⟩ (Q n))
    _ (gnpConditionedOptimizerFarProbability_tendsto_zero k hk p hp ε hε)
  filter_upwards [hQ] with n hn
  exact div_le_div_of_nonneg_right
    (gnpGraphEventProbability_mono ⟨hp.1.le, hp.2.le⟩ hn)
    (gnpInducedStarFreeProbability_pos (by omega) hp).le

/-- A sparse graph has at most `ξ n²` unordered edges. -/
noncomputable def gnpSparseGraphFinset (n : ℕ) (ξ : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G ↦ ((finiteGraphEdges G).card : ℝ) ≤ ξ * (n : ℝ)^2

/-- Exact-edge density deviations, normalized by `choose(n,2)`, not `n²`. -/
noncomputable def gnpEdgeDensityDeviationFinset (n : ℕ) (γ ε : ℝ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun G ↦
    ε ≤ |((finiteGraphEdges G).card : ℝ) / completeEdgeCount n - γ|

theorem gnpConditionedNonSparseProbability_tendsto_zero_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsub : p < pK k) (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (Finset.univ \ gnpSparseGraphFinset n ξ)) atTop (𝓝 0) := by
  apply gnpConditionedEvent_tendsto_zero_of_optimizerFar k hk p hp _ ξ hξ
  filter_upwards [eventually_ge_atTop 1] with n hn
  intro G hG
  obtain ⟨hfree, hbad⟩ := Finset.mem_inter.mp hG
  have hlarge : ξ * (n : ℝ)^2 < (finiteGraphEdges G).card := by
    simpa [gnpSparseGraphFinset] using (Finset.mem_sdiff.mp hbad).2
  rw [mem_gnpOptimizerFarInducedStarFinset]
  refine ⟨mem_inducedFreeGraphFinset.mp hfree, ?_⟩
  rw [cutDistToSet_gnpGraphonOptimizers_of_lt_pK k hk p hp hsub,
    graphonEdgeDensity_graphGraphon (by omega)]
  have hnsq : (0 : ℝ) < (n : ℝ)^2 := by positivity
  apply (le_div_iff₀ hnsq).mpr
  have he : (0 : ℝ) ≤ (finiteGraphEdges G).card := Nat.cast_nonneg _
  linarith

/-- The strict low-probability branch of Paper Theorem
`thm:gnp-typ-struc`: conditioned graphs have `o(n²)` edges. -/
theorem inducedStarGnpSparse_of_lt_pK
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsub : p < pK k) (ξ : ℝ) (hξ : 0 < ξ) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpSparseGraphFinset n ξ)) atTop (𝓝 1) := by
  have hbad := gnpConditionedNonSparseProbability_tendsto_zero_of_lt_pK
    k hk p hp hsub ξ hξ
  have hsum (n : ℕ) :
      gnpConditionedInducedStarProbability k n p (gnpSparseGraphFinset n ξ) +
        gnpConditionedInducedStarProbability k n p
          (Finset.univ \ gnpSparseGraphFinset n ξ) = 1 := by
    have heq : (Finset.univ \ gnpSparseGraphFinset n ξ) =
        Finset.univ.filter (fun G : SimpleGraph (Fin n) ↦
          ¬((finiteGraphEdges G).card : ℝ) ≤ ξ * (n : ℝ)^2) := by
      ext G
      simp [gnpSparseGraphFinset]
    rw [heq]
    exact gnpConditionedGraphProbability_filter_add_filter_not
      (gnpConditionedInducedStarProbability_denominator_pos (by omega) hp) _
  have hlim :=
    (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from tendsto_const_nhds).sub hbad
  simp only [sub_zero] at hlim
  apply hlim.congr
  intro n
  linarith [hsum n]

/-- Above the transition the unordered-edge density converges in
conditional probability to the scalar optimizer density. -/
theorem gnpConditionedEdgeDensity_tendsto_gammaFromProbability
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ gnpConditionedInducedStarProbability k n p
      (gnpEdgeDensityDeviationFinset n (gammaFromProbability k p) ε))
      atTop (𝓝 0) := by
  apply gnpConditionedEvent_tendsto_zero_of_optimizerFar k hk p hp _ (ε / 2)
    (half_pos hε)
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) < ε / 2 :=
    (tendsto_order.mp tendsto_one_div_atTop_nhds_zero_nat).2 _ (half_pos hε)
  filter_upwards [eventually_ge_atTop 2, hsmall] with n hn hsmalln
  intro G hG
  obtain ⟨hfree, hbad⟩ := Finset.mem_inter.mp hG
  have hdev : ε ≤ |((finiteGraphEdges G).card : ℝ) / completeEdgeCount n -
      gammaFromProbability k p| := (Finset.mem_filter.mp hbad).2
  refine mem_gnpOptimizerFarInducedStarFinset.mpr
    ⟨mem_inducedFreeGraphFinset.mp hfree, ?_⟩
  have hnorm := DenseGraph.abs_edgeDensity_sub_graphGraphonDensity_le hn G
  have htri := abs_sub_le (((finiteGraphEdges G).card : ℝ) / completeEdgeCount n)
    (graphonEdgeDensity (graphGraphon G)) (gammaFromProbability k p)
  have hopt := abs_edgeDensity_sub_gammaFromProbability_le_optimizerDistance
    k hk p hp hsuper (graphGraphon G)
  linarith

end InducedStars
