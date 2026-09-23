import InducedStars.Graphon.LevelSets
import InducedStars.Graphon.GraphonMantel
import InducedStars.Graphon.CandidateOptimization
import Mathlib.Tactic

/-!
# Universal graphon entropy reduction

This module reduces the graphon variational problem to the scalar optimization
theorem.  The final paper-facing wrapper below is completed once the graphon
Mantel module supplies its random-mass estimate.
-/

noncomputable section

open MeasureTheory Set

namespace InducedStars

/-- The random/one masses and the random-region mean form the exact scalar
feasible point once the graphon Mantel inequality is available. -/
theorem graphon_scalarFeasible_of_randomMass_bound
    (k : ℕ) (W : Graphon) (γ : ℝ)
    (hEdge : graphonEdgeDensity W = γ)
    (hRandom : 0 < graphonRandomMass W)
    (hMantel : graphonRandomMass W ≤
      ((k - 2 : ℕ) : ℝ) * graphonOneMass W) :
    ScalarFeasible k γ (graphonOneMass W) (graphonRandomMass W) := by
  have hp := graphonRandomMean_mem_Ioo W hRandom
  have hdecomp := graphonEdgeDensity_eq_oneMass_add_randomMass_mul_randomMean W
  rw [hEdge] at hdecomp
  refine
    { x_nonneg := graphonOneMass_nonneg W
      x_le_one := graphonOneMass_le_one W
      y_pos := hRandom
      y_le_one_sub_x := graphonRandomMass_le_one_sub_oneMass W
      y_le_delta_mul_x := ?_
      x_le_gamma := ?_
      gamma_le_x_add_y := ?_ }
  · simpa only [deltaK] using hMantel
  · have hmul : 0 ≤ graphonRandomMass W * graphonRandomMean W :=
      mul_nonneg hRandom.le hp.1.le
    linarith
  · have hmul : graphonRandomMass W * graphonRandomMean W ≤
        graphonRandomMass W :=
      mul_le_of_le_one_right hRandom.le hp.2.le
    linarith

/-- The scalar ratio attached to a positive random region is its average
graphon value. -/
theorem scalarRatio_graphonMasses
    (W : Graphon) (γ : ℝ)
    (hEdge : graphonEdgeDensity W = γ)
    (hRandom : 0 < graphonRandomMass W) :
    scalarRatio γ (graphonOneMass W) (graphonRandomMass W) =
      graphonRandomMean W := by
  have hdecomp := graphonEdgeDensity_eq_oneMass_add_randomMass_mul_randomMean W
  rw [hEdge] at hdecomp
  rw [scalarRatio]
  field_simp [hRandom.ne']
  nlinarith

/-- The scalar objective at the graphon masses is precisely the Jensen upper
bound. -/
theorem scalarObjective_graphonMasses
    (W : Graphon) (γ : ℝ)
    (hEdge : graphonEdgeDensity W = γ)
    (hRandom : 0 < graphonRandomMass W) :
    scalarObjective γ (graphonOneMass W) (graphonRandomMass W) =
      graphonRandomMass W * binaryEntropy (graphonRandomMean W) := by
  rw [scalarObjective, scalarRatio_graphonMasses W γ hEdge hRandom]

/-- Positivity in the scalar feasible range, including the weak form needed
for the zero-random-mass graphon branch. -/
theorem entropyDensity_nonneg
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    0 ≤ entropyDensity k γ := by
  rw [← scalarOptimizer_objective_eq hk hγ]
  exact mul_nonneg (scalarOptimizer_feasible hk hγ).y_pos.le
    (binaryEntropy_nonneg
      (scalarOptimizer_feasible hk hγ).ratio_nonneg
      (scalarOptimizer_feasible hk hγ).ratio_le_one)

/-- The scalar optimum has strictly positive entropy throughout the open
density interval. -/
theorem entropyDensity_pos
    (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    0 < entropyDensity k γ := by
  rw [← scalarOptimizer_objective_eq hk hγ, scalarObjective]
  apply mul_pos (scalarOptimizer_feasible hk hγ).y_pos
  by_cases hcrit : γ ≤ gammaK k
  · simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    rw [scalarRatio_lowerCandidate hk hγ.1.ne']
    exact binaryEntropy_pos (pK_pos (by omega)) (pK_lt_one (by omega))
  · have hcrit' : gammaK k < γ := lt_of_not_ge hcrit
    simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    rw [scalarRatio_upperBoundary k hk γ]
    exact binaryEntropy_pos
      ((pK_pos (by omega)).trans ((pK_lt_phaseLower_iff hk γ).2 hcrit'))
      (phaseLower_lt_one hk hγ.2)

/-- Universal entropy bound, parametrized by the graphon Mantel conclusion.
The paper-facing theorem supplies this hypothesis from induced-star freeness. -/
theorem graphonEntropy_le_entropyDensity_of_randomMass_bound
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hEdge : graphonEdgeDensity W = γ)
    (hMantel : graphonRandomMass W ≤
      ((k - 2 : ℕ) : ℝ) * graphonOneMass W) :
    graphonEntropy W ≤ entropyDensity k γ := by
  by_cases hzero : graphonRandomMass W = 0
  · rw [graphonEntropy_eq_zero_of_randomMass_eq_zero W hzero]
    exact entropyDensity_nonneg k hk γ hγ
  · have hRandom : 0 < graphonRandomMass W :=
      lt_of_le_of_ne (graphonRandomMass_nonneg W) (Ne.symm hzero)
    have hfeasible := graphon_scalarFeasible_of_randomMass_bound
      k W γ hEdge hRandom hMantel
    calc
      graphonEntropy W ≤
          graphonRandomMass W * binaryEntropy (graphonRandomMean W) :=
        graphonEntropy_le_randomMass_mul_entropy_randomMean W hRandom
      _ = scalarObjective γ (graphonOneMass W) (graphonRandomMass W) :=
        (scalarObjective_graphonMasses W γ hEdge hRandom).symm
      _ ≤ entropyDensity k γ :=
        hfeasible.objective_le_entropyDensity hk hγ

/-! ## Paper-facing consequences -/

/-- Every induced-`K_{1,k}`-free graphon of edge density `γ` satisfies the
universal entropy upper bound.  No optimizer or compactness hypothesis is
used. -/
theorem graphonEntropy_le_entropyDensity
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityFeasible k γ) :
    graphonEntropy W ≤ entropyDensity k γ := by
  exact graphonEntropy_le_entropyDensity_of_randomMass_bound
    k hk γ hγ W hW.2
      (graphonRandomMass_le_delta_oneMass k hk W hW.1)

/-- Every member of the explicit candidate family is an actual
fixed-density entropy optimizer. -/
theorem candidate_mem_fixedDensityOptimizers
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ candidateOptimizerFamily k γ) :
    W ∈ fixedDensityOptimizers k γ := by
  have hcandidate := VgammaOpt k hk γ hγ hW
  refine ⟨⟨hcandidate.1, hcandidate.2.1⟩, ?_⟩
  intro U hU
  calc
    graphonEntropy U ≤ entropyDensity k γ :=
      graphonEntropy_le_entropyDensity k hk γ hγ U hU
    _ = graphonEntropy W := hcandidate.2.2.symm

/-- The optimizer set is constructively nonempty: Goal 5a supplies a
candidate, and the universal upper bound proves that candidate optimal. -/
theorem fixedDensityOptimizers_nonempty
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    (fixedDensityOptimizers k γ).Nonempty := by
  obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
  exact ⟨W, candidate_mem_fixedDensityOptimizers k hk γ hγ hW⟩

/-- Every fixed-density optimizer attains the explicit scalar entropy
profile. -/
theorem IsFixedDensityOptimizer.entropy_eq_entropyDensity
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W)
    (hk : 3 ≤ k) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    graphonEntropy W = entropyDensity k γ := by
  apply le_antisymm
  · exact graphonEntropy_le_entropyDensity k hk γ hγ W hW.feasible
  · obtain ⟨U, hU⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
    have hUproperties := VgammaOpt k hk γ hγ hU
    calc
      entropyDensity k γ = graphonEntropy U := hUproperties.2.2.symm
      _ ≤ graphonEntropy W :=
        hW.entropy_le (candidate_mem_fixedDensityFeasible k hk γ hγ hU)

end InducedStars
