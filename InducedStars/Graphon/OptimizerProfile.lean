import InducedStars.Graphon.EntropyUpperBound
import InducedStars.Graphon.GraphonMantel
import Mathlib.Tactic

/-!
# Equality profiles of fixed-density graphon optimizers

This file packages the equality information from the graphon Mantel and
entropy bounds.  It deliberately stops before the connected-core
classification: that stability argument belongs to the next milestone.
-/

noncomputable section

open MeasureTheory Set

namespace InducedStars

/-- The value distribution and scalar coordinates forced for every
fixed-density entropy optimizer. -/
structure FixedDensityOptimizerProfile
    (k : ℕ) (γ : ℝ) (W : Graphon) where
  randomMean : ℝ
  randomMean_pos : 0 < randomMean
  randomMean_lt_one : randomMean < 1
  entropy_eq : graphonEntropy W = entropyDensity k γ
  randomMass_pos : 0 < graphonRandomMass W
  ae_threeValued :
    ∀ᵐ z ∂unitSquareMeasure,
      W.value z = 0 ∨ W.value z = randomMean ∨ W.value z = 1
  edgeDensity_decomposition :
    γ = graphonOneMass W + randomMean * graphonRandomMass W
  randomMass_le :
    graphonRandomMass W ≤
      ((k - 2 : ℕ) : ℝ) * graphonOneMass W
  oneMass_eq_optimizerX :
    graphonOneMass W = scalarOptimizerX k γ
  randomMass_eq_optimizerY :
    graphonRandomMass W = scalarOptimizerY k γ
  randomMass_eq_delta_mul_oneMass :
    graphonRandomMass W =
      ((k - 2 : ℕ) : ℝ) * graphonOneMass W

/-- The optimizer `y` coordinate always saturates the graphon Mantel
constraint, in both scalar regimes. -/
theorem scalarOptimizerY_eq_delta_mul_scalarOptimizerX
    (k : ℕ) (γ : ℝ) :
    scalarOptimizerY k γ =
      ((k - 2 : ℕ) : ℝ) * scalarOptimizerX k γ := by
  by_cases hcrit : γ ≤ gammaK k
  · simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    ring
  · simp only [scalarOptimizerX, scalarOptimizerY, hcrit, ↓reduceIte]
    ring

/-- The profile mean is the scalar quotient determined by its one- and
random-region masses. -/
theorem FixedDensityOptimizerProfile.scalarRatio_eq_randomMean
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W) :
    scalarRatio γ (graphonOneMass W) (graphonRandomMass W) =
      P.randomMean := by
  rw [scalarRatio]
  field_simp [P.randomMass_pos.ne']
  nlinarith [P.edgeDensity_decomposition]

/-- Every optimizer has positive random mass, equality in entropy Jensen,
the scalar optimizer coordinates, and saturation of graphon Mantel. -/
noncomputable def IsFixedDensityOptimizer.profile
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W)
    (hk : 3 ≤ k) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    FixedDensityOptimizerProfile k γ W := by
  have hFeasible := hW.feasible
  have hEntropy : graphonEntropy W = entropyDensity k γ :=
    hW.entropy_eq_entropyDensity hk hγ
  have hRandom : 0 < graphonRandomMass W := by
    by_contra hnot
    have hzero : graphonRandomMass W = 0 :=
      le_antisymm (le_of_not_gt hnot) (graphonRandomMass_nonneg W)
    have hEntropyZero := graphonEntropy_eq_zero_of_randomMass_eq_zero W hzero
    nlinarith [entropyDensity_pos k hk γ hγ]
  have hMantel :
      graphonRandomMass W ≤
        ((k - 2 : ℕ) : ℝ) * graphonOneMass W :=
    graphonRandomMass_le_delta_oneMass k hk W hFeasible.1
  have hScalar :
      ScalarFeasible k γ (graphonOneMass W) (graphonRandomMass W) :=
    graphon_scalarFeasible_of_randomMass_bound
      k W γ hFeasible.2 hRandom hMantel
  have hJensen :
      graphonEntropy W ≤
        graphonRandomMass W * binaryEntropy (graphonRandomMean W) :=
    graphonEntropy_le_randomMass_mul_entropy_randomMean W hRandom
  have hJensenEq :
      graphonEntropy W =
        graphonRandomMass W * binaryEntropy (graphonRandomMean W) :=
    le_antisymm hJensen (by
      calc
        graphonRandomMass W * binaryEntropy (graphonRandomMean W) =
            scalarObjective γ (graphonOneMass W) (graphonRandomMass W) :=
          (scalarObjective_graphonMasses W γ hFeasible.2 hRandom).symm
        _ ≤ entropyDensity k γ :=
          hScalar.objective_le_entropyDensity hk hγ
        _ = graphonEntropy W := hEntropy.symm)
  have hObjectiveEq :
      scalarObjective γ (graphonOneMass W) (graphonRandomMass W) =
        entropyDensity k γ := by
    calc
      scalarObjective γ (graphonOneMass W) (graphonRandomMass W) =
          graphonRandomMass W * binaryEntropy (graphonRandomMean W) :=
        scalarObjective_graphonMasses W γ hFeasible.2 hRandom
      _ = graphonEntropy W := hJensenEq.symm
      _ = entropyDensity k γ := hEntropy
  have hCoordinates :
      graphonOneMass W = scalarOptimizerX k γ ∧
        graphonRandomMass W = scalarOptimizerY k γ :=
    (hScalar.objective_eq_entropyDensity_iff hk hγ).mp hObjectiveEq
  refine
    { randomMean := graphonRandomMean W
      randomMean_pos := graphonRandomMean_pos W hRandom
      randomMean_lt_one := graphonRandomMean_lt_one W hRandom
      entropy_eq := hEntropy
      randomMass_pos := hRandom
      ae_threeValued :=
        graphon_ae_threeValued_of_entropy_eq W hRandom hJensenEq
      edgeDensity_decomposition := ?_
      randomMass_le := hMantel
      oneMass_eq_optimizerX := hCoordinates.1
      randomMass_eq_optimizerY := hCoordinates.2
      randomMass_eq_delta_mul_oneMass := ?_ }
  · exact hFeasible.2.symm.trans
      (graphonEdgeDensity_eq_oneMass_add_randomMean_mul_randomMass W)
  · calc
      graphonRandomMass W = scalarOptimizerY k γ := hCoordinates.2
      _ = ((k - 2 : ℕ) : ℝ) * scalarOptimizerX k γ :=
        scalarOptimizerY_eq_delta_mul_scalarOptimizerX k γ
      _ = ((k - 2 : ℕ) : ℝ) * graphonOneMass W := by
        rw [hCoordinates.1]

/-- A fixed-density optimizer together with its complete equality profile
exists constructively throughout the open density interval. -/
theorem exists_fixedDensityOptimizerProfile
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ W : Graphon,
      W ∈ fixedDensityOptimizers k γ ∧
        Nonempty (FixedDensityOptimizerProfile k γ W) := by
  obtain ⟨W, hW⟩ := fixedDensityOptimizers_nonempty k hk γ hγ
  exact ⟨W, hW, ⟨(show IsFixedDensityOptimizer k γ W from hW).profile hk hγ⟩⟩

/-! ## Exact scalar coordinates in the two regimes -/

theorem FixedDensityOptimizerProfile.oneMass_eq_of_lt_gammaK
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hsub : γ < gammaK k) :
    graphonOneMass W =
      γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k) := by
  rw [P.oneMass_eq_optimizerX]
  simp only [scalarOptimizerX, hsub.le, ↓reduceIte]

theorem FixedDensityOptimizerProfile.randomMass_eq_of_lt_gammaK
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hsub : γ < gammaK k) :
    graphonRandomMass W =
      ((k - 2 : ℕ) : ℝ) * γ /
        (1 + ((k - 2 : ℕ) : ℝ) * pK k) := by
  rw [P.randomMass_eq_optimizerY]
  simp only [scalarOptimizerY, hsub.le, ↓reduceIte]

theorem FixedDensityOptimizerProfile.randomMean_eq_of_lt_gammaK
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hsub : γ < gammaK k) :
    P.randomMean = pK k := by
  calc
    P.randomMean =
        scalarRatio γ (graphonOneMass W) (graphonRandomMass W) :=
      P.scalarRatio_eq_randomMean.symm
    _ = scalarRatio γ
        (γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k))
        (((k - 2 : ℕ) : ℝ) * γ /
          (1 + ((k - 2 : ℕ) : ℝ) * pK k)) := by
      rw [P.oneMass_eq_of_lt_gammaK hsub,
        P.randomMass_eq_of_lt_gammaK hsub]
    _ = pK k := scalarRatio_lowerCandidate hk hγ.1.ne'

theorem FixedDensityOptimizerProfile.mass_sum_lt_one_of_lt_gammaK
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hsub : γ < gammaK k) :
    graphonOneMass W + graphonRandomMass W < 1 := by
  rw [P.oneMass_eq_of_lt_gammaK hsub,
    P.randomMass_eq_of_lt_gammaK hsub]
  have hden :
      0 < 1 + ((k - 2 : ℕ) : ℝ) * pK k := by
    have hp : 0 < pK k := pK_pos (by omega)
    positivity
  have hkOne : (0 : ℝ) < (k - 1 : ℕ) := kSubOne_pos hk
  have hscaled :
      γ * ((k - 1 : ℕ) : ℝ) <
        1 + ((k - 2 : ℕ) : ℝ) * pK k := by
    rw [gammaK] at hsub
    exact (lt_div_iff₀ hkOne).mp hsub
  rw [← add_div, div_lt_one hden]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)] at hscaled ⊢
  nlinarith

theorem FixedDensityOptimizerProfile.oneMass_eq_of_gammaK_le
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hcrit : gammaK k ≤ γ) :
    graphonOneMass W = 1 / ((k - 1 : ℕ) : ℝ) := by
  rw [P.oneMass_eq_optimizerX]
  rcases hcrit.eq_or_lt with hEq | hlt
  · rw [← hEq]
    exact (scalarOptimizer_at_gammaK k hk).1
  · simp only [scalarOptimizerX, not_le_of_gt hlt, ↓reduceIte]

theorem FixedDensityOptimizerProfile.randomMass_eq_of_gammaK_le
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hcrit : gammaK k ≤ γ) :
    graphonRandomMass W =
      ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) := by
  rw [P.randomMass_eq_optimizerY]
  rcases hcrit.eq_or_lt with hEq | hlt
  · rw [← hEq]
    exact (scalarOptimizer_at_gammaK k hk).2
  · simp only [scalarOptimizerY, not_le_of_gt hlt, ↓reduceIte]

theorem FixedDensityOptimizerProfile.randomMean_eq_of_gammaK_le
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hcrit : gammaK k ≤ γ) :
    P.randomMean =
      ((((k - 1 : ℕ) : ℝ) * γ - 1) / ((k - 2 : ℕ) : ℝ)) := by
  calc
    P.randomMean =
        scalarRatio γ (graphonOneMass W) (graphonRandomMass W) :=
      P.scalarRatio_eq_randomMean.symm
    _ = scalarRatio γ
        (1 / ((k - 1 : ℕ) : ℝ))
        (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) := by
      rw [P.oneMass_eq_of_gammaK_le hk hcrit,
        P.randomMass_eq_of_gammaK_le hk hcrit]
    _ = phaseLower k γ := scalarRatio_upperBoundary k hk γ
    _ = ((((k - 1 : ℕ) : ℝ) * γ - 1) /
        ((k - 2 : ℕ) : ℝ)) := by
      rw [phaseLower]
      ring

theorem FixedDensityOptimizerProfile.mass_sum_eq_one_of_gammaK_le
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hcrit : gammaK k ≤ γ) :
    graphonOneMass W + graphonRandomMass W = 1 := by
  rw [P.oneMass_eq_of_gammaK_le hk hcrit,
    P.randomMass_eq_of_gammaK_le hk hcrit]
  have hkOne : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  field_simp [hkOne]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-- The complete subcritical optimizer profile. -/
theorem FixedDensityOptimizerProfile.subcritical_formulas
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (hsub : γ < gammaK k) :
    graphonOneMass W =
        γ / (1 + ((k - 2 : ℕ) : ℝ) * pK k) ∧
      graphonRandomMass W =
        ((k - 2 : ℕ) : ℝ) * γ /
          (1 + ((k - 2 : ℕ) : ℝ) * pK k) ∧
      P.randomMean = pK k ∧
      graphonOneMass W + graphonRandomMass W < 1 :=
  ⟨P.oneMass_eq_of_lt_gammaK hsub,
    P.randomMass_eq_of_lt_gammaK hsub,
    P.randomMean_eq_of_lt_gammaK hk hγ hsub,
    P.mass_sum_lt_one_of_lt_gammaK hk hsub⟩

/-- The complete critical/supercritical optimizer profile.  Equality at
`gammaK k` belongs to this branch. -/
theorem FixedDensityOptimizerProfile.criticalSupercritical_formulas
    {k : ℕ} {γ : ℝ} {W : Graphon}
    (P : FixedDensityOptimizerProfile k γ W)
    (hk : 3 ≤ k) (hcrit : gammaK k ≤ γ) :
    graphonOneMass W = 1 / ((k - 1 : ℕ) : ℝ) ∧
      graphonRandomMass W =
        ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) ∧
      P.randomMean =
        ((((k - 1 : ℕ) : ℝ) * γ - 1) / ((k - 2 : ℕ) : ℝ)) ∧
      graphonOneMass W + graphonRandomMass W = 1 :=
  ⟨P.oneMass_eq_of_gammaK_le hk hcrit,
    P.randomMass_eq_of_gammaK_le hk hcrit,
    P.randomMean_eq_of_gammaK_le hk hcrit,
    P.mass_sum_eq_one_of_gammaK_le hk hcrit⟩

end InducedStars
