import InducedStars.Graphon.Equivalence
import InducedStars.Graphon.ValueRegions
import Mathlib.Analysis.Convex.Integral

/-!
# Value level sets and entropy averaging for graphons

This file develops the measure-theoretic layer used in the graphon Mantel
inequality and the fixed-density entropy bound.  All level sets use the
canonical pointwise-bounded representative `Graphon.value`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace InducedStars

/-! ## The mean on the random region -/

/-- The average graphon value on the random region.  Mathlib's set average
provides the harmless totalized value zero when the region has zero measure. -/
noncomputable def graphonRandomMean (W : Graphon) : ℝ :=
  ⨍ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure

@[simp] theorem graphonRandomMean_eq_zero_of_randomMass_eq_zero
    (W : Graphon) (hRandom : graphonRandomMass W = 0) :
    graphonRandomMean W = 0 := by
  have hMeasure : unitSquareMeasure (graphonRandomRegion W) = 0 :=
    (measureReal_eq_zero_iff (μ := unitSquareMeasure)
      (s := graphonRandomRegion W)).mp (by
        simpa only [graphonRandomMass] using hRandom)
  rw [graphonRandomMean, Measure.restrict_eq_zero.mpr hMeasure,
    average_zero_measure]

theorem Graphon.integrable_value (W : Graphon) :
    Integrable W.value unitSquareMeasure :=
  W.integrable.congr (EventuallyEq.symm W.value_ae_eq)

theorem setIntegral_value_randomRegion_eq_randomMass_mul_randomMean (W : Graphon) :
    (∫ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure) =
      graphonRandomMass W * graphonRandomMean W := by
  symm
  simpa only [graphonRandomMass, graphonRandomMean, smul_eq_mul] using
    (measure_smul_setAverage (μ := unitSquareMeasure) W.value
      (s := graphonRandomRegion W) (by finiteness))

theorem setIntegral_value_oneRegion_eq_oneMass (W : Graphon) :
    (∫ z in graphonOneRegion W, W.value z ∂unitSquareMeasure) =
      graphonOneMass W := by
  calc
    _ = ∫ _z in graphonOneRegion W, (1 : ℝ) ∂unitSquareMeasure := by
      apply setIntegral_congr_fun (measurableSet_graphonOneRegion W)
      intro z hz
      exact hz
    _ = graphonOneMass W := by
      simp [graphonOneMass]

theorem graphonEdgeDensity_eq_oneMass_add_randomMean_mul_randomMass (W : Graphon) :
    graphonEdgeDensity W =
      graphonOneMass W + graphonRandomMean W * graphonRandomMass W := by
  rw [graphonEdgeDensity_eq_integral_value]
  calc
    (∫ z, W.value z ∂unitSquareMeasure) =
        ∫ z in graphonRandomRegion W ∪ graphonOneRegion W,
          W.value z ∂unitSquareMeasure := by
      rw [← integral_indicator (measurableSet_graphonRandomRegion W |>.union
        (measurableSet_graphonOneRegion W))]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ graphonRandomRegion W ∪ graphonOneRegion W
      · simp [hz]
      · simp [hz, graphon_value_eq_zero_of_not_mem_randomRegion_union_oneRegion W hz]
    _ = (∫ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure) +
        ∫ z in graphonOneRegion W, W.value z ∂unitSquareMeasure := by
      exact setIntegral_union (graphonRandomRegion_disjoint_oneRegion W)
        (measurableSet_graphonOneRegion W) W.integrable_value.integrableOn
        W.integrable_value.integrableOn
    _ = graphonOneMass W + graphonRandomMean W * graphonRandomMass W := by
      rw [setIntegral_value_randomRegion_eq_randomMass_mul_randomMean,
        setIntegral_value_oneRegion_eq_oneMass]
      ring

theorem graphonEdgeDensity_eq_oneMass_add_randomMass_mul_randomMean (W : Graphon) :
    graphonEdgeDensity W =
      graphonOneMass W + graphonRandomMass W * graphonRandomMean W := by
  rw [graphonEdgeDensity_eq_oneMass_add_randomMean_mul_randomMass, mul_comm]

private theorem setIntegral_value_randomRegion_pos
    (W : Graphon) (hRandom : 0 < graphonRandomMass W) :
    0 < ∫ z in graphonRandomRegion W, W.value z ∂unitSquareMeasure := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun z ↦ W.value_nonneg z)
    W.integrable_value.integrableOn]
  have hmeasure : 0 < unitSquareMeasure (graphonRandomRegion W) := by
    exact (ENNReal.toReal_pos_iff.mp hRandom).1
  refine lt_of_lt_of_le hmeasure (measure_mono ?_)
  intro z hz
  exact ⟨ne_of_gt hz.1, hz⟩

private theorem setIntegral_one_sub_value_randomRegion_pos
    (W : Graphon) (hRandom : 0 < graphonRandomMass W) :
    0 < ∫ z in graphonRandomRegion W, (1 - W.value z) ∂unitSquareMeasure := by
  have hIntegrable : Integrable (fun z : UnitSquare ↦ 1 - W.value z) unitSquareMeasure :=
    (integrable_const (1 : ℝ)).sub W.integrable_value
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun z ↦ sub_nonneg.mpr (W.value_le_one z))
    hIntegrable.integrableOn]
  have hmeasure : 0 < unitSquareMeasure (graphonRandomRegion W) := by
    exact (ENNReal.toReal_pos_iff.mp hRandom).1
  refine lt_of_lt_of_le hmeasure (measure_mono ?_)
  intro z hz
  exact ⟨sub_ne_zero.mpr (Ne.symm (ne_of_lt hz.2)), hz⟩

theorem graphonRandomMean_pos (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    0 < graphonRandomMean W := by
  have hIntegral := setIntegral_value_randomRegion_pos W hRandom
  rw [setIntegral_value_randomRegion_eq_randomMass_mul_randomMean] at hIntegral
  nlinarith [graphonRandomMass_nonneg W]

theorem graphonRandomMean_lt_one (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    graphonRandomMean W < 1 := by
  have hIntegral := setIntegral_one_sub_value_randomRegion_pos W hRandom
  have hOne :
      (∫ z in graphonRandomRegion W, (1 : ℝ) ∂unitSquareMeasure) =
        graphonRandomMass W := by
    simp [graphonRandomMass]
  have hValue := setIntegral_value_randomRegion_eq_randomMass_mul_randomMean W
  rw [integral_sub (integrable_const (1 : ℝ)).integrableOn
    W.integrable_value.integrableOn] at hIntegral
  rw [hOne, hValue] at hIntegral
  nlinarith

theorem graphonRandomMean_mem_Ioo (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    graphonRandomMean W ∈ Ioo (0 : ℝ) 1 :=
  ⟨graphonRandomMean_pos W hRandom, graphonRandomMean_lt_one W hRandom⟩

/-! ## Entropy decomposition and Jensen equality -/

theorem binaryEntropy_value_eq_zero_of_not_mem_randomRegion
    (W : Graphon) {z : UnitSquare} (hz : z ∉ graphonRandomRegion W) :
    binaryEntropy (W.value z) = 0 := by
  rcases graphon_value_eq_zero_or_one_of_not_mem_randomRegion W hz with hzero | hone
  · simp [hzero]
  · simp [hone]

theorem graphonEntropy_eq_setIntegral_randomRegion (W : Graphon) :
    graphonEntropy W =
      ∫ z in graphonRandomRegion W, binaryEntropy (W.value z) ∂unitSquareMeasure := by
  unfold graphonEntropy graphonValueFunctional
  rw [← integral_indicator (measurableSet_graphonRandomRegion W)]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : z ∈ graphonRandomRegion W
  · simp [hz]
  · simp [hz, binaryEntropy_value_eq_zero_of_not_mem_randomRegion W hz]

@[simp] theorem graphonEntropy_eq_zero_of_randomMass_eq_zero
    (W : Graphon) (hRandom : graphonRandomMass W = 0) :
    graphonEntropy W = 0 := by
  have hMeasure : unitSquareMeasure (graphonRandomRegion W) = 0 :=
    (measureReal_eq_zero_iff (μ := unitSquareMeasure)
      (s := graphonRandomRegion W)).mp (by
        simpa only [graphonRandomMass] using hRandom)
  rw [graphonEntropy_eq_setIntegral_randomRegion]
  simp [hMeasure]

/-- Jensen's inequality for binary entropy on the positive-measure random
region of a graphon. -/
theorem graphonEntropy_le_randomMass_mul_entropy_randomMean
    (W : Graphon) (hRandom : 0 < graphonRandomMass W) :
    graphonEntropy W ≤
      graphonRandomMass W * binaryEntropy (graphonRandomMean W) := by
  have hMassRealNe :
      unitSquareMeasure.real (graphonRandomRegion W) ≠ 0 := by
    simpa only [graphonRandomMass] using hRandom.ne'
  have hMassNe : unitSquareMeasure (graphonRandomRegion W) ≠ 0 :=
    (measureReal_ne_zero_iff (μ := unitSquareMeasure)
      (s := graphonRandomRegion W)).mp hMassRealNe
  let _ : NeZero (unitSquareMeasure (graphonRandomRegion W)) := ⟨hMassNe⟩
  have hJensen := binaryEntropy_strictConcaveOn.concaveOn.le_map_average
    binaryEntropy_continuousOn isClosed_Icc
    (ae_of_all (unitSquareMeasure.restrict (graphonRandomRegion W))
      fun z ↦ W.value_mem_Icc z)
    W.integrable_value.integrableOn
    (integrable_binaryEntropy_value W).integrableOn
  have hMassFinite : unitSquareMeasure (graphonRandomRegion W) ≠ ∞ := by finiteness
  rw [graphonEntropy_eq_setIntegral_randomRegion]
  calc
    (∫ z in graphonRandomRegion W, binaryEntropy (W.value z) ∂unitSquareMeasure) =
        graphonRandomMass W *
          (⨍ z in graphonRandomRegion W, binaryEntropy (W.value z)
            ∂unitSquareMeasure) := by
      symm
      simpa only [graphonRandomMass, smul_eq_mul] using
        (measure_smul_setAverage (μ := unitSquareMeasure)
          (fun z ↦ binaryEntropy (W.value z)) hMassFinite)
    _ ≤ graphonRandomMass W *
        binaryEntropy (⨍ z in graphonRandomRegion W, W.value z
          ∂unitSquareMeasure) :=
      mul_le_mul_of_nonneg_left hJensen (graphonRandomMass_nonneg W)
    _ = graphonRandomMass W * binaryEntropy (graphonRandomMean W) := rfl

/-- Equality in the entropy Jensen bound holds exactly when the graphon is
almost everywhere constant on its random region. -/
theorem graphonEntropy_eq_randomMass_mul_entropy_randomMean_iff
    (W : Graphon) (hRandom : 0 < graphonRandomMass W) :
    graphonEntropy W =
        graphonRandomMass W * binaryEntropy (graphonRandomMean W) ↔
      ∀ᵐ z ∂unitSquareMeasure.restrict (graphonRandomRegion W),
        W.value z = graphonRandomMean W := by
  have hMassFinite : unitSquareMeasure (graphonRandomRegion W) ≠ ∞ := by finiteness
  have hMassRealNe :
      unitSquareMeasure.real (graphonRandomRegion W) ≠ 0 := by
    simpa only [graphonRandomMass] using hRandom.ne'
  have hMassNe : unitSquareMeasure (graphonRandomRegion W) ≠ 0 :=
    (measureReal_ne_zero_iff (μ := unitSquareMeasure)
      (s := graphonRandomRegion W)).mp hMassRealNe
  let _ : NeZero (unitSquareMeasure (graphonRandomRegion W)) := ⟨hMassNe⟩
  constructor
  · intro hEq
    have hAverageEq :
        (⨍ z in graphonRandomRegion W, binaryEntropy (W.value z)
            ∂unitSquareMeasure) =
          binaryEntropy (⨍ z in graphonRandomRegion W, W.value z
            ∂unitSquareMeasure) := by
      have hScaled :
          graphonRandomMass W *
              (⨍ z in graphonRandomRegion W, binaryEntropy (W.value z)
                ∂unitSquareMeasure) =
            graphonRandomMass W * binaryEntropy (graphonRandomMean W) := by
        calc
          _ = ∫ z in graphonRandomRegion W, binaryEntropy (W.value z)
                ∂unitSquareMeasure := by
            simpa only [graphonRandomMass, smul_eq_mul] using
              (measure_smul_setAverage (μ := unitSquareMeasure)
                (fun z ↦ binaryEntropy (W.value z)) hMassFinite)
          _ = graphonEntropy W :=
            (graphonEntropy_eq_setIntegral_randomRegion W).symm
          _ = _ := hEq
      exact (mul_left_cancel₀ hRandom.ne' hScaled)
    have hStrict := binaryEntropy_strictConcaveOn.ae_eq_const_or_lt_map_average
      binaryEntropy_continuousOn isClosed_Icc
      (ae_of_all (unitSquareMeasure.restrict (graphonRandomRegion W))
        fun z ↦ W.value_mem_Icc z)
      W.integrable_value.integrableOn
      (integrable_binaryEntropy_value W).integrableOn
    rcases hStrict with hConst | hLt
    · filter_upwards [hConst] with z hz
      simpa only [graphonRandomMean, Function.const_apply] using hz
    · exact (ne_of_lt hLt hAverageEq).elim
  · intro hConst
    rw [graphonEntropy_eq_setIntegral_randomRegion]
    calc
      (∫ z in graphonRandomRegion W, binaryEntropy (W.value z) ∂unitSquareMeasure) =
          ∫ _z in graphonRandomRegion W,
            binaryEntropy (graphonRandomMean W) ∂unitSquareMeasure := by
        apply integral_congr_ae
        filter_upwards [hConst] with z hz
        rw [hz]
      _ = graphonRandomMass W * binaryEntropy (graphonRandomMean W) := by
        simp [graphonRandomMass, smul_eq_mul]

/-- Equality in Jensen gives the three-valued profile used later in optimizer
classification. -/
theorem graphon_ae_threeValued_of_entropy_eq
    (W : Graphon) (hRandom : 0 < graphonRandomMass W)
    (hEntropy : graphonEntropy W =
      graphonRandomMass W * binaryEntropy (graphonRandomMean W)) :
    ∀ᵐ z ∂unitSquareMeasure,
      W.value z = 0 ∨ W.value z = graphonRandomMean W ∨ W.value z = 1 := by
  have hConst :=
    (graphonEntropy_eq_randomMass_mul_entropy_randomMean_iff W hRandom).mp hEntropy
  rw [ae_restrict_iff' (measurableSet_graphonRandomRegion W)] at hConst
  filter_upwards [hConst] with z hz
  by_cases hRegion : z ∈ graphonRandomRegion W
  · exact Or.inr (Or.inl (hz hRegion))
  · rcases graphon_value_eq_zero_or_one_of_not_mem_randomRegion W hRegion with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr (Or.inr hone)

/-! ## Invariance under exact cut equivalence -/

/-- The random-region mass depends only on the cut-distance-zero class. -/
theorem graphonRandomMass_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonRandomMass U = graphonRandomMass W := by
  unfold graphonRandomMass graphonRandomRegion
  apply congrArg ENNReal.toReal
  change unitSquareMeasure (U.value ⁻¹' Ioo (0 : ℝ) 1) =
    unitSquareMeasure (W.value ⁻¹' Ioo (0 : ℝ) 1)
  calc
    unitSquareMeasure (U.value ⁻¹' Ioo (0 : ℝ) 1) =
        (Measure.map U.value unitSquareMeasure) (Ioo (0 : ℝ) 1) := by
      rw [Measure.map_apply U.measurable_value measurableSet_Ioo]
    _ = (Measure.map W.value unitSquareMeasure) (Ioo (0 : ℝ) 1) := by
      rw [graphonValueLaw_eq_of_cutDist_eq_zero U W hcut]
    _ = unitSquareMeasure (W.value ⁻¹' Ioo (0 : ℝ) 1) := by
      rw [Measure.map_apply W.measurable_value measurableSet_Ioo]

/-- The one-region mass depends only on the cut-distance-zero class. -/
theorem graphonOneMass_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonOneMass U = graphonOneMass W := by
  unfold graphonOneMass graphonOneRegion
  apply congrArg ENNReal.toReal
  change unitSquareMeasure (U.value ⁻¹' ({1} : Set ℝ)) =
    unitSquareMeasure (W.value ⁻¹' ({1} : Set ℝ))
  calc
    unitSquareMeasure (U.value ⁻¹' ({1} : Set ℝ)) =
        (Measure.map U.value unitSquareMeasure) ({1} : Set ℝ) := by
      rw [Measure.map_apply U.measurable_value (measurableSet_singleton 1)]
    _ = (Measure.map W.value unitSquareMeasure) ({1} : Set ℝ) := by
      rw [graphonValueLaw_eq_of_cutDist_eq_zero U W hcut]
    _ = unitSquareMeasure (W.value ⁻¹' ({1} : Set ℝ)) := by
      rw [Measure.map_apply W.measurable_value (measurableSet_singleton 1)]

/-- Fixed middle-band mass depends only on the cut-distance-zero class. -/
theorem graphonMiddleBandMass_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) (theta : ℝ) :
    graphonMiddleBandMass U theta = graphonMiddleBandMass W theta := by
  unfold graphonMiddleBandMass graphonMiddleBand
  apply congrArg ENNReal.toReal
  change unitSquareMeasure (U.value ⁻¹' Icc (2 * theta) (1 - 2 * theta)) =
    unitSquareMeasure (W.value ⁻¹' Icc (2 * theta) (1 - 2 * theta))
  calc
    unitSquareMeasure (U.value ⁻¹' Icc (2 * theta) (1 - 2 * theta)) =
        (Measure.map U.value unitSquareMeasure)
          (Icc (2 * theta) (1 - 2 * theta)) := by
      rw [Measure.map_apply U.measurable_value measurableSet_Icc]
    _ = (Measure.map W.value unitSquareMeasure)
          (Icc (2 * theta) (1 - 2 * theta)) := by
      rw [graphonValueLaw_eq_of_cutDist_eq_zero U W hcut]
    _ = unitSquareMeasure
          (W.value ⁻¹' Icc (2 * theta) (1 - 2 * theta)) := by
      rw [Measure.map_apply W.measurable_value measurableSet_Icc]

/-- Fixed upper-band mass depends only on the cut-distance-zero class. -/
theorem graphonUpperBandMass_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) (theta : ℝ) :
    graphonUpperBandMass U theta = graphonUpperBandMass W theta := by
  unfold graphonUpperBandMass graphonUpperBand
  apply congrArg ENNReal.toReal
  change unitSquareMeasure (U.value ⁻¹' Ioi (1 - 2 * theta)) =
    unitSquareMeasure (W.value ⁻¹' Ioi (1 - 2 * theta))
  calc
    unitSquareMeasure (U.value ⁻¹' Ioi (1 - 2 * theta)) =
        (Measure.map U.value unitSquareMeasure) (Ioi (1 - 2 * theta)) := by
      rw [Measure.map_apply U.measurable_value measurableSet_Ioi]
    _ = (Measure.map W.value unitSquareMeasure) (Ioi (1 - 2 * theta)) := by
      rw [graphonValueLaw_eq_of_cutDist_eq_zero U W hcut]
    _ = unitSquareMeasure (W.value ⁻¹' Ioi (1 - 2 * theta)) := by
      rw [Measure.map_apply W.measurable_value measurableSet_Ioi]

end InducedStars
