import InducedStars.Graphon.LevelSets
import Mathlib.Tactic

/-!
# Positive-measure flexible bands

This file isolates the analytic part of the exact-edge repair used in the
fixed-density enumeration transfer. A graphon with positive random mass has
a positive-measure closed value band bounded away from both zero and one.
The proof uses a countable exhaustion of the random region, repairing the
sum-of-uniforms step recorded as CFD-001.

The band indicator is also packaged as a {0,1}-valued graphon. Because the
Graphon carrier is an L¹ class, its canonical representative agrees with
the pointwise indicator almost everywhere, which is the strongest identity
available from Graphon.ofFun.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal

namespace InducedStars

/-! ## General closed value bands -/

/-- The part of the unit square on which the canonical value of W lies in
the closed interval [L,U]. -/
def graphonClosedBand (W : Graphon) (L U : ℝ) : Set UnitSquare :=
  {z | L ≤ W.value z ∧ W.value z ≤ U}

@[measurability]
theorem measurableSet_graphonClosedBand (W : Graphon) (L U : ℝ) :
    MeasurableSet (graphonClosedBand W L U) := by
  unfold graphonClosedBand
  measurability

/-- Real measure of a general closed graphon value band. -/
noncomputable def graphonClosedBandMass (W : Graphon) (L U : ℝ) : ℝ :=
  unitSquareMeasure.real (graphonClosedBand W L U)

@[simp]
theorem graphonClosedBandMass_nonneg (W : Graphon) (L U : ℝ) :
    0 ≤ graphonClosedBandMass W L U :=
  measureReal_nonneg

/-- Swapping the two coordinates preserves a closed value band. -/
theorem swap_mem_graphonClosedBand_iff (W : Graphon) (L U : ℝ) (z : UnitSquare) :
    (z.2, z.1) ∈ graphonClosedBand W L U ↔ z ∈ graphonClosedBand W L U := by
  simp only [graphonClosedBand, mem_ofPred_eq, W.value_swap]

/-- The random region is exhausted by closed symmetric bands whose endpoints
stay strictly between zero and one. -/
theorem graphonRandomRegion_subset_iUnion_closedBand (W : Graphon) :
    graphonRandomRegion W ⊆
      ⋃ n : ℕ, graphonClosedBand W
        (1 / ((n + 3 : ℕ) : ℝ)) (1 - 1 / ((n + 3 : ℕ) : ℝ)) := by
  intro z hz
  have hgap : 0 < min (W.value z) (1 - W.value z) :=
    lt_min hz.1 (sub_pos.mpr hz.2)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hgap
  rw [mem_iUnion]
  refine ⟨n, ?_⟩
  have hrecip :
      1 / ((n + 3 : ℕ) : ℝ) ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    apply one_div_le_one_div_of_le
    · positivity
    · norm_num
  have hn' :
      1 / ((n + 1 : ℕ) : ℝ) < min (W.value z) (1 - W.value z) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hn
  change
    1 / ((n + 3 : ℕ) : ℝ) ≤ W.value z ∧
      W.value z ≤ 1 - 1 / ((n + 3 : ℕ) : ℝ)
  constructor
  · exact hrecip.trans (hn'.le.trans (min_le_left _ _))
  · have hcomplement :
        1 / ((n + 3 : ℕ) : ℝ) ≤ 1 - W.value z :=
      hrecip.trans (hn'.le.trans (min_le_right _ _))
    linarith

/-- Positive random mass supplies a positive-measure closed band bounded away
from both endpoints of the unit interval. -/
theorem exists_graphonClosedBandMass_pos (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    ∃ L U : ℝ,
      0 < L ∧ L < U ∧ U < 1 ∧ 0 < graphonClosedBandMass W L U := by
  have hRandomMeasure : 0 < unitSquareMeasure (graphonRandomRegion W) := by
    exact (ENNReal.toReal_pos_iff.mp hRandom).1
  have hUnion :
      unitSquareMeasure
          (⋃ n : ℕ, graphonClosedBand W
            (1 / ((n + 3 : ℕ) : ℝ)) (1 - 1 / ((n + 3 : ℕ) : ℝ))) ≠ 0 := by
    exact (hRandomMeasure.trans_le
      (measure_mono (graphonRandomRegion_subset_iUnion_closedBand W))).ne'
  obtain ⟨n, hn⟩ :=
    exists_measure_pos_of_not_measure_iUnion_null hUnion
  let L : ℝ := 1 / ((n + 3 : ℕ) : ℝ)
  let U : ℝ := 1 - L
  have hL : 0 < L := by
    dsimp [L]
    positivity
  have hdenom : (2 : ℝ) < ((n + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 < n + 3 by omega)
  have hLhalf : L < 1 / 2 := by
    dsimp [L]
    exact one_div_lt_one_div_of_lt (by norm_num) hdenom
  have hLU : L < U := by
    dsimp [U]
    linarith
  have hU : U < 1 := by
    dsimp [U]
    linarith
  have hBandReal :
      0 < unitSquareMeasure.real
        (graphonClosedBand W
          (1 / ((n + 3 : ℕ) : ℝ)) (1 - 1 / ((n + 3 : ℕ) : ℝ))) := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨hn, by finiteness⟩
  refine ⟨L, U, hL, hLU, hU, ?_⟩
  simpa only [graphonClosedBandMass, L, U] using hBandReal

/-- Set-level form of exists_graphonClosedBandMass_pos. -/
theorem exists_graphonClosedBand_pos (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    ∃ L U : ℝ,
      0 < L ∧ L < U ∧ U < 1 ∧
        0 < unitSquareMeasure.real
          {z | L ≤ W.value z ∧ W.value z ≤ U} := by
  obtain ⟨L, U, hL, hLU, hU, hmass⟩ :=
    exists_graphonClosedBandMass_pos W hRandom
  exact ⟨L, U, hL, hLU, hU, by
    simpa only [graphonClosedBandMass, graphonClosedBand] using hmass⟩

/-! ## The indicator graphon of a flexible band -/

/-- Pointwise indicator of a closed graphon value band. -/
def flexibleBandIndicator (W : Graphon) (L U : ℝ) : UnitSquare → ℝ :=
  (graphonClosedBand W L U).indicator (fun _ ↦ 1)

@[simp]
theorem flexibleBandIndicator_apply (W : Graphon) (L U : ℝ) (z : UnitSquare) :
    flexibleBandIndicator W L U z =
      if L ≤ W.value z ∧ W.value z ≤ U then 1 else 0 := by
  classical
  by_cases hz : L ≤ W.value z ∧ W.value z ≤ U
  · have hmem : z ∈ graphonClosedBand W L U := hz
    rw [flexibleBandIndicator, indicator_of_mem hmem]
    simp [hz]
  · have hmem : z ∉ graphonClosedBand W L U := hz
    rw [flexibleBandIndicator, indicator_of_notMem hmem]
    simp [hz]

@[fun_prop]
theorem measurable_flexibleBandIndicator (W : Graphon) (L U : ℝ) :
    Measurable (flexibleBandIndicator W L U) := by
  exact measurable_const.indicator (measurableSet_graphonClosedBand W L U)

theorem integrable_flexibleBandIndicator (W : Graphon) (L U : ℝ) :
    Integrable (flexibleBandIndicator W L U) unitSquareMeasure := by
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_graphonClosedBand W L U)

theorem flexibleBandIndicator_nonneg (W : Graphon) (L U : ℝ) (z : UnitSquare) :
    0 ≤ flexibleBandIndicator W L U z := by
  by_cases hz : z ∈ graphonClosedBand W L U
  · rw [flexibleBandIndicator, indicator_of_mem hz]
    norm_num
  · rw [flexibleBandIndicator, indicator_of_notMem hz]

theorem flexibleBandIndicator_le_one (W : Graphon) (L U : ℝ) (z : UnitSquare) :
    flexibleBandIndicator W L U z ≤ 1 := by
  by_cases hz : z ∈ graphonClosedBand W L U
  · rw [flexibleBandIndicator, indicator_of_mem hz]
  · rw [flexibleBandIndicator, indicator_of_notMem hz]
    norm_num

theorem flexibleBandIndicator_swap (W : Graphon) (L U : ℝ) (z : UnitSquare) :
    flexibleBandIndicator W L U (z.2, z.1) =
      flexibleBandIndicator W L U z := by
  simp [flexibleBandIndicator_apply, W.value_swap]

/-- The {0,1}-valued graphon indicating the closed band [L,U] of W. -/
noncomputable def flexibleBandGraphon (W : Graphon) (L U : ℝ) : Graphon :=
  Graphon.ofFun (flexibleBandIndicator W L U)
    (integrable_flexibleBandIndicator W L U)
    (ae_of_all _ (flexibleBandIndicator_nonneg W L U))
    (ae_of_all _ (flexibleBandIndicator_le_one W L U))
    (flexibleBandIndicator_swap W L U)

/-- The chosen L¹ representative of the flexible-band graphon agrees almost
everywhere with the pointwise indicator. -/
theorem flexibleBandGraphon_ae_eq_indicator (W : Graphon) (L U : ℝ) :
    ∀ᵐ z ∂unitSquareMeasure,
      flexibleBandGraphon W L U z = flexibleBandIndicator W L U z := by
  exact Graphon.coe_ofFun (flexibleBandIndicator W L U)
    (integrable_flexibleBandIndicator W L U)
    (ae_of_all _ (flexibleBandIndicator_nonneg W L U))
    (ae_of_all _ (flexibleBandIndicator_le_one W L U))
    (flexibleBandIndicator_swap W L U)

/-- The canonical pointwise-bounded representative agrees almost everywhere
with the band indicator. -/
theorem flexibleBandGraphon_value_ae_eq_indicator (W : Graphon) (L U : ℝ) :
    ∀ᵐ z ∂unitSquareMeasure,
      (flexibleBandGraphon W L U).value z =
        flexibleBandIndicator W L U z := by
  filter_upwards [(flexibleBandGraphon W L U).value_ae_eq,
    flexibleBandGraphon_ae_eq_indicator W L U] with z hvalue hindicator
  exact hvalue.trans hindicator

/-- Explicit almost-everywhere if formula for the canonical representative
of the flexible-band graphon. -/
theorem flexibleBandGraphon_value_ae_eq_ite (W : Graphon) (L U : ℝ) :
    ∀ᵐ z ∂unitSquareMeasure,
      (flexibleBandGraphon W L U).value z =
        if L ≤ W.value z ∧ W.value z ≤ U then 1 else 0 := by
  filter_upwards [flexibleBandGraphon_value_ae_eq_indicator W L U]
    with z hz
  simpa only [flexibleBandIndicator_apply] using hz

/-- Edge density of the flexible-band graphon is exactly the real measure of
the underlying closed band. -/
theorem graphonEdgeDensity_flexibleBandGraphon (W : Graphon) (L U : ℝ) :
    graphonEdgeDensity (flexibleBandGraphon W L U) =
      graphonClosedBandMass W L U := by
  rw [graphonEdgeDensity_eq_integral_value]
  calc
    (∫ z : UnitSquare, (flexibleBandGraphon W L U).value z
        ∂unitSquareMeasure) =
        ∫ z : UnitSquare, flexibleBandIndicator W L U z
          ∂unitSquareMeasure := by
      exact integral_congr_ae
        (flexibleBandGraphon_value_ae_eq_indicator W L U)
    _ = graphonClosedBandMass W L U := by
      rw [flexibleBandIndicator, integral_indicator
        (measurableSet_graphonClosedBand W L U)]
      simp [graphonClosedBandMass]

/-! ## Positive random mass and entropy -/

/-- Positive random mass forces positive graphon entropy. -/
theorem graphonEntropy_pos_of_graphonRandomMass_pos (W : Graphon)
    (hRandom : 0 < graphonRandomMass W) :
    0 < graphonEntropy W := by
  rw [graphonEntropy_eq_setIntegral_randomRegion]
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun z ↦
      binaryEntropy_nonneg (W.value_nonneg z) (W.value_le_one z))
    (integrable_binaryEntropy_value W).integrableOn]
  have hMeasure : 0 < unitSquareMeasure (graphonRandomRegion W) := by
    exact (ENNReal.toReal_pos_iff.mp hRandom).1
  refine hMeasure.trans_le (measure_mono ?_)
  intro z hz
  exact ⟨(binaryEntropy_pos hz.1 hz.2).ne', hz⟩

/-- A graphon has positive entropy exactly when its random region has positive
measure. -/
theorem graphonEntropy_pos_iff_graphonRandomMass_pos (W : Graphon) :
    0 < graphonEntropy W ↔ 0 < graphonRandomMass W := by
  constructor
  · intro hEntropy
    have hne : graphonRandomMass W ≠ 0 := by
      intro hzero
      exact hEntropy.ne'
        (graphonEntropy_eq_zero_of_randomMass_eq_zero W hzero)
    exact lt_of_le_of_ne (graphonRandomMass_nonneg W) hne.symm
  · exact graphonEntropy_pos_of_graphonRandomMass_pos W

end InducedStars
