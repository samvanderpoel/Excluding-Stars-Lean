import InducedStars.Graphon.Basic

/-!
# Canonical graphon value regions

This axiom-free module collects the reusable measurable regions cut out by the
canonical pointwise-bounded representative `Graphon.value`, together with their
real masses and elementary relations.  Results involving entropy averages or
cut-distance-zero invariance remain in `Graphon.LevelSets`.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace InducedStars

/-! ## Random, one-valued, middle, and upper regions -/

/-- The region on which a graphon value is strictly between zero and one. -/
def graphonRandomRegion (W : Graphon) : Set UnitSquare :=
  {z | 0 < W.value z ∧ W.value z < 1}

/-- The region on which a graphon value is exactly one. -/
def graphonOneRegion (W : Graphon) : Set UnitSquare :=
  {z | W.value z = 1}

/-- The closed middle band used in the fixed-threshold graphon Mantel estimate. -/
def graphonMiddleBand (W : Graphon) (theta : ℝ) : Set UnitSquare :=
  {z | 2 * theta ≤ W.value z ∧ W.value z ≤ 1 - 2 * theta}

/-- The upper band used in the fixed-threshold graphon Mantel estimate. -/
def graphonUpperBand (W : Graphon) (theta : ℝ) : Set UnitSquare :=
  {z | 1 - 2 * theta < W.value z}

@[measurability]
theorem measurableSet_graphonRandomRegion (W : Graphon) :
    MeasurableSet (graphonRandomRegion W) := by
  unfold graphonRandomRegion
  measurability

@[measurability]
theorem measurableSet_graphonOneRegion (W : Graphon) :
    MeasurableSet (graphonOneRegion W) := by
  exact W.measurable_value (measurableSet_singleton 1)

@[measurability]
theorem measurableSet_graphonMiddleBand (W : Graphon) (theta : ℝ) :
    MeasurableSet (graphonMiddleBand W theta) := by
  unfold graphonMiddleBand
  measurability

@[measurability]
theorem measurableSet_graphonUpperBand (W : Graphon) (theta : ℝ) :
    MeasurableSet (graphonUpperBand W theta) := by
  unfold graphonUpperBand
  measurability

/-- Real measure of the random region. -/
noncomputable def graphonRandomMass (W : Graphon) : ℝ :=
  unitSquareMeasure.real (graphonRandomRegion W)

/-- Real measure of the one-valued region. -/
noncomputable def graphonOneMass (W : Graphon) : ℝ :=
  unitSquareMeasure.real (graphonOneRegion W)

/-- Real measure of the closed middle band. -/
noncomputable def graphonMiddleBandMass (W : Graphon) (theta : ℝ) : ℝ :=
  unitSquareMeasure.real (graphonMiddleBand W theta)

/-- Real measure of the upper band. -/
noncomputable def graphonUpperBandMass (W : Graphon) (theta : ℝ) : ℝ :=
  unitSquareMeasure.real (graphonUpperBand W theta)

@[simp] theorem graphonRandomMass_nonneg (W : Graphon) :
    0 ≤ graphonRandomMass W :=
  measureReal_nonneg

@[simp] theorem graphonOneMass_nonneg (W : Graphon) :
    0 ≤ graphonOneMass W :=
  measureReal_nonneg

@[simp] theorem graphonMiddleBandMass_nonneg (W : Graphon) (theta : ℝ) :
    0 ≤ graphonMiddleBandMass W theta :=
  measureReal_nonneg

@[simp] theorem graphonUpperBandMass_nonneg (W : Graphon) (theta : ℝ) :
    0 ≤ graphonUpperBandMass W theta :=
  measureReal_nonneg

private theorem unitSquareMeasure_real_univ :
    unitSquareMeasure.real (Set.univ : Set UnitSquare) = 1 := by
  simp [Measure.real]

theorem graphonRandomMass_le_one (W : Graphon) : graphonRandomMass W ≤ 1 := by
  rw [← unitSquareMeasure_real_univ]
  exact measureReal_mono (subset_univ _)

theorem graphonOneMass_le_one (W : Graphon) : graphonOneMass W ≤ 1 := by
  rw [← unitSquareMeasure_real_univ]
  exact measureReal_mono (subset_univ _)

theorem graphonMiddleBandMass_le_one (W : Graphon) (theta : ℝ) :
    graphonMiddleBandMass W theta ≤ 1 := by
  rw [← unitSquareMeasure_real_univ]
  exact measureReal_mono (subset_univ _)

theorem graphonUpperBandMass_le_one (W : Graphon) (theta : ℝ) :
    graphonUpperBandMass W theta ≤ 1 := by
  rw [← unitSquareMeasure_real_univ]
  exact measureReal_mono (subset_univ _)

theorem graphonRandomMass_mem_Icc (W : Graphon) :
    graphonRandomMass W ∈ Icc (0 : ℝ) 1 :=
  ⟨graphonRandomMass_nonneg W, graphonRandomMass_le_one W⟩

theorem graphonOneMass_mem_Icc (W : Graphon) :
    graphonOneMass W ∈ Icc (0 : ℝ) 1 :=
  ⟨graphonOneMass_nonneg W, graphonOneMass_le_one W⟩

theorem graphonMiddleBandMass_mem_Icc (W : Graphon) (theta : ℝ) :
    graphonMiddleBandMass W theta ∈ Icc (0 : ℝ) 1 :=
  ⟨graphonMiddleBandMass_nonneg W theta, graphonMiddleBandMass_le_one W theta⟩

theorem graphonUpperBandMass_mem_Icc (W : Graphon) (theta : ℝ) :
    graphonUpperBandMass W theta ∈ Icc (0 : ℝ) 1 :=
  ⟨graphonUpperBandMass_nonneg W theta, graphonUpperBandMass_le_one W theta⟩

theorem graphonRandomRegion_disjoint_oneRegion (W : Graphon) :
    Disjoint (graphonRandomRegion W) (graphonOneRegion W) := by
  rw [Set.disjoint_left]
  intro z hzRandom hzOne
  exact (ne_of_lt hzRandom.2) hzOne

theorem graphonRandomMass_add_oneMass_le_one (W : Graphon) :
    graphonRandomMass W + graphonOneMass W ≤ 1 := by
  unfold graphonRandomMass graphonOneMass
  rw [← measureReal_union (graphonRandomRegion_disjoint_oneRegion W)
    (measurableSet_graphonOneRegion W)]
  rw [← unitSquareMeasure_real_univ]
  exact measureReal_mono (subset_univ _)

theorem graphonRandomMass_le_one_sub_oneMass (W : Graphon) :
    graphonRandomMass W ≤ 1 - graphonOneMass W := by
  linarith [graphonRandomMass_add_oneMass_le_one W]

theorem graphon_value_eq_zero_or_one_of_not_mem_randomRegion
    (W : Graphon) {z : UnitSquare} (hz : z ∉ graphonRandomRegion W) :
    W.value z = 0 ∨ W.value z = 1 := by
  by_cases hzero : W.value z = 0
  · exact Or.inl hzero
  right
  by_contra hone
  apply hz
  exact ⟨lt_of_le_of_ne (W.value_nonneg z) (Ne.symm hzero),
    lt_of_le_of_ne (W.value_le_one z) hone⟩

theorem graphon_value_eq_zero_of_not_mem_randomRegion_union_oneRegion
    (W : Graphon) {z : UnitSquare}
    (hz : z ∉ graphonRandomRegion W ∪ graphonOneRegion W) :
    W.value z = 0 := by
  rcases graphon_value_eq_zero_or_one_of_not_mem_randomRegion W
      (fun hzRandom ↦ hz (Or.inl hzRandom)) with hzero | hone
  · exact hzero
  · exact (hz (Or.inr hone)).elim

/-! ## Nonzero region -/

/-- The region on which the canonical graphon value is nonzero. -/
def graphonNonzeroRegion (W : Graphon) : Set UnitSquare :=
  {z | W.value z ≠ 0}

@[measurability]
theorem measurableSet_graphonNonzeroRegion (W : Graphon) :
    MeasurableSet (graphonNonzeroRegion W) := by
  exact (W.measurable_value (measurableSet_singleton 0)).compl

/-- Real measure of the nonzero region of a graphon. -/
noncomputable def graphonNonzeroMass (W : Graphon) : ℝ :=
  unitSquareMeasure.real (graphonNonzeroRegion W)

@[simp] theorem graphonNonzeroMass_nonneg (W : Graphon) :
    0 ≤ graphonNonzeroMass W :=
  measureReal_nonneg

theorem graphonNonzeroRegion_eq_randomRegion_union_oneRegion (W : Graphon) :
    graphonNonzeroRegion W =
      graphonRandomRegion W ∪ graphonOneRegion W := by
  ext z
  simp only [graphonNonzeroRegion, graphonRandomRegion, graphonOneRegion,
    Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hz
    rcases lt_or_eq_of_le (W.value_le_one z) with hlt | hone
    · left
      exact ⟨lt_of_le_of_ne (W.value_nonneg z) (Ne.symm hz), hlt⟩
    · exact Or.inr hone
  · rintro (⟨hpos, _⟩ | hone)
    · exact hpos.ne'
    · simpa [hone]

/-- The nonzero mass is the sum of the random and one-valued masses. -/
theorem graphonNonzeroMass_eq_randomMass_add_oneMass (W : Graphon) :
    graphonNonzeroMass W =
      graphonRandomMass W + graphonOneMass W := by
  unfold graphonNonzeroMass graphonRandomMass graphonOneMass
  rw [graphonNonzeroRegion_eq_randomRegion_union_oneRegion,
    measureReal_union (graphonRandomRegion_disjoint_oneRegion W)
      (measurableSet_graphonOneRegion W)]

/-- Compatibility spelling with the one-valued contribution first. -/
theorem graphonNonzeroMass_eq_oneMass_add_randomMass (W : Graphon) :
    graphonNonzeroMass W =
      graphonOneMass W + graphonRandomMass W := by
  rw [graphonNonzeroMass_eq_randomMass_add_oneMass, add_comm]

end InducedStars
