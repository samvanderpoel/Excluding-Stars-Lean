import InducedStars.Graphon.Equivalence
import InducedStars.Graphon.LevelSets
import InducedStars.Graphon.TypeColoring
import InducedStars.Graphon.TypeGraphonSequence
import InducedStars.EdgeColoring.Extremal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Tactic

/-!
# The graphon kth-order Mantel inequality

This module transfers the finite colored kth-order Mantel inequality through
the Type Graphon Sequence Lemma.  A fixed positive threshold first separates
middle-valued cells from upper-valued cells.  Letting the threshold tend to
zero then gives the exact comparison between the random and one-valued
regions of an induced-star-free graphon.
-/

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Topology unitInterval

namespace InducedStars

open ColoredGraph

/-! ## Equal-cell regions and elementary measure estimates -/

/-- A finite union of canonical equal-cell rectangles. -/
def equalCellPairRegion {q : ℕ} (s : Finset (Fin q × Fin q)) : Set UnitSquare :=
  ⋃ p ∈ s, equalCell p.1 ×ˢ equalCell p.2

@[measurability] theorem measurableSet_equalCellPairRegion {q : ℕ}
    (s : Finset (Fin q × Fin q)) : MeasurableSet (equalCellPairRegion s) := by
  unfold equalCellPairRegion
  measurability

theorem measureReal_equalCell_prod {q : ℕ} (hq : 0 < q) (i j : Fin q) :
    unitSquareMeasure.real (equalCell i ×ˢ equalCell j) = (1 / (q : ℝ)) ^ 2 := by
  rw [Measure.real, show unitSquareMeasure (equalCell i ×ˢ equalCell j) =
      ENNReal.ofReal (1 / (q : ℝ)) ^ 2 from volume_equalCell_prod i j,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal]
  positivity

theorem measureReal_equalCellPairRegion {q : ℕ} (hq : 0 < q)
    (s : Finset (Fin q × Fin q)) :
    unitSquareMeasure.real (equalCellPairRegion s) =
      (s.card : ℝ) * (1 / (q : ℝ)) ^ 2 := by
  classical
  unfold equalCellPairRegion
  rw [measureReal_biUnion_finset]
  · simp_rw [measureReal_equalCell_prod hq]
    simp
  · intro a _ha b _hb hab
    exact pairwise_disjoint_equalCell_prod hab
  · intro p _hp
    exact (measurableSet_equalCell p.1).prod (measurableSet_equalCell p.2)

/-- The equal-cell red region has exactly the normalized red area of its
finite coloring. -/
theorem measureReal_equalCellPairRegion_orderedRed_eq
    {q : ℕ} (hq : 0 < q) (C : ColoredGraph (Fin q)) :
    unitSquareMeasure.real
        (equalCellPairRegion (C.orderedColorPairs .red)) =
      C.normalizedRedArea := by
  rw [measureReal_equalCellPairRegion hq,
    C.normalizedRedArea_eq_card_orderedRedPairs]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-- The equal-cell completed-blue region (whose ordered-pair accessor
includes the diagonal) has exactly the normalized blue-plus-diagonal area. -/
theorem measureReal_equalCellPairRegion_orderedBlue_eq
    {q : ℕ} (hq : 0 < q) (C : ColoredGraph (Fin q)) :
    unitSquareMeasure.real
        (equalCellPairRegion (C.orderedColorPairs .blue)) =
      C.normalizedBlueDiagonalArea := by
  rw [measureReal_equalCellPairRegion hq,
    C.normalizedBlueDiagonalArea_eq_card_orderedBluePairs hq]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

/-- The set where two canonical graphon values differ by at least `θ`. -/
def graphonL1BadSet (U W : Graphon) (θ : ℝ) : Set UnitSquare :=
  {z | θ ≤ |U.value z - W.value z|}

@[measurability] theorem measurableSet_graphonL1BadSet (U W : Graphon) (θ : ℝ) :
    MeasurableSet (graphonL1BadSet U W θ) := by
  unfold graphonL1BadSet
  measurability

theorem graphonL1BadSet_mul_le (U W : Graphon) (θ : ℝ) :
    θ * unitSquareMeasure.real (graphonL1BadSet U W θ) ≤ graphonL1Dist U W := by
  let f : UnitSquare → ℝ := fun z ↦ |U.value z - W.value z|
  have hf0 : 0 ≤ᵐ[unitSquareMeasure] f := Eventually.of_forall fun _ ↦ abs_nonneg _
  have hfint : Integrable f unitSquareMeasure := by
    apply Integrable.of_bound
      (continuous_abs.measurable.comp
        (U.measurable_value.sub W.measurable_value)).aestronglyMeasurable 1
    filter_upwards [] with z
    simp only [Function.comp_apply, Pi.sub_apply, Real.norm_eq_abs, abs_abs]
    exact abs_le.2 ⟨by linarith [U.value_nonneg z, W.value_le_one z],
      by linarith [U.value_le_one z, W.value_nonneg z]⟩
  have h := mul_meas_ge_le_integral_of_nonneg hf0 hfint θ
  change θ * unitSquareMeasure.real (graphonL1BadSet U W θ) ≤ _ at h
  calc
    θ * unitSquareMeasure.real (graphonL1BadSet U W θ) ≤
        ∫ z, |U.value z - W.value z| ∂unitSquareMeasure := h
    _ = ∫ z, |U z - W z| ∂unitSquareMeasure := by
      apply integral_congr_ae
      filter_upwards [U.value_ae_eq, W.value_ae_eq] with z hU hW
      rw [hU, hW]
    _ = graphonL1Dist U W := (graphonL1Dist_eq_integral U W).symm

theorem graphonL1BadSet_measure_le (U W : Graphon) {θ : ℝ} (hθ : 0 < θ) :
    unitSquareMeasure.real (graphonL1BadSet U W θ) ≤ graphonL1Dist U W / θ := by
  rw [le_div_iff₀ hθ]
  simpa [mul_comm] using graphonL1BadSet_mul_le U W θ

open Regularity

/-- The diagonal and oriented irregular cluster cells have area at most
`1/q + 2η`. The harmless factor two avoids asymptotic floor arithmetic. -/
theorem badClusterPairs_area_le {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {η : ℝ} (P : RegularPartition G η)
    (hq : 0 < P.clusterCount) (hη : 0 ≤ η) :
    ((badClusterPairs η P).card : ℝ) *
        (1 / (P.clusterCount : ℝ)) ^ 2 ≤
      1 / (P.clusterCount : ℝ) + 2 * η := by
  let q := P.clusterCount
  have hqℝ : (0 : ℝ) < q := by exact_mod_cast hq
  have hchoose : ((Nat.choose q 2 : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow q 2
  have hirr : ((irregularPairs G η P.clusters).card : ℝ) ≤
      η * (q : ℝ) ^ 2 :=
    P.irregular_pair_card_le.trans
      (mul_le_mul_of_nonneg_left hchoose hη)
  have hbad : (((badClusterPairs η P).card : ℕ) : ℝ) ≤
      (q : ℝ) + 2 * (η * (q : ℝ) ^ 2) := by
    calc
      (((badClusterPairs η P).card : ℕ) : ℝ) ≤
          (q : ℝ) + 2 * ((irregularPairs G η P.clusters).card : ℝ) := by
        exact_mod_cast card_badClusterPairs_le P
      _ ≤ (q : ℝ) + 2 * (η * (q : ℝ) ^ 2) := by gcongr
  calc
    ((badClusterPairs η P).card : ℝ) * (1 / (q : ℝ)) ^ 2 ≤
        ((q : ℝ) + 2 * (η * (q : ℝ) ^ 2)) *
          (1 / (q : ℝ)) ^ 2 := by gcongr
    _ = 1 / (q : ℝ) + 2 * η := by
      field_simp [hqℝ.ne']

/-- Real measures are monotone under almost-everywhere set inclusion. -/
theorem measureReal_mono_ae {s t : Set UnitSquare}
    (h : s ≤ᵐ[unitSquareMeasure] t) :
    unitSquareMeasure.real s ≤ unitSquareMeasure.real t := by
  rw [Measure.real, Measure.real]
  exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae h)

/-- A three-set union bound for real-valued measure. -/
theorem measureReal_union_union_le (s t u : Set UnitSquare) :
    unitSquareMeasure.real (s ∪ (t ∪ u)) ≤
      unitSquareMeasure.real s + unitSquareMeasure.real t +
        unitSquareMeasure.real u := by
  calc
    unitSquareMeasure.real (s ∪ (t ∪ u)) ≤
        unitSquareMeasure.real s + unitSquareMeasure.real (t ∪ u) :=
      measureReal_union_le _ _
    _ ≤ unitSquareMeasure.real s +
        (unitSquareMeasure.real t + unitSquareMeasure.real u) := by
      gcongr
      exact measureReal_union_le _ _
    _ = _ := by ring

/-! ## Cellwise comparison for a Type graphon -/

/-- Simultaneous canonical-value formula on every equal-cell rectangle of a
Type graphon.  The exceptional endpoint lines are irrelevant here; coverage
of the square is supplied separately by `ae_mem_iUnion_equalCell_prod`. -/
theorem typeGraphon_value_ae_eq_on_all_cells
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (T : RegularityType G η θ ℓ) :
    ∀ᵐ z ∂unitSquareMeasure,
      ∀ i j : Fin T.partition.clusterCount,
        z ∈ equalCell i ×ˢ equalCell j →
          (typeGraphon T).value z =
            graphDensity G (T.partition.clusters i) (T.partition.clusters j) := by
  apply (Filter.eventually_all.2 fun i ↦
    Filter.eventually_all.2 fun j ↦ ?_)
  filter_upwards [(typeGraphon T).value_ae_eq,
    typeGraphon_ae_eq_on_cell T i j] with z hvalue hcell
  intro hz
  exact hvalue.trans (hcell hz)

/-- Outside the regularity and `L¹` exceptional sets, the middle band of an
`L¹` target is covered by red cells of the completed Type coloring. -/
theorem graphonMiddleBand_ae_subset_typeRedRegion
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (T : RegularityType G η θ ℓ)
    (hq : 0 < T.partition.clusterCount) (U : Graphon) :
    graphonMiddleBand U θ ≤ᵐ[unitSquareMeasure]
      ((equalCellPairRegion
          ((typeCompleteColoring T).orderedColorPairs .red) ∪
        (equalCellPairRegion (badClusterPairs η T.partition) ∪
          graphonL1BadSet (typeGraphon T) U θ)) : Set UnitSquare) := by
  classical
  filter_upwards [typeGraphon_value_ae_eq_on_all_cells T,
    ae_mem_iUnion_equalCell_prod hq] with z hcell hcover
  intro hzMiddle
  by_cases hzL1 : z ∈ graphonL1BadSet (typeGraphon T) U θ
  · exact Or.inr (Or.inr hzL1)
  obtain ⟨p, hpCell⟩ := Set.mem_iUnion.1 hcover
  let i := p.1
  let j := p.2
  have hzCell : z ∈ equalCell i ×ˢ equalCell j := hpCell
  by_cases hpBad : (i, j) ∈ badClusterPairs η T.partition
  · right; left
    unfold equalCellPairRegion
    simp only [Set.mem_iUnion]
    exact ⟨(i, j), hpBad, hzCell⟩
  have hgood : i ≠ j ∧
      IsRegularPair G η (T.partition.clusters i) (T.partition.clusters j) := by
    simpa [badClusterPairs] using hpBad
  have hadj : T.coloredGraph.graph.Adj i j := by
    exact (T.partition.regularPairGraph_adj i j).2 hgood
  have habs : |(typeGraphon T).value z - U.value z| < θ := by
    simpa [graphonL1BadSet, not_le] using hzL1
  have hdensity :
      θ ≤ graphDensity G (T.partition.clusters i) (T.partition.clusters j) ∧
        graphDensity G (T.partition.clusters i) (T.partition.clusters j) ≤ 1 - θ := by
    rw [← hcell i j hzCell]
    have habs' := (abs_lt.mp habs)
    constructor <;> linarith [hzMiddle.1, hzMiddle.2]
  have hredEdge : T.coloredGraph.getEdgeColor i j hadj = .red :=
    (edgeColor_eq_red_iff T.partition T.delta_lt_half.le
      T.vertexColor hadj).2 hdensity
  have hred : (typeCompleteColoring T).color i j = .red :=
    (typeCompleteColoring_color_eq_red_iff T i j).2 ⟨hadj, hredEdge⟩
  have hpRed : (i, j) ∈ (typeCompleteColoring T).orderedColorPairs .red :=
    (ColoredGraph.mem_orderedColorPairs _ _ _ _).2 hred
  left
  unfold equalCellPairRegion
  simp only [Set.mem_iUnion]
  exact ⟨(i, j), hpRed, hzCell⟩

/-- Outside the regularity and `L¹` exceptional sets, completed-blue cells
(including diagonal cells) are covered by the upper band of the `L¹` target. -/
theorem typeBlueDiagonalRegion_ae_subset_graphonUpperBand
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (T : RegularityType G η θ ℓ) (U : Graphon) :
    equalCellPairRegion
        ((typeCompleteColoring T).orderedColorPairs .blue) ≤ᵐ[unitSquareMeasure]
      ((graphonUpperBand U θ ∪
        (equalCellPairRegion (badClusterPairs η T.partition) ∪
          graphonL1BadSet (typeGraphon T) U θ)) : Set UnitSquare) := by
  classical
  filter_upwards [typeGraphon_value_ae_eq_on_all_cells T] with z hcell
  intro hzBlue
  rcases Set.mem_iUnion.1 hzBlue with ⟨p, hp⟩
  rcases Set.mem_iUnion.1 hp with ⟨hpBlue, hzCell⟩
  let i := p.1
  let j := p.2
  change z ∈ equalCell i ×ˢ equalCell j at hzCell
  by_cases hzL1 : z ∈ graphonL1BadSet (typeGraphon T) U θ
  · exact Or.inr (Or.inr hzL1)
  by_cases hpBad : (i, j) ∈ badClusterPairs η T.partition
  · right; left
    unfold equalCellPairRegion
    simp only [Set.mem_iUnion]
    exact ⟨(i, j), hpBad, hzCell⟩
  have hgood : i ≠ j ∧
      IsRegularPair G η (T.partition.clusters i) (T.partition.clusters j) := by
    simpa [badClusterPairs] using hpBad
  have hadj : T.coloredGraph.graph.Adj i j := by
    exact (T.partition.regularPairGraph_adj i j).2 hgood
  have hblue : (typeCompleteColoring T).color i j = .blue :=
    (ColoredGraph.mem_orderedColorPairs _ _ _ _).1 hpBlue
  obtain hnotAdj | ⟨_hadj, hblueEdge⟩ :=
    (typeCompleteColoring_color_eq_blue_iff T i j).1 hblue
  · exact (hnotAdj hadj).elim
  have hdensity : 1 - θ <
      graphDensity G (T.partition.clusters i) (T.partition.clusters j) :=
    (edgeColor_eq_blue_iff T.partition T.delta_lt_half.le
      T.vertexColor hadj).1 (by simpa only [proof_irrel_heq] using hblueEdge)
  have habs : |(typeGraphon T).value z - U.value z| < θ := by
    simpa [graphonL1BadSet, not_le] using hzL1
  left
  change 1 - 2 * θ < U.value z
  rw [hcell i j hzCell] at habs
  have habs' := (abs_lt.mp habs)
  linarith

/-- The middle-band and blue-cell estimates with the two exceptional areas
displayed explicitly. -/
theorem typeGraphon_cell_error_estimate
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} {ℓ : ℕ} (T : RegularityType G η θ ℓ)
    (hq : 0 < T.partition.clusterCount) (U : Graphon) :
    graphonMiddleBandMass U θ ≤
        unitSquareMeasure.real (equalCellPairRegion
          ((typeCompleteColoring T).orderedColorPairs .red)) +
        unitSquareMeasure.real
          (equalCellPairRegion (badClusterPairs η T.partition)) +
        unitSquareMeasure.real (graphonL1BadSet (typeGraphon T) U θ) ∧
      unitSquareMeasure.real (equalCellPairRegion
          ((typeCompleteColoring T).orderedColorPairs .blue)) ≤
        graphonUpperBandMass U θ +
          unitSquareMeasure.real
            (equalCellPairRegion (badClusterPairs η T.partition)) +
          unitSquareMeasure.real (graphonL1BadSet (typeGraphon T) U θ) := by
  constructor
  · unfold graphonMiddleBandMass
    exact (measureReal_mono_ae
      (graphonMiddleBand_ae_subset_typeRedRegion T hq U)).trans
        (measureReal_union_union_le _ _ _)
  · unfold graphonUpperBandMass
    exact (measureReal_mono_ae
      (typeBlueDiagonalRegion_ae_subset_graphonUpperBand T U)).trans
        (measureReal_union_union_le _ _ _)

/-! ## The finite Mantel inequality on one Type level -/

/-- A single induced-star-free Type level satisfies the thresholded graphon
Mantel estimate, up to the explicit regularity, diagonal, and `L¹` errors. -/
theorem typeGraphon_middleBandMass_le_delta_mul_upperBandMass_add_error
    {n k : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {η θ : ℝ} (T : RegularityType G η θ (k + 1))
    (hk : 3 ≤ k) (hq : 0 < T.partition.clusterCount)
    (hfree : ¬ InducedEmbeds (inducedStar k) G) (U : Graphon) :
    graphonMiddleBandMass U θ ≤
      (delta k : ℝ) * graphonUpperBandMass U θ +
        ((delta k : ℝ) + 1) *
          (1 / (T.partition.clusterCount : ℝ) + 2 * η +
            graphonL1Dist (typeGraphon T) U / θ) := by
  classical
  let C := typeCompleteColoring T
  have hC : C ∈ ColoredGraph.Ck k T.partition.clusterCount :=
    typeCompleteColoring_mem_Ck hk T hfree
  have hcell := typeGraphon_cell_error_estimate T hq U
  have hfinite :
      unitSquareMeasure.real
          (equalCellPairRegion (C.orderedColorPairs .red)) ≤
        (delta k : ℝ) * unitSquareMeasure.real
          (equalCellPairRegion (C.orderedColorPairs .blue)) := by
    rw [measureReal_equalCellPairRegion_orderedRed_eq hq,
      measureReal_equalCellPairRegion_orderedBlue_eq hq]
    exact C.normalizedRedArea_le_delta_mul_normalizedBlueDiagonalArea hk hq hC
  have hbad :
      unitSquareMeasure.real
          (equalCellPairRegion (badClusterPairs η T.partition)) ≤
        1 / (T.partition.clusterCount : ℝ) + 2 * η := by
    rw [measureReal_equalCellPairRegion hq]
    exact badClusterPairs_area_le T.partition hq T.epsilon_pos.le
  have hL1 :
      unitSquareMeasure.real (graphonL1BadSet (typeGraphon T) U θ) ≤
        graphonL1Dist (typeGraphon T) U / θ :=
    graphonL1BadSet_measure_le _ _ T.delta_pos
  let redArea := unitSquareMeasure.real
    (equalCellPairRegion (C.orderedColorPairs .red))
  let blueArea := unitSquareMeasure.real
    (equalCellPairRegion (C.orderedColorPairs .blue))
  let badArea := unitSquareMeasure.real
    (equalCellPairRegion (badClusterPairs η T.partition))
  let l1Area := unitSquareMeasure.real (graphonL1BadSet (typeGraphon T) U θ)
  have hdelta : 0 ≤ (delta k : ℝ) := Nat.cast_nonneg _
  have hmiddle : graphonMiddleBandMass U θ ≤
      redArea + badArea + l1Area := by
    simpa [redArea, badArea, l1Area, C] using hcell.1
  have hfinite' : redArea ≤ (delta k : ℝ) * blueArea := by
    simpa [redArea, blueArea] using hfinite
  have hblue : blueArea ≤
      graphonUpperBandMass U θ + badArea + l1Area := by
    simpa [blueArea, badArea, l1Area, C] using hcell.2
  have hbad' : badArea ≤
      1 / (T.partition.clusterCount : ℝ) + 2 * η := by
    simpa [badArea] using hbad
  have hL1' : l1Area ≤ graphonL1Dist (typeGraphon T) U / θ := by
    simpa [l1Area] using hL1
  have herr : badArea + l1Area ≤
      (1 / (T.partition.clusterCount : ℝ) + 2 * η) +
        graphonL1Dist (typeGraphon T) U / θ :=
    add_le_add hbad' hL1'
  calc
    graphonMiddleBandMass U θ ≤ redArea + badArea + l1Area := hmiddle
    _ ≤ (delta k : ℝ) * blueArea + badArea + l1Area := by
      linarith
    _ ≤ (delta k : ℝ) *
          (graphonUpperBandMass U θ + badArea + l1Area) + badArea + l1Area := by
      have hmul := mul_le_mul_of_nonneg_left hblue hdelta
      linarith
    _ = (delta k : ℝ) * graphonUpperBandMass U θ +
          ((delta k : ℝ) + 1) * (badArea + l1Area) := by ring
    _ ≤ (delta k : ℝ) * graphonUpperBandMass U θ +
          ((delta k : ℝ) + 1) *
            ((1 / (T.partition.clusterCount : ℝ) + 2 * η) +
              graphonL1Dist (typeGraphon T) U / θ) := by
      have hmul :=
        mul_le_mul_of_nonneg_left herr (add_nonneg hdelta zero_le_one)
      linarith
    _ = _ := by ring

/-! ## Passage through the Type graphon sequence -/

/-- Fixed-threshold graphon form of the `k`th-order Mantel inequality. -/
theorem graphonMiddleBandMass_le_delta_mul_upperBandMass
    (k : ℕ) (hk : 3 ≤ k) (W : Graphon)
    (hfree : graphonInducedDensity (inducedStar k) W = 0)
    (θ : ℝ) (hθ : 0 < θ) (hθquarter : θ < 1 / 4) :
    graphonMiddleBandMass W θ ≤
      ((k - 2 : ℕ) : ℝ) * graphonUpperBandMass W θ := by
  have hθhalf : θ < 1 / 2 := by linarith
  obtain ⟨R⟩ := typeGraphonSequence (inducedStar k) W θ hθ hθhalf hfree
  let q : ℕ → ℕ := fun m ↦
    let _ : DecidableRel (R.host m).Adj := R.hostAdjDecidable m
    (R.typeData m).partition.clusterCount
  let err : ℕ → ℝ := fun m ↦
    1 / (q m : ℝ) + 2 * R.eta m +
      graphonL1Dist (R.graphonSeq m) R.l1Limit / θ
  have hrecip : Tendsto
      (fun m ↦ 1 / (q m : ℝ)) atTop (nhds 0) := by
    apply (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    simpa [q] using R.clusterCount_tendsto
  have heta : Tendsto (fun m ↦ 2 * R.eta m) atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds (x := (2 : ℝ))).mul R.eta_tendsto
  have hL1 : Tendsto
      (fun m ↦ graphonL1Dist (R.graphonSeq m) R.l1Limit / θ)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      R.l1_tendsto.mul (tendsto_const_nhds (x := θ⁻¹))
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using (hrecip.add heta).add hL1
  have hq : ∀ᶠ m in atTop, 0 < q m := by
    have hqTop : Tendsto q atTop atTop := by
      simpa [q] using R.clusterCount_tendsto
    filter_upwards [hqTop.eventually (eventually_ge_atTop 1)]
      with m hm
    omega
  have hlevel : ∀ᶠ m in atTop,
      graphonMiddleBandMass R.l1Limit θ ≤
        (delta k : ℝ) * graphonUpperBandMass R.l1Limit θ +
          ((delta k : ℝ) + 1) * err m := by
    filter_upwards [hq] with m hqm
    letI : DecidableRel (R.host m).Adj := R.hostAdjDecidable m
    have hm := typeGraphon_middleBandMass_le_delta_mul_upperBandMass_add_error
      (R.typeData m) hk (by simpa [q] using hqm)
        (R.host_inducedFree m) R.l1Limit
    rw [← R.graphonSeq_eq m] at hm
    simpa [err] using hm
  have hrhs : Tendsto
      (fun m ↦ (delta k : ℝ) * graphonUpperBandMass R.l1Limit θ +
        ((delta k : ℝ) + 1) * err m)
      atTop
      (nhds ((delta k : ℝ) * graphonUpperBandMass R.l1Limit θ)) := by
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_const_nhds (x := ((delta k : ℝ) + 1))).mul herr))
  have hlimit : graphonMiddleBandMass R.l1Limit θ ≤
      (delta k : ℝ) * graphonUpperBandMass R.l1Limit θ :=
    ge_of_tendsto hrhs hlevel
  have hcut := R.cutDist_l1Limit_target_eq_zero
  calc
    graphonMiddleBandMass W θ = graphonMiddleBandMass R.l1Limit θ :=
      (graphonMiddleBandMass_eq_of_cutDist_eq_zero R.l1Limit W hcut θ).symm
    _ ≤ (delta k : ℝ) * graphonUpperBandMass R.l1Limit θ := hlimit
    _ = ((k - 2 : ℕ) : ℝ) * graphonUpperBandMass W θ := by
      rw [graphonUpperBandMass_eq_of_cutDist_eq_zero R.l1Limit W hcut θ]
      rfl

/-! ## Removing the threshold -/

/-- A positive threshold schedule tending to zero, starting at `1/8`. -/
def graphonMantelThreshold (n : ℕ) : ℝ :=
  1 / (8 * ((n : ℝ) + 1))

theorem graphonMantelThreshold_pos (n : ℕ) :
    0 < graphonMantelThreshold n := by
  unfold graphonMantelThreshold
  positivity

theorem graphonMantelThreshold_tendsto_zero :
    Tendsto graphonMantelThreshold atTop (nhds 0) := by
  have h :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 8 : ℝ)
  have heq : graphonMantelThreshold =
      fun n : ℕ ↦ (1 / 8 : ℝ) * (1 / ((n : ℝ) + 1)) := by
    funext n
    dsimp [graphonMantelThreshold]
    field_simp
  rw [heq]
  simpa using h

/-- Pointwise, shrinking middle-band membership eventually agrees with
membership in the random region. -/
theorem eventually_mem_graphonMiddleBand_graphonMantelThreshold_iff
    (W : Graphon) (z : UnitSquare) :
    ∀ᶠ n in atTop,
      z ∈ graphonMiddleBand W (graphonMantelThreshold n) ↔
        z ∈ graphonRandomRegion W := by
  by_cases hz : z ∈ graphonRandomRegion W
  · have hleft : ∀ᶠ n in atTop,
        graphonMantelThreshold n < W.value z / 2 :=
      (tendsto_order.1 graphonMantelThreshold_tendsto_zero).2 _ (half_pos hz.1)
    have hright : ∀ᶠ n in atTop,
        graphonMantelThreshold n < (1 - W.value z) / 2 :=
      (tendsto_order.1 graphonMantelThreshold_tendsto_zero).2 _
        (half_pos (sub_pos.mpr hz.2))
    filter_upwards [hleft, hright] with n hnleft hnright
    constructor
    · exact fun _ ↦ hz
    · intro _
      change 2 * graphonMantelThreshold n ≤ W.value z ∧
        W.value z ≤ 1 - 2 * graphonMantelThreshold n
      constructor <;> linarith
  · obtain hzero | hone :=
      graphon_value_eq_zero_or_one_of_not_mem_randomRegion W hz
    · filter_upwards [] with n
      constructor
      · intro hn
        change 2 * graphonMantelThreshold n ≤ W.value z ∧ _ at hn
        rw [hzero] at hn
        linarith [graphonMantelThreshold_pos n]
      · exact fun hn ↦ (hz hn).elim
    · filter_upwards [] with n
      constructor
      · intro hn
        change _ ∧ W.value z ≤ 1 - 2 * graphonMantelThreshold n at hn
        rw [hone] at hn
        linarith [graphonMantelThreshold_pos n]
      · exact fun hn ↦ (hz hn).elim

/-- Pointwise, shrinking upper-band membership eventually agrees with
membership in the one-valued region. -/
theorem eventually_mem_graphonUpperBand_graphonMantelThreshold_iff
    (W : Graphon) (z : UnitSquare) :
    ∀ᶠ n in atTop,
      z ∈ graphonUpperBand W (graphonMantelThreshold n) ↔
        z ∈ graphonOneRegion W := by
  by_cases hz : z ∈ graphonOneRegion W
  · filter_upwards [] with n
    constructor
    · exact fun _ ↦ hz
    · intro _
      change 1 - 2 * graphonMantelThreshold n < W.value z
      rw [hz]
      linarith [graphonMantelThreshold_pos n]
  · have hzlt : W.value z < 1 :=
      lt_of_le_of_ne (W.value_le_one z) hz
    have hevent : ∀ᶠ n in atTop,
        graphonMantelThreshold n < (1 - W.value z) / 2 :=
      (tendsto_order.1 graphonMantelThreshold_tendsto_zero).2 _
        (half_pos (sub_pos.mpr hzlt))
    filter_upwards [hevent] with n hn
    constructor
    · intro hnupper
      change 1 - 2 * graphonMantelThreshold n < W.value z at hnupper
      linarith
    · exact fun hnOne ↦ (hz hnOne).elim

/-- The closed middle-band masses converge upward to the random-region mass. -/
theorem graphonMiddleBandMass_graphonMantelThreshold_tendsto (W : Graphon) :
    Tendsto (fun n ↦ graphonMiddleBandMass W (graphonMantelThreshold n))
      atTop (nhds (graphonRandomMass W)) := by
  unfold graphonMiddleBandMass graphonRandomMass
  exact (ENNReal.tendsto_toReal (by finiteness)).comp
    (tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop unitSquareMeasure
      (fun n ↦ measurableSet_graphonMiddleBand W (graphonMantelThreshold n))
      (eventually_mem_graphonMiddleBand_graphonMantelThreshold_iff W))

/-- The upper-band masses converge downward to the one-region mass. -/
theorem graphonUpperBandMass_graphonMantelThreshold_tendsto (W : Graphon) :
    Tendsto (fun n ↦ graphonUpperBandMass W (graphonMantelThreshold n))
      atTop (nhds (graphonOneMass W)) := by
  unfold graphonUpperBandMass graphonOneMass
  exact (ENNReal.tendsto_toReal (by finiteness)).comp
    (tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure atTop unitSquareMeasure
      (fun n ↦ measurableSet_graphonUpperBand W (graphonMantelThreshold n))
      (eventually_mem_graphonUpperBand_graphonMantelThreshold_iff W))

/-- Any fixed-threshold inequality valid down to zero passes to the exact
random/one mass inequality. -/
theorem exact_mass_inequality_of_fixed_threshold
    (W : Graphon) (d : ℝ)
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 8 →
      graphonMiddleBandMass W θ ≤ d * graphonUpperBandMass W θ) :
    graphonRandomMass W ≤ d * graphonOneMass W := by
  apply le_of_tendsto_of_tendsto'
    (graphonMiddleBandMass_graphonMantelThreshold_tendsto W)
    ((tendsto_const_nhds.mul
      (graphonUpperBandMass_graphonMantelThreshold_tendsto W)))
  intro n
  apply h (graphonMantelThreshold n) (graphonMantelThreshold_pos n)
  unfold graphonMantelThreshold
  apply one_div_le_one_div_of_le (a := (8 : ℝ)) (by norm_num)
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

/-- Exact graphon `k`th-order Mantel inequality. -/
theorem graphonRandomMass_le_delta_oneMass
    (k : ℕ) (hk : 3 ≤ k) (W : Graphon)
    (hfree : graphonInducedDensity (inducedStar k) W = 0) :
    graphonRandomMass W ≤ ((k - 2 : ℕ) : ℝ) * graphonOneMass W := by
  apply exact_mass_inequality_of_fixed_threshold W ((k - 2 : ℕ) : ℝ)
  intro θ hθ hθeighth
  apply graphonMiddleBandMass_le_delta_mul_upperBandMass k hk W hfree θ hθ
  linarith

end InducedStars
