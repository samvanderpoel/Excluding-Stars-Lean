import InducedStars.Graphon.Metric
import InducedStars.Graphon.ValueRegions

/-!
# Value-region masses under graphon relabeling

This file proves directly from measure preservation that relabeling a graphon
preserves its one-valued, random-valued, and nonzero regions in measure.  It
does not pass through cut-distance invariance or graphon value laws.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace InducedStars

namespace Graphon

/-- The canonical pointwise representative of a relabeled graphon agrees
almost everywhere with the pullback of the original canonical
representative. -/
theorem relabel_value_ae_eq (W : Graphon) (e : GraphonRelabeling) :
    ∀ᵐ z ∂unitSquareMeasure,
      (W.relabel e).value z = W.value (e.prodEquiv z) := by
  filter_upwards [(W.relabel e).value_ae_eq,
    W.relabel_ae_eq_value e] with z hzValue hzRelabel
  rw [hzValue, hzRelabel]
  rfl

/-- A product relabeling preserves the measure of every measurable subset of
the unit square. -/
theorem measure_preimage_prodEquiv (e : GraphonRelabeling)
    {S : Set UnitSquare} (hS : MeasurableSet S) :
    unitSquareMeasure (e.prodEquiv ⁻¹' S) = unitSquareMeasure S := by
  calc
    unitSquareMeasure (e.prodEquiv ⁻¹' S) =
        (Measure.map e.prodEquiv unitSquareMeasure) S := by
      rw [Measure.map_apply e.prodEquiv.measurable hS]
    _ = unitSquareMeasure S := by
      rw [e.measurePreserving_prodEquiv.map_eq]

/-- The one-valued region of a relabeling is almost everywhere the pullback
of the original one-valued region. -/
theorem graphonOneRegion_relabel_ae_eq (W : Graphon)
    (e : GraphonRelabeling) :
    graphonOneRegion (W.relabel e) =ᵐ[unitSquareMeasure]
      e.prodEquiv ⁻¹' graphonOneRegion W := by
  filter_upwards [W.relabel_value_ae_eq e] with z hz
  change ((W.relabel e).value z = 1) =
    (W.value (e.prodEquiv z) = 1)
  rw [hz]

/-- The random-valued region of a relabeling is almost everywhere the
pullback of the original random-valued region. -/
theorem graphonRandomRegion_relabel_ae_eq (W : Graphon)
    (e : GraphonRelabeling) :
    graphonRandomRegion (W.relabel e) =ᵐ[unitSquareMeasure]
      e.prodEquiv ⁻¹' graphonRandomRegion W := by
  filter_upwards [W.relabel_value_ae_eq e] with z hz
  change (0 < (W.relabel e).value z ∧ (W.relabel e).value z < 1) =
    (0 < W.value (e.prodEquiv z) ∧ W.value (e.prodEquiv z) < 1)
  rw [hz]

/-- A graphon relabeling preserves the exact one-valued mass. -/
@[simp] theorem graphonOneMass_relabel (W : Graphon)
    (e : GraphonRelabeling) :
    graphonOneMass (W.relabel e) = graphonOneMass W := by
  unfold graphonOneMass
  calc
    unitSquareMeasure.real (graphonOneRegion (W.relabel e)) =
        unitSquareMeasure.real (e.prodEquiv ⁻¹' graphonOneRegion W) :=
      measureReal_congr (W.graphonOneRegion_relabel_ae_eq e)
    _ = unitSquareMeasure.real (graphonOneRegion W) := by
      exact congrArg ENNReal.toReal
        (measure_preimage_prodEquiv e (measurableSet_graphonOneRegion W))

/-- A graphon relabeling preserves the exact random-valued mass. -/
@[simp] theorem graphonRandomMass_relabel (W : Graphon)
    (e : GraphonRelabeling) :
    graphonRandomMass (W.relabel e) = graphonRandomMass W := by
  unfold graphonRandomMass
  calc
    unitSquareMeasure.real (graphonRandomRegion (W.relabel e)) =
        unitSquareMeasure.real (e.prodEquiv ⁻¹' graphonRandomRegion W) :=
      measureReal_congr (W.graphonRandomRegion_relabel_ae_eq e)
    _ = unitSquareMeasure.real (graphonRandomRegion W) := by
      exact congrArg ENNReal.toReal
        (measure_preimage_prodEquiv e (measurableSet_graphonRandomRegion W))

/-- A graphon relabeling preserves the exact nonzero mass. -/
@[simp] theorem graphonNonzeroMass_relabel (W : Graphon)
    (e : GraphonRelabeling) :
    graphonNonzeroMass (W.relabel e) = graphonNonzeroMass W := by
  rw [graphonNonzeroMass_eq_oneMass_add_randomMass,
    graphonNonzeroMass_eq_oneMass_add_randomMass,
    W.graphonOneMass_relabel e, W.graphonRandomMass_relabel e]

end Graphon

end InducedStars
