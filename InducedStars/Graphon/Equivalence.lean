import InducedStars.Graphon.EquivalenceCore
import InducedStars.PriorInstances

/-!
# Project instances of graphon-equivalence inputs

The reusable proofs live in `EquivalenceCore` and take narrow theorem-valued
capabilities.  This compatibility module preserves every established
`InducedStars.*` declaration and instantiates those proofs from the approved
published inputs.
-/

noncomputable section

open MeasureTheory

namespace InducedStars

theorem commonPullback_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    ∃ φ ψ : UnitInterval → UnitInterval,
      MeasurePreserving φ volume volume ∧
      MeasurePreserving ψ volume volume ∧
      ∀ᵐ z ∂unitSquareMeasure,
        U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2) :=
  commonPullback_of_cutDist_eq_zero_of_inputs
    PriorInstances.cutZeroHomDensityInput
    PriorInstances.commonPullbackInput U W hcut

theorem graphonValueLaw_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    Measure.map U.value unitSquareMeasure =
      Measure.map W.value unitSquareMeasure :=
  graphonValueLaw_eq_of_cutDist_eq_zero_of_inputs
    PriorInstances.cutZeroHomDensityInput
    PriorInstances.commonPullbackInput U W hcut

theorem graphonValueIntegral_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0)
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ z : UnitSquare, g (U.value z) ∂unitSquareMeasure) =
      ∫ z : UnitSquare, g (W.value z) ∂unitSquareMeasure :=
  graphonValueIntegral_eq_of_cutDist_eq_zero_of_inputs
    PriorInstances.cutZeroHomDensityInput
    PriorInstances.commonPullbackInput U W hcut g hg

theorem graphonEntropy_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonEntropy U = graphonEntropy W :=
  graphonEntropy_eq_of_cutDist_eq_zero_of_inputs
    PriorInstances.cutZeroHomDensityInput
    PriorInstances.commonPullbackInput U W hcut

theorem graphonEdgeDensity_eq_of_cutDist_eq_zero
    (U W : Graphon) (hcut : cutDist U W = 0) :
    graphonEdgeDensity U = graphonEdgeDensity W :=
  graphonEdgeDensity_eq_of_cutDist_eq_zero_of_input
    PriorInstances.cutZeroHomDensityInput U W hcut

theorem graphonInducedDensity_eq_of_cutDist_eq_zero {f : ℕ}
    (F : SimpleGraph (Fin f)) (U W : Graphon)
    (hcut : cutDist U W = 0) :
    graphonInducedDensity F U = graphonInducedDensity F W :=
  graphonInducedDensity_eq_of_cutDist_eq_zero_of_input
    PriorInstances.cutZeroHomDensityInput F U W hcut

end InducedStars
