import DenseGraph.FiniteModels.WeightedGraph
import InducedStars.Graphon.Functionals
import InducedStars.Graphon.Metric

/-!
# Narrow published-input capabilities for reusable graphon arguments

These structures contain theorem-valued fields only.  They make the generic
proofs that consume graph-limit literature explicit and axiom-free: a client
may supply verified theorems, while the induced-star project supplies its
published assumptions in `InducedStars.PriorInstances`.
-/

open Filter MeasureTheory Set Topology

namespace DenseGraph

/-- Equality of all finite homomorphism densities at cut distance zero. -/
structure CutZeroHomDensityInput : Prop where
  homDensity_eq :
    ∀ (U W : InducedStars.Graphon), InducedStars.cutDist U W = 0 →
      ∀ (f : ℕ) (F : SimpleGraph (Fin f)),
        InducedStars.graphonHomDensity F U =
          InducedStars.graphonHomDensity F W

/-- A common-pullback theorem for graphons with equal homomorphism densities. -/
structure CommonPullbackInput : Prop where
  commonPullback :
    ∀ (U W : InducedStars.Graphon),
      (∀ (f : ℕ) (F : SimpleGraph (Fin f)),
        InducedStars.graphonHomDensity F U =
          InducedStars.graphonHomDensity F W) →
      ∃ φ ψ : InducedStars.UnitInterval → InducedStars.UnitInterval,
        MeasurePreserving φ volume volume ∧
        MeasurePreserving ψ volume volume ∧
        ∀ᵐ z ∂InducedStars.unitSquareMeasure,
          U.value (φ z.1, φ z.2) = W.value (ψ z.1, ψ z.2)

/-- Sequential upper semicontinuity of bit-valued graphon entropy. -/
structure EntropySemicontinuityInput : Prop where
  eventually_le :
    ∀ (Wseq : ℕ → InducedStars.Graphon) (W : InducedStars.Graphon),
      Tendsto (fun n ↦ InducedStars.cutDist (Wseq n) W) atTop (nhds 0) →
      ∀ ε > 0,
        ∀ᶠ n in atTop,
          InducedStars.graphonEntropy (Wseq n) ≤
            InducedStars.graphonEntropy W + ε

/-- Representative-level sequential compactness for the cut pseudometric. -/
structure SequentialCompactnessInput : Prop where
  compact_subsequence :
    ∀ W : ℕ → InducedStars.Graphon,
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ U : InducedStars.Graphon,
          Tendsto (fun n ↦ InducedStars.cutDist (W (σ n)) U)
            atTop (nhds 0)

/-- Qualitative finite alignment of equal-cell weighted graphons by a vertex
permutation.  This record deliberately exposes no quantitative modulus: a
consumer chooses a desired same-label cut error and receives some positive
graphon cut radius that guarantees it. -/
structure FiniteWeightedAlignmentInput : Prop where
  align :
    ∀ η : ℝ, 0 < η →
      ∃ τ : ℝ, 0 < τ ∧
        ∀ {n : ℕ}
          (A B : FiniteWeightedGraph (Fin n)),
            InducedStars.cutDist A.toGraphon B.toGraphon < τ →
              ∃ π : Equiv.Perm (Fin n),
                FiniteWeightedGraph.finiteLabeledCutDist
                    A (B.permute π) < η

end DenseGraph
