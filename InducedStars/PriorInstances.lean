import DenseGraph.FiniteModels.Janson
import DenseGraph.Graphon.Inputs
import DenseGraph.Regularity.Inputs
import InducedStars.PriorLiterature

/-!
# Project-specific prior-literature inputs

This module packages the published assumptions from
`InducedStars.PriorLiterature` as explicit values of the axiom-free input
interfaces used by reusable cores.
-/

namespace InducedStars.PriorInstances

universe u

/-- The Böttcher--Taraz--Würfl homogeneous-subpartition input used by the
project's regularity-type compatibility layer. -/
theorem homogeneousSubpartitionInput : DenseGraph.HomogeneousSubpartitionInput.{u} where
  homogeneousSubpartition := PriorLiterature.btwHomogeneousSubpartition

/-- The BCLSV cut-zero homomorphism-density input used by graphon-equivalence
compatibility theorems. -/
theorem cutZeroHomDensityInput : DenseGraph.CutZeroHomDensityInput where
  homDensity_eq := PriorLiterature.bclsvHomDensity_eq_of_cutDist_eq_zero

/-- The Borgs--Chayes--Lovász common-pullback input used by graphon-equivalence
compatibility theorems. -/
theorem commonPullbackInput : DenseGraph.CommonPullbackInput where
  commonPullback :=
    PriorLiterature.borgsChayesLovaszCommonPullback_of_homDensity_eq

/-- The Hatami--Janson--Szegedy sequential entropy-semicontinuity input. -/
theorem entropySemicontinuityInput : DenseGraph.EntropySemicontinuityInput where
  eventually_le :=
    PriorLiterature.hatamiJansonSzegedyEntropyUpperSemicontinuous

/-- The BCLSV representative-level sequential cut-compactness input. -/
theorem sequentialCompactnessInput : DenseGraph.SequentialCompactnessInput where
  compact_subsequence := PriorLiterature.bclsvGraphonSequentialCompactness

/-- The BCLSV finite weighted-alignment input used to replace a fractional
graphon relabeling by a permutation of equal finite vertex sets. -/
theorem finiteWeightedAlignmentInput : DenseGraph.FiniteWeightedAlignmentInput :=
  PriorLiterature.bclsvFiniteWeightedAlignment

/-- The Riordan--Warnke principal-upset Janson input used by the finite
defect-penalty arguments. -/
theorem principalJansonInput : DenseGraph.PrincipalJansonInput :=
  PriorLiterature.riordanWarnkePrincipalJanson

end InducedStars.PriorInstances
