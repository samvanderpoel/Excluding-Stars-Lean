import DenseGraph.Analysis
import DenseGraph.Graphon.Inputs
import DenseGraph.Graphon.FiniteCutCover
import DenseGraph.Graphon.ZeroDistance
import InducedStars.Graphon.CellRelabeling
import InducedStars.Graphon.CutLimit
import InducedStars.Graphon.EquivalenceCore
import InducedStars.Graphon.Functionals
import InducedStars.Graphon.LabeledPartitionRelabeling
import InducedStars.Graphon.LimitInputs
import InducedStars.Graphon.PartitionAlignment
import InducedStars.Graphon.PartitionCut
import InducedStars.Graphon.RelabelingValueMass
import InducedStars.Graphon.SetDistance
import InducedStars.Graphon.StepEstimates
import InducedStars.Graphon.TypeSequenceLimits
import InducedStars.Graphon.ValueRegions

/-!
# Reusable graphon infrastructure

The implementation remains canonical in the established `InducedStars`
modules.  These exports provide a neutral, curated API without duplicating
proof bodies.  Published graph-limit facts are accepted only through the
explicit capability records in `DenseGraph.Graphon.Inputs`.
-/

namespace DenseGraph

export InducedStars
  (UnitInterval UnitSquare unitSquareMeasure Graphon IntegrableKernel
    graphonL1Dist MeasurableCut cutNorm cutNormNN GraphonRelabeling cutDist
    cutDistNN equalCell matrixGraphon graphGraphon finiteGraphEdges
    graphonPairValue graphonHomIntegrand graphonInducedIntegrand
    graphonHomDensity graphonInducedDensity constantGraphon zeroGraphon
    oneGraphon graphonValueFunctional graphonEntropy graphonEdgeDensity
    graphonRandomRegion graphonOneRegion graphonMiddleBand graphonUpperBand
    graphonNonzeroRegion graphonRandomMass graphonOneMass
    graphonMiddleBandMass graphonUpperBandMass graphonNonzeroMass
    measurableSet_graphonRandomRegion measurableSet_graphonOneRegion
    measurableSet_graphonMiddleBand measurableSet_graphonUpperBand
    measurableSet_graphonNonzeroRegion
    graphonRandomMass_nonneg graphonOneMass_nonneg
    graphonMiddleBandMass_nonneg graphonUpperBandMass_nonneg
    graphonNonzeroMass_nonneg graphonRandomMass_le_one
    graphonOneMass_le_one graphonMiddleBandMass_le_one
    graphonUpperBandMass_le_one graphonRandomMass_mem_Icc
    graphonOneMass_mem_Icc graphonMiddleBandMass_mem_Icc
    graphonUpperBandMass_mem_Icc graphonRandomRegion_disjoint_oneRegion
    graphonRandomMass_add_oneMass_le_one
    graphonRandomMass_le_one_sub_oneMass
    graphon_value_eq_zero_or_one_of_not_mem_randomRegion
    graphon_value_eq_zero_of_not_mem_randomRegion_union_oneRegion
    graphonNonzeroRegion_eq_randomRegion_union_oneRegion
    graphonNonzeroMass_eq_randomMass_add_oneMass
    graphonNonzeroMass_eq_oneMass_add_randomMass
    cutDistToSet finiteGraphFarFromSet
    diagonalProductMap measurePreserving_diagonalProductMap
    inducedExpansionGraph graphonInducedDensity_inclusionExclusion
    commonPullback_of_cutDist_eq_zero_of_inputs
    graphonValueLaw_eq_of_cutDist_eq_zero_of_inputs
    graphonValueIntegral_eq_of_cutDist_eq_zero_of_inputs
    graphonEntropy_eq_of_cutDist_eq_zero_of_inputs
    graphonEdgeDensity_eq_of_cutDist_eq_zero_of_input
    graphonInducedDensity_eq_of_cutDist_eq_zero_of_input)

namespace Graphon

export InducedStars.Graphon
  (NestedDensityMatrices refinementIndex matrixBlockAverage
    relabel_value_ae_eq measure_preimage_prodEquiv
    graphonOneRegion_relabel_ae_eq graphonRandomRegion_relabel_ae_eq
    graphonOneMass_relabel graphonRandomMass_relabel graphonNonzeroMass_relabel
    strictMono_extraction_comp
    tendsto_subsequence finite_constant_subsequence
    boundedNat_constant_subsequence finiteFamily_constant_subsequence)

end Graphon
end DenseGraph
