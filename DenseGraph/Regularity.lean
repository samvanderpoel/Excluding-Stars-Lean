import DenseGraph.Graphon
import DenseGraph.Regularity.Inputs
import DenseGraph.Regularity.ColoredRealization
import DenseGraph.Regularity.ColoredBlowUp
import DenseGraph.Regularity.ColoredEdit
import InducedStars.Regularity.Refinement
import InducedStars.Regularity.TypeCore
import InducedStars.Regularity.WeightedCut

/-!
# Reusable dense regularity infrastructure

This module contains ordinary and colored regularity data, prescribed
refinement, induced embeddings, and abstract Type structures.  The sole
published ingredient used by the paper's Type construction is represented by
`DenseGraph.HomogeneousSubpartitionInput`; no project instance is imported.
-/

namespace DenseGraph.Regularity

export InducedStars.Regularity
  (graphDensity IsRegularPair RegularPartition HomogeneousSubpartition
    InducedEmbeddingConfiguration InducedEmbeds EquitableInitialPartition
    EquipartitionTrimResult UniformRefiningRegularPartitionResult
    exists_inducedEmbedding_tolerance
    exists_uniformRefiningRegularPartition
    exists_uniformRefiningRegularPartition_with_minClusterSize
    TypeVertexColor RegularityColoredGraph reducedColoredGraph RegularityType
    existsTypeVertexColors_of_largeRegularPartition_of_embedding_withInput
    existsTypeVertexColors_of_largeRegularPartition_withInput
    inducedEmbeds_congr)

end DenseGraph.Regularity
