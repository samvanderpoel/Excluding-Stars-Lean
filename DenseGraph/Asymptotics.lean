import DenseGraph.FiniteModels
import DenseGraph.Asymptotics.SequentialUniformity
import DenseGraph.Combinatorics.SequenceExtension
import DenseGraph.Combinatorics.CompactSequenceUniformity
import DenseGraph.Combinatorics.PositiveSequenceUniformity
import InducedStars.Asymptotics.ExponentialRatio
import InducedStars.Asymptotics.GnpDensity
import InducedStars.Asymptotics.RepairScale

/-!
# Reusable dense-graph asymptotic arithmetic

This axiom-free layer collects graph-order normalization, canonical floor
edge sequences, edit-radius scaling, and normalized-log gap conversion.
Published entropy-transfer theorems remain opt-in through project wrappers.
-/

namespace DenseGraph

export InducedStars
  (quarter_square_le_completeEdgeCount completeEdgeCount_ge_quarter_square
    ratio_le_exp_neg_completeEdgeCount_of_normalizedLog_gap
    ratio_le_exp_neg_square_of_normalizedLog_gap floorEdgeCountSequence
    floorEdgeCountSequence_le_completeEdgeCount
    floorEdgeCountSequence_hasAsymptoticEdgeDensity
    fractionalEditRadius_orderedSquare_tendsto
    eventually_fractionalEditRadius_orderedSquare_lt)

end DenseGraph
