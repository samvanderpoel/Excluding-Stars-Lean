import InducedStars.Analysis.Entropy
import InducedStars.Analysis.RelativeEntropy

/-!
# Reusable scalar analysis

This import exposes the axiom-free base-two entropy and binary relative
entropy APIs under the neutral `DenseGraph` namespace.  Star parameters and
the paper's scalar optimizer remain outside this module.
-/

namespace DenseGraph

export InducedStars
  (log2 realLogTwo_pos realLogTwo_ne_zero log2_mul log2_div log2_pow log2_inv
    log2_pos log2_nonneg binaryEntropy binaryEntropy_eq_formula
    binaryEntropy_nonneg binaryEntropy_pos binaryEntropy_eq_zero
    binaryEntropy_continuous binaryEntropy_continuousOn
    binaryEntropy_differentiableAt hasDerivAt_binaryEntropy deriv_binaryEntropy
    binaryEntropy_strictConcaveOn binaryEntropy_strictConcaveOn_Ioo
    hasDerivAt_log2 binaryEntropy_sub_mul_log2_div
    binaryEntropy_add_one_sub_mul_log2_div entropyPerspective
    entropyPerspective_strictMono entropyPerspective_mono
    entropyPerspective_eq_iff binaryRelativeEntropy
    binaryRelativeEntropy_zero_eq_log2_inv
    binaryRelativeEntropy_one_eq_log2_inv
    binaryRelativeEntropy_eq_negEntropy_add
    binaryRelativeEntropy_eq_entropy_tangent binaryRelativeEntropy_continuousOn
    binaryRelativeEntropy_pos_of_ne binaryRelativeEntropy_nonneg
    binaryRelativeEntropy_eq_zero_iff)

end DenseGraph
