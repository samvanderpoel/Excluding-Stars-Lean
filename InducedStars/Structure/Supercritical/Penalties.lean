import InducedStars.Structure.Supercritical.Basic
import InducedStars.Structure.Supercritical.CleanSparsePenalty
import InducedStars.Structure.Supercritical.CountingSetup
import InducedStars.Structure.Supercritical.JointAbsorption
import InducedStars.Structure.Supercritical.MediumCandidateCounting
import InducedStars.Structure.Supercritical.MediumPenalty
import InducedStars.Structure.Supercritical.MatchingPenalty
import InducedStars.Structure.Supercritical.ProfileRealization
import InducedStars.Structure.Supercritical.ProfileReindexing

/-!
# Supercritical counting and defect-penalty interfaces

This facade exposes the completed deterministic counting setup used by the
supercritical penalties: unordered part-pair profiles, exact defect shifts,
profile windows and multiplicities, the defective/clean/medium/fixed-defect
families, realization of the canonical close profile, finite potential-star
candidate and overlap counts, fixed-count/Janson comparison, and the complete
paper-facing medium-degree, matching-defect, and clean sparse-set penalties.
It also exposes the axiom-free joint cross-plus-sparse absorption comparison
used in `lemma:super-Fstar`, including its signed-shift aggregate interface.  The
final supercritical aggregation remains downstream.
-/

namespace InducedStars

end InducedStars
