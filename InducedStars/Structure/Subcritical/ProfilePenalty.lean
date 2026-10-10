import InducedStars.Structure.Subcritical.AggregationProfileError
import InducedStars.Structure.Subcritical.ProfileMatchingZero
import InducedStars.Structure.Subcritical.ProfileComplexity
import InducedStars.Structure.Subcritical.LocalCompensationMain
import InducedStars.Structure.Subcritical.ProfileBound

/-!
# Geometric inputs for fixed-remainder profile counting

The same graph family supplies the close-division geometry, induced-star
freeness, exact edge count, and global minimality used in the profile proof.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon : ℝ}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}

/-- Finite structural inputs, with no probability or counting conclusion.
The same family supplies the maxima in the matching exponent throughout. -/
structure SubcriticalAggregationGeometry (hk : 3 ≤ k)
    (F : Finset (SimpleGraph (Fin n))) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k) (R₀ m : ℕ)
    (omega eta theta alpha delta epsilon : ℝ) : Prop where
  close : ∀ G ∈ F, Nonempty (SubcriticalCloseStructureResult hk G D L R₀
    omega eta theta alpha delta epsilon)
  free : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G
  edges : ∀ G ∈ F, (finiteGraphEdges G).card = m
  minimal : ∀ G ∈ F, ∀ E : SubcriticalDivision k (Fin n),
    subcriticalDefectCost G D ≤ subcriticalDefectCost G E

end InducedStars
