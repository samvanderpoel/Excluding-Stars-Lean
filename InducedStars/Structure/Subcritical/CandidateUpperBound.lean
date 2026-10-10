import InducedStars.Structure.Subcritical.ProfileAggregation
import InducedStars.Structure.Subcritical.CleanCanonical
import InducedStars.Structure.Subcritical.CandidateGeometry
import InducedStars.Structure.Subcritical.AggregationFeasibility

/-!
# Polynomial reserve for retained-key profile counting

Paper: the polynomial absorption in `lemma:profile-bound-K1k` and
`lemma:NtaunmWUpperBdK1k`. This scalar reserve is uniform in the division.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical Topology
namespace InducedStars

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon tau : ℝ}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}

/-- A scalar, division-independent polynomial reserve. -/
def subcriticalAggregationPolynomialReserve
    (k n R₀ : ℕ) (eta theta : ℝ) : Prop :=
  ((n : ℝ) + 1) ^
      (2 * subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) +
        6 * subcriticalActiveIndexBound eta R₀ + 2) ≤
    Real.exp (subcriticalAggregationConstant k eta R₀ * n)

theorem eventually_subcriticalAggregationPolynomialReserve
    (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀) :
    ∀ᶠ n : ℕ in atTop, subcriticalAggregationPolynomialReserve k n R₀ eta theta := by
  exact DenseGraph.eventually_natCast_add_one_pow_le_exp_mul
    (2 * subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) +
      6 * subcriticalActiveIndexBound eta R₀ + 2)
    (subcriticalAggregationConstant_pos hk heta hR)

end InducedStars
