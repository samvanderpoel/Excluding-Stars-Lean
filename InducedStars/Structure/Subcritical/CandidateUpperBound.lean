import InducedStars.Structure.Subcritical.ProfileAggregation
import InducedStars.Structure.Subcritical.CleanCanonical
import InducedStars.Structure.Subcritical.CandidateGeometry
import InducedStars.Structure.Subcritical.AggregationFeasibility

/-!
# The fixed-division and fixed-candidate cut-ball upper bounds

Paper: Lemma `lemma:NtaunmWUpperBdK1k`. The proof reserves both penalties before absorbing the uniformly bounded profile prefactors. Counts are
compared by multiplication, so a zero clean partition function is valid.
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

/-- Pure finite fixed-division upper bound, including a zero partition
function. No lower comparison or conditional-proportion claim is made. -/
theorem subcriticalDivision_card_le_cleanPartitionFunctionCore
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n)))
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta) :
    (F.card : ℝ) ≤ (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  have hclean := subcriticalCleanDivision_card_le_of_geometry hk F D L
    omega eta theta alpha delta epsilon P.localConditions.retained_order
    P.localConditions.eta_pos.le P.localConditions.theta_pos.le
    P.localConditions.retained_visible (by have := P.localConditions.alpha_small; linarith)
    P.residual.delta_pos.le P.retained_inverse homega P.epsilon_cap P.residual.sparse_scale
    A.free A.edges (fun G hG ↦ A.close G (mem_subcriticalCleanDivisionGraphFinset F G |>.mp hG).1)
  have hnonclean := subcriticalNoncleanDivision_card_le hk J F P hetaOne homega hdensity A hpoly
  have hpartition := card_subcriticalClean_add_nonclean (D := D) (eta := eta) (R₀ := R₀) F
  have hcleanR : ((subcriticalCleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      cleanRetainedPartitionFunction D eta R₀ m delta := by exact_mod_cast hclean
  have hpartitionR : (F.card : ℝ) =
      (subcriticalCleanDivisionGraphFinset F D eta R₀).card +
        (subcriticalNoncleanDivisionGraphFinset F D eta R₀).card := by
    exact_mod_cast hpartition.symm
  rw [hpartitionR]
  nlinarith only [hcleanR, hnonclean]

/-- Fixed-division specialization using the one common cut-to-division
bridge; the graph family inside every profile exponent is unchanged. -/
theorem subcriticalCandidateDivision_card_le_cleanPartitionFunction
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (D : SubcriticalDivision k (Fin n))
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon)) :
    ((subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D).card : ℝ) ≤
      (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        cleanRetainedPartitionFunction D eta R₀ m delta :=
  subcriticalDivision_card_le_cleanPartitionFunctionCore hk PriorInstances.principalJansonInput _
    P hetaOne homega hdensity
    (subcriticalCandidateDivision_aggregationGeometry hk hn D hbridge) hpoly

/-- Stronger than the paper's displayed cut-ball estimate: only a factor
`1+exp(-c*n)` is lost. Ordered compatible divisions occur once in this sum,
not once per compatibility witness and not with an extra cardinality factor. -/
theorem subcriticalCandidateCutBall_card_le_cleanPartitionSum
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon)) :
    ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
      (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        ∑ D ∈ subcriticalCompatibleDivisions k n L eta delta R₀,
          (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) := by
  rw [subcriticalCandidateCutBall_eq_biUnion_divisions hk hn hbridge,
    Finset.card_biUnion]
  · push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun D _ ↦
      subcriticalCandidateDivision_card_le_cleanPartitionFunction hk hn D P hetaOne homega
        hdensity hpoly hbridge
  · intro D _ E _ hDE
    exact subcriticalCandidateDivision_pairwiseDisjoint hk hn hDE

theorem subcriticalCandidateCutBall_card_le_exp_cleanPartitionSum
    (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
          L R₀ omega eta theta alpha delta epsilon)) :
    ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
      Real.exp (n : ℝ) *
        ∑ D ∈ subcriticalCompatibleDivisions k n L eta delta R₀,
          (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) := by
  apply (subcriticalCandidateCutBall_card_le_cleanPartitionSum hk hn P hetaOne homega
    hdensity hpoly hbridge).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hc := subcriticalAggregationConstant_pos hk P.localConditions.eta_pos
    P.localConditions.retained_order
  have hexp : Real.exp (-subcriticalAggregationConstant k eta R₀ * n) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Nat.cast_nonneg n))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n from le_trans (by omega) P.profile_order)
  linarith [Real.add_one_le_exp (n : ℝ)]

end InducedStars
