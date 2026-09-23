import InducedStars.Structure.Subcritical.AggregationProfileError
import InducedStars.Structure.Subcritical.ProfileMatchingZero
import InducedStars.Structure.Subcritical.ProfileComplexity
import InducedStars.Structure.Subcritical.LocalCompensationMain
import InducedStars.Structure.Subcritical.ProfileBound

/-!
# The combined finite profile penalty

All three completed estimates are applied to exactly the same graph family.
The polynomial prefactor is retained, and a uniform portion of both
the root and the matching rate is reserved before summing profiles.
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

theorem subcriticalProfilePenaltyCore
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
        (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) *
        Real.exp (-(48 * subcriticalAggregationConstant k eta R₀) *
          subcriticalProfileComplexity p * n) := by
  by_cases hne : (subcriticalProfileClassGraphFinset F alpha p).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G₀, hG₀⟩ := hne
  obtain ⟨hG₀F, hp⟩ := mem_subcriticalProfileClassGraphFinset.mp hG₀
  let R := (A.close G₀ hG₀F).some
  have hR := P.localConditions.retained_order
  have heta := P.localConditions.eta_pos
  have htheta := P.localConditions.theta_pos
  have halpha := P.localConditions.alpha_pos
  have hdelta := P.residual.delta_pos
  have hepsilon := P.residual.epsilon_pos
  have hcutoff := P.localConditions.retained_visible
  have hret := D.retainedPartIndices_subset_visiblePartIndices hR htheta.le hcutoff
  have hthetaEta : theta ≤ eta := by
    have hRreal : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
    exact hcutoff.trans (div_le_self heta.le (by linarith))
  have hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ) :=
    fun a ha ↦ R.visible_part_card_ge_half homega a ha
  have hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * n := by
    rw [hp.roots_eq]
    exact R.badRoots_card_le halpha htheta (by have := P.profile_order; omega)
      hR homega hcutoff
  have hsparse G (hG : G ∈ F) :=
    (A.close G hG).some.sparseSideControls heta.le hR P.retained_inverse homega hthetaEta
      (P.epsilon_cap.trans (min_le_left _ _))
      (P.epsilon_cap.trans (min_le_right _ _)) P.residual.sparse_scale (A.free G hG)
  have hhead := (R.profileActiveCapacityHeadroom hR htheta.le homega hcutoff
    (A.edges G₀ hG₀F) (hsparse G₀ hG₀F).1 hdensity P.density_headroom
    hdelta.le P.shift_headroom).2
  have hround := R.profileActiveRoundingReserve hR heta.le htheta hdelta hcutoff
    P.active_rounding
  have hb : (p.b : ℝ) ≤ subcriticalSparseSideConstant k * eta * (n : ℝ)^2 := by
    rw [← hp.edge_count]
    exact (hsparse G₀ hG₀F).1
  have hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2 :=
    P.localConditions.root_fraction.trans (by nlinarith [mul_pos halpha htheta])
  have hbound := subcriticalProfileBound_of_geometry F p m alpha delta epsilon hk
    P.profile_order halpha.le P.localConditions.alpha_small htheta.le hdelta.le hepsilon.le
    P.localConditions.density_lower P.localConditions.density_upper hround hret hpart hroot hrho
    (fun G hG ↦ A.free G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
    (fun G hG ↦ (hsparse G (mem_subcriticalProfileClassGraphFinset.mp hG).1).2.2)
    (fun G hG ↦ A.edges G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
    (fun G hG ↦ (A.close G (mem_subcriticalProfileClassGraphFinset.mp hG).1).some.actualRetainedEdgeCountVector_mem_narrowWindow hR heta.le htheta.le
        P.retained_inverse homega hcutoff (by have := P.localConditions.alpha_small; linarith)
        P.epsilon_cap P.residual.sparse_scale
        (A.free G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
        (A.edges G (mem_subcriticalProfileClassGraphFinset.mp hG).1))
    (fun G hG ↦ (A.close G (mem_subcriticalProfileClassGraphFinset.mp hG).1).some.defect_cost_le)
    hhead hb
  have hlocal : (∑ v ∈ p.roots,
      subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
        alpha delta epsilon v) ≤
      -subcriticalAggregationRootRate k eta R₀ * n * p.roots.card := by
    have hh := Finset.sum_le_sum (fun v hv ↦ subcriticalLocalCompensation_of_geometry
      hk P.localConditions R homega (A.free G₀ hG₀F) (A.minimal G₀ hG₀F) hp hroot
      m (subcriticalSparseSideConstant k) v hv)
    simpa only [Finset.sum_const, nsmul_eq_mul, subcriticalAggregationRootRate,
      div_eq_mul_inv, neg_mul, mul_neg, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmatching := subcriticalResidualMatchingEstimateCore_all_ell hk J F p m
    (subcriticalSparseSideConstant k) heta hetaOne hR P.residual
    (fun a ha ↦ R.retainedPart_card_lower_bound hR heta.le ha) hpart A.free
    (fun G hG ↦ (A.close G hG).some.defect_cost_le)
  have herr := P.profile_error_le p
  have hrootRate := mul_le_mul_of_nonneg_right
    (subcriticalAggregationConstant_le_root k eta R₀)
    (show (0 : ℝ) ≤ n * p.roots.card by positivity)
  have hmatchingRate := mul_le_mul_of_nonneg_right
    (subcriticalAggregationConstant_le_matching k eta R₀)
    (show (0 : ℝ) ≤ p.ell * n by positivity)
  have hexp : (∑ v ∈ p.roots,
      subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
        alpha delta epsilon v) +
      subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
        alpha delta epsilon + subcriticalProfileErrorBudget alpha delta epsilon p ≤
      -(48 * subcriticalAggregationConstant k eta R₀) * subcriticalProfileComplexity p * n := by
    change _ ≤ -(48 * subcriticalAggregationConstant k eta R₀) *
      ((p.roots.card + p.ell : ℕ) : ℝ) * n
    simp only [Nat.cast_add]
    change subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
      alpha delta epsilon ≤ -subcriticalAggregationMatchingRate k eta R₀ * p.ell * n at hmatching
    have hc := subcriticalAggregationConstant_pos hk heta hR
    nlinarith [show 0 ≤ subcriticalAggregationConstant k eta R₀ * p.ell * n by positivity]
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))

end InducedStars
