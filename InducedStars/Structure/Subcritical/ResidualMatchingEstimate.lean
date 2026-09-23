import InducedStars.Structure.Subcritical.ResidualJanson
import InducedStars.Structure.Subcritical.ResidualMatchingParameters
import InducedStars.PriorInstances

/-!
# The residual matching exponent

Paper: Lemma `lemma:residual-matching-estimate-K1k`. The exact existing
matching weight is summed over its actual residual-pattern family before
taking the maximum over rooted patterns. Weighted Hamming enumeration counts varying remainders, endpoint cleaning gives candidate abundance, and one polarity applies to the entire matching. The safe-log
convention and its zero-weight branch are preserved.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped Classical
namespace InducedStars
variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta theta alpha delta epsilon : ℝ}

/-- Uniformity in the remainder, compatible leftover, and narrow vector
allows the proved probability penalty to pass through the existing maximum. -/
theorem subcriticalResidualSafeMaximum_le_of_geometry
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C : ℝ) (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hnum : SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ))
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (hell : 1 ≤ p.ell) (TB R : SimpleGraph (Fin n))
    (hR : R ∈ subcriticalResidualDefectPatternFinset F alpha p TB) :
    subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        subcriticalResidualMatchingKappa eta R₀) * p.ell * n) := by
  have hret := D.retainedPartIndices_subset_visiblePartIndices hR₀
    hnum.theta_pos.le hnum.theta_cutoff
  obtain ⟨M, hlarge, hsmall⟩ := subcriticalResidualPattern_exists_matching hR
    heta hetaOne hR₀ hell (by simpa only [Fintype.card_fin] using hnum.matching_room)
  have hdegree := subcriticalResidualPattern_standardDegree_le_of_geometry hk hR
    hnum.alpha_pos.le hnum.theta_pos.le hnum.epsilon_pos.le hnum.epsilon_theta
    hnum.sparse_scale hret hfree hdefect
  have hroot := subcriticalResidualPattern_roots_card_le_of_finite_geometry hR
    hnum.alpha_pos hnum.theta_pos (by simpa only [Fintype.card_fin] using hnum.order_pos)
    hret (by simpa only [Fintype.card_fin] using hvisible)
    (by simpa only [Fintype.card_fin] using hdefect)
  have hroots : (p.roots.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2 := by
    have hh := mul_le_mul_of_nonneg_right hnum.roots_room (Nat.cast_nonneg n)
    simp only [Fintype.card_fin] at hroot
    linarith
  unfold subcriticalResidualSafeMaximum
  apply subcriticalFiniteMax_le (Real.exp_pos _).le
  intro z hz
  obtain ⟨_, hL, hm⟩ := (Finset.mem_filter.mp hz).2
  have hcompat := (mem_subcriticalLeftoverDefectPatternFinset F alpha p TB R z.2.1).mp
    (subcriticalLeftoverDefectPatternFinsetWithRemainder_subset F alpha p z.1 TB R hL)
  exact subcriticalResidualMatchingSafeProbability_le hk J heta hR₀ M hcompat z.1 z.2.2 hm
    hnum.delta_palette (subcriticalResidualDegreeCoefficient_nonneg k
      hnum.alpha_pos.le hnum.theta_pos.le) hnum.degree_cap hdegree hpart hroots
    (by simpa only [Fintype.card_fin] using hsmall) hlarge

/-- Paper: Lemma `lemma:residual-matching-estimate-K1k`.
Finite capability-parametric form. All hypotheses are explicit scalar,
part-size, star-freeness, or edit-budget conditions; no candidate count,
probability estimate, or conclusion-shaped assumption is supplied.
The exponent is the original natural-unit `subcriticalProfileMatchingExponent`.
The proof uses the global polarity, weighted residual enumeration, and endpoint-clean candidates. -/
theorem subcriticalResidualMatchingEstimateCore
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C : ℝ) (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hnum : SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ))
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (hell : 1 ≤ p.ell) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤
      -(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * subcriticalResidualMatchingKappa eta R₀)) * p.ell * n := by
  have hret := D.retainedPartIndices_subset_visiblePartIndices hR₀
    hnum.theta_pos.le hnum.theta_cutoff
  have hsmall (G : SimpleGraph (Fin n)) (hG : G ∈ F) (v : Fin n) :
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * Fintype.card (Fin n) := by
    simpa only [Fintype.card_fin] using subcriticalResidual_smallSide_bound_of_geometry
      hk G D hnum.theta_pos.le hnum.epsilon_pos.le hnum.epsilon_theta hnum.sparse_scale
      (hfree G hG) (hdefect G hG) v
  have hh := subcriticalResidualMatchingExponent_le_of_safeMaximum F p m C delta epsilon
    (subcriticalResidualMatchingConstant k eta R₀) (subcriticalResidualMatchingKappa eta R₀)
    (subcriticalResidualMatchingConstant_pos hk heta hR₀)
    (subcriticalResidualMatchingKappa_pos heta hR₀)
    (by simpa only [Fintype.card_fin] using hnum.order_pos)
    hnum.alpha_pos.le hnum.theta_pos.le hnum.degree_half hret hsmall
    (fun TB _ R hR ↦ by
      simpa only [Fintype.card_fin] using subcriticalResidualSafeMaximum_le_of_geometry
        hk J F p m C heta hetaOne hR₀ hnum hpart hvisible hfree hdefect hell TB R hR)
    (by simpa only [Fintype.card_fin] using hnum.enumeration_error)
    (by simpa only [Fintype.card_fin] using hnum.fallback_order)
  simpa only [Fintype.card_fin] using hh

/-- Paper: Lemma `lemma:residual-matching-estimate-K1k`.
The published-input specialization of the fully proved finite adapter.
Its sole project-specific assumption is the approved Riordan--Warnke
principal-event Janson theorem; no graphon alignment input is required. -/
theorem subcriticalResidualMatchingEstimate
    (hk : 3 ≤ k)
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C : ℝ) (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hnum : SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ))
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2)
    (hell : 1 ≤ p.ell) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤
      -(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * subcriticalResidualMatchingKappa eta R₀)) * p.ell * n :=
  subcriticalResidualMatchingEstimateCore hk PriorInstances.principalJansonInput F p m C
    heta hetaOne hR₀ hnum hpart hvisible hfree hdefect hell

end InducedStars
