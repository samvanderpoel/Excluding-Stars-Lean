import InducedStars.Structure.Subcritical.FineStructureParameters

/-!
# A noncircular input radius for subcritical cleanup

First choose the geometric bridge radius, then cap the grouped counting
radius by it. Concentration, already proved at every positive radius, is
applied only afterwards. No output ball is fed back into an earlier estimate.
-/

noncomputable section
open Filter Set
namespace InducedStars

namespace SubcriticalFineStructureParameters

variable {k : ℕ} {gamma xi : ℝ}

theorem exists_inputRadius (hk : 3 ≤ k)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (P : SubcriticalFineStructureParameters k gamma xi) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ} (hn : n0 ≤ n),
        SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn)
          (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
          P.R₀ (m n) P.eta P.delta tau (subcriticalAggregationConstant k P.eta P.R₀) ∧
        SubcriticalMinimizerBridge hk (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
          P.R₀ 1 P.eta P.theta P.alpha P.delta P.epsilon tau n := by
  obtain ⟨tauBridge, htauBridge, hbridge⟩ := subcriticalCloseStructure_of_global_minimal
    k hk P.R₀ P.order_one 1 P.eta P.theta P.alpha P.delta P.epsilon (by norm_num)
    P.eta_pos P.theta_pos P.alpha_pos P.delta_pos P.epsilon_pos
  obtain ⟨tau, htau, hcap, hgroup⟩ := subcriticalGroupedUpperBound_fixedDensity
    k hk hgamma P.R₀ 1 P.eta P.theta P.alpha P.delta P.epsilon tauBridge
    (by norm_num) (by norm_num) P.eta_one htauBridge P.aggregation
  refine ⟨tau, htau, ?_⟩
  intro m hm
  obtain ⟨nGroup, hnGroup, hgroup⟩ := hgroup
    (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
    (subcriticalDistinguishedGraphon_mem_candidateOptimizerFamily k hk gamma hgamma) m hm
  obtain ⟨nBridge, _, hbridge⟩ := hbridge
    (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
  refine ⟨max nGroup nBridge, hnGroup.trans (le_max_left _ _), ?_⟩
  intro n hn
  refine ⟨hgroup ((le_max_left _ _).trans hn), ?_⟩
  intro G D hmin hG
  exact hbridge ((le_max_right _ _).trans hn) G D hmin (hG.trans_le hcap)

def inputRadius (P : SubcriticalFineStructureParameters k gamma xi) (hk : 3 ≤ k)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) : ℝ :=
  (P.exists_inputRadius hk hgamma).choose

theorem inputRadius_pos (P : SubcriticalFineStructureParameters k gamma xi) (hk : 3 ≤ k)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) : 0 < P.inputRadius hk hgamma :=
  (P.exists_inputRadius hk hgamma).choose_spec.1

theorem inputRadius_spec (P : SubcriticalFineStructureParameters k gamma xi) (hk : 3 ≤ k)
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ} (hn : n0 ≤ n),
      SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn)
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
        P.R₀ (m n) P.eta P.delta (P.inputRadius hk hgamma)
          (subcriticalAggregationConstant k P.eta P.R₀) ∧
      SubcriticalMinimizerBridge hk (subcriticalDistinguishedBlockSequence k hk gamma hgamma)
        P.R₀ 1 P.eta P.theta P.alpha P.delta P.epsilon (P.inputRadius hk hgamma) n :=
  (P.exists_inputRadius hk hgamma).choose_spec.2 m hm

end SubcriticalFineStructureParameters
end InducedStars
