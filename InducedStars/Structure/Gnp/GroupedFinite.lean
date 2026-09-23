import InducedStars.Structure.Subcritical.GroupedUpperBound

/-!
# Fixed-count retained-key bounds without a density-regime restriction

The counting cores use a positive finite lower density, not the assertion
that the candidate has a strictly subcritical density. This interface keeps
the radius before the representation and applies, in particular, to the
full complete-core endpoint in the critical weighted argument.

Grouping fixes the retained key and the entire remainder graph.
There is no deduplication of a previously proved full-division bound.
-/

noncomputable section
open Filter Finset Set
open scoped Classical BigOperators Topology
namespace InducedStars

/-- The existing finite grouped proof is uniform over all edge counts above
the explicit lower bound, with no candidate-density hypothesis. The scalar
parameter package is the already proved, quantitative hierarchy. -/
theorem gnpGroupedUpperBound_of_eventual_parameters
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (R₀ : ℕ) (omega eta theta alpha delta epsilon tauMax : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) (hetaOne : eta ≤ 1)
    (htauMax : 0 < tauMax)
    (hparameters : ∀ᶠ n : ℕ in atTop,
      SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      ∀ L : AdmissibleBlockSequence k,
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0,
          ∀ {n : ℕ} (hn : n0 ≤ n) (m : ℕ),
            gamma / 8 * (n : ℝ)^2 ≤ m →
            SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn) L R₀ m eta delta tau
              (subcriticalAggregationConstant k eta R₀) := by
  obtain ⟨nParameters, hparameters⟩ := Filter.eventually_atTop.mp hparameters
  have P0 := hparameters nParameters le_rfl
  obtain ⟨tauBridge, htauBridge, hbridge⟩ := subcriticalCloseStructure_of_global_minimal k hk R₀
    P0.localConditions.retained_order omega eta theta alpha delta epsilon homega
    P0.localConditions.eta_pos P0.localConditions.theta_pos P0.localConditions.alpha_pos
    P0.residual.delta_pos P0.residual.epsilon_pos
  obtain ⟨nPolynomial, hpoly⟩ := Filter.eventually_atTop.mp
    (eventually_subcriticalAggregationPolynomialReserve (theta := theta) hk
      P0.localConditions.eta_pos P0.localConditions.retained_order)
  let tau := min tauBridge tauMax
  refine ⟨tau, lt_min htauBridge htauMax, min_le_right _ _, ?_⟩
  intro L
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge (max nParameters nPolynomial)
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn m hdensity
  have P := hparameters n ((le_max_left _ _).trans ((le_max_right _ _).trans hn))
  have hp := hpoly n ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hb : SubcriticalMinimizerBridge hk L R₀ omega eta theta alpha delta epsilon tau n := by
    intro G D hmin hG
    exact hbridge ((le_max_left _ _).trans hn) G D hmin (hG.trans_le (min_le_left _ _))
  have hkey K := subcriticalCanonicalRetainedKey_card_bounds hk (hn0.trans hn)
    PriorInstances.principalJansonInput K P hetaOne homegaOne hdensity hp hb
  have hball := subcriticalCandidateCutBall_retainedKey_card_bounds hk (hn0.trans hn)
    PriorInstances.principalJansonInput P hetaOne homegaOne hdensity hp hb
  exact ⟨fun K ↦ (hkey K).1, fun K ↦ (hkey K).2, hball.1, hball.2⟩

end InducedStars
