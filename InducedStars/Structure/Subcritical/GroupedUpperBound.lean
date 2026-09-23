import InducedStars.Structure.Subcritical.GroupedProfileAggregation
import InducedStars.Structure.Subcritical.UpperBoundMain
import InducedStars.Structure.Subcritical.RetainedKeyFamilies

/-!
# Uniform candidate-ball upper bounds indexed by retained keys

The radius is chosen for all globally minimizing completions before
the candidate representation. Profile maxima are formed only after this
radius is fixed, and the final sum ranges over the finite retained-key image.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical Topology
namespace InducedStars

section Finite

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon tau : ℝ}
  {L : AdmissibleBlockSequence k}

/-- The candidate ball is partitioned by the finite image of compatible
retained keys. Repeated full completions never index this sum. -/
theorem subcriticalCandidateCutBall_retainedKey_card_bounds
    (hk : 3 ≤ k) (hn : k - 1 ≤ n) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (hpoly : subcriticalAggregationPolynomialReserve k n R₀ eta theta)
    (hbridge : SubcriticalMinimizerBridge hk L R₀ omega eta theta alpha delta epsilon tau n) :
    let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
    (((subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn).card : ℝ) ≤
      Real.exp (-subcriticalAggregationConstant k eta R₀ * n) *
        ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          (retainedKeyCleanPartitionFunction K eta m delta : ℝ)) ∧
    ((F.card : ℝ) ≤ (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          (retainedKeyCleanPartitionFunction K eta m delta : ℝ)) := by
  let F := subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau
  let FN := subcriticalCanonicalNoncleanGraphFinset F eta R₀ hk hn
  let f := fun G : SimpleGraph (Fin n) ↦
    retainedKey (canonicalSubcriticalDivision G R₀ hk (by simpa using hn)) eta R₀
  have hcanonical G (hG : cutDist (graphGraphon G) (WLambda hk L) < tau) :=
    hbridge G (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
      (canonicalSubcriticalDivision_minimal G R₀ hk (by simpa using hn)) hG
  have hmaps : ∀ G ∈ F, f G ∈ compatibleRetainedKeys k n L eta delta R₀ := by
    intro G hG
    exact retainedKey_mem_compatibleRetainedKeys
      (subcriticalCanonicalDivision_mem_compatible hk hn hcanonical hG)
  have hcountF : F.card = ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      (subcriticalCanonicalRetainedKeyGraphFinset F K eta R₀ hk (by simpa using hn)).card :=
    Finset.card_eq_sum_card_fiberwise (f := f) hmaps
  have hcountN : FN.card = ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      (subcriticalCanonicalRetainedKeyGraphFinset FN K eta R₀ hk (by simpa using hn)).card :=
    Finset.card_eq_sum_card_fiberwise (f := f)
      (fun G hG ↦ hmaps G ((Finset.mem_filter.mp hG).1))
  have hkey K := subcriticalCanonicalRetainedKey_card_bounds
    hk hn J K P hetaOne homega hdensity hpoly hbridge
  constructor
  · change (FN.card : ℝ) ≤ _
    rw [hcountN, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun K _ ↦ (hkey K).1
  · change (F.card : ℝ) ≤ _
    rw [hcountF, Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun K _ ↦ (hkey K).2

end Finite

/-- The new grouped comparisons. These are conclusions obtained from the
fixed-(key,remainder) argument, not assumptions identifying old full-division
sums with their deduplicated versions. -/
structure SubcriticalGroupedCandidateUpperBounds
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) (L : AdmissibleBlockSequence k)
    (R₀ m : ℕ) (eta delta tau c : ℝ) : Prop where
  key_nonclean : ∀ K : SubcriticalRetainedKey k (Fin n),
    ((subcriticalCanonicalRetainedKeyGraphFinset
      (subcriticalCanonicalNoncleanGraphFinset
        (subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau) eta R₀ hk hn)
      K eta R₀ hk (by simpa using hn)).card : ℝ) ≤
      Real.exp (-c * n) * retainedKeyCleanPartitionFunction K eta m delta
  key_total : ∀ K : SubcriticalRetainedKey k (Fin n),
    ((subcriticalCanonicalRetainedKeyGraphFinset
      (subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau)
      K eta R₀ hk (by simpa using hn)).card : ℝ) ≤
      (1 + Real.exp (-c * n)) * retainedKeyCleanPartitionFunction K eta m delta
  cutBall_nonclean : ((subcriticalCanonicalNoncleanGraphFinset
      (subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau) eta R₀ hk hn).card : ℝ) ≤
    Real.exp (-c * n) * ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      (retainedKeyCleanPartitionFunction K eta m delta : ℝ)
  cutBall : ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
    (1 + Real.exp (-c * n)) * ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      (retainedKeyCleanPartitionFunction K eta m delta : ℝ)

/-- One radius, chosen before the explicit candidate representation, supplies
every fixed-remainder minimizing completion. The eventual scalar hierarchy
is exactly the existing hierarchy; no probability/counting bound is an input. -/
theorem subcriticalGroupedUpperBound_of_eventual_parameters
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (omega eta theta alpha delta epsilon tauMax : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) (hetaOne : eta ≤ 1)
    (htauMax : 0 < tauMax)
    (hparameters : ∀ᶠ n : ℕ in atTop,
      SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      ∀ L : AdmissibleBlockSequence k,
        WLambda hk L ∈ candidateOptimizerFamily k gamma →
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
  intro L _hL
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

/-- The approved retained-key replacement of the upper comparison in
paper Lemma `lemma:NtaunmWUpperBdK1k`. All earlier positive caps are honored,
and the radius precedes the candidate representation. -/
theorem subcriticalGroupedUpperBound
    (k : ℕ) (hk : 3 ≤ k) {gamma omega : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (etaMax thetaMax alphaMax deltaMax epsilonMax tauMax : ℝ)
    (hetaMax : 0 < etaMax) (hthetaMax : 0 < thetaMax)
    (halphaMax : 0 < alphaMax) (hdeltaMax : 0 < deltaMax)
    (hepsilonMax : 0 < epsilonMax) (htauMax : 0 < tauMax) (Rmin : ℕ) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaMax ∧ eta ≤ omega ∧ eta ≤ 1 ∧
      ∃ R₀ : ℕ, 1 ≤ R₀ ∧ Rmin ≤ R₀ ∧ 1 / (R₀ : ℝ) ≤ eta ∧
      ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧
      ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧
      (∀ᶠ n : ℕ in atTop,
        SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n) ∧
      0 < subcriticalAggregationConstant k eta R₀ ∧
      ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
        ∀ L : AdmissibleBlockSequence k,
          WLambda hk L ∈ candidateOptimizerFamily k gamma →
          ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0,
            ∀ {n : ℕ} (hn : n0 ≤ n) (m : ℕ), gamma / 8 * (n : ℝ)^2 ≤ m →
              SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn) L R₀ m eta delta tau
                (subcriticalAggregationConstant k eta R₀) := by
  obtain ⟨eta, heta, hecap, heomega, heone, heres, R₀, hR, hRmin, hinv⟩ :=
    exists_subcriticalAggregationOuterParameters k hgamma.1 homega hetaMax Rmin
  obtain ⟨theta, htheta, htcap, ha⟩ := exists_subcriticalAggregationParameters
    hk hgamma.1 heta hR hinv heres thetaMax hthetaMax
  obtain ⟨alpha, halpha, hacap, hd⟩ := ha alphaMax halphaMax
  obtain ⟨delta, hdelta, hdcap, he⟩ := hd deltaMax hdeltaMax
  obtain ⟨epsilon, hepsilon, hepcap, hparameters⟩ := he epsilonMax hepsilonMax
  refine ⟨eta, heta, hecap, heomega, heone, R₀, hR, hRmin, hinv,
    theta, htheta, htcap, alpha, halpha, hacap, delta, hdelta, hdcap,
    epsilon, hepsilon, hepcap, hparameters,
    subcriticalAggregationConstant_pos hk heta hR, ?_⟩
  exact subcriticalGroupedUpperBound_of_eventual_parameters k hk hgamma R₀
    omega eta theta alpha delta epsilon tauMax homega homegaOne heone htauMax hparameters

/-- Exact-density sequences supply the order threshold independently of all
key and remainder choices. -/
theorem subcriticalGroupedUpperBound_fixedDensity
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (omega eta theta alpha delta epsilon tauMax : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) (hetaOne : eta ≤ 1)
    (htauMax : 0 < tauMax)
    (hparameters : ∀ᶠ n : ℕ in atTop,
      SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      ∀ L : AdmissibleBlockSequence k,
        WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ} (hn : n0 ≤ n),
          SubcriticalGroupedCandidateUpperBounds hk (hn0.trans hn) L R₀ (m n) eta delta tau
            (subcriticalAggregationConstant k eta R₀) := by
  obtain ⟨tau, htau, htcap, hbound⟩ := subcriticalGroupedUpperBound_of_eventual_parameters
    k hk hgamma R₀ omega eta theta alpha delta epsilon tauMax
    homega homegaOne hetaOne htauMax hparameters
  refine ⟨tau, htau, htcap, ?_⟩
  intro L hL m hm
  obtain ⟨nBound, hnBound, hbound⟩ := hbound L hL
  obtain ⟨nDensity, hdensity⟩ := Filter.eventually_atTop.mp
    (hm.eventually_subcritical_lower_density hgamma.1)
  refine ⟨max nBound nDensity, hnBound.trans (le_max_left _ _), ?_⟩
  intro n hn
  exact hbound ((le_max_left _ _).trans hn) (m n)
    (hdensity n ((le_max_right _ _).trans hn))

end InducedStars
