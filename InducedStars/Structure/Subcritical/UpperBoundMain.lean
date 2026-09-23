import InducedStars.Structure.Subcritical.CandidateUpperBound

/-!
# The completed fixed-optimizer-ball upper bound

Paper: Lemma `lemma:NtaunmWUpperBdK1k`. All parameters and the radius
precede the explicit candidate representation. This is only the upper
comparison; no canonical-clean lower bound, retained-mass gap, or final
subcritical typical-structure conclusion is asserted.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical Topology
namespace InducedStars

/-- The two upper comparisons, retaining the stronger cut-ball coefficient
and the separate nonclean bound. This is a conclusion, not an input. -/
structure SubcriticalCandidateUpperBounds
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) (L : AdmissibleBlockSequence k)
    (R₀ m : ℕ) (eta delta tau c : ℝ) : Prop where
  nonclean : ∀ D : SubcriticalDivision k (Fin n),
    ((subcriticalNoncleanDivisionGraphFinset
      (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D)
      D eta R₀).card : ℝ) ≤
      Real.exp (-c * n) * cleanRetainedPartitionFunction D eta R₀ m delta
  division : ∀ D : SubcriticalDivision k (Fin n),
    ((subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D).card : ℝ) ≤
      (1 + Real.exp (-c * n)) * cleanRetainedPartitionFunction D eta R₀ m delta
  cutBall : ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
    (1 + Real.exp (-c * n)) *
      ∑ D ∈ subcriticalCompatibleDivisions k n L eta delta R₀,
        (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ)
  cutBall_exp : ((subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau).card : ℝ) ≤
    Real.exp (n : ℝ) *
      ∑ D ∈ subcriticalCompatibleDivisions k n L eta delta R₀,
        (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ)

/-- One common bridge and eventual scalar tuple instantiate every finite
estimate on the same actual canonical fibers. The optional radius cap is
applied before those families are defined, not by a safe-log monotonicity
argument. Both penalties retain a common polynomial reserve. -/
theorem subcriticalNtaunmWUpperBound_of_eventual_parameters
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
            SubcriticalCandidateUpperBounds hk (hn0.trans hn) L R₀ m eta delta tau
              (subcriticalAggregationConstant k eta R₀) := by
  obtain ⟨nParameters, hparameters⟩ := Filter.eventually_atTop.mp hparameters
  have P0 := hparameters nParameters le_rfl
  obtain ⟨tauBridge, htauBridge, hbridge⟩ := subcriticalCloseStructure k hk R₀
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
  have hb (G : SimpleGraph (Fin n)) (hG : cutDist (graphGraphon G) (WLambda hk L) < tau) :
      Nonempty (SubcriticalCloseStructureResult hk G
        (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
        L R₀ omega eta theta alpha delta epsilon) :=
    hbridge ((le_max_left _ _).trans hn) G (hG.trans_le (min_le_left _ _))
  constructor
  · intro D
    exact subcriticalNoncleanDivision_card_le hk PriorInstances.principalJansonInput _ P
      hetaOne homegaOne hdensity (subcriticalCandidateDivision_aggregationGeometry hk
        (hn0.trans hn) D hb) hp
  · exact fun D ↦ subcriticalCandidateDivision_card_le_cleanPartitionFunction hk
      (hn0.trans hn) D P hetaOne homegaOne hdensity hp hb
  · exact subcriticalCandidateCutBall_card_le_cleanPartitionSum hk
      (hn0.trans hn) P hetaOne homegaOne hdensity hp hb
  · exact subcriticalCandidateCutBall_card_le_exp_cleanPartitionSum hk
      (hn0.trans hn) P hetaOne homegaOne hdensity hp hb

/-- Paper: Lemma `lemma:NtaunmWUpperBdK1k`, both conclusions.
The source's arbitrary fixed polynomial is absorbed using both complexity
penalties. All selected parameters respect arbitrary earlier caps;
the positive radius is independent of the explicit candidate representation.
The exponential coefficient in the paper's weaker cut-ball bound can be
chosen to be the explicit constant `C=1`.
-/
theorem subcriticalNtaunmWUpperBound
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
              SubcriticalCandidateUpperBounds hk (hn0.trans hn) L R₀ m eta delta tau
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
  exact subcriticalNtaunmWUpperBound_of_eventual_parameters k hk hgamma R₀
    omega eta theta alpha delta epsilon tauMax homega homegaOne heone htauMax hparameters

/-- Every positive asymptotic edge density supplies the finite lower-density
condition. No feasibility or rounding assumption on early terms is needed. -/
theorem HasAsymptoticEdgeDensity.eventually_subcritical_lower_density
    {m : ℕ → ℕ} {gamma : ℝ} (hm : HasAsymptoticEdgeDensity m gamma)
    (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop, gamma / 8 * (n : ℝ)^2 ≤ m n := by
  have hd := (tendsto_order.1 hm).1 (gamma / 2) (by linarith)
  filter_upwards [hd, eventually_ge_atTop 2] with n hn hn2
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hepos : (0 : ℝ) < completeEdgeCount n := by
    rw [completeEdgeCount, Nat.cast_choose_two]
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    exact div_pos (mul_pos hnpos (by linarith)) (by norm_num)
  have h := (lt_div_iff₀ hepos).mp hn
  rw [completeEdgeCount, Nat.cast_choose_two] at h
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  nlinarith [mul_nonneg hgamma.le
    (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hnR))]

/-- Fixed-density specialization for an arbitrary edge-count sequence with
the existing asymptotic-density convention, not merely a floor sequence. -/
theorem subcriticalNtaunmWUpperBound_fixedDensity
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
          SubcriticalCandidateUpperBounds hk (hn0.trans hn) L R₀ (m n) eta delta tau
            (subcriticalAggregationConstant k eta R₀) := by
  obtain ⟨tau, htau, htcap, hbound⟩ := subcriticalNtaunmWUpperBound_of_eventual_parameters
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
