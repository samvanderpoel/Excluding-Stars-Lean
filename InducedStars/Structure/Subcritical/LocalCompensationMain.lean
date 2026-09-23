import InducedStars.Structure.Subcritical.LocalCompensation
import InducedStars.Structure.Subcritical.LocalPenaltyFeasibility

/-!
# Local compensation for canonical divisions in a candidate cut ball

The cut radius is chosen before the explicit candidate sequence. A nonempty
profile class supplies an actual graph, its canonical minimality, and its
close-structure witness; no geometric conclusion is postulated for a profile.
-/

noncomputable section
open Finset Filter
open scoped Topology Classical

namespace InducedStars

/-- A nonempty profile class in a canonical candidate division supplies all
the actual graph geometry used by local compensation. Only the completed
cut-to-division bridge enters this witness extraction. -/
theorem subcriticalProfileClass_close_geometry
    {k n R₀ m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) (hR₀ : 1 ≤ R₀)
    {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon tau : ℝ}
    (halpha : 0 < alpha) (htheta : 0 < theta) (homega : omega ≤ 1)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (D : SubcriticalDivision k (Fin n)) (p : SubcriticalProfile D eta R₀ theta)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
        Nonempty (SubcriticalCloseStructureResult hk G
          (canonicalSubcriticalDivision G R₀ hk (by simpa only [Fintype.card_fin] using hn))
          L R₀ omega eta theta alpha delta epsilon))
    (hne : (subcriticalProfileClassGraphFinset
      (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D)
      alpha p).Nonempty) :
    ∃ G : SimpleGraph (Fin n),
      ∃ R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon,
        ¬ Regularity.InducedEmbeds (inducedStar k) G ∧
        (∀ E : SubcriticalDivision k (Fin n), subcriticalDefectCost G D ≤ subcriticalDefectCost G E) ∧
        RealizesSubcriticalProfile G alpha p ∧
        (p.roots.card : ℝ) ≤ subcriticalProfileRootFraction alpha theta epsilon * n := by
  obtain ⟨G, hG⟩ := hne
  obtain ⟨hGF, hreal⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
  obtain ⟨hball, hcanonical⟩ := mem_subcriticalCandidateDivisionGraphFinset.mp hGF
  obtain ⟨hfamily, hcut⟩ := mem_subcriticalCandidateCutBallGraphFinset.mp hball
  have hfree := (mem_inducedStarFreeGraphFinsetWithEdges.mp hfamily).1
  obtain ⟨Rcan⟩ := hbridge G hcut
  have R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon := by
    simpa only [hcanonical] using Rcan
  refine ⟨G, R, hfree, ?_, hreal, ?_⟩
  · intro E
    simpa only [hcanonical] using
      canonicalSubcriticalDivision_minimal G R₀ hk (by simpa only [Fintype.card_fin] using hn) E
  · rw [hreal.roots_eq]
    exact R.badRoots_card_le halpha htheta (by omega) hR₀ homega hcutoff

/-- Candidate-cut-ball local compensation from an eventually valid common
scalar package. The single positive radius precedes every explicit candidate
representation; only the final order threshold depends on that representation. -/
theorem subcriticalLocalCompensation_of_eventual_parameters
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (hparameters : ∀ᶠ n : ℕ in atTop,
      SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (D : SubcriticalDivision k (Fin n))
            (p : SubcriticalProfile D eta R₀ theta),
            let F := subcriticalCandidateDivisionGraphFinset
              k n m (WLambda hk L) tau R₀ hk (hn0.trans hn) D
            (subcriticalProfileClassGraphFinset F alpha p).Nonempty →
              ∀ v ∈ p.roots,
                subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
                  alpha delta epsilon v ≤
                    -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ)) := by
  obtain ⟨nParameters, hparameters⟩ := Filter.eventually_atTop.mp hparameters
  have P0 := hparameters nParameters le_rfl
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ P0.retained_order
    omega eta theta alpha delta epsilon homega P0.eta_pos P0.theta_pos P0.alpha_pos
    hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge nParameters
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn m D p
  dsimp only
  intro hne v hv
  have hnBridge' : nBridge ≤ n := (le_max_left _ _).trans hn
  have hnParameters : nParameters ≤ n := (le_max_right _ _).trans hn
  have P := hparameters n hnParameters
  obtain ⟨G, R, hfree, hminimal, hp, hB⟩ :=
    subcriticalProfileClass_close_geometry hk (hn0.trans hn) P.retained_order
      P.alpha_pos P.theta_pos homegaOne P.retained_visible D p
      (fun G hcut ↦ hbridge hnBridge' G hcut) hne
  exact subcriticalLocalCompensation_of_geometry hk P R homegaOne hfree hminimal hp hB
    m (subcriticalSparseSideConstant k) v hv

/-- Paper: Lemma `lemma:local-compensation-K1k`.
There are genuine positive parameters, below arbitrary positive outer caps,
for which every root of every nonempty canonical candidate profile class has
the common negative local exponent. The proof uses the unified component
deficit, the exact own relative-entropy loss, and placement optimality.
No matching or Janson estimate occurs. The cut radius precedes the candidate,
and the penalty constant `subcriticalLocalPenaltyUnit k = A_k/100` depends only on `k`. -/
theorem subcriticalLocalCompensation
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀) (omega eta : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) (heta : 0 < eta)
    (thetaMax alphaMax deltaMax epsilonMax epsilonSlope : ℝ)
    (hthetaMax : 0 < thetaMax) (halphaMax : 0 < alphaMax)
    (hdeltaMax : 0 < deltaMax) (hepsilonMax : 0 < epsilonMax)
    (hepsilonSlope : 0 < epsilonSlope) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧
          ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧
            epsilon ≤ min eta (theta ^ 2) ∧ epsilon ≤ delta * epsilonSlope ∧
            (∀ᶠ n : ℕ in atTop,
              SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n) ∧
            ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
              WLambda hk L ∈ candidateOptimizerFamily k gamma →
                ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
                  ∀ (m : ℕ) (D : SubcriticalDivision k (Fin n))
                    (p : SubcriticalProfile D eta R₀ theta),
                    let F := subcriticalCandidateDivisionGraphFinset
                      k n m (WLambda hk L) tau R₀ hk (hn0.trans hn) D
                    (subcriticalProfileClassGraphFinset F alpha p).Nonempty →
                      ∀ v ∈ p.roots,
                        subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
                          alpha delta epsilon v ≤
                            -(subcriticalLocalPenaltyUnit k * eta * n / (R₀ : ℝ)) := by
  obtain ⟨theta, ht, htMax, hvisible, hrelocation⟩ :=
    exists_subcriticalLocalTheta k hk R₀ hR₀ eta thetaMax heta hthetaMax
  obtain ⟨alpha, ha, haMax, delta, hd, hdMax, epsilon, he, heMax, heCap, heSlope, hP⟩ :=
    exists_subcriticalLocalPenaltyParameters k hk R₀ hR₀ eta theta heta ht
      hvisible hrelocation alphaMax deltaMax epsilonMax epsilonSlope
      halphaMax hdeltaMax hepsilonMax hepsilonSlope
  refine ⟨theta, ht, htMax, alpha, ha, haMax, delta, hd, hdMax,
    epsilon, he, heMax, heCap, heSlope, hP, ?_⟩
  exact subcriticalLocalCompensation_of_eventual_parameters k hk hgamma R₀
    omega eta theta alpha delta epsilon homega homegaOne hd he hP

end InducedStars
