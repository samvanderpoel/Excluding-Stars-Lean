import InducedStars.Structure.Subcritical.ProfileBound

/-!
# The profile bound for canonical divisions in a candidate cut ball

The cut radius precedes the candidate block representation. Only the order
threshold depends on that representation. The finite counting core is local;
the wrapper inherits only the finite weighted alignment input through the
completed cut-to-division bridge. Natural units, fixed-remainder summation, the small-alpha range, and root-avoiding residual safety are explicit.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

/-- Paper: Lemma `lemma:profile-bound-K1k`.
The polynomial factor is exactly `n^(6*|I|)`, comprising two factors with
exponent `3*|I|`. All analytic exponents use natural units, the
remainder is fixed until its leftover fiber is summed, the high-row
range follows from `5*alpha ≤ 1/2`, and residual safety excludes
root vertices. No later local-tail or matching penalty is used.
The density band is finite and the radius is uniform in the candidate. -/
theorem subcriticalProfileBound
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (_hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (homegaOne : omega ≤ 1)
    (heta : 0 < eta) (htheta : 0 < theta) (halpha : 0 < alpha)
    (hdelta : 0 < delta) (hepsilon : 0 < epsilon)
    (halphaHalf : 5 * alpha ≤ 1 / 2)
    (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hepsilonCap : epsilon ≤ min eta (theta ^ 2))
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hreserve : subcriticalSparseSideConstant k * eta + epsilon ≤ gamma / 16)
    (hshift : epsilon ≤ delta * gamma / 192) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ), gamma / 8 * (n : ℝ) ^ 2 ≤ m →
            ∀ (D : SubcriticalDivision k (Fin n))
              (p : SubcriticalProfile D eta R₀ theta),
              let F := subcriticalCandidateDivisionGraphFinset
                k n m (WLambda hk L) tau R₀ hk (hn0.trans hn) D
              ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
                (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
                  cleanRetainedPartitionFunction D eta R₀ m delta *
                    Real.exp ((∑ v ∈ p.roots,
                      subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
                        alpha delta epsilon v) +
                      subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
                        alpha delta epsilon +
                      subcriticalProfileErrorBudget alpha delta epsilon p) := by
  obtain ⟨tau, htau, hbridge⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨nBridge, hnBridge, hbridge⟩ := hbridge L
  let n0 := max nBridge (max (Nat.ceil (1 / theta))
    (subcriticalActiveRoundingThreshold delta theta))
  have hn0 : k - 1 ≤ n0 := hnBridge.trans (le_max_left _ _)
  refine ⟨n0, hn0, ?_⟩
  intro n hn m hdensity D p
  dsimp only
  let F := subcriticalCandidateDivisionGraphFinset
    k n m (WLambda hk L) tau R₀ hk (hn0.trans hn) D
  have hnBridge' : nBridge ≤ n := (le_max_left _ _).trans hn
  have hceil : Nat.ceil (1 / theta) ≤ n :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnround : subcriticalActiveRoundingThreshold delta theta ≤ n :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hn2 : 2 ≤ n := by omega
  have hscale : 1 ≤ theta * n := by
    have hdiv : 1 / theta ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hceil)
    simpa only [mul_comm] using (div_le_iff₀ htheta).mp hdiv
  have hthetaEta : theta ≤ eta := by
    have hR : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR₀
    exact hcutoff.trans (div_le_self heta.le (by linarith))
  have hdata (G : SimpleGraph (Fin n))
      (hG : G ∈ subcriticalProfileClassGraphFinset F alpha p) :
      ¬ Regularity.InducedEmbeds (inducedStar k) G ∧
        (finiteGraphEdges G).card = m ∧
        Nonempty (SubcriticalCloseStructureResult hk G D L R₀
          omega eta theta alpha delta epsilon) := by
    obtain ⟨hGF, _⟩ := mem_subcriticalProfileClassGraphFinset.mp hG
    obtain ⟨hball, hcanonical⟩ := mem_subcriticalCandidateDivisionGraphFinset.mp hGF
    obtain ⟨hfamily, hcut⟩ := mem_subcriticalCandidateCutBallGraphFinset.mp hball
    obtain ⟨hfree, hedges⟩ := mem_inducedStarFreeGraphFinsetWithEdges.mp hfamily
    have hR := hbridge hnBridge' G hcut
    refine ⟨hfree, ?_, ?_⟩
    · simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using hedges
    · simpa only [hcanonical] using hR
  have hsparse G (hG : G ∈ subcriticalProfileClassGraphFinset F alpha p) :=
    (hdata G hG).2.2.some.sparseSideControls heta.le hR₀ hinv homegaOne hthetaEta
      (hepsilonCap.trans (min_le_left _ _)) (hepsilonCap.trans (min_le_right _ _))
      hscale (hdata G hG).1
  by_cases hne : (subcriticalProfileClassGraphFinset F alpha p).Nonempty
  · obtain ⟨G₀, hG₀⟩ := hne
    let R := (hdata G₀ hG₀).2.2.some
    have hret := D.retainedPartIndices_subset_visiblePartIndices hR₀ htheta.le hcutoff
    have hpart : ∀ a ∈ D.visiblePartIndices theta,
        theta * Fintype.card (Fin n) / 2 ≤ ((D.part a).card : ℝ) := by
      intro a ha
      simpa only [Fintype.card_fin] using R.visible_part_card_ge_half homegaOne a ha
    have hroot : (p.roots.card : ℝ) ≤
        subcriticalProfileRootFraction alpha theta epsilon * Fintype.card (Fin n) := by
      have hp := (mem_subcriticalProfileClassGraphFinset.mp hG₀).2
      rw [hp.roots_eq, Fintype.card_fin]
      exact R.badRoots_card_le halpha htheta (by omega) hR₀ homegaOne hcutoff
    have hhead := (R.profileActiveCapacityHeadroom hR₀ htheta.le homegaOne hcutoff
      (hdata G₀ hG₀).2.1 (hsparse G₀ hG₀).1 hdensity hreserve hdelta.le hshift).2
    have hround := R.profileActiveRoundingReserve hR₀ heta.le htheta hdelta hcutoff hnround
    have hb : (p.b : ℝ) ≤ subcriticalSparseSideConstant k * eta * (n : ℝ)^2 := by
      rw [← (mem_subcriticalProfileClassGraphFinset.mp hG₀).2.edge_count]
      exact (hsparse G₀ hG₀).1
    exact subcriticalProfileBound_of_geometry F p m alpha delta epsilon hk hn2
      halpha.le halphaHalf htheta.le hdelta.le hepsilon.le hdp hdq hround hret
      (by simpa only [Fintype.card_fin] using hpart)
      (by simpa only [Fintype.card_fin] using hroot) hrho
      (fun G hG ↦ (hdata G hG).1)
      (fun G hG ↦ (hsparse G hG).2.2)
      (fun G hG ↦ (hdata G hG).2.1)
      (fun G hG ↦ (hdata G hG).2.2.some.actualRetainedEdgeCountVector_mem_narrowWindow
        hR₀ heta.le htheta.le hinv homegaOne hcutoff (by linarith)
        hepsilonCap hscale (hdata G hG).1 (hdata G hG).2.1)
      (fun G hG ↦ (hdata G hG).2.2.some.defect_cost_le) hhead hb
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
    change ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

end InducedStars
