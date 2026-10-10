import InducedStars.Structure.Subcritical.SeparatedBallComparison
import InducedStars.Structure.Subcritical.DistinguishedConcentrationCore

/-!
# Distinguished subcritical cut concentration

The local candidate-ball estimate is now proved from the
retained-key count and exact matching transfers. The finite optimizer cover
uses one common positive radius selected before the candidate centres.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical
namespace InducedStars

/-- A common positive ball radius makes every separated candidate's local
probability tend to zero. The original edge-count sequence is unrestricted
beyond its prescribed asymptotic density. -/
theorem subcriticalSeparatedCandidateBallProbability_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) {gamma separation tauMax : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hsep : 0 < separation)
    (htauMax : 0 < tauMax) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      ∀ L : AdmissibleBlockSequence k, IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          Tendsto (fun n ↦
            ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) /
              (inducedStarFreeGraphFinsetWithEdges k n (m n)).card) atTop (𝓝 0) := by
  obtain ⟨nu, hnu, tau, htau, htauMax', hbound⟩ :=
    subcriticalSeparatedCandidateBallComparison k hk hgamma hsep htauMax
  refine ⟨tau, htau, htauMax', ?_⟩
  intro L hL hdist m hm
  have hpos := eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma
    ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩ m hm
  have hlimit : Tendsto (fun n : ℕ ↦ Real.exp (-nu*n*Real.log n)) atTop (𝓝 0) := by
    have hrate : subcriticalSeparatedComparisonRate (512*nu) = nu := by
      unfold subcriticalSeparatedComparisonRate
      ring
    simpa only [hrate] using tendsto_subcriticalSeparatedComparison_zero
      (show 0 < 512*nu by positivity)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity)
    (g := fun n : ℕ ↦ Real.exp (-nu*n*Real.log n))
  · filter_upwards [hbound L hL hdist m hm, hpos] with n hn hnonempty
    have hden : (0 : ℝ) < (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := by
      exact_mod_cast hnonempty.card_pos
    apply (div_le_iff₀ hden).mpr
    simpa only [inducedStarFreeGraphCountWithEdges, inducedFreeGraphCountWithEdges,
      inducedStarFreeGraphFinsetWithEdges, mul_comm] using hn
  · exact hlimit

/-- Every fixed positive cut neighbourhood of the distinguished one-block
optimizer contains asymptotically all induced-star-free exact-edge graphs.
No separated-ball counting hypothesis remains in the public theorem. -/
theorem subcriticalDistinguishedCutConcentration
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (radius : ℝ) (hradius : 0 < radius)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ subcriticalDistinguishedFarProbability k hk gamma hgamma radius n (m n))
      atTop (𝓝 0) := by
  obtain ⟨tau, htau, htauRadius, hlocal⟩ :=
    subcriticalSeparatedCandidateBallProbability_tendsto_zero k hk hgamma
      (show 0 < radius/2 by positivity) hradius
  exact subcriticalDistinguishedCutConcentration_of_candidate_bounds k hk hgamma
    hradius htau htauRadius m hm (fun L hL hdist ↦ hlocal L hL hdist m hm)

end InducedStars
