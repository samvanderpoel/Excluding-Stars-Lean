import InducedStars.Structure.Supercritical.MediumJanson
import InducedStars.Structure.Supercritical.MediumRefinement
import Mathlib.Tactic

/-!
# The supercritical medium-degree refinement-fiber penalty

This file joins the exact refinement injection with the fixed-cardinality
Janson estimate.  Candidate abundance is deliberately an explicit
hypothesis: its later uniform construction is independent of this
probability-to-counting bridge.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance mediumFiberPenaltyDecidableRel
    {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-- A quadratic Janson bound for the selected witness bounds its entire
refinement fiber, relative to the exact cross-profile multiplicity of the
graph selecting that witness. -/
theorem card_supercriticalMediumRefinedGraphFinset_le_profileMultiplicity_mul_exp
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (K : SupercriticalMediumGraph
      k hk gamma hgamma alpha m n tau hn D)
    {delta candidateRate conditioningRate : ℝ}
    (hcandidateRate : 0 < candidateRate)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hnlarge : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hnone : 1 ≤ n)
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity K.1 (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hcandidate : candidateRate * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk
        (supercriticalMediumWitnessOfMem halpha K.2)).card : ℝ))
    (hconditioning :
      (supercriticalMediumFixedModel
        (supercriticalMediumWitnessOfMem halpha K.2)).conditioningFactor ≤
          Real.exp (conditioningRate * (n : ℝ) ^ 2)) :
    ((supercriticalMediumRefinedGraphFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card : ℝ) ≤
      (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
  let w := supercriticalMediumWitnessOfMem halpha K.2
  let M := supercriticalMediumFixedModel w
  let E := supercriticalMediumInducedFreeSampleEvent halpha K
  have hcount :=
    card_supercriticalMediumRefinedGraphFinset_le_profileMultiplicity_mul_probability
      halpha K
  have hjanson :
      M.outcomeEventProbability
          (supercriticalMediumTaggedInducedFreeEvent k w) ≤
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
    exact supercriticalMediumFixedInducedFreeProbability_le_exp
      hk hgamma w hcandidateRate hdelta hbalanced hnlarge hnone hfull hsmall
        hcandidate hconditioning
  have hsample :
      M.eventProbability E ≤
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
    rw [show E = M.sampleEvent
        (supercriticalMediumTaggedInducedFreeEvent k w) by
      simpa [E, M, w] using
        supercriticalMediumInducedFreeSampleEvent_eq_sampleEvent halpha K]
    simpa [DenseGraph.FixedCardinalityBlockModel.outcomeEventProbability]
      using hjanson
  calc
    ((supercriticalMediumRefinedGraphFinset
      k hk gamma hgamma alpha halpha m n tau hn
        (supercriticalMediumRefinementKeyOf halpha K)).card : ℝ) ≤
      (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        M.eventProbability E := by simpa [M, E, w] using hcount
    _ ≤ (supercriticalProfileMultiplicity (crossEdgeProfile K.1 D) : ℝ) *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsample (by positivity)

end InducedStars
