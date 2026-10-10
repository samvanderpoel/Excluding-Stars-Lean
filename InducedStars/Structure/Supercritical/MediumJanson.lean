import InducedStars.PriorInstances
import InducedStars.Structure.Supercritical.MediumCandidateCounting
import InducedStars.Structure.Supercritical.MediumJansonScalars
import InducedStars.Structure.Supercritical.MediumProbability
import Mathlib.Tactic

/-!
# Janson penalty for one supercritical medium witness

This file combines the concrete potential-star enumeration with the tagged
Bernoulli model.  The required-coordinate family lives in the one global
orientation of `lemma:super-FPiprime`, so the only non-foundational input below is the
published Riordan--Warnke principal-upset Janson theorem.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance mediumJansonDecidableRel
    {n : ℕ} (G : SimpleGraph (Fin n)) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Explicit constants -/

/-- Maximum number of random roles used by one potential induced star. -/
def supercriticalMediumRandomRoleBound (k : ℕ) : ℕ :=
  2 * (k - 2) + (k - 2) ^ 2

/-- Uniform probability floor for one complete potential-star event. -/
def supercriticalMediumEventProbabilityFloor (k : ℕ) (gamma : ℝ) : ℝ :=
  mediumSuccessProbabilityFloor k gamma ^
    supercriticalMediumRandomRoleBound k

/-- Coefficient in the concrete unordered dependency-sum estimate. -/
def supercriticalMediumDependencyCoefficient (k : ℕ) : ℝ :=
  (2 * (supercriticalMediumRandomRoleBound k) ^ 2 : ℕ)

/-- Quadratic Bernoulli penalty obtained from a candidate-count rate. -/
def supercriticalMediumBernoulliPenalty
    (k : ℕ) (gamma candidateRate : ℝ) : ℝ :=
  mediumJansonQuadraticPenalty
    (candidateRate * supercriticalMediumEventProbabilityFloor k gamma)
    (supercriticalMediumDependencyCoefficient k)

theorem supercriticalMediumEventProbabilityFloor_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    0 < supercriticalMediumEventProbabilityFloor k gamma := by
  unfold supercriticalMediumEventProbabilityFloor
  exact pow_pos (mediumSuccessProbabilityFloor_pos hk hgamma) _

theorem supercriticalMediumDependencyCoefficient_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < supercriticalMediumDependencyCoefficient k := by
  unfold supercriticalMediumDependencyCoefficient
  exact_mod_cast (show 0 < 2 * (supercriticalMediumRandomRoleBound k) ^ 2 by
    have : 0 < supercriticalMediumRandomRoleBound k := by
      unfold supercriticalMediumRandomRoleBound
      omega
    positivity)

theorem supercriticalMediumBernoulliPenalty_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma candidateRate : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (hcandidate : 0 < candidateRate) :
    0 < supercriticalMediumBernoulliPenalty k gamma candidateRate := by
  apply mediumJansonQuadraticPenalty_pos
  · exact mul_pos hcandidate
      (supercriticalMediumEventProbabilityFloor_pos hk hgamma)
  · exact supercriticalMediumDependencyCoefficient_pos hk

/-! ## Tagged overlap and event estimates -/

/-- Forgetting the block tags does not change the concrete unordered
dependency graph. -/
theorem supercriticalMediumTaggedUnorderedOverlappingPairs_eq
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {alpha : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D) :
    DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          supercriticalMediumTaggedRequired hk K.1) =
      DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1) := by
  classical
  ext KL
  rcases KL with ⟨K, L⟩
  rw [DenseGraph.FiniteBernoulliProduct.mem_unorderedOverlappingPairs,
    DenseGraph.FiniteBernoulliProduct.mem_unorderedOverlappingPairs,
    supercriticalMediumTaggedRequired_disjoint_iff hk K.1 L.1]

/-- Concrete tagged dependency-degree sum bound. -/
theorem supercriticalMediumTaggedJansonDelta_upper
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {alpha : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D) :
    (supercriticalMediumOrientedBernoulliModel w).principalJansonDelta
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          supercriticalMediumTaggedRequired hk K.1) ≤
      supercriticalMediumDependencyCoefficient k *
        (n : ℝ) ^ (2 * k - 2) := by
  apply mediumJansonDelta_upper
  rw [supercriticalMediumTaggedUnorderedOverlappingPairs_eq hk w]
  have h := mediumUnorderedOverlappingPairs_card_le_explicit hk (w := w)
  have h' :
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1)).card : ℝ) ≤
        ((2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 *
          n ^ (2 * k - 2) : ℕ) : ℝ) := by
    exact_mod_cast h
  simpa [supercriticalMediumDependencyCoefficient,
    supercriticalMediumRandomRoleBound, Nat.cast_mul, Nat.cast_pow] using h'

/-- Every concrete potential-star principal event has one uniform positive
probability floor in the oriented model. -/
theorem supercriticalMediumTaggedPrincipalEvent_probability_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {G : SimpleGraph (Fin n)} {alpha delta : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hn : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (K : SupercriticalMediumCandidateIndex hk w) :
    supercriticalMediumEventProbabilityFloor k gamma ≤
      (supercriticalMediumOrientedBernoulliModel w).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
          (supercriticalMediumTaggedRequired hk K.1)) := by
  apply principalSuccessEvent_probability_lower
      (supercriticalMediumOrientedBernoulliModel w)
      (supercriticalMediumTaggedRequired hk K.1)
      (mediumSuccessProbabilityFloor_pos hk hgamma).le
      (mediumSuccessProbabilityFloor_le_one hk hgamma)
      (supercriticalMediumTaggedRequired_card_le hk K.1)
  intro c _hc
  rw [supercriticalMediumOrientedBernoulliModel_probability]
  apply supercriticalMediumOrientedCoordinateProbability_lower_of_balanced
    hk w hdelta hbalanced hn _ hsmall c
  intro e
  convert hfull e using 1 <;> exact Subsingleton.elim _ _

/-- Candidate abundance and the event floor give the exact tagged Janson
expectation lower bound. -/
theorem supercriticalMediumTaggedJansonMu_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {G : SimpleGraph (Fin n)} {alpha delta candidateRate : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hn : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hcandidate : candidateRate * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ)) :
    candidateRate * supercriticalMediumEventProbabilityFloor k gamma *
        (n : ℝ) ^ k ≤
      (supercriticalMediumOrientedBernoulliModel w).principalJansonMu
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          supercriticalMediumTaggedRequired hk K.1) := by
  apply mediumJansonMu_lower
  · exact (supercriticalMediumEventProbabilityFloor_pos hk hgamma).le
  · exact supercriticalMediumTaggedPrincipalEvent_probability_lower
      hk hgamma w hdelta hbalanced hn hfull hsmall
  · simpa [card_supercriticalMediumCandidateIndex] using hcandidate

/-! ## Bernoulli Janson penalty -/

/-- The complete quadratic Bernoulli avoidance estimate for one medium
witness and its concrete candidate family. -/
theorem supercriticalMediumBernoulliAvoidancePenalty
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {G : SimpleGraph (Fin n)} {alpha delta candidateRate : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D)
    (hcandidateRate : 0 < candidateRate)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hnlarge : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hnone : 1 ≤ n)
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hcandidate : candidateRate * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ)) :
    (supercriticalMediumOrientedBernoulliModel w).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
          (fun K : SupercriticalMediumCandidateIndex hk w ↦
            supercriticalMediumTaggedRequired hk K.1)) ≤
      Real.exp (-(supercriticalMediumBernoulliPenalty
        k gamma candidateRate * (n : ℝ) ^ 2)) := by
  let P := supercriticalMediumOrientedBernoulliModel w
  let required := fun K : SupercriticalMediumCandidateIndex hk w ↦
    supercriticalMediumTaggedRequired hk K.1
  let a := candidateRate * supercriticalMediumEventProbabilityFloor k gamma
  let b := supercriticalMediumDependencyCoefficient k
  have ha : 0 < a := mul_pos hcandidateRate
    (supercriticalMediumEventProbabilityFloor_pos hk hgamma)
  have hb : 0 < b := supercriticalMediumDependencyCoefficient_pos hk
  have hmu : a * (n : ℝ) ^ k ≤ P.principalJansonMu required := by
    simpa [P, required, a] using supercriticalMediumTaggedJansonMu_lower
      hk hgamma w hdelta hbalanced hnlarge hfull hsmall hcandidate
  have hmuPos : 0 < P.principalJansonMu required :=
    lt_of_lt_of_le (mul_pos ha (pow_pos (by exact_mod_cast hnone) _)) hmu
  have hDelta : P.principalJansonDelta required ≤
      b * (n : ℝ) ^ (2 * k - 2) := by
    simpa [P, required, b] using
      supercriticalMediumTaggedJansonDelta_upper hk w
  apply mediumStarJansonAvoidance
      InducedStars.PriorInstances.principalJansonInput P required hmuPos
  · simpa [supercriticalMediumBernoulliPenalty, a, b] using
      mediumJansonQuadraticPenalty_mul_sq_le_mu_half
        hk hnone ha hmu
  · intro hDeltaPos
    simpa [supercriticalMediumBernoulliPenalty, a, b] using
      mediumJansonQuadraticPenalty_mul_sq_le_mu_sq_div_delta
        hk hnone ha hb hmu hDelta hDeltaPos

/-! ## Transfer back to the fixed-cardinality model -/

/-- Before absorbing the polynomial conditioning loss, the exact fixed-size
induced-free probability is bounded by the conditioning factor times the
quadratic Bernoulli penalty. -/
theorem supercriticalMediumFixedInducedFreeProbability_le
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {G : SimpleGraph (Fin n)} {alpha delta candidateRate : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D)
    (hcandidateRate : 0 < candidateRate)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hnlarge : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hnone : 1 ≤ n)
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hcandidate : candidateRate * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ)) :
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      (supercriticalMediumFixedModel w).conditioningFactor *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate * (n : ℝ) ^ 2)) := by
  calc
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      (supercriticalMediumFixedModel w).conditioningFactor *
        (supercriticalMediumOrientedBernoulliModel w).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            (fun K : SupercriticalMediumCandidateIndex hk w ↦
              supercriticalMediumTaggedRequired hk K.1)) := by
      exact supercriticalMediumFixedProbability_le_conditioning_mul_avoidance
        hk w (mediumStarCandidateFinset hk w)
    _ ≤ (supercriticalMediumFixedModel w).conditioningFactor *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate * (n : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left
        (supercriticalMediumBernoulliAvoidancePenalty hk hgamma w
          hcandidateRate hdelta hbalanced hnlarge hnone hfull hsmall
          hcandidate)
        (supercriticalMediumFixedModel w).conditioningFactor_pos.le

/-- Absorb any supplied quadratic upper bound for the conditioning factor.
The separate asymptotic block-count lemma supplies this hypothesis uniformly
in the finite instance. -/
theorem supercriticalMediumFixedInducedFreeProbability_le_exp
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {G : SimpleGraph (Fin n)} {alpha delta candidateRate conditioningRate : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G alpha D)
    (hcandidateRate : 0 < candidateRate)
    (hdelta : 0 < delta)
    (hbalanced : ∀ i : Fin (k - 1),
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) ≤
        ((D.parts i).card : ℝ))
    (hnlarge : 4 * ((k - 1 : ℕ) : ℝ) ≤ delta * (n : ℝ))
    (hnone : 1 ≤ n)
    (hfull : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) -
        supercriticalOffDiagonal k gamma| ≤ delta)
    (hsmall : 2 * delta <
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma) / 2)
    (hcandidate : candidateRate * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ))
    (hconditioning : (supercriticalMediumFixedModel w).conditioningFactor ≤
      Real.exp (conditioningRate * (n : ℝ) ^ 2)) :
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
  calc
    (supercriticalMediumFixedModel w).outcomeEventProbability
        (supercriticalMediumTaggedInducedFreeEvent k w) ≤
      (supercriticalMediumFixedModel w).conditioningFactor *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate * (n : ℝ) ^ 2)) :=
      supercriticalMediumFixedInducedFreeProbability_le hk hgamma w
        hcandidateRate hdelta hbalanced hnlarge hnone hfull hsmall hcandidate
    _ ≤ Real.exp (conditioningRate * (n : ℝ) ^ 2) *
        Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate * (n : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hconditioning (Real.exp_nonneg _)
    _ = Real.exp (-(supercriticalMediumBernoulliPenalty
          k gamma candidateRate - conditioningRate) * (n : ℝ) ^ 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

end InducedStars
