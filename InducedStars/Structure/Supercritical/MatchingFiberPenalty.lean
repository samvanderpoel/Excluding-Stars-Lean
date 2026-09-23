import InducedStars.Structure.Supercritical.MatchingCandidateOverlapTotal
import InducedStars.Structure.Supercritical.MatchingEncoding
import InducedStars.Structure.Supercritical.MatchingJanson
import Mathlib.Tactic

/-!
# Concrete Janson penalty for a fixed supercritical defect/profile fiber

This file instantiates the representation-independent matching Janson layer
with the tagged full-profile model and the concrete candidate family.  It
keeps the candidate-abundance and overlap constants explicit so the finite
enumeration module remains the unique source of those estimates.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-- The final matching-defect rate after substituting the concrete candidate
abundance and dependency-count coefficients.  It depends only on `k` and
`gamma`. -/
def supercriticalMatchingPenaltyConstant (k : ℕ) (gamma : ℝ) : ℝ :=
  supercriticalMatchingFixedPenalty k gamma
    (supercriticalMatchingCandidateRate k)
    (supercriticalMatchingDependencyCoefficient k : ℝ)

theorem supercriticalMatchingPenaltyConstant_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    0 < supercriticalMatchingPenaltyConstant k gamma := by
  exact supercriticalMatchingFixedPenalty_pos hk hgamma
    (supercriticalMatchingCandidateRate_pos hk)
    (supercriticalMatchingDependencyCoefficient_cast_pos hk)

/-! ## Concrete required family and event floor -/

/-- Required tagged coordinates for the complete matching-candidate family. -/
def supercriticalMatchingTaggedRequiredFamily
    {k n : ℕ} (hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (profile : SupercriticalEdgeProfile D) :
    SupercriticalMatchingCandidateIndex hk M →
      Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  fun K ↦ matchingRequiredSuccessCoordinates hk profile (K.candidate hk)

/-- Every required coordinate has at least the common success probability in
the one matching-wide orientation. -/
theorem supercriticalMatchingOrientedCoordinateProbability_lower
    {k n : ℕ} (_hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    {m : ℕ} {rho delta : ℝ} {t : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    {qFloor : ℝ}
    (hlower : qFloor ≤ rho - delta)
    (hupper : rho + delta ≤ 1 - qFloor)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    qFloor ≤ (orientedMatchingBernoulliProduct M profile).probability c := by
  have hboth := supercriticalProfile_or_complement_probability_lower
    hprofile hlower hupper c
  rw [orientedMatchingBernoulliProduct_probability]
  by_cases hc : matchingCoordinateSuccessPresent M profile c
  · simpa [hc] using hboth.1
  · simpa [hc] using hboth.2

/-- Uniform complete-event probability for every concrete matching
candidate. -/
theorem supercriticalMatchingPrincipalEvent_probability_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    {m : ℕ} {rho delta : ℝ} {t : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    (hlower : supercriticalMatchingSuccessFloor k gamma ≤ rho - delta)
    (hupper : rho + delta ≤
      1 - supercriticalMatchingSuccessFloor k gamma)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    supercriticalMatchingEventProbabilityFloor k gamma ≤
      (orientedMatchingBernoulliProduct M profile).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
          (supercriticalMatchingTaggedRequiredFamily hk M profile K)) := by
  apply principalSuccessEvent_probability_lower
      (orientedMatchingBernoulliProduct M profile)
      (supercriticalMatchingTaggedRequiredFamily hk M profile K)
      (supercriticalMatchingSuccessFloor_pos hk hgamma).le
      (supercriticalMatchingSuccessFloor_le_one hk hgamma)
      (matchingRequiredSuccessCoordinates_card_le_roleBound
        hk profile (K.candidate hk))
  intro c _hc
  exact supercriticalMatchingOrientedCoordinateProbability_lower
    hk M profile hprofile hlower hupper c

/-! ## Concrete expectation, dependency, and Bernoulli avoidance -/

/-- Candidate abundance gives the exact matching-scale Janson expectation
lower bound. -/
theorem supercriticalMatchingTaggedJansonMu_lower
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    {m : ℕ} {rho delta : ℝ} {t : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    (hlower : supercriticalMatchingSuccessFloor k gamma ≤ rho - delta)
    (hupper : rho + delta ≤
      1 - supercriticalMatchingSuccessFloor k gamma)
    {candidateRate : ℝ}
    (hcard : candidateRate * (M.edges.card : ℝ) *
        (n : ℝ) ^ (k - 1) ≤
      (Fintype.card (SupercriticalMatchingCandidateIndex hk M) : ℝ)) :
    candidateRate * supercriticalMatchingEventProbabilityFloor k gamma *
        (M.edges.card : ℝ) * (n : ℝ) ^ (k - 1) ≤
      (orientedMatchingBernoulliProduct M profile).principalJansonMu
        (supercriticalMatchingTaggedRequiredFamily hk M profile) := by
  apply supercriticalMatchingJansonMu_lower
  · exact (supercriticalMatchingEventProbabilityFloor_pos hk hgamma).le
  · exact supercriticalMatchingPrincipalEvent_probability_lower
      hk hgamma M profile hprofile hlower hupper
  · exact hcard

/-- A concrete unordered-overlap count gives the tagged matching dependency
sum bound. -/
theorem supercriticalMatchingTaggedJansonDelta_upper
    {k n : ℕ} (hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (profile : SupercriticalEdgeProfile D)
    {dependencyCoefficient : ℝ}
    (hpairs :
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (supercriticalMatchingTaggedRequiredFamily hk M profile)).card : ℝ) ≤
          dependencyCoefficient * (M.edges.card : ℝ) *
            (n : ℝ) ^ (2 * k - 3)) :
    (orientedMatchingBernoulliProduct M profile).principalJansonDelta
        (supercriticalMatchingTaggedRequiredFamily hk M profile) ≤
      dependencyCoefficient * (M.edges.card : ℝ) *
        (n : ℝ) ^ (2 * k - 3) :=
  supercriticalMatchingJansonDelta_upper
    (orientedMatchingBernoulliProduct M profile)
    (supercriticalMatchingTaggedRequiredFamily hk M profile) hpairs

/-- Complete Bernoulli avoidance estimate for the concrete matching family. -/
theorem supercriticalMatchingTaggedBernoulliAvoidancePenalty
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    {m : ℕ} {rho delta : ℝ} {t : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    (hlower : supercriticalMatchingSuccessFloor k gamma ≤ rho - delta)
    (hupper : rho + delta ≤
      1 - supercriticalMatchingSuccessFloor k gamma)
    {candidateRate dependencyCoefficient : ℝ}
    (hcandidate : 0 < candidateRate)
    (hdependency : 0 < dependencyCoefficient)
    (hn : 1 ≤ n) (hmatching : 1 ≤ M.edges.card)
    (hcard : candidateRate * (M.edges.card : ℝ) *
        (n : ℝ) ^ (k - 1) ≤
      (Fintype.card (SupercriticalMatchingCandidateIndex hk M) : ℝ))
    (hpairs :
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (supercriticalMatchingTaggedRequiredFamily hk M profile)).card : ℝ) ≤
          dependencyCoefficient * (M.edges.card : ℝ) *
            (n : ℝ) ^ (2 * k - 3)) :
    (orientedMatchingBernoulliProduct M profile).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
          (supercriticalMatchingTaggedRequiredFamily hk M profile)) ≤
      Real.exp (-(matchingJansonLinearPenalty
          (candidateRate * supercriticalMatchingEventProbabilityFloor k gamma)
          dependencyCoefficient *
        (M.edges.card : ℝ) * (n : ℝ))) := by
  apply supercriticalMatchingBernoulliAvoidancePenalty
      (orientedMatchingBernoulliProduct M profile)
      (supercriticalMatchingTaggedRequiredFamily hk M profile)
      hk hn hmatching hcandidate
      (supercriticalMatchingEventProbabilityFloor_pos hk hgamma)
      hdependency
  · exact supercriticalMatchingTaggedJansonMu_lower
      hk hgamma M profile hprofile hlower hupper hcard
  · exact supercriticalMatchingTaggedJansonDelta_upper
      hk M profile hpairs

/-! ## Fixed-profile event transfer -/

/-- Flipping the literal induced-free event by the matching-wide orientation
puts it inside the concrete principal avoidance event. -/
theorem supercriticalProfileInducedFree_flipEvent_subset_matchingAvoidance
    {k n : ℕ} (hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (profile : SupercriticalEdgeProfile D) :
    DenseGraph.FiniteBernoulliProduct.flipEvent
        (matchingGlobalFlipSet M profile)
        (supercriticalProfileTaggedInducedFreeEvent k D T profile) ⊆
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
        (supercriticalMatchingTaggedRequiredFamily hk M profile) := by
  classical
  intro outcome hout
  rw [DenseGraph.FiniteBernoulliProduct.mem_flipEvent] at hout
  have hfree :=
    (mem_supercriticalProfileTaggedInducedFreeEvent.mp hout)
  have hav := inducedStarFree_implies_matchingPrincipalAvoidance
    hk profile (fun K : SupercriticalMatchingCandidateIndex hk M ↦
      K.candidate hk)
    (DenseGraph.FiniteBernoulliProduct.flipOutcome
      (matchingGlobalFlipSet M profile) outcome) hfree
  simpa [matchingOrientedOutcome,
    supercriticalMatchingTaggedRequiredFamily,
    DenseGraph.FiniteBernoulliProduct.flipOutcome,
    symmDiff_assoc] using hav

/-- Exact fixed-count-to-oriented-Bernoulli comparison for the literal
induced-free event in one prescribed profile fiber. -/
theorem supercriticalMatchingFixedProfileProbability_le_conditioning_mul_avoidance
    {k n : ℕ} (hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (profile : SupercriticalEdgeProfile D) :
    (supercriticalFixedProfileBlockModel D profile).outcomeEventProbability
        (supercriticalProfileTaggedInducedFreeEvent k D T profile) ≤
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor *
        (orientedMatchingBernoulliProduct M profile).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            (supercriticalMatchingTaggedRequiredFamily hk M profile)) := by
  exact supercriticalMatchingFixedProbability_le_conditioning_mul_avoidance
    (supercriticalFixedProfileBlockModel D profile)
    (supercriticalProfileTaggedInducedFreeEvent k D T profile)
    (matchingGlobalFlipSet M profile)
    (supercriticalMatchingTaggedRequiredFamily hk M profile)
    (supercriticalProfileInducedFree_flipEvent_subset_matchingAvoidance
      hk M profile)

/-- Fixed-profile induced-free probability with the final defect-count
exponent.  The `h = 0` case is handled by the generic transfer theorem. -/
theorem supercriticalMatchingFixedProfileInducedFreeProbability_le_exp
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    {m : ℕ} {rho delta : ℝ} {t : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    (hlower : supercriticalMatchingSuccessFloor k gamma ≤ rho - delta)
    (hupper : rho + delta ≤
      1 - supercriticalMatchingSuccessFloor k gamma)
    {candidateRate dependencyCoefficient cMat scale : ℝ} {h : ℕ}
    (hcandidate : 0 < candidateRate)
    (hdependency : 0 < dependencyCoefficient)
    (hcMat : 0 ≤ cMat)
    (hn : 1 ≤ n) (hmatching : h ≠ 0 → 1 ≤ M.edges.card)
    (hdefect : (h : ℝ) ≤ scale * (M.edges.card : ℝ))
    (hrate : 2 * cMat * scale ≤
      matchingJansonLinearPenalty
        (candidateRate * supercriticalMatchingEventProbabilityFloor k gamma)
        dependencyCoefficient)
    (hconditioning : h ≠ 0 →
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor ≤
        Real.exp (cMat * (h : ℝ) * (n : ℝ)))
    (hcard : candidateRate * (M.edges.card : ℝ) *
        (n : ℝ) ^ (k - 1) ≤
      (Fintype.card (SupercriticalMatchingCandidateIndex hk M) : ℝ))
    (hpairs :
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (supercriticalMatchingTaggedRequiredFamily hk M profile)).card : ℝ) ≤
          dependencyCoefficient * (M.edges.card : ℝ) *
            (n : ℝ) ^ (2 * k - 3)) :
    (supercriticalFixedProfileBlockModel D profile).outcomeEventProbability
        (supercriticalProfileTaggedInducedFreeEvent k D T profile) ≤
      Real.exp (-(cMat * (h : ℝ) * (n : ℝ))) := by
  apply supercriticalMatchingFixedInducedFreeProbability_le_exp
    (supercriticalFixedProfileBlockModel D profile)
    (supercriticalProfileTaggedInducedFreeEvent k D T profile)
    hcMat hdefect hrate hconditioning
  intro hh
  calc
    (supercriticalFixedProfileBlockModel D profile).outcomeEventProbability
        (supercriticalProfileTaggedInducedFreeEvent k D T profile) ≤
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor *
        (orientedMatchingBernoulliProduct M profile).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            (supercriticalMatchingTaggedRequiredFamily hk M profile)) :=
      supercriticalMatchingFixedProfileProbability_le_conditioning_mul_avoidance
        hk M profile
    _ ≤ (supercriticalFixedProfileBlockModel D profile).conditioningFactor *
        Real.exp (-(matchingJansonLinearPenalty
            (candidateRate * supercriticalMatchingEventProbabilityFloor k gamma)
            dependencyCoefficient *
          (M.edges.card : ℝ) * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (supercriticalMatchingTaggedBernoulliAvoidancePenalty
          hk hgamma M profile hprofile hlower hupper
          hcandidate hdependency hn (hmatching hh) hcard hpairs)
        (supercriticalFixedProfileBlockModel D profile).conditioningFactor_pos.le

/-! ## Exact profile-fiber cardinality -/

/-- The explicit finite-geometry matching penalty after the candidate and
overlap enumerations have been supplied.  The homogeneous matching is the
canonical selected half of the dominant location fiber, so its built-in
`matchingNumber_le` field is exactly the paper's `4(k-1)` loss.

This theorem uses only the Riordan--Warnke input through the preceding
Janson theorem.  The close-structure theorem is not used here; its local
role is to establish the low-degree hypotheses consumed by the concrete
enumeration estimates. -/
theorem supercriticalMatchingPenalty_of_enumeration
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hnVertices : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hnVertices D)
    {rho delta : ℝ}
    (hprofile : SupercriticalProfileAtShift D m rho delta
      (supercriticalDefectShift T D) profile)
    (hlower : supercriticalMatchingSuccessFloor k gamma ≤ rho - delta)
    (hupper : rho + delta ≤
      1 - supercriticalMatchingSuccessFloor k gamma)
    {candidateRate dependencyCoefficient : ℝ}
    (hcandidate : 0 < candidateRate)
    (hdependency : 0 < dependencyCoefficient)
    (hn : 1 ≤ n)
    (hconditioning : supercriticalMatchingNumber D T ≠ 0 →
      let cMat := supercriticalMatchingFixedPenalty
        k gamma candidateRate dependencyCoefficient
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor ≤
        Real.exp (cMat * (supercriticalMatchingNumber D T : ℝ) * (n : ℝ)))
    (hcard :
      let M := selectedSupercriticalHomogeneousMatching D T hT
      candidateRate * (M.edges.card : ℝ) * (n : ℝ) ^ (k - 1) ≤
        (Fintype.card (SupercriticalMatchingCandidateIndex hk M) : ℝ))
    (hpairs :
      let M := selectedSupercriticalHomogeneousMatching D T hT
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (supercriticalMatchingTaggedRequiredFamily hk M profile)).card : ℝ) ≤
          dependencyCoefficient * (M.edges.card : ℝ) *
            (n : ℝ) ^ (2 * k - 3)) :
    ((supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hnVertices D T profile).card : ℝ) ≤
      (supercriticalProfileMultiplicity profile : ℝ) *
        Real.exp (-(supercriticalMatchingFixedPenalty
          k gamma candidateRate dependencyCoefficient *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  let cMat := supercriticalMatchingFixedPenalty
    k gamma candidateRate dependencyCoefficient
  have hcMat : 0 ≤ cMat :=
    (supercriticalMatchingFixedPenalty_pos
      hk hgamma hcandidate hdependency).le
  have hmatching : supercriticalMatchingNumber D T ≠ 0 →
      1 ≤ M.edges.card := by
    intro hh
    have hpos : 0 < supercriticalMatchingNumber D T := Nat.pos_of_ne_zero hh
    have hle := M.matchingNumber_le
    by_contra hnot
    have hz : M.edges.card = 0 := by omega
    simp [hz] at hle
    omega
  have hdefect : (supercriticalMatchingNumber D T : ℝ) ≤
      (4 * ((k - 1 : ℕ) : ℝ)) * (M.edges.card : ℝ) := by
    exact_mod_cast M.matchingNumber_le
  have hrate : 2 * cMat * (4 * ((k - 1 : ℕ) : ℝ)) ≤
      matchingJansonLinearPenalty
        (candidateRate * supercriticalMatchingEventProbabilityFloor k gamma)
        dependencyCoefficient := by
    have heq := twice_supercriticalMatchingFixedPenalty_mul_scale
      (gamma := gamma) (candidateRate := candidateRate)
      (dependencyCoefficient := dependencyCoefficient) hk
    simpa [cMat, supercriticalMatchingBernoulliPenalty] using heq.le
  have hprob :=
    supercriticalMatchingFixedProfileInducedFreeProbability_le_exp
      hk hgamma M profile hprofile hlower hupper
      hcandidate hdependency hcMat hn hmatching hdefect hrate
      (fun hh ↦ by simpa [cMat] using hconditioning hh)
      (by simpa [M] using hcard) (by simpa [M] using hpairs)
  have hencode :=
    card_supercriticalFixedDefectProfileGraphFinset_le_profileMultiplicity_mul_probability
      k hk gamma hgamma alpha m n tau hnVertices D T profile
  rw [supercriticalFixedProfileInducedFreeSampleEvent_eq_sampleEvent]
      at hencode
  have hencode' :
      ((supercriticalFixedDefectProfileGraphFinset
          k hk gamma hgamma alpha m n tau hnVertices D T profile).card : ℝ) ≤
        (supercriticalProfileMultiplicity profile : ℝ) *
          (supercriticalFixedProfileBlockModel D profile).outcomeEventProbability
            (supercriticalProfileTaggedInducedFreeEvent k D T profile) := by
    simpa [DenseGraph.FixedCardinalityBlockModel.outcomeEventProbability]
      using hencode
  exact hencode'.trans
    (mul_le_mul_of_nonneg_left hprob (by positivity))

/-- The core finite penalty after the geometric abundance hypotheses have
been made explicit.  Candidate abundance and the density floor are discharged
here; only the quantitative unordered-overlap estimate remains as a separate
input.  This separation makes the trust boundary transparent: the
probabilistic part below the overlap count uses only Riordan--Warnke. -/
theorem supercriticalMatchingPenalty_of_quantitativeOverlap
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hnVertices : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (profile : SupercriticalEdgeProfile D)
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hnVertices D)
    {delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdeltaCount : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hdeltaFloor : 4 * delta ≤
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma))
    (hnlarge : (100 * (k : ℝ)) ≤ (n : ℝ))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) delta
      (supercriticalDefectShift T D) profile)
    {dependencyCoefficient : ℝ}
    (hdependency : 0 < dependencyCoefficient)
    (hn : 1 ≤ n)
    (hconditioning : supercriticalMatchingNumber D T ≠ 0 →
      let cMat := supercriticalMatchingFixedPenalty k gamma
        (supercriticalMatchingCandidateRate k) dependencyCoefficient
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor ≤
        Real.exp (cMat * (supercriticalMatchingNumber D T : ℝ) * (n : ℝ)))
    (hpairs :
      let M := selectedSupercriticalHomogeneousMatching D T hT
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (supercriticalMatchingTaggedRequiredFamily hk M profile)).card : ℝ) ≤
          dependencyCoefficient * (M.edges.card : ℝ) *
            (n : ℝ) ^ (2 * k - 3)) :
    ((supercriticalFixedDefectProfileGraphFinset
        k hk gamma hgamma alpha m n tau hnVertices D T profile).card : ℝ) ≤
      (supercriticalProfileMultiplicity profile : ℝ) *
        Real.exp (-(supercriticalMatchingFixedPenalty k gamma
          (supercriticalMatchingCandidateRate k) dependencyCoefficient *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  have hfloor := supercriticalMatchingSuccessFloor_densityBand
    hk hgamma hdeltaFloor
  have hcardFinset := matchingStarCandidateFinset_card_lower_rate hk
    halpha hdelta0 hdeltaCount hnlarge D T hT hclose hlow
  have hcard : supercriticalMatchingCandidateRate k *
      (M.edges.card : ℝ) * (n : ℝ) ^ (k - 1) ≤
        (Fintype.card (SupercriticalMatchingCandidateIndex hk M) : ℝ) := by
    rw [card_supercriticalMatchingCandidateIndex]
    simpa [M] using hcardFinset
  exact supercriticalMatchingPenalty_of_enumeration
    k hk gamma hgamma alpha m n tau hnVertices D T profile hT
    hprofile hfloor.1 hfloor.2
    (supercriticalMatchingCandidateRate_pos hk) hdependency hn
    hconditioning (by simpa [M] using hcard) (by simpa [M] using hpairs)

/-- Core matching-defect penalty from explicit close-structure geometry.

The threshold is uniform in `alpha`, `delta`, and all finite data because it
only absorbs the fixed-profile conditioning polynomial into the concrete
positive rate `supercriticalMatchingPenaltyConstant k gamma`.  Candidate
abundance and overlap counting are local finite theorems.  Consequently, the
only project-specific axiom below this result is the approved
Riordan--Warnke principal Janson input. -/
theorem supercriticalMatchingPenalty_of_closeStructure
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (alpha : ℝ) (m : ℕ) (tau : ℝ) (hnVertices : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
        (profile : SupercriticalEdgeProfile D)
        (hT : T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hnVertices D)
        (delta : ℝ),
        alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * (k : ℝ))) →
        0 ≤ delta →
        delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)) →
        4 * delta ≤ min (supercriticalOffDiagonal k gamma)
          (1 - supercriticalOffDiagonal k gamma) →
        (∀ i : Fin (k - 1),
          |((D.parts i).card : ℝ) -
              (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n) →
        (∀ v : Fin n, ∀ i : Fin (k - 1),
          HasLowDegreeInPart T alpha D v i) →
        SupercriticalProfileAtShift D m
          (supercriticalOffDiagonal k gamma) delta
          (supercriticalDefectShift T D) profile →
        ((supercriticalFixedDefectProfileGraphFinset
            k hk gamma hgamma alpha m n tau hnVertices D T profile).card : ℝ) ≤
          (supercriticalProfileMultiplicity profile : ℝ) *
            Real.exp (-(supercriticalMatchingPenaltyConstant k gamma *
              (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  have hcMat := supercriticalMatchingPenaltyConstant_pos hk hgamma
  filter_upwards
      [eventually_supercriticalFixedProfile_conditioningFactor_le_exp_mul_hn
        k hcMat,
       eventually_ge_atTop (1 : ℕ),
       eventually_ge_atTop (100 * k)]
      with n hconditioning hn hnlarge
  intro alpha m tau hnVertices D T profile hT delta
    halpha hdelta0 hdeltaCount hdeltaFloor hclose hlow hprofile
  have hnlargeReal : (100 * (k : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hnlarge
  have hpenalty := supercriticalMatchingPenalty_of_quantitativeOverlap
    k hk gamma hgamma alpha m n tau hnVertices D T profile hT
    halpha hdelta0 hdeltaCount hdeltaFloor hnlargeReal hclose hlow hprofile
    (supercriticalMatchingDependencyCoefficient_cast_pos hk) hn
    (fun hh ↦ hconditioning D profile (supercriticalMatchingNumber D T)
      (Nat.one_le_iff_ne_zero.mpr hh))
    (by
      change ((matchingOverlappingCandidatePairFinset
        (M := selectedSupercriticalHomogeneousMatching D T hT)
        hk profile).card : ℝ) ≤ _
      exact matchingOverlappingCandidatePairFinset_card_cast_le
        (M := selectedSupercriticalHomogeneousMatching D T hT) hk profile)
  simpa [supercriticalMatchingPenaltyConstant] using hpenalty

end InducedStars
