import DenseGraph.FiniteModels.BernoulliPolarity
import InducedStars.Structure.Supercritical.MatchingJanson

/-!
# Capability-parametric residual matching Janson bounds

The residual-star geometry supplies a candidate count and an unordered
overlap count.  This module reuses the established matching-scale scalar
calculation.  In particular its Janson capability is an explicit argument:
none of the theorems here instantiates a published assumption.

Mixed edge/nonedge cylinders are transported by one shared polarity, as
used in the paper.  The inherited scalar proof separates the zero-dependency
case before using a denominator involving the dependency sum.
-/

noncomputable section

open Finset

namespace InducedStars

universe u v

/-- Explicit residual Janson rate from its expectation and unordered-overlap
coefficients.  These coefficients can be fixed before the defect parameters. -/
def subcriticalResidualJansonLinearConstant (cMu cDelta : ℝ) : ℝ :=
  matchingJansonLinearPenalty cMu cDelta

theorem subcriticalResidualJansonLinearConstant_pos {cMu cDelta : ℝ}
    (hMu : 0 < cMu) (hDelta : 0 < cDelta) :
    0 < subcriticalResidualJansonLinearConstant cMu cDelta :=
  matchingJansonLinearPenalty_pos hMu hDelta

/-- Candidate avoidance at the residual matching scale.  For positive `n,t`,
the reused proof treats `Delta = 0` explicitly.  When either scale is zero,
the conclusion is the exact probability bound one. -/
theorem subcriticalResidualCandidateAvoidanceProbability_le
    {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (J : DenseGraph.PrincipalJansonInput.{u, v})
    (P : DenseGraph.FiniteBernoulliProduct Ω) (required : I → Finset Ω)
    {k n t : ℕ} {cMu cDelta : ℝ}
    (hk : 3 ≤ k) (hMu : 0 < cMu) (hDelta : 0 < cDelta)
    (hmu : cMu * (t : ℝ) * (n : ℝ) ^ (k - 1) ≤
      P.principalJansonMu required)
    (hdelta : P.principalJansonDelta required ≤
      cDelta * (t : ℝ) * (n : ℝ) ^ (2 * k - 3)) :
    P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
      Real.exp (-(subcriticalResidualJansonLinearConstant cMu cDelta *
        (t : ℝ) * (n : ℝ))) := by
  by_cases hn : n = 0
  · simpa [hn] using P.eventProbability_le_one
      (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required)
  by_cases ht : t = 0
  · simpa [ht] using P.eventProbability_le_one
      (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required)
  exact matchingJansonAvoidance J P required hk (Nat.one_le_iff_ne_zero.mpr hn)
    (Nat.one_le_iff_ne_zero.mpr ht) hMu hDelta hmu hdelta

/-- Uniform atom floor, including after the global edge/nonedge polarity. -/
theorem subcriticalResidualPolarizedPrincipalProbability_lower
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : DenseGraph.FiniteBernoulliProduct Ω) (flip required : Finset Ω)
    {rho : ℝ} {M : ℕ} (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hband : ∀ e, P.probability e ∈ Set.Icc rho (1 - rho))
    (hcard : required.card ≤ M) :
    rho ^ M ≤ (P.complementCoordinates flip).eventProbability
      (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent required) := by
  apply principalSuccessEvent_probability_lower _ _ hrho0 hrho1 hcard
  intro e _
  exact (P.complementCoordinates_probability_mem_symmetric_band flip hband e).1

/-- Candidate abundance and a lower atom probability give the required
expectation estimate, without a probabilistic capability. -/
theorem subcriticalResidualCandidateMu_lower
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω) (required : I → Finset Ω)
    {k n t : ℕ} {candidateRate eventFloor : ℝ}
    (hevent0 : 0 ≤ eventFloor)
    (hevent : ∀ i, eventFloor ≤ P.eventProbability
      (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent (required i)))
    (hcard : candidateRate * (t : ℝ) * (n : ℝ) ^ (k - 1) ≤
      (Fintype.card I : ℝ)) :
    candidateRate * eventFloor * (t : ℝ) * (n : ℝ) ^ (k - 1) ≤
      P.principalJansonMu required :=
  supercriticalMatchingJansonMu_lower P required hevent0 hevent hcard

/-- The unordered overlap count bounds the unordered dependency sum because
every joint event has probability at most one. -/
theorem subcriticalResidualCandidateDelta_upper
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω) (required : I → Finset Ω)
    {k n t : ℕ} {cDelta : ℝ}
    (hpairs : ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      required).card : ℝ) ≤ cDelta * (t : ℝ) * (n : ℝ) ^ (2 * k - 3)) :
    P.principalJansonDelta required ≤
      cDelta * (t : ℝ) * (n : ℝ) ^ (2 * k - 3) :=
  supercriticalMatchingJansonDelta_upper P required hpairs

/-- Transport an actual event into candidate avoidance by one fixed polarity.
The inclusion is the sole geometry-dependent input at this step. -/
theorem subcriticalResidualPolarizedAvoidanceProbability_le
    {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (J : DenseGraph.PrincipalJansonInput.{u, v})
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (event : Finset (Finset Ω)) (flip : Finset Ω) (required : I → Finset Ω)
    {k n t : ℕ} {cMu cDelta : ℝ}
    (hk : 3 ≤ k) (hMu : 0 < cMu) (hDelta : 0 < cDelta)
    (hsubset : DenseGraph.FiniteBernoulliProduct.flipEvent flip event ⊆
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required)
    (hmu : cMu * (t : ℝ) * (n : ℝ) ^ (k - 1) ≤
      (P.complementCoordinates flip).principalJansonMu required)
    (hdelta : (P.complementCoordinates flip).principalJansonDelta required ≤
      cDelta * (t : ℝ) * (n : ℝ) ^ (2 * k - 3)) :
    P.eventProbability event ≤
      Real.exp (-(subcriticalResidualJansonLinearConstant cMu cDelta *
        (t : ℝ) * (n : ℝ))) := by
  rw [← P.complementCoordinates_eventProbability_flipEvent flip event]
  exact ((P.complementCoordinates flip).eventProbability_mono hsubset).trans
    (subcriticalResidualCandidateAvoidanceProbability_le J _ required
      hk hMu hDelta hmu hdelta)

/-- A thinned matching of size at least `lambda*ell/(8*kappa)` converts the
candidate rate into the profile matching scale. -/
theorem subcriticalResidualCandidateRate_le_matchingRate
    {c lambda kappa : ℝ} {t ell n : ℕ}
    (hc : 0 ≤ c) (hlambda : 0 ≤ lambda) (hkappa : 0 < kappa)
    (hsize : lambda * (ell : ℝ) / (8 * kappa) ≤ (t : ℝ)) :
    Real.exp (-(c * (t : ℝ) * (n : ℝ))) ≤
      Real.exp (-((c * lambda / 8) / kappa * (ell : ℝ) * (n : ℝ))) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  calc
    (c * lambda / 8) / kappa * (ell : ℝ) * (n : ℝ) =
        c * (lambda * (ell : ℝ) / (8 * kappa)) * (n : ℝ) := by ring
    _ ≤ c * (t : ℝ) * (n : ℝ) := by gcongr

end InducedStars
