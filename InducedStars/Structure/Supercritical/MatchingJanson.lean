import InducedStars.PriorInstances
import InducedStars.Structure.Supercritical.MatchingJansonScalars
import InducedStars.Structure.Supercritical.MediumCandidates
import Mathlib.Tactic

/-!
# Abstract Janson and fixed-count transfer for the matching penalty

The concrete matching geometries supply only three inputs to this module: a
finite candidate family, one principal required-coordinate set per candidate,
and an unordered-overlap count.  The results below convert those inputs into
the linear matching penalty and then perform the exact-cardinality transfer.

The sole probabilistic theorem used in the Janson step is the approved
Riordan--Warnke principal-upset input exposed by `PriorInstances`.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-! ## Expectation and dependency adapters -/

/-- Candidate abundance and a uniform event floor give expectation of order
`q * n^(k-1)`.  This statement is representation-independent. -/
theorem supercriticalMatchingJansonMu_lower
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) {k n q : ℕ}
    {candidateRate eventFloor : ℝ}
    (hevent0 : 0 ≤ eventFloor)
    (hevent : ∀ i, eventFloor ≤ P.eventProbability
      (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent (required i)))
    (hcard : candidateRate * (q : ℝ) * (n : ℝ) ^ (k - 1) ≤
      (Fintype.card I : ℝ)) :
    candidateRate * eventFloor * (q : ℝ) * (n : ℝ) ^ (k - 1) ≤
      P.principalJansonMu required := by
  have h := mediumJansonMu_lower P required hevent0 hevent
    (c := candidateRate * (q : ℝ)) (k := k - 1) (n := n) (by
      simpa [mul_assoc] using hcard)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-- An unordered overlapping-pair estimate gives the matching dependency-sum
bound, since every event-intersection probability is at most one. -/
theorem supercriticalMatchingJansonDelta_upper
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) {k n q : ℕ}
    {dependencyCoefficient : ℝ}
    (hpairs : ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      required).card : ℝ) ≤
        dependencyCoefficient * (q : ℝ) * (n : ℝ) ^ (2 * k - 3)) :
    P.principalJansonDelta required ≤
      dependencyCoefficient * (q : ℝ) * (n : ℝ) ^ (2 * k - 3) :=
  mediumJansonDelta_upper P required hpairs

/-! ## Linear Bernoulli avoidance -/

set_option maxHeartbeats 800000 in
-- Extra heartbeats cover the nonlinear normalization in the positive
-- dependency branch.
/-- Janson avoidance from the two matching-scale estimates.  The proof
separates `Δ = 0`, so no division by zero is hidden in the interface. -/
theorem matchingJansonAvoidance
    {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (J : DenseGraph.PrincipalJansonInput.{u, v})
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    {k n q : ℕ} {a b : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (ha : 0 < a) (hb : 0 < b)
    (hμ : a * (q : ℝ) * (n : ℝ) ^ (k - 1) ≤
      P.principalJansonMu required)
    (hΔ : P.principalJansonDelta required ≤
      b * (q : ℝ) * (n : ℝ) ^ (2 * k - 3)) :
    P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
      Real.exp (-(matchingJansonLinearPenalty a b *
        (q : ℝ) * (n : ℝ))) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hμpos : 0 < P.principalJansonMu required :=
    lt_of_lt_of_le (mul_pos (mul_pos ha hqR)
      (pow_pos hnR (k - 1))) hμ
  have htargetMu : matchingJansonLinearPenalty a b *
      (q : ℝ) * (n : ℝ) ≤ P.principalJansonMu required / 2 :=
    matchingJansonLinearPenalty_mul_matching_mul_n_le_mu_half
      hk hn ha hμ
  by_cases hΔzero : P.principalJansonDelta required = 0
  · calc
      P.eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
          Real.exp (-P.principalJansonMu required) :=
        DenseGraph.PrincipalJansonInput.principalJanson_avoidance_le_exp_neg_of_delta_eq_zero
          J P required hμpos hΔzero
      _ ≤ Real.exp (-(matchingJansonLinearPenalty a b *
          (q : ℝ) * (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        apply neg_le_neg
        exact htargetMu.trans (half_le_self hμpos.le)
  · have hΔpos : 0 < P.principalJansonDelta required :=
      lt_of_le_of_ne (P.principalJansonDelta_nonneg required)
        (Ne.symm hΔzero)
    have htargetDelta : matchingJansonLinearPenalty a b *
        (q : ℝ) * (n : ℝ) ≤
          (P.principalJansonMu required) ^ 2 /
            (4 * P.principalJansonDelta required) :=
      matchingJansonLinearPenalty_mul_matching_mul_n_le_mu_sq_div_delta
        hk hn ha hb hμ hΔ hΔpos
    calc
      P.eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
          Real.exp (-min (P.principalJansonMu required / 2)
            ((P.principalJansonMu required) ^ 2 /
              (4 * P.principalJansonDelta required))) :=
        DenseGraph.PrincipalJansonInput.principalJanson_avoidance_le_exp_neg_min
          J P required hμpos hΔpos
      _ ≤ Real.exp (-(matchingJansonLinearPenalty a b *
          (q : ℝ) * (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        exact neg_le_neg (le_min htargetMu htargetDelta)

/-- Paper-facing Bernoulli penalty.  Its expectation coefficient is the
candidate rate times the uniform complete-event floor, while its dependency
coefficient remains an explicit argument so concrete overlap counting can
choose any proved `k`-only constant. -/
theorem supercriticalMatchingBernoulliAvoidancePenalty
    {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    {k n q : ℕ} {candidateRate eventFloor dependencyCoefficient : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hcandidate : 0 < candidateRate) (hevent : 0 < eventFloor)
    (hdependency : 0 < dependencyCoefficient)
    (hμ : candidateRate * eventFloor * (q : ℝ) *
        (n : ℝ) ^ (k - 1) ≤ P.principalJansonMu required)
    (hΔ : P.principalJansonDelta required ≤
        dependencyCoefficient * (q : ℝ) *
          (n : ℝ) ^ (2 * k - 3)) :
    P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
      Real.exp (-(matchingJansonLinearPenalty
          (candidateRate * eventFloor) dependencyCoefficient *
        (q : ℝ) * (n : ℝ))) := by
  exact matchingJansonAvoidance
    InducedStars.PriorInstances.principalJansonInput
    P required hk hn hq (mul_pos hcandidate hevent) hdependency
    (by simpa [mul_assoc] using hμ) hΔ

/-! ## Exact conditioning and the `h(T)` exponent -/

/-- Exact fixed-cardinality comparison after one global coordinate
complementation.  The only combinatorial input is inclusion of the flipped
event in the principal avoidance event. -/
theorem supercriticalMatchingFixedProbability_le_conditioning_mul_avoidance
    {A Ω C : Type*} [Fintype A] [DecidableEq A]
    [Fintype Ω] [DecidableEq Ω]
    [Fintype C] [LinearOrder C]
    (M : DenseGraph.FixedCardinalityBlockModel A Ω)
    (baseEvent : Finset (Finset M.Coordinate))
    (flip : Finset M.Coordinate)
    (required : C → Finset M.Coordinate)
    (hsubset : DenseGraph.FiniteBernoulliProduct.flipEvent flip baseEvent ⊆
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) :
    M.outcomeEventProbability baseEvent ≤
      M.conditioningFactor *
        (M.associatedBernoulli.complementCoordinates flip).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            required) := by
  classical
  calc
    M.outcomeEventProbability baseEvent ≤
        M.conditioningFactor *
          M.associatedBernoulli.eventProbability baseEvent :=
      M.fixedCardinality_eventProbability_le_conditioningFactor_mul baseEvent
    _ = M.conditioningFactor *
        (M.associatedBernoulli.complementCoordinates flip).eventProbability
          (DenseGraph.FiniteBernoulliProduct.flipEvent flip baseEvent) := by
      rw [DenseGraph.FiniteBernoulliProduct.complementCoordinates_eventProbability_flipEvent]
    _ ≤ M.conditioningFactor *
        (M.associatedBernoulli.complementCoordinates flip).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
            required) := by
      exact mul_le_mul_of_nonneg_left
        ((M.associatedBernoulli.complementCoordinates flip).eventProbability_mono
          hsubset) M.conditioningFactor_pos.le

/-- If the Bernoulli exponent is `penalty*q*n`, the defect count satisfies
`h ≤ scale*q`, and conditioning costs at most `exp(cMat*h*n)`, then
`2*cMat*scale ≤ penalty` leaves the final exponent `cMat*h*n`.

The theorem treats `h = 0` separately, where the claimed upper bound is the
tautological probability bound one. -/
theorem supercriticalMatchingFixedInducedFreeProbability_le_exp
    {A Ω : Type*} [Fintype A] [DecidableEq A]
    [Fintype Ω] [DecidableEq Ω]
    (M : DenseGraph.FixedCardinalityBlockModel A Ω)
    (baseEvent : Finset (Finset M.Coordinate))
    {n q h : ℕ} {penalty cMat scale : ℝ}
    (hcMat : 0 ≤ cMat)
    (hdefect : (h : ℝ) ≤ scale * (q : ℝ))
    (hrate : 2 * cMat * scale ≤ penalty)
    (hconditioning : h ≠ 0 → M.conditioningFactor ≤
      Real.exp (cMat * (h : ℝ) * (n : ℝ)))
    (hfixed : h ≠ 0 → M.outcomeEventProbability baseEvent ≤
      M.conditioningFactor *
        Real.exp (-(penalty * (q : ℝ) * (n : ℝ)))) :
    M.outcomeEventProbability baseEvent ≤
      Real.exp (-(cMat * (h : ℝ) * (n : ℝ))) := by
  by_cases hh : h = 0
  · subst h
    simpa [DenseGraph.FixedCardinalityBlockModel.outcomeEventProbability] using
      M.eventProbability_le_one (M.sampleEvent baseEvent)
  · have hq0 : (0 : ℝ) ≤ q := by positivity
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have htwice : 2 * cMat * (h : ℝ) ≤ penalty * (q : ℝ) := by
      calc
        2 * cMat * (h : ℝ) ≤ 2 * cMat * (scale * (q : ℝ)) := by
          gcongr
        _ = (2 * cMat * scale) * (q : ℝ) := by ring
        _ ≤ penalty * (q : ℝ) := by gcongr
    calc
      M.outcomeEventProbability baseEvent ≤
          M.conditioningFactor *
            Real.exp (-(penalty * (q : ℝ) * (n : ℝ))) := hfixed hh
      _ ≤ Real.exp (cMat * (h : ℝ) * (n : ℝ)) *
            Real.exp (-(penalty * (q : ℝ) * (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right (hconditioning hh)
          (Real.exp_nonneg _)
      _ = Real.exp ((cMat * (h : ℝ) - penalty * (q : ℝ)) *
            (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(cMat * (h : ℝ) * (n : ℝ))) := by
        apply Real.exp_le_exp.mpr
        have : cMat * (h : ℝ) - penalty * (q : ℝ) ≤
            -(cMat * (h : ℝ)) := by linarith
        calc
          (cMat * (h : ℝ) - penalty * (q : ℝ)) * (n : ℝ) ≤
              (-(cMat * (h : ℝ))) * (n : ℝ) := by gcongr
          _ = -(cMat * (h : ℝ) * (n : ℝ)) := by ring

/-- The full-profile conditioning factor has only fixed-degree polynomial
cost and is therefore eventually absorbed by `exp(c*h*n)` uniformly for
every positive integer `h`. -/
theorem eventually_supercriticalFixedProfile_conditioningFactor_le_exp_mul_hn
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : SupercriticalDivision k (Fin n))
      (profile : SupercriticalEdgeProfile D) (h : ℕ), 1 ≤ h →
      (supercriticalFixedProfileBlockModel D profile).conditioningFactor ≤
        Real.exp (c * (h : ℝ) * (n : ℝ)) := by
  filter_upwards
      [eventually_polynomial_le_exp_mul_hn
        (Fintype.card (SupercriticalPartPair k)) hc]
      with n hn D profile h hh
  have hpoly :
      ((((n ^ 2 + 1 : ℕ) : ℝ)) ^
          Fintype.card (SupercriticalPartPair k)) ≤
        Real.exp (c * (h : ℝ) * (n : ℝ)) := by
    simpa [Nat.cast_pow] using hn h hh
  exact ((supercriticalFixedProfileBlockModel D profile).conditioningFactor_le_nsq_pow
    n (fun e ↦ by
      rw [card_supercriticalFixedProfileBlockModel_block]
      simpa using crossEdgeCapacity_le_card_sq D e)).trans hpoly

end InducedStars
