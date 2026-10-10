import DenseGraph.FiniteModels.BernoulliProduct
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Principal-event Janson interface

This file records the narrow reusable capability needed to apply Janson's
inequality to principal up-sets in a finite Bernoulli product.  The capability
itself is axiom-free: projects instantiate it from an audited published input.
The dependency sum below is deliberately over unordered overlapping pairs.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace DenseGraph

universe u v

namespace FiniteBernoulliProduct

variable {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype I] [LinearOrder I]

/-- The unordered pairs of distinct principal events whose required
coordinate sets overlap.  The linear order selects one representative of
each unordered pair. -/
def unorderedOverlappingPairs (required : I → Finset Ω) : Finset (I × I) :=
  Finset.univ.filter fun ij ↦
    ij.1 < ij.2 ∧ ¬Disjoint (required ij.1) (required ij.2)

@[simp] theorem mem_unorderedOverlappingPairs
    (required : I → Finset Ω) (i j : I) :
    (i, j) ∈ unorderedOverlappingPairs required ↔
      i < j ∧ ¬Disjoint (required i) (required j) := by
  simp [unorderedOverlappingPairs]

/-- The event that none of a finite family of principal success events
occurs. -/
def principalAvoidanceEvent (required : I → Finset Ω) :
    Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ ∀ i, ¬required i ⊆ outcome

@[simp] theorem mem_principalAvoidanceEvent
    (required : I → Finset Ω) (outcome : Finset Ω) :
    outcome ∈ principalAvoidanceEvent required ↔
      ∀ i, ¬required i ⊆ outcome := by
  simp [principalAvoidanceEvent]

/-- The sum of the probabilities of the principal events. -/
def principalJansonMu (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) : ℝ :=
  ∑ i, P.eventProbability (principalSuccessEvent (required i))

/-- The Janson dependency sum over unordered, distinct, overlapping pairs.
For principal events their intersection is the principal event requiring the
union of the two coordinate sets. -/
def principalJansonDelta (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) : ℝ :=
  ∑ ij ∈ unorderedOverlappingPairs required,
    P.eventProbability
      (principalSuccessEvent (required ij.1 ∪ required ij.2))

/-- The same overlap sum expanded with both orientations of every unordered
pair.  This is the convention used for `Δ` in Riordan--Warnke Theorem 1. -/
def principalJansonOrderedDelta (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) : ℝ :=
  ∑ ij ∈ unorderedOverlappingPairs required,
    (P.eventProbability
        (principalSuccessEvent (required ij.1 ∪ required ij.2)) +
      P.eventProbability
        (principalSuccessEvent (required ij.2 ∪ required ij.1)))

/-- Exact ordered/unordered conversion.  Symmetry of union makes the two
orientations of each unordered overlapping pair contribute equally. -/
theorem principalJansonOrderedDelta_eq_two_mul
    (P : FiniteBernoulliProduct Ω) (required : I → Finset Ω) :
    P.principalJansonOrderedDelta required =
      2 * P.principalJansonDelta required := by
  classical
  unfold principalJansonOrderedDelta principalJansonDelta
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [show required ij.2 ∪ required ij.1 = required ij.1 ∪ required ij.2 from
    Finset.union_comm _ _]
  ring

theorem principalJansonMu_nonneg (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) :
    0 ≤ P.principalJansonMu required := by
  exact Finset.sum_nonneg fun i _ ↦ P.eventProbability_nonneg _

theorem principalJansonDelta_nonneg (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) :
    0 ≤ P.principalJansonDelta required := by
  exact Finset.sum_nonneg fun ij _ ↦ P.eventProbability_nonneg _

end FiniteBernoulliProduct

/-- A narrow theorem-valued interface for the denominator form of Janson's
inequality on principal up-sets in a finite independent Bernoulli product.

`principalJansonDelta` is the **unordered** overlap sum, hence the published
ordered-pair denominator becomes `μ + 2 * Δ`. -/
structure PrincipalJansonInput : Prop where
  avoidance_le :
    ∀ {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
      [Fintype I] [LinearOrder I]
      (P : FiniteBernoulliProduct Ω) (required : I → Finset Ω),
      P.eventProbability
          (FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
        Real.exp
          (-((P.principalJansonMu required) ^ 2 /
            (P.principalJansonMu required +
              2 * P.principalJansonDelta required)))

namespace PrincipalJansonInput

open FiniteBernoulliProduct

variable {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
  [Fintype I] [LinearOrder I]

/-- The paper's minimum form, with the positivity assumptions needed to make
its division by `Δ` literal real arithmetic. -/
theorem principalJanson_avoidance_le_exp_neg_min
    (J : PrincipalJansonInput.{u, v}) (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    (hμ : 0 < P.principalJansonMu required)
    (hΔ : 0 < P.principalJansonDelta required) :
    P.eventProbability (principalAvoidanceEvent required) ≤
      Real.exp
        (-min (P.principalJansonMu required / 2)
          ((P.principalJansonMu required) ^ 2 /
            (4 * P.principalJansonDelta required))) := by
  let μ := P.principalJansonMu required
  let Δ := P.principalJansonDelta required
  have hden : 0 < μ + 2 * Δ := by dsimp [μ, Δ]; positivity
  have hfourΔ : 0 < 4 * Δ := by dsimp [Δ]; positivity
  have hcompare :
      min (μ / 2) (μ ^ 2 / (4 * Δ)) ≤
        μ ^ 2 / (μ + 2 * Δ) := by
    by_cases hsmall : 2 * Δ ≤ μ
    · refine (min_le_left _ _).trans ?_
      apply (le_div_iff₀ hden).2
      have hμ0 : 0 ≤ μ := hμ.le
      nlinarith [sq_nonneg μ]
    · have hlarge : μ ≤ 2 * Δ := le_of_not_ge hsmall
      refine (min_le_right _ _).trans ?_
      apply div_le_div_of_nonneg_left (sq_nonneg μ) hden
      nlinarith
  calc
    P.eventProbability (principalAvoidanceEvent required) ≤
        Real.exp (-(μ ^ 2 / (μ + 2 * Δ))) := by
      simpa [μ, Δ] using
        PrincipalJansonInput.avoidance_le J (Ω := Ω) (I := I) P required
    _ ≤ Real.exp (-min (μ / 2) (μ ^ 2 / (4 * Δ))) := by
      exact Real.exp_le_exp.mpr (neg_le_neg hcompare)
    _ = _ := by rfl

/-- In the zero-overlap case the denominator form reduces to `exp (-μ)`.
This is the nonsingular companion to the minimum form. -/
theorem principalJanson_avoidance_le_exp_neg_of_delta_eq_zero
    (J : PrincipalJansonInput.{u, v}) (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    (hμ : 0 < P.principalJansonMu required)
    (hΔ : P.principalJansonDelta required = 0) :
    P.eventProbability (principalAvoidanceEvent required) ≤
      Real.exp (-P.principalJansonMu required) := by
  have hμne : P.principalJansonMu required ≠ 0 := ne_of_gt hμ
  simpa [hΔ, hμne, pow_two] using
    PrincipalJansonInput.avoidance_le J (Ω := Ω) (I := I) P required

/-- A reusable quadratic-exponent corollary.  Later applications establish
the two displayed lower bounds from their expectation and dependency
estimates; keeping that algebra here prevents a second Janson conversion. -/
theorem avoidance_le_exp_neg_of_mu_lower_dependency_upper
    (J : PrincipalJansonInput.{u, v}) (P : FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    {n : ℕ} {c : ℝ} (hμ : 0 < P.principalJansonMu required)
    (hΔ : 0 < P.principalJansonDelta required)
    (hμquad : c * (n : ℝ) ^ 2 ≤
      P.principalJansonMu required / 2)
    (hΔquad : c * (n : ℝ) ^ 2 ≤
      (P.principalJansonMu required) ^ 2 /
        (4 * P.principalJansonDelta required)) :
    P.eventProbability (principalAvoidanceEvent required) ≤
      Real.exp (-(c * (n : ℝ) ^ 2)) := by
  calc
    P.eventProbability (principalAvoidanceEvent required) ≤
        Real.exp
          (-min (P.principalJansonMu required / 2)
            ((P.principalJansonMu required) ^ 2 /
              (4 * P.principalJansonDelta required))) :=
      principalJanson_avoidance_le_exp_neg_min J P required hμ hΔ
    _ ≤ Real.exp (-(c * (n : ℝ) ^ 2)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (le_min hμquad hΔquad)

end PrincipalJansonInput

end DenseGraph
