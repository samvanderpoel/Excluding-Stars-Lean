import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Sets
import Mathlib.Tactic

/-!
# Finite inhomogeneous Bernoulli products

This file develops an elementary, real-valued probability mass on the
Boolean cube of a finite coordinate type.  Outcomes are represented by the
finite set of successful coordinates.  The construction is independent of
the graph-specific finite models and is entirely axiom-free.
-/

noncomputable section

open Finset Set
open scoped BigOperators symmDiff

namespace DenseGraph

/-- A finite family of mutually independent Bernoulli coordinates, recorded
by their success probabilities. -/
structure FiniteBernoulliProduct (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  probability : Ω → ℝ
  probability_mem_Icc : ∀ e, probability e ∈ Set.Icc (0 : ℝ) 1

namespace FiniteBernoulliProduct

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The mass of an outcome, represented by its finite set of successful
coordinates. -/
def outcomeWeight (P : FiniteBernoulliProduct Ω) (outcome : Finset Ω) : ℝ :=
  ∏ e : Ω, if e ∈ outcome then P.probability e else 1 - P.probability e

/-- The one-product definition of an outcome weight is the usual product over
successes times the product over failures. -/
theorem outcomeWeight_eq_success_mul_failure
    (P : FiniteBernoulliProduct Ω) (outcome : Finset Ω) :
    P.outcomeWeight outcome =
      (∏ e ∈ outcome, P.probability e) *
        ∏ e ∈ outcomeᶜ, (1 - P.probability e) := by
  classical
  have hsuccess :
      (Finset.univ : Finset Ω).filter (· ∈ outcome) = outcome := by
    ext e
    simp
  have hfailure :
      (Finset.univ : Finset Ω).filter (fun e ↦ e ∉ outcome) = outcomeᶜ := by
    ext e
    simp
  change (∏ e ∈ (Finset.univ : Finset Ω),
      if e ∈ outcome then P.probability e else 1 - P.probability e) = _
  rw [Finset.prod_ite]
  rw [hsuccess, hfailure]

/-- Every outcome has nonnegative mass. -/
theorem outcomeWeight_nonneg (P : FiniteBernoulliProduct Ω)
    (outcome : Finset Ω) :
    0 ≤ P.outcomeWeight outcome := by
  classical
  unfold outcomeWeight
  exact Finset.prod_nonneg fun e _ ↦ by
    split_ifs
    · exact (P.probability_mem_Icc e).1
    · exact sub_nonneg.mpr (P.probability_mem_Icc e).2

/-- Finite subsets are equivalent to Boolean predicates on the coordinate
type. -/
private noncomputable def outcomeOfPredicate (q : Ω → Prop) : Finset Ω := by
  classical
  exact Finset.univ.filter q

@[simp] private theorem mem_outcomeOfPredicate (q : Ω → Prop) (e : Ω) :
    e ∈ outcomeOfPredicate q ↔ q e := by
  classical
  simp [outcomeOfPredicate]

@[simp] private theorem outcomeOfPredicate_membership (outcome : Finset Ω) :
    outcomeOfPredicate (fun e ↦ e ∈ outcome) = outcome := by
  ext e
  simp

private noncomputable def outcomeIndicatorEquiv :
    Finset Ω ≃ (Ω → Prop) := by
  classical
  exact
    { toFun := fun outcome e ↦ e ∈ outcome
      invFun := outcomeOfPredicate
      left_inv := fun outcome ↦ by
        ext e
        simp
      right_inv := fun q ↦ by
        funext e
        apply propext
        simp }

/-- The outcome masses of a finite Bernoulli product sum to one. -/
theorem sum_outcomeWeight_eq_one (P : FiniteBernoulliProduct Ω) :
    ∑ outcome : Finset Ω, P.outcomeWeight outcome = 1 := by
  classical
  calc
    (∑ outcome : Finset Ω, P.outcomeWeight outcome) =
        ∑ q : Ω → Prop,
          ∏ e : Ω, if q e then P.probability e else 1 - P.probability e := by
      apply Fintype.sum_equiv outcomeIndicatorEquiv
      intro outcome
      unfold outcomeWeight
      apply Finset.prod_congr rfl
      intro e _
      by_cases he : e ∈ outcome <;> simp [outcomeIndicatorEquiv, he]
    _ = ∏ e : Ω,
          ∑ b : Prop, if b then P.probability e else 1 - P.probability e := by
      rw [Fintype.prod_sum]
    _ = 1 := by simp

/-- Probability of a finite event in the Boolean cube. -/
def eventProbability (P : FiniteBernoulliProduct Ω)
    (event : Finset (Finset Ω)) : ℝ :=
  ∑ outcome ∈ event, P.outcomeWeight outcome

/-- Every event has nonnegative probability. -/
theorem eventProbability_nonneg (P : FiniteBernoulliProduct Ω)
    (event : Finset (Finset Ω)) :
    0 ≤ P.eventProbability event := by
  exact Finset.sum_nonneg fun outcome _ ↦ P.outcomeWeight_nonneg outcome

/-- Event probability is monotone under event inclusion. -/
theorem eventProbability_mono (P : FiniteBernoulliProduct Ω)
    {event₁ event₂ : Finset (Finset Ω)} (h : event₁ ⊆ event₂) :
    P.eventProbability event₁ ≤ P.eventProbability event₂ := by
  unfold eventProbability
  exact Finset.sum_le_sum_of_subset_of_nonneg h
    (fun outcome _ _ ↦ P.outcomeWeight_nonneg outcome)

/-- Every event has probability at most one. -/
theorem eventProbability_le_one (P : FiniteBernoulliProduct Ω)
    (event : Finset (Finset Ω)) :
    P.eventProbability event ≤ 1 := by
  rw [← P.sum_outcomeWeight_eq_one]
  exact P.eventProbability_mono (Finset.subset_univ event)

@[simp] theorem eventProbability_univ (P : FiniteBernoulliProduct Ω) :
    P.eventProbability (Finset.univ : Finset (Finset Ω)) = 1 := by
  simpa only [eventProbability] using P.sum_outcomeWeight_eq_one

/-- Additivity on disjoint finite events. -/
theorem eventProbability_union (P : FiniteBernoulliProduct Ω)
    {event₁ event₂ : Finset (Finset Ω)} (hdisjoint : Disjoint event₁ event₂) :
    P.eventProbability (event₁ ∪ event₂) =
      P.eventProbability event₁ + P.eventProbability event₂ := by
  unfold eventProbability
  exact Finset.sum_union hdisjoint

/-- Simultaneously complement the listed coordinate probabilities. -/
def complementCoordinates (P : FiniteBernoulliProduct Ω)
    (flip : Finset Ω) : FiniteBernoulliProduct Ω where
  probability e := if e ∈ flip then 1 - P.probability e else P.probability e
  probability_mem_Icc e := by
    split_ifs
    · have hp := P.probability_mem_Icc e
      exact ⟨sub_nonneg.mpr hp.2, sub_le_self 1 hp.1⟩
    · exact P.probability_mem_Icc e

@[simp] theorem complementCoordinates_probability (P : FiniteBernoulliProduct Ω)
    (flip : Finset Ω) (e : Ω) :
    (P.complementCoordinates flip).probability e =
      if e ∈ flip then 1 - P.probability e else P.probability e :=
  rfl

/-- Complement the membership status of every coordinate in `flip`. -/
def flipOutcome (flip outcome : Finset Ω) : Finset Ω :=
  outcome ∆ flip

@[simp] theorem mem_flipOutcome (flip outcome : Finset Ω) (e : Ω) :
    e ∈ flipOutcome flip outcome ↔
      (e ∈ outcome ∧ e ∉ flip) ∨ (e ∈ flip ∧ e ∉ outcome) := by
  simp [flipOutcome, Finset.mem_symmDiff, and_comm]

/-- Coordinatewise complementation is an involutive bijection of the Boolean
cube. -/
def flipOutcomeEquiv (flip : Finset Ω) : Finset Ω ≃ Finset Ω where
  toFun := flipOutcome flip
  invFun := flipOutcome flip
  left_inv outcome := by
    simp [flipOutcome, symmDiff_assoc]
  right_inv outcome := by
    simp [flipOutcome, symmDiff_assoc]

@[simp] theorem flipOutcomeEquiv_apply (flip outcome : Finset Ω) :
    flipOutcomeEquiv flip outcome = flipOutcome flip outcome :=
  rfl

/-- Complementing an outcome and the corresponding probability coordinates
preserves its exact mass. -/
theorem complementCoordinates_outcomeWeight_flipOutcome
    (P : FiniteBernoulliProduct Ω) (flip outcome : Finset Ω) :
    (P.complementCoordinates flip).outcomeWeight (flipOutcome flip outcome) =
      P.outcomeWeight outcome := by
  classical
  unfold outcomeWeight
  apply Finset.prod_congr rfl
  intro e _
  by_cases heo : e ∈ outcome <;> by_cases hef : e ∈ flip <;>
    simp [mem_flipOutcome, heo, hef] <;> ring

/-- The image of an event under coordinatewise complementation. -/
def flipEvent (flip : Finset Ω) (event : Finset (Finset Ω)) :
    Finset (Finset Ω) :=
  event.map (flipOutcomeEquiv flip).toEmbedding

@[simp] theorem mem_flipEvent (flip : Finset Ω)
    (event : Finset (Finset Ω)) (outcome : Finset Ω) :
    outcome ∈ flipEvent flip event ↔ flipOutcome flip outcome ∈ event := by
  classical
  rw [flipEvent, Finset.mem_map]
  constructor
  · rintro ⟨base, hbase, hbaseEq⟩
    rw [← hbaseEq]
    simpa [flipOutcomeEquiv, flipOutcome, symmDiff_assoc] using hbase
  · intro hbase
    refine ⟨flipOutcome flip outcome, hbase, ?_⟩
    simp [flipOutcomeEquiv, flipOutcome, symmDiff_assoc]

/-- Coordinatewise complementation transports the product law exactly. -/
theorem complementCoordinates_eventProbability_flipEvent
    (P : FiniteBernoulliProduct Ω) (flip : Finset Ω)
    (event : Finset (Finset Ω)) :
    (P.complementCoordinates flip).eventProbability (flipEvent flip event) =
      P.eventProbability event := by
  classical
  unfold eventProbability flipEvent
  rw [Finset.sum_map]
  simp [complementCoordinates_outcomeWeight_flipOutcome]

/-- The event that every coordinate in `required` succeeds. -/
def principalSuccessEvent (required : Finset Ω) : Finset (Finset Ω) :=
  Finset.univ.filter (required ⊆ ·)

@[simp] theorem mem_principalSuccessEvent (required outcome : Finset Ω) :
    outcome ∈ principalSuccessEvent required ↔ required ⊆ outcome := by
  simp [principalSuccessEvent]

/-- The event that one specified coordinate succeeds. -/
def coordinateSuccessEvent (e : Ω) : Finset (Finset Ω) :=
  principalSuccessEvent {e}

/-- The event that one specified coordinate fails. -/
def coordinateFailureEvent (e : Ω) : Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ e ∉ outcome

@[simp] theorem mem_coordinateFailureEvent (e : Ω) (outcome : Finset Ω) :
    outcome ∈ coordinateFailureEvent e ↔ e ∉ outcome := by
  simp [coordinateFailureEvent]

/-- A coordinate summand used to expand the mass of a principal event. -/
private noncomputable def principalCoordinateWeight
    (P : FiniteBernoulliProduct Ω) (required : Finset Ω)
    (e : Ω) (b : Prop) : ℝ := by
  classical
  exact if e ∈ required then
    if b then P.probability e else 0
  else if b then P.probability e else 1 - P.probability e

private theorem principal_product_eq_indicator_weight
    (P : FiniteBernoulliProduct Ω) (required : Finset Ω) (q : Ω → Prop) :
    (∏ e : Ω, principalCoordinateWeight P required e (q e)) =
      if required ⊆ outcomeOfPredicate q then
        P.outcomeWeight (outcomeOfPredicate q)
      else 0 := by
  classical
  by_cases hrequired : required ⊆ outcomeOfPredicate q
  · rw [if_pos hrequired]
    unfold principalCoordinateWeight outcomeWeight
    apply Finset.prod_congr rfl
    intro e _
    by_cases her : e ∈ required
    · have hqe : q e := by
        simpa using hrequired her
      simp [her, hqe]
    · by_cases hqe : q e <;> simp [her, hqe]
  · rw [if_neg hrequired]
    simp only [Finset.subset_iff] at hrequired
    push_neg at hrequired
    obtain ⟨e, her, hqe⟩ := hrequired
    have hfactor : principalCoordinateWeight P required e (q e) = 0 := by
      have hnq : ¬q e := by simpa using hqe
      simp [principalCoordinateWeight, her, hnq]
    exact Finset.prod_eq_zero (Finset.mem_univ e) hfactor

/-- A principal success event has the expected exact product probability. -/
theorem eventProbability_principalSuccessEvent
    (P : FiniteBernoulliProduct Ω) (required : Finset Ω) :
    P.eventProbability (principalSuccessEvent required) =
      ∏ e ∈ required, P.probability e := by
  classical
  calc
    P.eventProbability (principalSuccessEvent required) =
        ∑ outcome : Finset Ω,
      if required ⊆ outcome then P.outcomeWeight outcome else 0 := by
      simp only [eventProbability, principalSuccessEvent, Finset.sum_filter,
        Finset.mem_univ, if_true]
    _ = ∑ q : Ω → Prop,
          if required ⊆ outcomeOfPredicate q then
            P.outcomeWeight (outcomeOfPredicate q) else 0 := by
      apply Fintype.sum_equiv outcomeIndicatorEquiv
      intro outcome
      simp [outcomeIndicatorEquiv]
    _ = ∑ q : Ω → Prop,
          ∏ e : Ω, principalCoordinateWeight P required e (q e) := by
      apply Finset.sum_congr rfl
      intro q _
      exact (principal_product_eq_indicator_weight P required q).symm
    _ = ∏ e : Ω, ∑ b : Prop, principalCoordinateWeight P required e b := by
      rw [Fintype.prod_sum]
    _ = ∏ e : Ω, if e ∈ required then P.probability e else 1 := by
      apply Finset.prod_congr rfl
      intro e _
      by_cases her : e ∈ required <;> simp [principalCoordinateWeight, her]
    _ = ∏ e ∈ required, P.probability e := by
      exact Fintype.prod_ite_mem required P.probability

/-- Audit-stable name for the exact principal-event probability formula. -/
theorem principalSuccessEvent_probability
    (P : FiniteBernoulliProduct Ω) (required : Finset Ω) :
    P.eventProbability (principalSuccessEvent required) =
      ∏ e ∈ required, P.probability e :=
  P.eventProbability_principalSuccessEvent required

@[simp] theorem eventProbability_coordinateSuccessEvent
    (P : FiniteBernoulliProduct Ω) (e : Ω) :
    P.eventProbability (coordinateSuccessEvent e) = P.probability e := by
  simp [coordinateSuccessEvent, eventProbability_principalSuccessEvent]

/-- Exact probability of a one-coordinate failure cylinder. -/
@[simp] theorem eventProbability_coordinateFailureEvent
    (P : FiniteBernoulliProduct Ω) (e : Ω) :
    P.eventProbability (coordinateFailureEvent e) = 1 - P.probability e := by
  have hdisjoint : Disjoint (coordinateFailureEvent e) (coordinateSuccessEvent e) := by
    rw [Finset.disjoint_left]
    intro outcome hfailure hsuccess
    exact (mem_coordinateFailureEvent e outcome).mp hfailure <|
      (mem_principalSuccessEvent {e} outcome).mp hsuccess (by simp)
  have hunion :
      coordinateFailureEvent e ∪ coordinateSuccessEvent e =
        (Finset.univ : Finset (Finset Ω)) := by
    ext outcome
    by_cases he : e ∈ outcome <;>
      simp [coordinateFailureEvent, coordinateSuccessEvent,
        principalSuccessEvent, he]
  have hadd := P.eventProbability_union hdisjoint
  rw [hunion, P.eventProbability_univ,
    P.eventProbability_coordinateSuccessEvent] at hadd
  linarith

/-- Intersecting two principal events unions their required-coordinate sets. -/
theorem principalSuccessEvent_inter (required₁ required₂ : Finset Ω) :
    principalSuccessEvent required₁ ∩ principalSuccessEvent required₂ =
      principalSuccessEvent (required₁ ∪ required₂) := by
  ext outcome
  simp [Finset.union_subset_iff]

/-- Exact intersection probability for two principal success events. -/
theorem eventProbability_principalSuccessEvent_inter
    (P : FiniteBernoulliProduct Ω) (required₁ required₂ : Finset Ω) :
    P.eventProbability
        (principalSuccessEvent required₁ ∩ principalSuccessEvent required₂) =
      ∏ e ∈ required₁ ∪ required₂, P.probability e := by
  rw [principalSuccessEvent_inter,
    eventProbability_principalSuccessEvent]

/-- Principal events on disjoint required-coordinate sets are independent,
expressed as the exact product identity for their intersection. -/
theorem eventProbability_principalSuccessEvent_inter_eq_mul_of_disjoint
    (P : FiniteBernoulliProduct Ω) {required₁ required₂ : Finset Ω}
    (hdisjoint : Disjoint required₁ required₂) :
    P.eventProbability
        (principalSuccessEvent required₁ ∩ principalSuccessEvent required₂) =
      P.eventProbability (principalSuccessEvent required₁) *
        P.eventProbability (principalSuccessEvent required₂) := by
  rw [eventProbability_principalSuccessEvent_inter,
    eventProbability_principalSuccessEvent,
    eventProbability_principalSuccessEvent]
  exact Finset.prod_union hdisjoint

end FiniteBernoulliProduct

end DenseGraph
