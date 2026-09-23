import DenseGraph.FiniteModels.BernoulliProduct

/-!
# Arbitrary supported events in finite Bernoulli products

An event is supported on a coordinate set when changing other coordinates
does not change membership.  Finite cylinder decomposition proves independence
for arbitrary events with disjoint supports, including arbitrary finite
intersections of such events.  No positivity of the coordinate probabilities
is needed: deterministic coordinates are allowed.
-/

noncomputable section

open Finset
open scoped BigOperators symmDiff

namespace DenseGraph.FiniteBernoulliProduct

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Event membership is determined by the outcome's restriction to `support`. -/
def EventSupportedOn (event : Finset (Finset Ω)) (support : Finset Ω) : Prop :=
  ∀ outcome₁ outcome₂ : Finset Ω,
    outcome₁ ∩ support = outcome₂ ∩ support →
      (outcome₁ ∈ event ↔ outcome₂ ∈ event)

/-- Equivalent pointwise formulation of event support. -/
theorem eventSupportedOn_iff (event : Finset (Finset Ω)) (support : Finset Ω) :
    EventSupportedOn event support ↔
      ∀ outcome₁ outcome₂ : Finset Ω,
        (∀ e ∈ support, e ∈ outcome₁ ↔ e ∈ outcome₂) →
          (outcome₁ ∈ event ↔ outcome₂ ∈ event) := by
  constructor
  · intro h outcome₁ outcome₂ hagree
    apply h outcome₁ outcome₂
    ext e
    by_cases he : e ∈ support
    · simpa [he] using hagree e he
    · simp [he]
  · intro h outcome₁ outcome₂ hagree
    apply h outcome₁ outcome₂
    intro e he
    have := Finset.ext_iff.mp hagree e
    simpa [he] using this

namespace EventSupportedOn

/-- Enlarging the coordinate support preserves support. -/
theorem mono {event : Finset (Finset Ω)} {A B : Finset Ω}
    (h : EventSupportedOn event A) (hAB : A ⊆ B) : EventSupportedOn event B := by
  intro outcome₁ outcome₂ hagree
  apply h outcome₁ outcome₂
  have := congrArg (fun outcome : Finset Ω ↦ outcome ∩ A) hagree
  simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hAB] using this

/-- Every finite event is supported on all coordinates. -/
theorem univ (event : Finset (Finset Ω)) :
    EventSupportedOn event Finset.univ := by
  intro outcome₁ outcome₂ hagree
  simp only [Finset.inter_univ] at hagree
  rw [hagree]

/-- The impossible event has any support. -/
theorem empty (A : Finset Ω) : EventSupportedOn ∅ A := by
  intro outcome₁ outcome₂ _
  simp

/-- The certain event has any support. -/
theorem universal (A : Finset Ω) :
    EventSupportedOn (Finset.univ : Finset (Finset Ω)) A := by
  intro outcome₁ outcome₂ _
  simp

/-- Complements use the same coordinates. -/
theorem compl {event : Finset (Finset Ω)} {A : Finset Ω}
    (h : EventSupportedOn event A) : EventSupportedOn eventᶜ A := by
  intro outcome₁ outcome₂ hagree
  simpa only [Finset.mem_compl] using not_congr (h outcome₁ outcome₂ hagree)

/-- Intersections use the union of their supports. -/
theorem inter {event₁ event₂ : Finset (Finset Ω)} {A B : Finset Ω}
    (h₁ : EventSupportedOn event₁ A) (h₂ : EventSupportedOn event₂ B) :
    EventSupportedOn (event₁ ∩ event₂) (A ∪ B) := by
  intro outcome₁ outcome₂ hagree
  simp only [Finset.mem_inter]
  exact and_congr
    (h₁.mono Finset.subset_union_left outcome₁ outcome₂ hagree)
    (h₂.mono Finset.subset_union_right outcome₁ outcome₂ hagree)

/-- Unions use the union of their supports. -/
theorem union {event₁ event₂ : Finset (Finset Ω)} {A B : Finset Ω}
    (h₁ : EventSupportedOn event₁ A) (h₂ : EventSupportedOn event₂ B) :
    EventSupportedOn (event₁ ∪ event₂) (A ∪ B) := by
  intro outcome₁ outcome₂ hagree
  simp only [Finset.mem_union]
  exact or_congr
    (h₁.mono Finset.subset_union_left outcome₁ outcome₂ hagree)
    (h₂.mono Finset.subset_union_right outcome₁ outcome₂ hagree)

end EventSupportedOn

/-- The cylinder specifying exactly the successful coordinates in `support`.
When `pattern` is not a subset of `support`, this event is empty. -/
def cylinderEvent (support pattern : Finset Ω) : Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ outcome ∩ support = pattern

@[simp] theorem mem_cylinderEvent (support pattern outcome : Finset Ω) :
    outcome ∈ cylinderEvent support pattern ↔ outcome ∩ support = pattern := by
  simp [cylinderEvent]

theorem cylinderEvent_supportedOn (support pattern : Finset Ω) :
    EventSupportedOn (cylinderEvent support pattern) support := by
  intro outcome₁ outcome₂ hagree
  simp only [mem_cylinderEvent, hagree]

/-- Distinct patterns give disjoint cylinders on the same support. -/
theorem cylinderEvent_disjoint {support pattern₁ pattern₂ : Finset Ω}
    (hne : pattern₁ ≠ pattern₂) :
    Disjoint (cylinderEvent support pattern₁) (cylinderEvent support pattern₂) := by
  rw [Finset.disjoint_left]
  intro outcome h₁ h₂
  exact hne ((mem_cylinderEvent _ _ _).mp h₁ |>.symm.trans
    ((mem_cylinderEvent _ _ _).mp h₂))

/-- Coordinate complementation may equivalently be moved from the event to
the product law. -/
theorem eventProbability_flipEvent_eq_complementCoordinates
    (P : FiniteBernoulliProduct Ω) (flip : Finset Ω)
    (event : Finset (Finset Ω)) :
    P.eventProbability (flipEvent flip event) =
      (P.complementCoordinates flip).eventProbability event := by
  unfold eventProbability flipEvent
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro outcome _
  have h := P.complementCoordinates_outcomeWeight_flipOutcome
    flip (flipOutcome flip outcome)
  simpa [flipOutcomeEquiv, flipOutcome, symmDiff_assoc] using h.symm

/-- A cylinder is obtained from a principal success event by complementing
the specified failures. -/
theorem flipEvent_principalSuccessEvent_eq_cylinderEvent
    {support pattern : Finset Ω} (hpattern : pattern ⊆ support) :
    flipEvent (support \ pattern) (principalSuccessEvent support) =
      cylinderEvent support pattern := by
  ext outcome
  simp only [mem_flipEvent, mem_principalSuccessEvent, mem_cylinderEvent]
  constructor
  · intro h
    ext e
    by_cases hes : e ∈ support
    · have he := h hes
      by_cases hep : e ∈ pattern <;>
        simp_all [mem_flipOutcome]
    · have hep : e ∉ pattern := fun he ↦ hes (hpattern he)
      simp [hes, hep]
  · intro h e hes
    have he : e ∈ outcome ↔ e ∈ pattern := by
      simpa only [Finset.mem_inter, hes, and_true] using Finset.ext_iff.mp h e
    by_cases hep : e ∈ pattern
    · have heo := he.mpr hep
      simp [mem_flipOutcome, hes, hep, heo]
    · have heo : e ∉ outcome := fun ho ↦ hep (he.mp ho)
      simp [mem_flipOutcome, hes, hep, heo]

/-- Exact probability of an arbitrary finite success/failure cylinder. -/
theorem eventProbability_cylinderEvent
    (P : FiniteBernoulliProduct Ω) {support pattern : Finset Ω}
    (hpattern : pattern ⊆ support) :
    P.eventProbability (cylinderEvent support pattern) =
      ∏ e ∈ support, if e ∈ pattern then P.probability e else 1 - P.probability e := by
  rw [← flipEvent_principalSuccessEvent_eq_cylinderEvent hpattern,
    eventProbability_flipEvent_eq_complementCoordinates,
    eventProbability_principalSuccessEvent]
  apply Finset.prod_congr rfl
  intro e hes
  by_cases hep : e ∈ pattern <;> simp [hes, hep]

/-- Intersecting compatible cylinders unions both the supports and patterns. -/
theorem cylinderEvent_inter_of_disjoint {A B a b : Finset Ω}
    (hAB : Disjoint A B) (ha : a ⊆ A) (hb : b ⊆ B) :
    cylinderEvent A a ∩ cylinderEvent B b = cylinderEvent (A ∪ B) (a ∪ b) := by
  ext outcome
  simp only [Finset.mem_inter, mem_cylinderEvent]
  constructor
  · rintro ⟨hA, hB⟩
    rw [Finset.inter_union_distrib_left, hA, hB]
  · intro h
    have hdis := Finset.disjoint_left.mp hAB
    constructor
    · ext e
      have he := Finset.ext_iff.mp h e
      by_cases heA : e ∈ A
      · have heB : e ∉ B := fun heB ↦ hdis heA heB
        have heb : e ∉ b := fun heb ↦ heB (hb heb)
        simpa [heA, heB, heb] using he
      · have hea : e ∉ a := fun hea ↦ heA (ha hea)
        simp [heA, hea]
    · ext e
      have he := Finset.ext_iff.mp h e
      by_cases heB : e ∈ B
      · have heA : e ∉ A := fun heA ↦ hdis heA heB
        have hea : e ∉ a := fun hea ↦ heA (ha hea)
        simpa [heA, heB, hea] using he
      · have heb : e ∉ b := fun heb ↦ heB (hb heb)
        simp [heB, heb]

/-- Arbitrary success/failure cylinders on disjoint supports are independent. -/
theorem eventProbability_cylinderEvent_inter_eq_mul
    (P : FiniteBernoulliProduct Ω) {A B a b : Finset Ω}
    (hAB : Disjoint A B) (ha : a ⊆ A) (hb : b ⊆ B) :
    P.eventProbability (cylinderEvent A a ∩ cylinderEvent B b) =
      P.eventProbability (cylinderEvent A a) *
        P.eventProbability (cylinderEvent B b) := by
  rw [cylinderEvent_inter_of_disjoint hAB ha hb,
    eventProbability_cylinderEvent P (Finset.union_subset_union ha hb),
    eventProbability_cylinderEvent P ha, eventProbability_cylinderEvent P hb,
    Finset.prod_union hAB]
  congr 1
  · apply Finset.prod_congr rfl
    intro e heA
    have heb : e ∉ b := fun heb ↦ Finset.disjoint_left.mp hAB heA (hb heb)
    simp [heb]
  · apply Finset.prod_congr rfl
    intro e heB
    have hea : e ∉ a := fun hea ↦ Finset.disjoint_left.mp hAB (ha hea) heB
    simp [hea]

/-- Patterns accepted by an event on a fixed support. -/
def eventPatterns (event : Finset (Finset Ω)) (support : Finset Ω) :
    Finset (Finset Ω) := support.powerset.filter (· ∈ event)

@[simp] theorem mem_eventPatterns (event : Finset (Finset Ω)) (support pattern : Finset Ω) :
    pattern ∈ eventPatterns event support ↔ pattern ⊆ support ∧ pattern ∈ event := by
  simp [eventPatterns]

/-- Every supported event is the disjoint union of its accepted cylinders. -/
theorem EventSupportedOn.eq_biUnion_patterns {event : Finset (Finset Ω)}
    {support : Finset Ω} (h : EventSupportedOn event support) :
    event = (eventPatterns event support).biUnion (cylinderEvent support) := by
  ext outcome
  simp only [Finset.mem_biUnion, mem_eventPatterns, mem_cylinderEvent]
  constructor
  · intro ho
    refine ⟨outcome ∩ support, ⟨Finset.inter_subset_right, ?_⟩, rfl⟩
    exact (h outcome (outcome ∩ support) (by simp [Finset.inter_assoc])).mp ho
  · rintro ⟨pattern, ⟨hpattern, hp⟩, heq⟩
    exact (h outcome pattern (by simpa [Finset.inter_eq_left.mpr hpattern] using heq)).mpr hp

/-- Cylinder decomposition remains exact after intersection with any other
event; only the decomposed event needs a support hypothesis. -/
theorem eventProbability_inter_eq_sum_patterns
    (P : FiniteBernoulliProduct Ω) {event other : Finset (Finset Ω)}
    {support : Finset Ω} (h : EventSupportedOn event support) :
    P.eventProbability (event ∩ other) =
      ∑ pattern ∈ eventPatterns event support,
        P.eventProbability (cylinderEvent support pattern ∩ other) := by
  conv_lhs => rw [h.eq_biUnion_patterns, Finset.biUnion_inter]
  unfold eventProbability
  apply Finset.sum_biUnion
  intro a _ b _ hab
  exact (cylinderEvent_disjoint hab).mono Finset.inter_subset_left Finset.inter_subset_left

/-- Probability is the sum of the probabilities of the accepted cylinders. -/
theorem eventProbability_eq_sum_patterns
    (P : FiniteBernoulliProduct Ω) {event : Finset (Finset Ω)}
    {support : Finset Ω} (h : EventSupportedOn event support) :
    P.eventProbability event =
      ∑ pattern ∈ eventPatterns event support,
        P.eventProbability (cylinderEvent support pattern) := by
  simpa only [Finset.inter_univ] using
    P.eventProbability_inter_eq_sum_patterns (other := Finset.univ) h

/-- Any two finite events supported on disjoint coordinate sets are
independent.  This is not restricted to principal or monotone events. -/
theorem eventProbability_inter_eq_mul_of_disjoint_support
    (P : FiniteBernoulliProduct Ω) {event₁ event₂ : Finset (Finset Ω)}
    {A B : Finset Ω} (h₁ : EventSupportedOn event₁ A)
    (h₂ : EventSupportedOn event₂ B) (hAB : Disjoint A B) :
    P.eventProbability (event₁ ∩ event₂) =
      P.eventProbability event₁ * P.eventProbability event₂ := by
  rw [P.eventProbability_inter_eq_sum_patterns h₁,
    P.eventProbability_eq_sum_patterns h₁,
    P.eventProbability_eq_sum_patterns h₂, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.inter_comm, P.eventProbability_inter_eq_sum_patterns h₂,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.inter_comm]
  exact P.eventProbability_cylinderEvent_inter_eq_mul hAB
    ((mem_eventPatterns _ _ _).mp ha).1 ((mem_eventPatterns _ _ _).mp hb).1

/-- The intersection of a finite family of events, including the empty
intersection, which is the certain event. -/
def eventIntersection {ι : Type*} (indices : Finset ι)
    (events : ι → Finset (Finset Ω)) : Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ ∀ i ∈ indices, outcome ∈ events i

@[simp] theorem mem_eventIntersection {ι : Type*} (indices : Finset ι)
    (events : ι → Finset (Finset Ω)) (outcome : Finset Ω) :
    outcome ∈ eventIntersection indices events ↔ ∀ i ∈ indices, outcome ∈ events i := by
  simp [eventIntersection]

@[simp] theorem eventIntersection_empty {ι : Type*}
    (events : ι → Finset (Finset Ω)) : eventIntersection ∅ events = Finset.univ := by
  ext outcome
  simp

@[simp] theorem eventIntersection_insert {ι : Type*} [DecidableEq ι]
    (i : ι) (indices : Finset ι) (events : ι → Finset (Finset Ω)) :
    eventIntersection (insert i indices) events = events i ∩ eventIntersection indices events := by
  ext outcome
  simp

/-- A finite intersection is supported on the union of the coordinate
supports of its constituent events. -/
theorem EventSupportedOn.eventIntersection {ι : Type*} (indices : Finset ι)
    (events : ι → Finset (Finset Ω)) (supports : ι → Finset Ω)
    (h : ∀ i ∈ indices, EventSupportedOn (events i) (supports i)) :
    EventSupportedOn (eventIntersection indices events) (indices.biUnion supports) := by
  intro outcome₁ outcome₂ hagree
  simp only [mem_eventIntersection]
  apply forall₂_congr
  intro i hi
  exact (h i hi).mono (Finset.subset_biUnion_of_mem supports hi) outcome₁ outcome₂ hagree

/-- A finite family of arbitrary events with pairwise disjoint coordinate
supports has exact product probability for its intersection. -/
theorem eventProbability_intersection_eq_prod
    (P : FiniteBernoulliProduct Ω) {ι : Type*} (indices : Finset ι)
    (events : ι → Finset (Finset Ω)) (supports : ι → Finset Ω)
    (h : ∀ i ∈ indices, EventSupportedOn (events i) (supports i))
    (hdisjoint : Set.PairwiseDisjoint (↑indices) supports) :
    P.eventProbability (eventIntersection indices events) =
      ∏ i ∈ indices, P.eventProbability (events i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert i indices hi ih =>
    have hrest : ∀ j ∈ indices, EventSupportedOn (events j) (supports j) :=
      fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    have hpair : Set.PairwiseDisjoint (↑indices) supports := by
      intro a ha b hb hab
      exact hdisjoint (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
    have hcross : Disjoint (supports i) (indices.biUnion supports) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisjoint (Finset.mem_insert_self i indices) (Finset.mem_insert_of_mem hj)
        (ne_of_mem_of_not_mem hj hi).symm
    rw [eventIntersection_insert,
      P.eventProbability_inter_eq_mul_of_disjoint_support
        (h i (Finset.mem_insert_self i indices))
        (EventSupportedOn.eventIntersection indices events supports hrest) hcross,
      ih hrest hpair, Finset.prod_insert hi]

end DenseGraph.FiniteBernoulliProduct
