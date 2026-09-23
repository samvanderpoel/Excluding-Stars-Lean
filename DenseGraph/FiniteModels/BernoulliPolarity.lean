import DenseGraph.FiniteModels.BernoulliEvents
import DenseGraph.FiniteModels.Janson

/-!
# One global polarity for mixed Bernoulli events

A mixed event asks for some coordinates to succeed and others to fail.
Provided these requirements are consistent across the whole candidate
family, one common coordinate complementation turns every event into a
principal success event.  Probability transport uses the existing Boolean
cube involution; no correlation theorem for mixed events is assumed.
-/

noncomputable section

open Finset
open scoped symmDiff

namespace DenseGraph.FiniteBernoulliProduct

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The cylinder requiring all `present` coordinates and no `absent` coordinate. -/
def mixedSuccessEvent (present absent : Finset Ω) : Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ present ⊆ outcome ∧ Disjoint absent outcome

@[simp] theorem mem_mixedSuccessEvent (present absent outcome : Finset Ω) :
    outcome ∈ mixedSuccessEvent present absent ↔
      present ⊆ outcome ∧ Disjoint absent outcome := by
  simp [mixedSuccessEvent]

/-- A single global flip converts any compatible mixed cylinder to the
principal event on its full coordinate support. -/
theorem mem_mixedSuccessEvent_iff_subset_flipOutcome
    {present absent flip outcome : Finset Ω}
    (hpresent : Disjoint present flip) (habsent : absent ⊆ flip) :
    outcome ∈ mixedSuccessEvent present absent ↔
      present ∪ absent ⊆ flipOutcome flip outcome := by
  rw [mem_mixedSuccessEvent]
  constructor
  · rintro ⟨hp, ha⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · exact (mem_flipOutcome _ _ _).mpr
        (Or.inl ⟨hp he, Finset.disjoint_left.mp hpresent he⟩)
    · exact (mem_flipOutcome _ _ _).mpr
        (Or.inr ⟨habsent he, Finset.disjoint_left.mp ha he⟩)
  · intro h
    constructor
    · intro e he
      have hf := (mem_flipOutcome _ _ _).mp (h (Finset.mem_union_left _ he))
      exact hf.elim And.left (fun hf ↦ False.elim
        (Finset.disjoint_left.mp hpresent he hf.1))
    · rw [Finset.disjoint_left]
      intro e he ho
      have hf := (mem_flipOutcome _ _ _).mp (h (Finset.mem_union_right _ he))
      exact hf.elim (fun hf ↦ hf.2 (habsent he)) (fun hf ↦ hf.2 ho)

theorem flipEvent_mixedSuccessEvent
    {present absent flip : Finset Ω}
    (hpresent : Disjoint present flip) (habsent : absent ⊆ flip) :
    flipEvent flip (mixedSuccessEvent present absent) =
      principalSuccessEvent (present ∪ absent) := by
  ext outcome
  rw [mem_flipEvent, mem_mixedSuccessEvent_iff_subset_flipOutcome hpresent habsent,
    mem_principalSuccessEvent]
  simp [flipOutcome, symmDiff_assoc]

/-- Exact probability of a mixed event after the shared change of coordinates. -/
theorem eventProbability_mixedSuccessEvent
    (P : FiniteBernoulliProduct Ω) {present absent flip : Finset Ω}
    (hpresent : Disjoint present flip) (habsent : absent ⊆ flip) :
    P.eventProbability (mixedSuccessEvent present absent) =
      (P.complementCoordinates flip).eventProbability
        (principalSuccessEvent (present ∪ absent)) := by
  rw [← flipEvent_mixedSuccessEvent hpresent habsent,
    complementCoordinates_eventProbability_flipEvent]

/-- Avoidance of every mixed candidate event. -/
def mixedAvoidanceEvent {I : Type*} [Fintype I]
    (present absent : I → Finset Ω) : Finset (Finset Ω) :=
  Finset.univ.filter fun outcome ↦ ∀ i, outcome ∉ mixedSuccessEvent (present i) (absent i)

@[simp] theorem mem_mixedAvoidanceEvent {I : Type*} [Fintype I]
    (present absent : I → Finset Ω) (outcome : Finset Ω) :
    outcome ∈ mixedAvoidanceEvent present absent ↔
      ∀ i, outcome ∉ mixedSuccessEvent (present i) (absent i) := by
  simp [mixedAvoidanceEvent]

/-- The entire avoidance event is transported using the same global polarity,
including coordinates unused by an individual candidate. -/
theorem flipEvent_mixedAvoidanceEvent
    {I : Type*} [Fintype I] [LinearOrder I]
    (present absent : I → Finset Ω) (flip : Finset Ω)
    (hpresent : ∀ i, Disjoint (present i) flip)
    (habsent : ∀ i, absent i ⊆ flip) :
    flipEvent flip (mixedAvoidanceEvent present absent) =
      principalAvoidanceEvent (fun i ↦ present i ∪ absent i) := by
  ext outcome
  simp only [mem_flipEvent, mem_mixedAvoidanceEvent, mem_principalAvoidanceEvent]
  apply forall_congr'
  intro i
  rw [mem_mixedSuccessEvent_iff_subset_flipOutcome (hpresent i) (habsent i)]
  simp [flipOutcome, symmDiff_assoc]

theorem eventProbability_mixedAvoidanceEvent
    {I : Type*} [Fintype I] [LinearOrder I]
    (P : FiniteBernoulliProduct Ω)
    (present absent : I → Finset Ω) (flip : Finset Ω)
    (hpresent : ∀ i, Disjoint (present i) flip)
    (habsent : ∀ i, absent i ⊆ flip) :
    P.eventProbability (mixedAvoidanceEvent present absent) =
      (P.complementCoordinates flip).eventProbability
        (principalAvoidanceEvent (fun i ↦ present i ∪ absent i)) := by
  rw [← flipEvent_mixedAvoidanceEvent present absent flip hpresent habsent,
    complementCoordinates_eventProbability_flipEvent]

/-- Pairwise compatibility of every required success with every required
failure constructs one common global flip set. -/
theorem exists_globalPolarity
    {I : Type*} [Fintype I]
    (present absent : I → Finset Ω)
    (hconsistent : ∀ i j, Disjoint (present i) (absent j)) :
    ∃ flip : Finset Ω, (∀ i, Disjoint (present i) flip) ∧
      ∀ i, absent i ⊆ flip := by
  classical
  refine ⟨Finset.univ.biUnion absent, ?_, ?_⟩
  · intro i
    rw [Finset.disjoint_left]
    intro e he hf
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (hconsistent i j) he hj
  · intro i e he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, he⟩

/-- A symmetric compact density band survives arbitrary global polarity. -/
theorem complementCoordinates_probability_mem_symmetric_band
    (P : FiniteBernoulliProduct Ω) (flip : Finset Ω) {rho : ℝ}
    (hband : ∀ e, P.probability e ∈ Set.Icc rho (1 - rho)) (e : Ω) :
    (P.complementCoordinates flip).probability e ∈ Set.Icc rho (1 - rho) := by
  rw [complementCoordinates_probability]
  split_ifs
  · obtain ⟨hlo, hhi⟩ := hband e
    constructor <;> linarith
  · exact hband e

end DenseGraph.FiniteBernoulliProduct
