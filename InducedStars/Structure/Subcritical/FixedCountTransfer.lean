import InducedStars.Structure.Subcritical.ActiveModelsRealization

/-! # Fixed-count transfer for retained active random graphs

Paper: Lemma `lemma:fixed-count-transfer-K1k`. The finite binomial mode bound
gives the exact product of capacity-plus-one factors, including endpoint
quotas and the empty family. Stirling's formula is not required.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Independent Bernoulli trials on active coordinates only. -/
abbrev subcriticalActiveBernoulliModel {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (mvec : RetainedEdgeCountVector D eta R₀) :=
  (subcriticalActiveFixedBlockModel mvec).associatedBernoulli

@[simp] theorem subcriticalActiveBernoulliModel_probability
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (e : (subcriticalActiveFixedBlockModel mvec).Coordinate) :
    (subcriticalActiveBernoulliModel mvec).probability e =
      (mvec.count e.1 : ℝ) / retainedActiveCapacity D eta R₀ e.1 := by
  change DenseGraph.FixedCardinalityBlockModel.quotaParameter
    (retainedActivePotentialEdges D eta R₀ e.1).card (mvec.count e.1) = _
  rw [retainedActivePotentialEdges_card]
  rfl

/-- Joint success probabilities factor for every finite set of coordinates:
this includes coordinates in distinct retained pairs. -/
theorem subcriticalActiveBernoulliModel_independent
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (A : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate) :
    (subcriticalActiveBernoulliModel mvec).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent A) =
      ∏ e ∈ A, (subcriticalActiveBernoulliModel mvec).probability e :=
  (subcriticalActiveBernoulliModel mvec).eventProbability_principalSuccessEvent A

theorem subcriticalActiveBernoulliModel_disjoint_independent
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    {A B : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate}
    (h : Disjoint A B) :
    (subcriticalActiveBernoulliModel mvec).eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent A ∩
          DenseGraph.FiniteBernoulliProduct.principalSuccessEvent B) =
      (subcriticalActiveBernoulliModel mvec).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent A) *
        (subcriticalActiveBernoulliModel mvec).eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent B) :=
  (subcriticalActiveBernoulliModel mvec).eventProbability_principalSuccessEvent_inter_eq_mul_of_disjoint h

/-- Pull back any event of graphs along the common deterministic realization. -/
def subcriticalActiveGraphEvent {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (E : Set (SimpleGraph V)) :
    Finset (Finset (subcriticalActiveFixedBlockModel mvec).Coordinate) :=
  Finset.univ.filter fun S ↦ subcriticalActiveBernoulliGraphFromOutcome H T S ∈ E

def subcriticalActiveFixedProbability {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (E : Set (SimpleGraph V)) : ℝ :=
  (subcriticalActiveFixedBlockModel mvec).outcomeEventProbability
    (subcriticalActiveGraphEvent H T mvec E)

def subcriticalActiveBernoulliProbability {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (mvec : RetainedEdgeCountVector D eta R₀)
    (E : Set (SimpleGraph V)) : ℝ :=
  (subcriticalActiveBernoulliModel mvec).eventProbability
    (subcriticalActiveGraphEvent H T mvec E)

set_option backward.isDefEq.respectTransparency false in
theorem subcriticalActiveFixedProbability_eq_eventProbability
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) (E : Set (SimpleGraph V)) :
    subcriticalActiveFixedProbability H T mvec E =
      (subcriticalActiveFixedBlockModel mvec).eventProbability
        (Finset.univ.filter fun S ↦ subcriticalActiveGraphFromOutcome H T S ∈ E) := by
  unfold subcriticalActiveFixedProbability
    DenseGraph.FixedCardinalityBlockModel.outcomeEventProbability
  congr 1
  ext S
  simp only [DenseGraph.FixedCardinalityBlockModel.mem_sampleEvent,
    subcriticalActiveGraphEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    subcriticalActiveGraphFromOutcome]

/-- With no active pairs there is a unique outcome, of weight one. -/
theorem subcriticalActiveFixedBlockModel_empty_sampleWeight
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    [IsEmpty (RetainedActivePair D eta R₀)]
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : (subcriticalActiveFixedBlockModel mvec).Sample) :
    (subcriticalActiveFixedBlockModel mvec).sampleWeight S = 1 := by
  rw [DenseGraph.FixedCardinalityBlockModel.sampleWeight_eq,
    ← DenseGraph.FixedCardinalityBlockModel.card_sample,
    subcriticalActiveFixedBlockModel_card_of_isEmpty]
  norm_num

/-- Exact conditioning identity, with a strictly positive conditioning event. -/
theorem subcriticalActiveFixedProbability_eq_conditioned
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) (E : Set (SimpleGraph V)) :
    subcriticalActiveFixedProbability H T mvec E =
      (subcriticalActiveBernoulliModel mvec).eventProbability
          (subcriticalActiveGraphEvent H T mvec E ∩
            (subcriticalActiveFixedBlockModel mvec).cardinalityConditionEvent) /
        (subcriticalActiveBernoulliModel mvec).eventProbability
          (subcriticalActiveFixedBlockModel mvec).cardinalityConditionEvent ∧
      0 < (subcriticalActiveBernoulliModel mvec).eventProbability
        (subcriticalActiveFixedBlockModel mvec).cardinalityConditionEvent :=
  ⟨(subcriticalActiveFixedBlockModel mvec).outcomeEventProbability_eq_conditioned_ratio _,
    (subcriticalActiveFixedBlockModel mvec).associatedBernoulli_conditionProbability_pos⟩

theorem subcriticalFixedCountTransfer_product
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) (E : Set (SimpleGraph V)) :
    subcriticalActiveFixedProbability H T mvec E ≤
      (∏ e : RetainedActivePair D eta R₀,
        ((retainedActiveCapacity D eta R₀ e + 1 : ℕ) : ℝ)) *
          subcriticalActiveBernoulliProbability H T mvec E := by
  have h := (subcriticalActiveFixedBlockModel mvec).fixedCardinality_eventProbability_le_conditioningFactor_mul
      (subcriticalActiveGraphEvent H T mvec E)
  simpa [subcriticalActiveFixedProbability, subcriticalActiveBernoulliProbability,
    subcriticalActiveBernoulliModel,
    DenseGraph.FixedCardinalityBlockModel.conditioningFactor,
    subcriticalActiveFixedBlockModel, retainedEdgeChoiceModel,
    retainedActivePotentialEdges_card] using h

theorem subcriticalActiveCapacity_le_sq (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (e : RetainedActivePair D eta R₀) :
    retainedActiveCapacity D eta R₀ e ≤ Fintype.card V ^ 2 := by
  rw [retainedActiveCapacity, pow_two]
  exact Nat.mul_le_mul (Finset.card_le_univ _) (Finset.card_le_univ _)

theorem subcriticalActiveConditioningFactor_le {n : ℕ} (hn : 2 ≤ n)
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ : ℕ) :
    (∏ e : RetainedActivePair D eta R₀,
      ((retainedActiveCapacity D eta R₀ e + 1 : ℕ) : ℝ)) ≤
        (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) := by
  have hb (e : RetainedActivePair D eta R₀) :
      ((retainedActiveCapacity D eta R₀ e + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 3 := by
    have hcap := subcriticalActiveCapacity_le_sq D eta R₀ e
    simp only [Fintype.card_fin] at hcap
    have hn' : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hcap' : (retainedActiveCapacity D eta R₀ e : ℝ) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast hcap
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  calc
    _ ≤ ∏ _e : RetainedActivePair D eta R₀, (n : ℝ) ^ 3 :=
      Finset.prod_le_prod (fun _ _ ↦ by positivity) (fun e _ ↦ hb e)
    _ = _ := by simp [← pow_mul]

/-- Paper: Lemma `lemma:fixed-count-transfer-K1k`.
The absolute constant is `C = 3`; no density-band or Stirling hypothesis is needed. -/
theorem subcriticalFixedCountTransfer {n : ℕ} (hn : 2 ≤ n)
    {D : SubcriticalDivision k (Fin n)} {eta : ℝ} {R₀ : ℕ}
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph (Fin n))
    (mvec : RetainedEdgeCountVector D eta R₀) (E : Set (SimpleGraph (Fin n))) :
    subcriticalActiveFixedProbability H T mvec E ≤
      (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        subcriticalActiveBernoulliProbability H T mvec E :=
  (subcriticalFixedCountTransfer_product H T mvec E).trans
    (mul_le_mul_of_nonneg_right (subcriticalActiveConditioningFactor_le hn D eta R₀)
      ((subcriticalActiveBernoulliModel mvec).eventProbability_nonneg _))

end InducedStars
