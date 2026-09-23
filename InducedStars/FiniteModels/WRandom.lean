import InducedStars.Graphon.Densities
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite graphs sampled from a graphon

This file gives a finite, real-valued presentation of the standard
`W`-random labeled graph law.  Conditional on latent points, its mass at a
graph is exactly the induced-density integrand already used by the graphon
layer.  All normalization and event identities below are proved by finite
edge factorization.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## Conditional masses -/

/-- An unordered non-loop pair of vertices of `Fin n`. -/
private abbrev PossibleEdge (n : ℕ) :=
  {e : Sym2 (Fin n) // ¬e.IsDiag}

/-- The edge-membership Boolean pattern of a labeled simple graph. -/
private def graphEdgeIndicator {n : ℕ} (G : SimpleGraph (Fin n)) :
    PossibleEdge n → Prop :=
  fun e ↦ e.1 ∈ G.edgeSet

/-- Build a labeled simple graph from a Boolean choice on every possible edge. -/
private noncomputable def graphFromEdgeIndicator {n : ℕ}
    (p : PossibleEdge n → Prop) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : ¬e.IsDiag, p ⟨e, h⟩}

private noncomputable def graphEdgeIndicatorEquiv (n : ℕ) :
    SimpleGraph (Fin n) ≃ (PossibleEdge n → Prop) where
  toFun := graphEdgeIndicator
  invFun := graphFromEdgeIndicator
  left_inv G := by
    apply (SimpleGraph.edgeSet_inj).mp
    ext e
    constructor
    · intro he
      have hnonDiag :=
        (graphFromEdgeIndicator (graphEdgeIndicator G)).not_isDiag_of_mem_edgeSet he
      simpa [graphFromEdgeIndicator, graphEdgeIndicator, hnonDiag] using he
    · intro he
      have hnonDiag := G.not_isDiag_of_mem_edgeSet he
      simp [graphFromEdgeIndicator, graphEdgeIndicator, he, hnonDiag]
  right_inv p := by
    funext e
    apply propext
    simp [graphFromEdgeIndicator, graphEdgeIndicator, e.2]

private theorem possibleEdge_mem_compl_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) (e : PossibleEdge n) :
    e.1 ∈ Gᶜ.edgeSet ↔ e.1 ∉ G.edgeSet := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : u ≠ v := by
        simpa only [Sym2.mk_isDiag_iff] using he
      simp [SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj, huv]

private def presentPossibleEdgeEquiv {n : ℕ} (G : SimpleGraph (Fin n)) :
    {e : PossibleEdge n // graphEdgeIndicator G e} ≃ G.edgeSet where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, G.not_isDiag_of_mem_edgeSet e.2⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def absentPossibleEdgeEquiv {n : ℕ} (G : SimpleGraph (Fin n)) :
    {e : PossibleEdge n // ¬graphEdgeIndicator G e} ≃ Gᶜ.edgeSet where
  toFun e := ⟨e.1.1, (possibleEdge_mem_compl_iff G e.1).2 e.2⟩
  invFun e := by
    let pe : PossibleEdge n :=
      ⟨e.1, (Gᶜ).not_isDiag_of_mem_edgeSet e.2⟩
    exact ⟨pe, (possibleEdge_mem_compl_iff G pe).1 e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The conditional probability weight of a labeled graph given latent
positions.  This is the existing induced-density integrand, now exposed with
the probabilistic argument order. -/
noncomputable def wRandomConditionalWeight {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n)) : ℝ :=
  graphonInducedIntegrand G W x

theorem measurable_wRandomConditionalWeight {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    Measurable (fun x ↦ wRandomConditionalWeight W x G) :=
  measurable_graphonInducedIntegrand G W

theorem wRandomConditionalWeight_nonneg {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n)) :
    0 ≤ wRandomConditionalWeight W x G :=
  graphonInducedIntegrand_nonneg G W x

theorem wRandomConditionalWeight_le_one {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n)) :
    wRandomConditionalWeight W x G ≤ 1 :=
  graphonInducedIntegrand_le_one G W x

theorem wRandomConditionalWeight_mem_Icc {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n)) :
    wRandomConditionalWeight W x G ∈ Icc (0 : ℝ) 1 :=
  ⟨wRandomConditionalWeight_nonneg W x G,
    wRandomConditionalWeight_le_one W x G⟩

theorem integrable_wRandomConditionalWeight {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    Integrable (fun x ↦ wRandomConditionalWeight W x G)
      (volume : Measure (Fin n → UnitInterval)) :=
  integrable_graphonInducedIntegrand G W

private noncomputable def possibleEdgeProduct {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (p : PossibleEdge n → Prop) : ℝ := by
  classical
  exact ∏ e : PossibleEdge n,
    if p e then graphonPairValue W x e.1 else 1 - graphonPairValue W x e.1

private theorem wRandomConditionalWeight_eq_possibleEdgeProduct {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n)) :
    wRandomConditionalWeight W x G =
      possibleEdgeProduct W x (graphEdgeIndicator G) := by
  classical
  let edgeValue : PossibleEdge n → ℝ := fun e ↦ graphonPairValue W x e.1
  let nonedgeValue : PossibleEdge n → ℝ := fun e ↦ 1 - graphonPairValue W x e.1
  have hpresent :
      (∏ e : {e : PossibleEdge n // graphEdgeIndicator G e}, edgeValue e.1) =
        ∏ e : G.edgeSet, graphonPairValue W x e.1 := by
    exact Fintype.prod_equiv (presentPossibleEdgeEquiv G) _ _ (fun _ ↦ rfl)
  have habsent :
      (∏ e : {e : PossibleEdge n // ¬graphEdgeIndicator G e}, nonedgeValue e.1) =
        ∏ e : Gᶜ.edgeSet, (1 - graphonPairValue W x e.1) := by
    exact Fintype.prod_equiv (absentPossibleEdgeEquiv G) _ _ (fun _ ↦ rfl)
  have hpresentFilter :
      (∏ e ∈ (Finset.univ.filter (graphEdgeIndicator G) :
          Finset (PossibleEdge n)), edgeValue e) =
        ∏ e : {e : PossibleEdge n // graphEdgeIndicator G e}, edgeValue e.1 :=
    Finset.prod_subtype _ (by simp) edgeValue
  have habsentFilter :
      (∏ e ∈ (Finset.univ.filter (fun e ↦ ¬graphEdgeIndicator G e) :
          Finset (PossibleEdge n)), nonedgeValue e) =
        ∏ e : {e : PossibleEdge n // ¬graphEdgeIndicator G e}, nonedgeValue e.1 :=
    Finset.prod_subtype _ (by simp) nonedgeValue
  have hedge :
      (∏ e ∈ finiteGraphEdges G, graphonPairValue W x e) =
        ∏ e : G.edgeSet, graphonPairValue W x e.1 :=
    Finset.prod_subtype (finiteGraphEdges G) (mem_finiteGraphEdges G)
      (fun e ↦ graphonPairValue W x e)
  have hnonedge :
      (∏ e ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x e)) =
        ∏ e : Gᶜ.edgeSet, (1 - graphonPairValue W x e.1) :=
    Finset.prod_subtype (finiteGraphEdges Gᶜ) (mem_finiteGraphEdges Gᶜ)
      (fun e ↦ 1 - graphonPairValue W x e)
  rw [wRandomConditionalWeight, graphonInducedIntegrand, hedge, hnonedge,
    ← hpresent, ← habsent, ← hpresentFilter, ← habsentFilter]
  simpa only [possibleEdgeProduct, edgeValue, nonedgeValue] using
    (Finset.prod_ite
      (s := (Finset.univ : Finset (PossibleEdge n)))
      (p := graphEdgeIndicator G) edgeValue nonedgeValue).symm

/-- Conditional masses of all labeled graphs sum to one. -/
theorem sum_wRandomConditionalWeight {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) :
    ∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G = 1 := by
  classical
  let edgeValue : PossibleEdge n → ℝ := fun e ↦ graphonPairValue W x e.1
  let nonedgeValue : PossibleEdge n → ℝ := fun e ↦ 1 - graphonPairValue W x e.1
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G) =
        ∑ p : PossibleEdge n → Prop, possibleEdgeProduct W x p := by
      apply Fintype.sum_equiv (graphEdgeIndicatorEquiv n)
      intro G
      change wRandomConditionalWeight W x G =
        possibleEdgeProduct W x (graphEdgeIndicator G)
      exact wRandomConditionalWeight_eq_possibleEdgeProduct W x G
    _ = ∏ e : PossibleEdge n,
          ∑ b : Prop, if b then edgeValue e else nonedgeValue e := by
      simp only [possibleEdgeProduct, edgeValue, nonedgeValue]
      rw [Fintype.prod_sum]
    _ = ∏ _e : PossibleEdge n, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro e
      simp [edgeValue, nonedgeValue]
    _ = 1 := by simp

/-- Audit-name alias for conditional normalization. -/
theorem wRandomConditionalWeight_sum {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) :
    ∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G = 1 :=
  sum_wRandomConditionalWeight W x

/-! ## Marginal graph masses -/

/-- The marginal mass of one labeled graph under the standard `W`-random
graph law. -/
noncomputable def wRandomGraphMass {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∫ x : Fin n → UnitInterval, wRandomConditionalWeight W x G

theorem wRandomGraphMass_eq_graphonInducedDensity {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    wRandomGraphMass W G = graphonInducedDensity G W :=
  rfl

theorem wRandomGraphMass_nonneg {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    0 ≤ wRandomGraphMass W G :=
  integral_nonneg (wRandomConditionalWeight_nonneg W · G)

theorem wRandomGraphMass_le_one {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    wRandomGraphMass W G ≤ 1 := by
  unfold wRandomGraphMass
  calc
    (∫ x : Fin n → UnitInterval, wRandomConditionalWeight W x G) ≤
        ∫ _x : Fin n → UnitInterval, (1 : ℝ) :=
      integral_mono (integrable_wRandomConditionalWeight W G)
        (integrable_const 1) (wRandomConditionalWeight_le_one W · G)
    _ = 1 := by simp

theorem wRandomGraphMass_mem_Icc {n : ℕ} (W : Graphon)
    (G : SimpleGraph (Fin n)) :
    wRandomGraphMass W G ∈ Icc (0 : ℝ) 1 :=
  ⟨wRandomGraphMass_nonneg W G, wRandomGraphMass_le_one W G⟩

/-- Marginal masses of all labeled graphs sum to one. -/
theorem sum_wRandomGraphMass {n : ℕ} (W : Graphon) :
    ∑ G : SimpleGraph (Fin n), wRandomGraphMass W G = 1 := by
  classical
  unfold wRandomGraphMass
  rw [← integral_finsetSum Finset.univ]
  · simp_rw [sum_wRandomConditionalWeight]
    simp
  · intro G _hG
    exact integrable_wRandomConditionalWeight W G

/-- Audit-name alias for marginal normalization. -/
theorem wRandomGraphMass_sum {n : ℕ} (W : Graphon) :
    ∑ G : SimpleGraph (Fin n), wRandomGraphMass W G = 1 :=
  sum_wRandomGraphMass W

/-! ## Graph-only events -/

/-- Probability of a graph-only event under the marginal `W`-random graph
law.  The event is a set, while the definition is the finite labeled-graph
sum. -/
noncomputable def wRandomGraphEventProbability {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n), if G ∈ A then wRandomGraphMass W G else 0

private noncomputable def graphsInEvent {n : ℕ}
    (A : Set (SimpleGraph (Fin n))) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter (· ∈ A)

theorem wRandomGraphEventProbability_eq_sum_filter {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability W A =
      ∑ G ∈ graphsInEvent A, wRandomGraphMass W G := by
  classical
  unfold wRandomGraphEventProbability graphsInEvent
  rw [Finset.sum_filter]

theorem wRandomGraphEventProbability_nonneg {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    0 ≤ wRandomGraphEventProbability W A := by
  classical
  unfold wRandomGraphEventProbability
  exact Finset.sum_nonneg fun G _ ↦ by
    split_ifs
    · exact wRandomGraphMass_nonneg W G
    · exact le_rfl

theorem wRandomGraphEventProbability_le_one {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability W A ≤ 1 := by
  classical
  calc
    wRandomGraphEventProbability W A ≤
        ∑ G : SimpleGraph (Fin n), wRandomGraphMass W G := by
      unfold wRandomGraphEventProbability
      apply Finset.sum_le_sum
      intro G _hG
      by_cases hGA : G ∈ A
      · simp [hGA]
      · simp [hGA, wRandomGraphMass_nonneg W G]
    _ = 1 := sum_wRandomGraphMass W

theorem wRandomGraphEventProbability_mem_Icc {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability W A ∈ Icc (0 : ℝ) 1 :=
  ⟨wRandomGraphEventProbability_nonneg W A,
    wRandomGraphEventProbability_le_one W A⟩

theorem wRandomGraphEventProbability_mono {n : ℕ} (W : Graphon)
    {A B : Set (SimpleGraph (Fin n))} (hAB : A ⊆ B) :
    wRandomGraphEventProbability W A ≤ wRandomGraphEventProbability W B := by
  classical
  unfold wRandomGraphEventProbability
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hGA : G ∈ A
  · have hGB : G ∈ B := hAB hGA
    simp [hGA, hGB]
  · by_cases hGB : G ∈ B
    · simpa [hGA, hGB] using wRandomGraphMass_nonneg W G
    · simp [hGA, hGB]

theorem wRandomGraphEventProbability_union_le {n : ℕ} (W : Graphon)
    (A B : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability W (A ∪ B) ≤
      wRandomGraphEventProbability W A + wRandomGraphEventProbability W B := by
  classical
  unfold wRandomGraphEventProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hGA : G ∈ A <;> by_cases hGB : G ∈ B <;>
    simp [hGA, hGB, wRandomGraphMass_nonneg W G]

@[simp] theorem wRandomGraphEventProbability_univ {n : ℕ} (W : Graphon) :
    wRandomGraphEventProbability W (Set.univ : Set (SimpleGraph (Fin n))) = 1 := by
  classical
  simpa [wRandomGraphEventProbability] using sum_wRandomGraphMass (n := n) W

@[simp] theorem wRandomGraphEventProbability_empty {n : ℕ} (W : Graphon) :
    wRandomGraphEventProbability W (∅ : Set (SimpleGraph (Fin n))) = 0 := by
  simp [wRandomGraphEventProbability]

/-! ## Joint latent-position/graph events -/

/-- A joint sampling event, bundled with exactly the measurability needed to
integrate its conditional graph probability. -/
structure WRandomJointEvent (n : ℕ) where
  Holds : (Fin n → UnitInterval) → SimpleGraph (Fin n) → Prop
  measurableSet_holds : ∀ G, MeasurableSet {x | Holds x G}

namespace WRandomJointEvent

/-- A graph-only event, regarded as a joint event. -/
def ofGraphSet {n : ℕ} (A : Set (SimpleGraph (Fin n))) : WRandomJointEvent n where
  Holds := fun _x G ↦ G ∈ A
  measurableSet_holds G := by
    by_cases hG : G ∈ A <;> simp [hG]

/-- A measurable latent-position event, regarded as a joint event. -/
def ofLatentSet {n : ℕ} (A : Set (Fin n → UnitInterval))
    (hA : MeasurableSet A) : WRandomJointEvent n where
  Holds := fun x _G ↦ x ∈ A
  measurableSet_holds _G := hA

/-- Union of two measurable joint events. -/
def union {n : ℕ} (P Q : WRandomJointEvent n) : WRandomJointEvent n where
  Holds := fun x G ↦ P.Holds x G ∨ Q.Holds x G
  measurableSet_holds G := (P.measurableSet_holds G).union (Q.measurableSet_holds G)

end WRandomJointEvent

/-- Conditional probability of a joint event at fixed latent positions. -/
noncomputable def wRandomJointEventIntegrand {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) (x : Fin n → UnitInterval) : ℝ := by
  classical
  exact ∑ G : SimpleGraph (Fin n),
    if P.Holds x G then wRandomConditionalWeight W x G else 0

theorem measurable_wRandomJointEventIntegrand {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    Measurable (wRandomJointEventIntegrand W P) := by
  classical
  unfold wRandomJointEventIntegrand
  exact Finset.measurable_sum _ fun G _hG ↦
    Measurable.ite (P.measurableSet_holds G)
      (measurable_wRandomConditionalWeight W G) measurable_const

theorem wRandomJointEventIntegrand_nonneg {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) (x : Fin n → UnitInterval) :
    0 ≤ wRandomJointEventIntegrand W P x := by
  classical
  unfold wRandomJointEventIntegrand
  exact Finset.sum_nonneg fun G _ ↦ by
    split_ifs
    · exact wRandomConditionalWeight_nonneg W x G
    · exact le_rfl

theorem wRandomJointEventIntegrand_le_one {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W P x ≤ 1 := by
  classical
  calc
    wRandomJointEventIntegrand W P x ≤
        ∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G := by
      unfold wRandomJointEventIntegrand
      apply Finset.sum_le_sum
      intro G _hG
      by_cases hP : P.Holds x G
      · simp [hP]
      · simp [hP, wRandomConditionalWeight_nonneg W x G]
    _ = 1 := sum_wRandomConditionalWeight W x

theorem integrable_wRandomJointEventIntegrand {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    Integrable (wRandomJointEventIntegrand W P)
      (volume : Measure (Fin n → UnitInterval)) := by
  refine Integrable.of_bound
    (measurable_wRandomJointEventIntegrand W P).aestronglyMeasurable 1 ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (wRandomJointEventIntegrand_nonneg W P x)]
  exact wRandomJointEventIntegrand_le_one W P x

/-- Joint probability obtained by first sampling latent points and then a
conditionally independent labeled graph. -/
noncomputable def wRandomJointEventProbability {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) : ℝ :=
  ∫ x : Fin n → UnitInterval, wRandomJointEventIntegrand W P x

theorem wRandomJointEventProbability_nonneg {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    0 ≤ wRandomJointEventProbability W P :=
  integral_nonneg (wRandomJointEventIntegrand_nonneg W P)

theorem wRandomJointEventProbability_le_one {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    wRandomJointEventProbability W P ≤ 1 := by
  unfold wRandomJointEventProbability
  calc
    (∫ x : Fin n → UnitInterval, wRandomJointEventIntegrand W P x) ≤
        ∫ _x : Fin n → UnitInterval, (1 : ℝ) :=
      integral_mono (integrable_wRandomJointEventIntegrand W P)
        (integrable_const 1) (wRandomJointEventIntegrand_le_one W P)
    _ = 1 := by simp

theorem wRandomJointEventProbability_mem_Icc {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    wRandomJointEventProbability W P ∈ Icc (0 : ℝ) 1 :=
  ⟨wRandomJointEventProbability_nonneg W P,
    wRandomJointEventProbability_le_one W P⟩

/-- Joint probability is monotone under pointwise event inclusion. -/
theorem wRandomJointEventProbability_mono {n : ℕ} (W : Graphon)
    {P Q : WRandomJointEvent n}
    (hPQ : ∀ x G, P.Holds x G → Q.Holds x G) :
    wRandomJointEventProbability W P ≤ wRandomJointEventProbability W Q := by
  apply integral_mono (integrable_wRandomJointEventIntegrand W P)
    (integrable_wRandomJointEventIntegrand W Q)
  intro x
  classical
  unfold wRandomJointEventIntegrand
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hP : P.Holds x G
  · have hQ : Q.Holds x G := hPQ x G hP
    simp [hP, hQ]
  · by_cases hQ : Q.Holds x G
    · simpa [hP, hQ] using wRandomConditionalWeight_nonneg W x G
    · simp [hP, hQ]

private theorem wRandomJointEventIntegrand_union_le {n : ℕ} (W : Graphon)
    (P Q : WRandomJointEvent n) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W (P.union Q) x ≤
      wRandomJointEventIntegrand W P x + wRandomJointEventIntegrand W Q x := by
  classical
  unfold wRandomJointEventIntegrand WRandomJointEvent.union
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hP : P.Holds x G <;> by_cases hQ : Q.Holds x G <;>
    simp [hP, hQ, wRandomConditionalWeight_nonneg W x G]

/-- Union bound for measurable joint events. -/
theorem wRandomJointEventProbability_union_le {n : ℕ} (W : Graphon)
    (P Q : WRandomJointEvent n) :
    wRandomJointEventProbability W (P.union Q) ≤
      wRandomJointEventProbability W P + wRandomJointEventProbability W Q := by
  unfold wRandomJointEventProbability
  calc
    (∫ x : Fin n → UnitInterval, wRandomJointEventIntegrand W (P.union Q) x) ≤
        ∫ x : Fin n → UnitInterval,
          (wRandomJointEventIntegrand W P x + wRandomJointEventIntegrand W Q x) :=
      integral_mono (integrable_wRandomJointEventIntegrand W (P.union Q))
        ((integrable_wRandomJointEventIntegrand W P).add
          (integrable_wRandomJointEventIntegrand W Q))
        (wRandomJointEventIntegrand_union_le W P Q)
    _ = _ := integral_add
      (integrable_wRandomJointEventIntegrand W P)
      (integrable_wRandomJointEventIntegrand W Q)

/-- Graph-only predicates in the joint model recover the marginal event
probability. -/
theorem wRandomJointEventProbability_ofGraphSet {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomJointEventProbability W (WRandomJointEvent.ofGraphSet A) =
      wRandomGraphEventProbability W A := by
  classical
  unfold wRandomJointEventProbability wRandomJointEventIntegrand
    wRandomGraphEventProbability WRandomJointEvent.ofGraphSet
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro G _hG
    by_cases hGA : G ∈ A
    · simp [hGA, wRandomGraphMass]
    · simp [hGA]
  · intro G _hG
    by_cases hGA : G ∈ A
    · simpa [hGA] using integrable_wRandomConditionalWeight W G
    · simp [hGA]

/-- Product-volume probability of a measurable latent-position event. -/
noncomputable def wRandomLatentEventProbability {n : ℕ}
    (A : Set (Fin n → UnitInterval)) : ℝ :=
  (volume : Measure (Fin n → UnitInterval)).real A

/-- Latent-only predicates in the joint model recover product-volume
probability. -/
theorem wRandomJointEventProbability_ofLatentSet {n : ℕ} (W : Graphon)
    (A : Set (Fin n → UnitInterval)) (hA : MeasurableSet A) :
    wRandomJointEventProbability W (WRandomJointEvent.ofLatentSet A hA) =
      wRandomLatentEventProbability A := by
  classical
  have hpoint (x : Fin n → UnitInterval) :
      wRandomJointEventIntegrand W (WRandomJointEvent.ofLatentSet A hA) x =
        A.indicator (fun _ ↦ (1 : ℝ)) x := by
    by_cases hx : x ∈ A
    · simp [wRandomJointEventIntegrand, WRandomJointEvent.ofLatentSet, hx,
        sum_wRandomConditionalWeight]
    · simp [wRandomJointEventIntegrand, WRandomJointEvent.ofLatentSet, hx]
  unfold wRandomJointEventProbability wRandomLatentEventProbability
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_indicator_const (1 : ℝ) hA]
  simp

/-! ## Conditional coordinate marginals -/

/-- Under the conditional graph law, the probability that a fixed
non-loop pair is present is its graphon value. -/
theorem sum_wRandomConditionalWeight_indicator_edge {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (e : Sym2 (Fin n)) (he : ¬e.IsDiag) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      (if e ∈ finiteGraphEdges G then (1 : ℝ) else 0)) =
      graphonPairValue W x e := by
  classical
  let pe : PossibleEdge n := ⟨e, he⟩
  let edgeValue : PossibleEdge n → ℝ := fun a ↦ graphonPairValue W x a.1
  let nonedgeValue : PossibleEdge n → ℝ :=
    fun a ↦ 1 - graphonPairValue W x a.1
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
        (if e ∈ finiteGraphEdges G then (1 : ℝ) else 0)) =
        ∑ p : PossibleEdge n → Prop,
          possibleEdgeProduct W x p * (if p pe then 1 else 0) := by
      apply Fintype.sum_equiv (graphEdgeIndicatorEquiv n)
      intro G
      rw [wRandomConditionalWeight_eq_possibleEdgeProduct]
      congr 2
      apply propext
      exact mem_finiteGraphEdges G e
    _ = ∑ p : PossibleEdge n → Prop,
          ∏ a : PossibleEdge n,
            if p a then edgeValue a
            else if a = pe then 0 else nonedgeValue a := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hp : p pe
      · rw [if_pos hp, mul_one]
        unfold possibleEdgeProduct
        apply Finset.prod_congr rfl
        intro a _ha
        by_cases hpa : p a
        · simp [hpa, edgeValue]
        · have hane : a ≠ pe := fun h ↦ hpa (h ▸ hp)
          simp [hpa, hane, nonedgeValue]
      · rw [if_neg hp, mul_zero]
        have hzero : (if p pe then edgeValue pe
            else if pe = pe then 0 else nonedgeValue pe) = 0 := by
          simp [hp]
        exact (Finset.prod_eq_zero (Finset.mem_univ pe) hzero).symm
    _ = ∏ a : PossibleEdge n,
          ∑ b : Prop,
            if b then edgeValue a
            else if a = pe then 0 else nonedgeValue a := by
      rw [Fintype.prod_sum]
    _ = graphonPairValue W x e := by
      rw [show (∏ a : PossibleEdge n,
          ∑ b : Prop,
            if b then edgeValue a
            else if a = pe then 0 else nonedgeValue a) =
          edgeValue pe * ∏ a ∈ (Finset.univ.erase pe : Finset (PossibleEdge n)),
            (1 : ℝ) by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ pe)]
        congr 1
        · simp
        · apply Finset.prod_congr rfl
          intro a ha
          have hane : a ≠ pe := (Finset.mem_erase.mp ha).1
          simp [hane, edgeValue, nonedgeValue]]
      simp [edgeValue, pe]

/-- Distinct non-loop edge coordinates are conditionally independent. -/
theorem sum_wRandomConditionalWeight_indicator_two_edges {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval)
    (e f : Sym2 (Fin n)) (he : ¬e.IsDiag) (hf : ¬f.IsDiag) (hef : e ≠ f) :
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
      (if e ∈ finiteGraphEdges G then (1 : ℝ) else 0) *
      (if f ∈ finiteGraphEdges G then (1 : ℝ) else 0)) =
      graphonPairValue W x e * graphonPairValue W x f := by
  classical
  let pe : PossibleEdge n := ⟨e, he⟩
  let pf : PossibleEdge n := ⟨f, hf⟩
  have hpepf : pe ≠ pf := by
    intro h
    exact hef (congrArg Subtype.val h)
  let edgeValue : PossibleEdge n → ℝ := fun a ↦ graphonPairValue W x a.1
  let nonedgeValue : PossibleEdge n → ℝ :=
    fun a ↦ 1 - graphonPairValue W x a.1
  calc
    (∑ G : SimpleGraph (Fin n), wRandomConditionalWeight W x G *
        (if e ∈ finiteGraphEdges G then (1 : ℝ) else 0) *
        (if f ∈ finiteGraphEdges G then (1 : ℝ) else 0)) =
        ∑ p : PossibleEdge n → Prop,
          possibleEdgeProduct W x p * (if p pe then 1 else 0) *
            (if p pf then 1 else 0) := by
      apply Fintype.sum_equiv (graphEdgeIndicatorEquiv n)
      intro G
      rw [wRandomConditionalWeight_eq_possibleEdgeProduct]
      congr 3 <;> apply propext
      · exact mem_finiteGraphEdges G e
      · exact mem_finiteGraphEdges G f
    _ = ∑ p : PossibleEdge n → Prop,
          ∏ a : PossibleEdge n,
            if p a then edgeValue a
            else if a = pe ∨ a = pf then 0 else nonedgeValue a := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpe : p pe
      · by_cases hpf : p pf
        · rw [if_pos hpe, if_pos hpf, mul_one, mul_one]
          unfold possibleEdgeProduct
          apply Finset.prod_congr rfl
          intro a _ha
          by_cases hpa : p a
          · simp [hpa, edgeValue]
          · have hane : ¬(a = pe ∨ a = pf) := by
              rintro (h | h)
              · exact hpa (h ▸ hpe)
              · exact hpa (h ▸ hpf)
            simp [hpa, hane, nonedgeValue]
        · rw [if_pos hpe, if_neg hpf, mul_one, mul_zero]
          have hzero : (if p pf then edgeValue pf
              else if pf = pe ∨ pf = pf then 0 else nonedgeValue pf) = 0 := by
            simp [hpf]
          exact (Finset.prod_eq_zero (Finset.mem_univ pf) hzero).symm
      · rw [if_neg hpe, mul_zero, zero_mul]
        have hzero : (if p pe then edgeValue pe
            else if pe = pe ∨ pe = pf then 0 else nonedgeValue pe) = 0 := by
          simp [hpe]
        exact (Finset.prod_eq_zero (Finset.mem_univ pe) hzero).symm
    _ = ∏ a : PossibleEdge n,
          ∑ b : Prop,
            if b then edgeValue a
            else if a = pe ∨ a = pf then 0 else nonedgeValue a := by
      rw [Fintype.prod_sum]
    _ = graphonPairValue W x e * graphonPairValue W x f := by
      let q : PossibleEdge n → ℝ := fun a ↦
        ∑ b : Prop, if b then edgeValue a
          else if a = pe ∨ a = pf then 0 else nonedgeValue a
      have hqpe : q pe = edgeValue pe := by simp [q, hpepf]
      have hqpf : q pf = edgeValue pf := by simp [q, hpepf.symm]
      have hrest : (∏ a ∈ ((Finset.univ.erase pe).erase pf :
          Finset (PossibleEdge n)), q a) = 1 := by
        apply Finset.prod_eq_one
        intro a ha
        have haf : a ≠ pf := (Finset.mem_erase.mp ha).1
        have hae : a ≠ pe := (Finset.mem_erase.mp
          (Finset.mem_erase.mp ha).2).1
        simp [q, hae, haf, edgeValue, nonedgeValue]
      change (∏ a : PossibleEdge n, q a) = _
      calc
        (∏ a : PossibleEdge n, q a) =
            q pe * ∏ a ∈ (Finset.univ.erase pe : Finset (PossibleEdge n)),
              q a := (Finset.mul_prod_erase _ _ (Finset.mem_univ pe)).symm
        _ = q pe * (q pf *
              ∏ a ∈ ((Finset.univ.erase pe).erase pf :
                Finset (PossibleEdge n)), q a) := by
            rw [Finset.mul_prod_erase _ _
              (show pf ∈ (Finset.univ.erase pe : Finset (PossibleEdge n)) by
                simp [hpepf.symm])]
        _ = edgeValue pe * edgeValue pf := by rw [hqpe, hqpf, hrest, mul_one]
        _ = graphonPairValue W x e * graphonPairValue W x f := by rfl

end InducedStars
