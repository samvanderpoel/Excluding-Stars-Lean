import InducedStars.C4.DefectModels

/-!
# Fixed-defect models with frozen cross coordinates

The high-degree arguments freeze all pairs from a chosen vertex to a chosen
set. Frozen present pairs are counted in the forced quota; frozen absent
pairs are not. Only the complementary cross universe is sampled.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars
open Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual frozen cross pairs and their prescribed successful subset. -/
structure C4FrozenCrossData (D : C4Division V) where
  frozen : Finset (Sym2 V)
  present : Finset (Sym2 V)
  frozen_subset : frozen ⊆ c4CrossPotentialEdges D
  present_subset : present ⊆ frozen

namespace C4FrozenCrossData

variable {D : C4Division V} (W : C4FrozenCrossData D)

def optional : Finset (Sym2 V) := c4CrossPotentialEdges D \ W.frozen

theorem optional_subset : W.optional ⊆ c4CrossPotentialEdges D := Finset.sdiff_subset

theorem present_subset_cross : W.present ⊆ c4CrossPotentialEdges D :=
  W.present_subset.trans W.frozen_subset

theorem present_disjoint_optional : Disjoint W.present W.optional := by
  apply Finset.disjoint_left.mpr
  intro e hp ho
  exact (Finset.mem_sdiff.mp ho).2 (W.present_subset hp)

theorem optional_card_add_frozen : W.optional.card + W.frozen.card =
    (c4CrossPotentialEdges D).card := Finset.card_sdiff_add_card_eq_card W.frozen_subset

theorem present_union_subset_cross {C : Finset (Sym2 V)} (hC : C ⊆ W.optional) :
    W.present ∪ C ⊆ c4CrossPotentialEdges D :=
  Finset.union_subset W.present_subset_cross (hC.trans W.optional_subset)

theorem present_union_inter_frozen {C : Finset (Sym2 V)} (hC : C ⊆ W.optional) :
    (W.present ∪ C) ∩ W.frozen = W.present := by
  ext e
  have hp := fun h : e ∈ W.present => W.present_subset h
  have hc := fun h : e ∈ C => (Finset.mem_sdiff.mp (hC h)).2
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

theorem pinned_cross_eq_present_union (C : Finset (Sym2 V))
    (hpin : C ∩ W.frozen = W.present) : W.present ∪ (C \ W.frozen) = C := by
  rw [← hpin]
  ext e
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
  tauto

def graphOfChoice (T : SimpleGraph V) (C : Finset (Sym2 V)) : SimpleGraph V :=
  c4DefectGraphOfCrossChoice D T (W.present ∪ C)

theorem card_graphOfChoice (T : SimpleGraph V) {C : Finset (Sym2 V)}
    (hC : C ⊆ W.optional) :
    (finiteGraphEdges (W.graphOfChoice T C)).card =
      c4FixedDefectInternalCount D T + W.present.card + C.card := by
  rw [graphOfChoice, card_edges_c4DefectGraphOfCrossChoice D T
    (W.present_union_subset_cross hC),
    Finset.card_union_of_disjoint (W.present_disjoint_optional.mono_right hC)]
  omega

theorem graphOfChoice_defect (T : SimpleGraph V) (hT : C4DefectSupported D T)
    {C : Finset (Sym2 V)} (hC : C ⊆ W.optional) :
    c4DefectGraph (W.graphOfChoice T C) D = T :=
  c4DefectGraph_of_crossChoice D T hT (W.present_union_subset_cross hC)

theorem graphOfChoice_pinned (T : SimpleGraph V) {C : Finset (Sym2 V)}
    (hC : C ⊆ W.optional) :
    c4CrossEdges (W.graphOfChoice T C) D ∩ W.frozen = W.present := by
  rw [graphOfChoice, c4CrossEdges_defectGraphOfCrossChoice D T
    (W.present_union_subset_cross hC), W.present_union_inter_frozen hC]

def quota (T : SimpleGraph V) (m : ℕ) : ℕ :=
  m - c4FixedDefectInternalCount D T - W.present.card

/-- This explicit signed identity includes the subtraction of every frozen
success. Its lower guard is a genuine finite feasibility condition. -/
theorem quota_signed (T : SimpleGraph V) {m : ℕ}
    (hm : c4FixedDefectInternalCount D T + W.present.card ≤ m) :
    (W.quota T m : ℤ) = (m : ℤ)-c4FixedDefectInternalCount D T-W.present.card := by
  unfold quota
  omega

def model (q : ℕ) (hq : q ≤ W.optional.card) :
    DenseGraph.FixedCardinalityBlockModel Unit (Sym2 V) where
  block _ := W.optional
  pairwiseDisjoint := by intro i _ j _ hij; exact False.elim (hij (Subsingleton.elim _ _))
  quota _ := q
  quota_le _ := hq

abbrev Coordinate := Σ _ : Unit, ↥W.optional

def coordinateEmbedding : W.Coordinate ↪ Sym2 V where
  toFun e := e.2.val
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hab : a = b := Subtype.ext h
    subst b
    rfl

def choiceOfOutcome (outcome : Finset W.Coordinate) : Finset (Sym2 V) :=
  outcome.map W.coordinateEmbedding

theorem choiceOfOutcome_subset (outcome : Finset W.Coordinate) :
    W.choiceOfOutcome outcome ⊆ W.optional := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
  exact x.2.prop

theorem coordinate_mem_choice (e : W.Coordinate) (outcome : Finset W.Coordinate) :
    e.2.val ∈ W.choiceOfOutcome outcome ↔ e ∈ outcome :=
  Finset.mem_map' W.coordinateEmbedding

def outcomeGraph (T : SimpleGraph V) (outcome : Finset W.Coordinate) : SimpleGraph V :=
  W.graphOfChoice T (W.choiceOfOutcome outcome)

theorem outcomeGraph_adj_cross (T : SimpleGraph V) (outcome : Finset W.Coordinate)
    {x y : V} (hx : x ∈ D.independentPart) (hy : y ∈ D.cliquePart) :
    (W.outcomeGraph T outcome).Adj x y ↔
      s(x,y) ∈ W.present ∨ s(x,y) ∈ W.choiceOfOutcome outcome := by
  rw [outcomeGraph, graphOfChoice, c4DefectGraphOfCrossChoice_adj_cross D T _ hx hy]
  exact Finset.mem_union

theorem outcomeGraph_adj_independent (T : SimpleGraph V) (outcome : Finset W.Coordinate)
    {x y : V} (hx : x ∈ D.independentPart) (hy : y ∈ D.independentPart) :
    (W.outcomeGraph T outcome).Adj x y ↔ T.Adj x y :=
  c4DefectGraphOfCrossChoice_adj_independent D T
    (W.present_union_subset_cross (W.choiceOfOutcome_subset outcome)) hx hy

theorem outcomeGraph_adj_clique (T : SimpleGraph V) (outcome : Finset W.Coordinate)
    {x y : V} (hx : x ∈ D.cliquePart) (hy : y ∈ D.cliquePart) :
    (W.outcomeGraph T outcome).Adj x y ↔ x ≠ y ∧ ¬T.Adj x y :=
  c4DefectGraphOfCrossChoice_adj_clique D T
    (W.present_union_subset_cross (W.choiceOfOutcome_subset outcome)) hx hy

def freeEvent (T : SimpleGraph V) : Finset (Finset W.Coordinate) :=
  univ.filter fun outcome => ¬InducedEmbeds inducedC4 (W.outcomeGraph T outcome)

@[simp] theorem mem_freeEvent (T : SimpleGraph V) (outcome : Finset W.Coordinate) :
    outcome ∈ W.freeEvent T ↔ ¬InducedEmbeds inducedC4 (W.outcomeGraph T outcome) := by
  simp only [freeEvent, Finset.mem_filter, Finset.mem_univ, true_and]

@[simp] theorem model_sampleSpaceCard (q : ℕ) (hq : q ≤ W.optional.card) :
    (W.model q hq).sampleSpaceCard = W.optional.card.choose q := by
  simp [model, DenseGraph.FixedCardinalityBlockModel.sampleSpaceCard]

@[simp] theorem model_conditioningFactor (q : ℕ) (hq : q ≤ W.optional.card) :
    (W.model q hq).conditioningFactor = (W.optional.card : ℝ)+1 := by
  simp [model, DenseGraph.FixedCardinalityBlockModel.conditioningFactor]

theorem choiceOfSample (q : ℕ) (hq : q ≤ W.optional.card) (S : (W.model q hq).Sample) :
    W.choiceOfOutcome ((W.model q hq).sampleOutcome S) =
      (W.model q hq).selectedInBlock S () := by
  ext e
  constructor
  · intro he
    obtain ⟨⟨⟨⟩, c⟩, hc, heq⟩ := Finset.mem_map.mp he
    exact Finset.mem_map.mpr ⟨c,
      (DenseGraph.FixedCardinalityBlockModel.mem_sampleOutcome _ _ _).mp hc, heq⟩
  · intro he
    obtain ⟨c, hc, heq⟩ := Finset.mem_map.mp he
    exact Finset.mem_map.mpr ⟨⟨(), c⟩,
      (DenseGraph.FixedCardinalityBlockModel.mem_sampleOutcome _ _ _).mpr hc, heq⟩

def sampleOfChoice (q : ℕ) (hq : q ≤ W.optional.card) (C : Finset (Sym2 V))
    (hC : C ⊆ W.optional) (hcard : C.card = q) : (W.model q hq).Sample := fun _ =>
  ⟨C.subtype (fun e => e ∈ W.optional), Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, by
      change (C.subtype (fun e => e ∈ W.optional)).card = q
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr (fun e he => hC he)]
      exact hcard⟩⟩

theorem choiceOfSampleOfChoice (q : ℕ) (hq : q ≤ W.optional.card) (C : Finset (Sym2 V))
    (hC : C ⊆ W.optional) (hcard : C.card = q) :
    W.choiceOfOutcome ((W.model q hq).sampleOutcome (W.sampleOfChoice q hq C hC hcard)) = C := by
  rw [W.choiceOfSample]
  exact Finset.subtype_map_of_mem (fun e he => hC he)

def freeFiber {n : ℕ} {D : C4Division (Fin n)} (W : C4FrozenCrossData D)
    (T : SimpleGraph (Fin n)) (m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (c4FixedDefectFreeFiber D T m).filter fun G => c4CrossEdges G D ∩ W.frozen = W.present

@[simp] theorem mem_freeFiber {n : ℕ} {D : C4Division (Fin n)} (W : C4FrozenCrossData D)
    (T : SimpleGraph (Fin n)) (m : ℕ) (G : SimpleGraph (Fin n)) :
    G ∈ W.freeFiber T m ↔
      ((c4DefectGraph G D = T ∧ (finiteGraphEdges G).card = m) ∧ ¬InducedEmbeds inducedC4 G) ∧
        c4CrossEdges G D ∩ W.frozen = W.present := by
  simp only [freeFiber, Finset.mem_filter, mem_c4FixedDefectFreeFiber]

/-- Any actual graph in the frozen family determines one successful sample.
The natural quota identity follows from its exact edge count, including
forced successes, even if the general family is empty at early parameters. -/
theorem card_freeFiber_le_sampleEvent {n : ℕ} {D : C4Division (Fin n)}
    (W : C4FrozenCrossData D) (T : SimpleGraph (Fin n)) (m : ℕ)
    (hq : W.quota T m ≤ W.optional.card) :
    (W.freeFiber T m).card ≤
      ((W.model (W.quota T m) hq).sampleEvent (W.freeEvent T)).card := by
  let M := W.model (W.quota T m) hq
  let graphOfSample : M.Sample → SimpleGraph (Fin n) := fun S =>
    W.outcomeGraph T (M.sampleOutcome S)
  have hsub : W.freeFiber T m ⊆ (M.sampleEvent (W.freeEvent T)).image graphOfSample := by
    intro G hG
    obtain ⟨⟨⟨hdef, he⟩, hfree⟩, hpin⟩ := (W.mem_freeFiber T m G).mp hG
    let C := c4CrossEdges G D \ W.frozen
    have hC : C ⊆ W.optional := by
      intro e he
      exact Finset.mem_sdiff.mpr ⟨c4CrossEdges_subset G D (Finset.mem_sdiff.mp he).1,
        (Finset.mem_sdiff.mp he).2⟩
    have hgraphC : W.graphOfChoice T C = G := by
      rw [graphOfChoice, W.pinned_cross_eq_present_union _ hpin,
        c4DefectGraphOfCrossChoice_crossEdges G D hdef]
    have hcard : C.card = W.quota T m := by
      have h := W.card_graphOfChoice T hC
      rw [hgraphC, he] at h
      unfold quota
      omega
    let S : M.Sample := W.sampleOfChoice (W.quota T m) hq C hC hcard
    have hgraph : graphOfSample S = G := by
      dsimp [graphOfSample, outcomeGraph, S, M]
      rw [W.choiceOfSampleOfChoice]
      exact hgraphC
    refine Finset.mem_image.mpr ⟨S, ?_, hgraph⟩
    apply (DenseGraph.FixedCardinalityBlockModel.mem_sampleEvent M (W.freeEvent T) S).mpr
    apply (W.mem_freeEvent T (M.sampleOutcome S)).mpr
    change ¬InducedEmbeds inducedC4 (graphOfSample S)
    rw [hgraph]
    exact hfree
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Transfer an avoidance estimate in the actual reduced Bernoulli universe
to the actual frozen graph family. This finite adapter keeps its polynomial
conditioning cost and one exact reduced binomial slice explicit. -/
theorem card_freeFiber_le_of_bernoulli {n : ℕ} {D : C4Division (Fin n)}
    (W : C4FrozenCrossData D) (T : SimpleGraph (Fin n)) (m : ℕ)
    (hq : W.quota T m ≤ W.optional.card) {bound : ℝ}
    (hprob : (W.model (W.quota T m) hq).associatedBernoulli.eventProbability
      (W.freeEvent T) ≤ bound) :
    ((W.freeFiber T m).card : ℝ) ≤
      (W.optional.card.choose (W.quota T m) : ℝ)*((W.optional.card : ℝ)+1)*bound := by
  let M := W.model (W.quota T m) hq
  have hp := M.fixedCardinality_eventProbability_le_conditioningFactor_mul (W.freeEvent T)
  have hbound := hp.trans (mul_le_mul_of_nonneg_left hprob M.conditioningFactor_pos.le)
  change M.eventProbability (M.sampleEvent (W.freeEvent T)) ≤ _ at hbound
  rw [M.eventProbability_eq_card_div] at hbound
  have hspos : (0 : ℝ) < M.sampleSpaceCard := Nat.cast_pos.mpr M.sampleSpaceCard_pos
  have hcount := (div_le_iff₀ hspos).mp hbound
  have hfamily : ((W.freeFiber T m).card : ℝ) ≤ (M.sampleEvent (W.freeEvent T)).card := by
    exact_mod_cast W.card_freeFiber_le_sampleEvent T m hq
  have h := hfamily.trans hcount
  simpa only [M, W.model_sampleSpaceCard, W.model_conditioningFactor,
    mul_assoc, mul_left_comm, mul_comm] using h

end C4FrozenCrossData

/-- The vertex-to-set coordinates frozen in both high-degree arguments. -/
def c4CrossStar (v : V) (Z : Finset V) : Finset (Sym2 V) := Z.map (Sym2.mkEmbedding v)

@[simp] theorem card_c4CrossStar (v : V) (Z : Finset V) : (c4CrossStar v Z).card = Z.card := by
  simp [c4CrossStar]

theorem mk_mem_c4CrossStar (v : V) (Z : Finset V) (x y : V) :
    s(x,y) ∈ c4CrossStar v Z ↔ (x=v ∧ y∈Z) ∨ (y=v ∧ x∈Z) := by
  simp only [c4CrossStar, Finset.mem_map]
  constructor
  · rintro ⟨z, hz, he⟩
    change s(v,z)=s(x,y) at he
    rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact Or.inl ⟨rfl,hz⟩
    · exact Or.inr ⟨rfl,hz⟩
  · rintro (⟨rfl,hy⟩ | ⟨rfl,hx⟩)
    · exact ⟨y,hy,rfl⟩
    · exact ⟨x,hx,Sym2.eq_swap⟩

def c4FrozenCrossStar (D : C4Division V) (v : V) (Z : Finset V)
    (hcross : ∀ z ∈ Z, s(v,z) ∈ c4CrossPotentialEdges D) (present : Bool) :
    C4FrozenCrossData D where
  frozen := c4CrossStar v Z
  present := if present then c4CrossStar v Z else ∅
  frozen_subset := by
    intro e he
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp he
    exact hcross z hz
  present_subset := by cases present <;> simp

@[simp] theorem c4FrozenCrossStar_frozen (D : C4Division V) (v : V) (Z : Finset V)
    (hcross : ∀ z ∈ Z, s(v,z) ∈ c4CrossPotentialEdges D) (present : Bool) :
    (c4FrozenCrossStar D v Z hcross present).frozen = c4CrossStar v Z := rfl

@[simp] theorem c4FrozenCrossStar_present (D : C4Division V) (v : V) (Z : Finset V)
    (hcross : ∀ z ∈ Z, s(v,z) ∈ c4CrossPotentialEdges D) (present : Bool) :
    (c4FrozenCrossStar D v Z hcross present).present =
      if present then c4CrossStar v Z else ∅ := rfl

theorem c4FrozenCrossStar_optional_card (D : C4Division V) (v : V) (Z : Finset V)
    (hcross : ∀ z ∈ Z, s(v,z) ∈ c4CrossPotentialEdges D) (present : Bool) :
    (c4FrozenCrossStar D v Z hcross present).optional.card + Z.card =
      (c4CrossPotentialEdges D).card := by
  simpa using (c4FrozenCrossStar D v Z hcross present).optional_card_add_frozen

end InducedStars
