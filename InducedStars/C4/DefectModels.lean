import InducedStars.C4.SplitFibers
import DenseGraph.FiniteModels.FixedCardinalityBlocks

/-!
# Exact fixed-defect cross-coordinate models

Paper: the random graphs in Lemma `lemma:c4-matching`. Positive defects
within the independent side and missing clique edges within the clique side
are fixed. Only cross pairs are sampled. All fixed-count statements retain
the lower feasibility guard and the signed internal-edge correction.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars
open Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An admissible defect has no cross edge. Empty sides are allowed. -/
def C4DefectSupported (D : C4Division V) (T : SimpleGraph V) : Prop :=
  ∀ x y, T.Adj x y →
    (x ∈ D.independentPart ∧ y ∈ D.independentPart) ∨
      (x ∈ D.cliquePart ∧ y ∈ D.cliquePart)

theorem c4DefectGraph_supported (G : SimpleGraph V) (D : C4Division V) :
    C4DefectSupported D (c4DefectGraph G D) := by
  intro x y h
  rcases (c4DefectGraph_adj G D x y).mp h with h | h
  · exact Or.inl ⟨h.1, h.2.1⟩
  · exact Or.inr ⟨h.1, h.2.1⟩

/-- The forced internal edges after fixing the signed defect. -/
def c4FixedDefectInternalGraph (D : C4Division V) (T : SimpleGraph V) : SimpleGraph V :=
  c4WithinGraph T D.independentPart ⊔ c4WithinGraph Tᶜ D.cliquePart

def c4FixedDefectInternalCount (D : C4Division V) (T : SimpleGraph V) : ℕ :=
  (finiteGraphEdges (c4FixedDefectInternalGraph D T)).card

/-- The actual graph obtained from a set of selected cross coordinates. -/
def c4DefectGraphOfCrossChoice (D : C4Division V) (T : SimpleGraph V)
    (C : Finset (Sym2 V)) : SimpleGraph V :=
  c4FixedDefectInternalGraph D T ⊔ SimpleGraph.fromEdgeSet (C : Set (Sym2 V))

@[simp] theorem c4DefectGraphOfCrossChoice_adj (D : C4Division V) (T : SimpleGraph V)
    (C : Finset (Sym2 V)) (x y : V) :
    (c4DefectGraphOfCrossChoice D T C).Adj x y ↔
      ((x ∈ D.independentPart ∧ y ∈ D.independentPart ∧ T.Adj x y) ∨
        (x ∈ D.cliquePart ∧ y ∈ D.cliquePart ∧ x ≠ y ∧ ¬T.Adj x y)) ∨
          (s(x, y) ∈ C ∧ x ≠ y) := by
  simp [c4DefectGraphOfCrossChoice, c4FixedDefectInternalGraph,
    c4WithinGraph_adj, SimpleGraph.fromEdgeSet_adj]

theorem c4FixedDefectInternal_edges_disjoint_cross (D : C4Division V) (T : SimpleGraph V) :
    Disjoint (finiteGraphEdges (c4FixedDefectInternalGraph D T)) (c4CrossPotentialEdges D) := by
  apply Finset.disjoint_left.mpr
  intro e he hc
  induction e using Sym2.inductionOn with
  | _ x y =>
    have h := (mk_mem_finiteGraphEdges _ _ _).mp he
    have hc' := (mk_mem_c4CrossPotentialEdges D x y).mp hc
    simp only [c4FixedDefectInternalGraph, SimpleGraph.sup_adj, c4WithinGraph_adj,
      C4Division.mem_cliquePart] at h hc'
    tauto

theorem finiteGraphEdges_c4DefectGraphOfCrossChoice (D : C4Division V) (T : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    finiteGraphEdges (c4DefectGraphOfCrossChoice D T C) =
      finiteGraphEdges (c4FixedDefectInternalGraph D T) ∪ C := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, c4DefectGraphOfCrossChoice, SimpleGraph.sup_adj,
      SimpleGraph.fromEdgeSet_adj, Finset.mem_coe, Finset.mem_union]
    have hne : s(x, y) ∈ C → x ≠ y := fun h ↦ ne_of_mem_c4CrossPotentialEdges D (hC h)
    tauto

theorem c4CrossEdges_defectGraphOfCrossChoice (D : C4Division V) (T : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    c4CrossEdges (c4DefectGraphOfCrossChoice D T C) D = C := by
  rw [c4CrossEdges, finiteGraphEdges_c4DefectGraphOfCrossChoice D T hC,
    Finset.union_inter_distrib_right,
    Finset.disjoint_iff_inter_eq_empty.mp (c4FixedDefectInternal_edges_disjoint_cross D T),
    Finset.inter_eq_left.mpr hC, Finset.empty_union]

theorem c4DefectGraphOfCrossChoice_injectiveOn (D : C4Division V) (T : SimpleGraph V) :
    Set.InjOn (c4DefectGraphOfCrossChoice D T) {C | C ⊆ c4CrossPotentialEdges D} := by
  intro C hC E hE heq
  have h := congrArg (fun G ↦ c4CrossEdges G D) heq
  simpa [c4CrossEdges_defectGraphOfCrossChoice D T hC,
    c4CrossEdges_defectGraphOfCrossChoice D T hE] using h

theorem card_edges_c4DefectGraphOfCrossChoice (D : C4Division V) (T : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    (finiteGraphEdges (c4DefectGraphOfCrossChoice D T C)).card =
      c4FixedDefectInternalCount D T + C.card := by
  rw [finiteGraphEdges_c4DefectGraphOfCrossChoice D T hC,
    Finset.card_union_of_disjoint ((c4FixedDefectInternal_edges_disjoint_cross D T).mono_right hC)]
  rfl

theorem c4DefectGraph_of_crossChoice (D : C4Division V) (T : SimpleGraph V)
    (hT : C4DefectSupported D T) {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) :
    c4DefectGraph (c4DefectGraphOfCrossChoice D T C) D = T := by
  ext x y
  have hcross := fun h : s(x, y) ∈ C ↦ (mk_mem_c4CrossPotentialEdges D x y).mp (hC h)
  have hsupport := hT x y
  have hloop := fun h : T.Adj x y ↦ h.ne
  simp only [c4DefectGraph_adj, c4DefectGraphOfCrossChoice_adj,
    C4Division.mem_cliquePart] at hcross hsupport ⊢
  tauto

theorem c4DefectGraphOfCrossChoice_crossEdges (G : SimpleGraph V) (D : C4Division V)
    {T : SimpleGraph V} (hT : c4DefectGraph G D = T) :
    c4DefectGraphOfCrossChoice D T (c4CrossEdges G D) = G := by
  ext x y
  have h : (c4DefectGraph G D).Adj x y ↔ T.Adj x y := by rw [hT]
  simp only [c4DefectGraph_adj, C4Division.mem_cliquePart] at h
  simp only [c4DefectGraphOfCrossChoice_adj, c4CrossEdges, Finset.mem_inter,
    mk_mem_finiteGraphEdges, mk_mem_c4CrossPotentialEdges, C4Division.mem_cliquePart]
  have hloop := fun h : G.Adj x y ↦ h.ne
  tauto

theorem c4FixedDefectInternalCount_signed (D : C4Division V) (T : SimpleGraph V) :
    c4FixedDefectInternalCount D T +
        (finiteGraphEdges (T.induce (D.cliquePart : Set V))).card =
      Nat.choose D.cliquePart.card 2 +
        (finiteGraphEdges (T.induce (D.independentPart : Set V))).card := by
  have hbase := c4EdgeCount_add_cliqueDefects
    (c4DefectGraphOfCrossChoice D T ∅) D
  have hA : (c4DefectGraphOfCrossChoice D T ∅).induce (D.independentPart : Set V) =
      T.induce (D.independentPart : Set V) := by
    ext x y
    simp only [SimpleGraph.induce_adj, c4DefectGraphOfCrossChoice_adj, Finset.notMem_empty,
      false_and, or_false, x.prop, y.prop, true_and]
    have hx : x.val ∉ D.cliquePart := by simpa using x.prop
    simp [hx]
  have hB : (c4DefectGraphOfCrossChoice D T ∅)ᶜ.induce (D.cliquePart : Set V) =
      T.induce (D.cliquePart : Set V) := by
    ext x y
    have hx : x.val ∉ D.independentPart := (D.mem_cliquePart x.val).mp x.prop
    have hxB : x.val ∈ D.cliquePart := x.prop
    have hyB : y.val ∈ D.cliquePart := y.prop
    simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj,
      c4DefectGraphOfCrossChoice_adj, hx, false_and, Finset.notMem_empty,
      or_false, false_or, hxB, hyB, true_and]
    have hloop := fun h : T.Adj x.val y.val ↦ h.ne
    tauto
  rw [hA, hB, c4CrossEdges_defectGraphOfCrossChoice D T (Finset.empty_subset _),
    Finset.card_empty, add_zero,
    card_edges_c4DefectGraphOfCrossChoice D T (Finset.empty_subset _),
    Finset.card_empty, add_zero] at hbase
  exact hbase

/-- The selected cross count, guarded by the forced internal edge count in
all exact-fiber theorems. -/
def c4FixedDefectQuota (D : C4Division V) (T : SimpleGraph V) (m : ℕ) : ℕ :=
  m - c4FixedDefectInternalCount D T

theorem c4FixedDefectQuota_signed (D : C4Division V) (T : SimpleGraph V) {m : ℕ}
    (hm : c4FixedDefectInternalCount D T ≤ m) :
    (c4FixedDefectQuota D T m : ℤ) = (m : ℤ) - Nat.choose D.cliquePart.card 2 -
      (finiteGraphEdges (T.induce (D.independentPart : Set V))).card +
      (finiteGraphEdges (T.induce (D.cliquePart : Set V))).card := by
  have h := c4FixedDefectInternalCount_signed D T
  unfold c4FixedDefectQuota
  omega

def c4FixedDefectFiber {n : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n))
    (m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  univ.filter fun G ↦ c4DefectGraph G D = T ∧ (finiteGraphEdges G).card = m

@[simp] theorem mem_c4FixedDefectFiber {n m : ℕ} {D : C4Division (Fin n)}
    {T G : SimpleGraph (Fin n)} :
    G ∈ c4FixedDefectFiber D T m ↔ c4DefectGraph G D = T ∧ (finiteGraphEdges G).card = m := by
  simp [c4FixedDefectFiber]

theorem c4FixedDefectFiber_eq_image {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (hT : C4DefectSupported D T) (m : ℕ) :
    c4FixedDefectFiber D T m =
      if c4FixedDefectInternalCount D T ≤ m then
        ((c4CrossPotentialEdges D).powersetCard (c4FixedDefectQuota D T m)).image
          (c4DefectGraphOfCrossChoice D T)
      else ∅ := by
  by_cases hm : c4FixedDefectInternalCount D T ≤ m
  · rw [if_pos hm]
    ext G
    constructor
    · rintro hG
      obtain ⟨hdef, he⟩ := mem_c4FixedDefectFiber.mp hG
      have hcard := card_edges_c4DefectGraphOfCrossChoice D T (c4CrossEdges_subset G D)
      rw [c4DefectGraphOfCrossChoice_crossEdges G D hdef, he] at hcard
      exact Finset.mem_image.mpr ⟨c4CrossEdges G D,
        Finset.mem_powersetCard.mpr ⟨c4CrossEdges_subset G D, by
          unfold c4FixedDefectQuota; omega⟩,
        c4DefectGraphOfCrossChoice_crossEdges G D hdef⟩
    · rintro hG
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hG
      obtain ⟨hC, hcard⟩ := Finset.mem_powersetCard.mp hC
      refine mem_c4FixedDefectFiber.mpr ⟨c4DefectGraph_of_crossChoice D T hT hC, ?_⟩
      rw [card_edges_c4DefectGraphOfCrossChoice D T hC, hcard]
      unfold c4FixedDefectQuota
      omega
  · rw [if_neg hm]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    obtain ⟨hdef, he⟩ := mem_c4FixedDefectFiber.mp hG
    have hcard := card_edges_c4DefectGraphOfCrossChoice D T (c4CrossEdges_subset G D)
    rw [c4DefectGraphOfCrossChoice_crossEdges G D hdef, he] at hcard
    omega

theorem card_c4FixedDefectFiber {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (hT : C4DefectSupported D T) (m : ℕ) :
    (c4FixedDefectFiber D T m).card =
      if c4FixedDefectInternalCount D T ≤ m then
        Nat.choose (D.independentPart.card * D.cliquePart.card) (c4FixedDefectQuota D T m)
      else 0 := by
  rw [c4FixedDefectFiber_eq_image D T hT]
  by_cases hm : c4FixedDefectInternalCount D T ≤ m
  · rw [if_pos hm, if_pos hm, Finset.card_image_iff.mpr]
    · rw [Finset.card_powersetCard, card_c4CrossPotentialEdges]
    · intro C hC E hE heq
      exact c4DefectGraphOfCrossChoice_injectiveOn D T
        (Finset.mem_powersetCard.mp hC).1 (Finset.mem_powersetCard.mp hE).1 heq
  · simp [hm]

/-- The one-block fixed-count model on precisely the optional cross pairs. -/
def c4FixedCrossModel (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) :
    DenseGraph.FixedCardinalityBlockModel Unit (Sym2 V) where
  block _ := c4CrossPotentialEdges D
  pairwiseDisjoint := by intro i _ j _ hij; exact False.elim (hij (Subsingleton.elim _ _))
  quota _ := q
  quota_le _ := hq

/-- Tagged coordinates agree definitionally with the existing one-block
conditioning interface; the tag carries no extra random information. -/
abbrev C4CrossCoordinate (D : C4Division V) := Σ _ : Unit, ↥(c4CrossPotentialEdges D)

def c4CrossCoordinateEmbedding (D : C4Division V) : C4CrossCoordinate D ↪ Sym2 V where
  toFun e := e.2.val
  inj' := by
    rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := Subsingleton.elim _ _
    subst j
    have hab : a = b := Subtype.ext h
    subst b
    rfl

def c4CrossChoiceOfOutcome (D : C4Division V) (outcome : Finset (C4CrossCoordinate D)) :
    Finset (Sym2 V) := outcome.map (c4CrossCoordinateEmbedding D)

theorem c4CrossChoiceOfOutcome_subset (D : C4Division V)
    (outcome : Finset (C4CrossCoordinate D)) :
    c4CrossChoiceOfOutcome D outcome ⊆ c4CrossPotentialEdges D := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp he
  exact x.2.prop

theorem c4DefectGraphOfCrossChoice_adj_independent (D : C4Division V) (T : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) {x y : V}
    (hx : x ∈ D.independentPart) (hy : y ∈ D.independentPart) :
    (c4DefectGraphOfCrossChoice D T C).Adj x y ↔ T.Adj x y := by
  have hc : s(x, y) ∉ C := by
    intro h
    have h := (mk_mem_c4CrossPotentialEdges D x y).mp (hC h)
    simp [C4Division.mem_cliquePart, hx, hy] at h
  simp [c4DefectGraphOfCrossChoice_adj, C4Division.mem_cliquePart, hx, hy, hc]

theorem c4DefectGraphOfCrossChoice_adj_clique (D : C4Division V) (T : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ c4CrossPotentialEdges D) {x y : V}
    (hx : x ∈ D.cliquePart) (hy : y ∈ D.cliquePart) :
    (c4DefectGraphOfCrossChoice D T C).Adj x y ↔ x ≠ y ∧ ¬T.Adj x y := by
  have hxA := (D.mem_cliquePart x).mp hx
  have hyA := (D.mem_cliquePart y).mp hy
  have hc : s(x, y) ∉ C := by
    intro h
    have h := (mk_mem_c4CrossPotentialEdges D x y).mp (hC h)
    tauto
  simp [c4DefectGraphOfCrossChoice_adj, hxA, hyA, hx, hy, hc]

theorem c4DefectGraphOfCrossChoice_adj_cross (D : C4Division V) (T : SimpleGraph V)
    (C : Finset (Sym2 V)) {x y : V} (hx : x ∈ D.independentPart) (hy : y ∈ D.cliquePart) :
    (c4DefectGraphOfCrossChoice D T C).Adj x y ↔ s(x, y) ∈ C := by
  have hyA := (D.mem_cliquePart y).mp hy
  have hxB : x ∉ D.cliquePart := by simpa using hx
  have hne : x ≠ y := by intro h; subst y; exact hyA hx
  simp [c4DefectGraphOfCrossChoice_adj, hx, hyA, hxB, hne]

theorem c4CrossChoiceOfSample (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) (S : (c4FixedCrossModel D q hq).Sample) :
    c4CrossChoiceOfOutcome D ((c4FixedCrossModel D q hq).sampleOutcome S) =
      (c4FixedCrossModel D q hq).selectedInBlock S () := by
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

@[simp] theorem card_c4CrossChoiceOfSample (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) (S : (c4FixedCrossModel D q hq).Sample) :
    (c4CrossChoiceOfOutcome D ((c4FixedCrossModel D q hq).sampleOutcome S)).card = q := by
  rw [c4CrossChoiceOfSample]
  exact DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock _ _ ()

@[simp] theorem c4FixedCrossModel_sampleSpaceCard (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) :
    (c4FixedCrossModel D q hq).sampleSpaceCard = Nat.choose (c4CrossPotentialEdges D).card q := by
  simp [DenseGraph.FixedCardinalityBlockModel.sampleSpaceCard, c4FixedCrossModel]

@[simp] theorem c4FixedCrossModel_conditioningFactor (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) :
    (c4FixedCrossModel D q hq).conditioningFactor = (c4CrossPotentialEdges D).card + 1 := by
  simp [DenseGraph.FixedCardinalityBlockModel.conditioningFactor, c4FixedCrossModel]

def c4FixedCrossSampleOfChoice (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) (C : Finset (Sym2 V))
    (hC : C ⊆ c4CrossPotentialEdges D) (hcard : C.card = q) :
    (c4FixedCrossModel D q hq).Sample := fun _ ↦
  ⟨C.subtype (fun e ↦ e ∈ c4CrossPotentialEdges D), Finset.mem_powersetCard.mpr
    ⟨Finset.subset_univ _, by
      change (C.subtype (fun e ↦ e ∈ c4CrossPotentialEdges D)).card = q
      rw [Finset.card_subtype, Finset.filter_eq_self.mpr (fun e he ↦ hC he)]
      exact hcard⟩⟩

theorem c4CrossChoiceOfSampleOfChoice (D : C4Division V) (q : ℕ)
    (hq : q ≤ (c4CrossPotentialEdges D).card) (C : Finset (Sym2 V))
    (hC : C ⊆ c4CrossPotentialEdges D) (hcard : C.card = q) :
    c4CrossChoiceOfOutcome D ((c4FixedCrossModel D q hq).sampleOutcome
      (c4FixedCrossSampleOfChoice D q hq C hC hcard)) = C := by
  rw [c4CrossChoiceOfSample]
  exact Finset.subtype_map_of_mem (fun e he ↦ hC he)

def c4DefectOutcomeGraph (D : C4Division V) (T : SimpleGraph V)
    (outcome : Finset (C4CrossCoordinate D)) : SimpleGraph V :=
  c4DefectGraphOfCrossChoice D T (c4CrossChoiceOfOutcome D outcome)

def c4DefectFreeOutcomeEvent (D : C4Division V) (T : SimpleGraph V) :
    Finset (Finset (C4CrossCoordinate D)) :=
  univ.filter fun outcome ↦ ¬InducedEmbeds inducedC4 (c4DefectOutcomeGraph D T outcome)

@[simp] theorem mem_c4DefectFreeOutcomeEvent (D : C4Division V) (T : SimpleGraph V)
    (outcome : Finset (C4CrossCoordinate D)) :
    outcome ∈ c4DefectFreeOutcomeEvent D T ↔
      ¬InducedEmbeds inducedC4 (c4DefectOutcomeGraph D T outcome) := by
  simp only [c4DefectFreeOutcomeEvent, Finset.mem_filter, Finset.mem_univ, true_and]

def c4FixedDefectFreeFiber {n : ℕ} (D : C4Division (Fin n)) (T : SimpleGraph (Fin n))
    (m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (c4FixedDefectFiber D T m).filter fun G ↦ ¬InducedEmbeds inducedC4 G

@[simp] theorem mem_c4FixedDefectFreeFiber {n m : ℕ} {D : C4Division (Fin n)}
    {T G : SimpleGraph (Fin n)} :
    G ∈ c4FixedDefectFreeFiber D T m ↔
      (c4DefectGraph G D = T ∧ (finiteGraphEdges G).card = m) ∧ ¬InducedEmbeds inducedC4 G := by
  simp only [c4FixedDefectFreeFiber, Finset.mem_filter, mem_c4FixedDefectFiber]

/-- Every actual fixed-defect C4-free graph has a corresponding successful
fixed sample. This is the graph-count bridge, not just a probability bound
for a model disconnected from the finite graph family. -/
theorem card_c4FixedDefectFreeFiber_le_sampleEvent {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (m : ℕ)
    (hquota : c4FixedDefectQuota D T m ≤ (c4CrossPotentialEdges D).card) :
    (c4FixedDefectFreeFiber D T m).card ≤
      ((c4FixedCrossModel D (c4FixedDefectQuota D T m) hquota).sampleEvent
        (c4DefectFreeOutcomeEvent D T)).card := by
  let M := c4FixedCrossModel D (c4FixedDefectQuota D T m) hquota
  let graphOfSample : M.Sample → SimpleGraph (Fin n) := fun S ↦
    c4DefectOutcomeGraph D T (M.sampleOutcome S)
  have hsub : c4FixedDefectFreeFiber D T m ⊆
      (M.sampleEvent (c4DefectFreeOutcomeEvent D T)).image graphOfSample := by
    intro G hG
    obtain ⟨⟨hdef, he⟩, hfree⟩ := mem_c4FixedDefectFreeFiber.mp hG
    have hcard : (c4CrossEdges G D).card = c4FixedDefectQuota D T m := by
      have h := card_edges_c4DefectGraphOfCrossChoice D T (c4CrossEdges_subset G D)
      rw [c4DefectGraphOfCrossChoice_crossEdges G D hdef, he] at h
      unfold c4FixedDefectQuota
      omega
    let S : M.Sample := c4FixedCrossSampleOfChoice D (c4FixedDefectQuota D T m)
      hquota (c4CrossEdges G D) (c4CrossEdges_subset G D) hcard
    have hgraph : graphOfSample S = G := by
      dsimp [graphOfSample, c4DefectOutcomeGraph, S, M]
      rw [c4CrossChoiceOfSampleOfChoice,
        c4DefectGraphOfCrossChoice_crossEdges G D hdef]
    refine Finset.mem_image.mpr ⟨S, ?_, hgraph⟩
    have hmember : M.sampleOutcome S ∈ c4DefectFreeOutcomeEvent D T := by
      apply (mem_c4DefectFreeOutcomeEvent D T (M.sampleOutcome S)).mpr
      change ¬InducedEmbeds inducedC4 (graphOfSample S)
      rw [hgraph]
      exact hfree
    exact (DenseGraph.FixedCardinalityBlockModel.mem_sampleEvent M
      (c4DefectFreeOutcomeEvent D T) S).mpr hmember
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end InducedStars
