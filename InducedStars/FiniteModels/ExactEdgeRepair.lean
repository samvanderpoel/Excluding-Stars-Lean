import InducedStars.Asymptotics.FlexiblePairAbundance
import InducedStars.FiniteModels.ConditionalSupport
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Deterministic exact-edge repair

This file deterministically repairs a graphon sample to a prescribed number
of edges.  Only pairs lying in a fixed closed band `[L,U]` are toggled, so a
positive conditional sampling weight remains positive when `0 < L` and
`U < 1`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## A deterministic initial segment of a finite ordered set -/

/-- A choice-fixed first `r` elements of a finite set.  This is the finite-set
version of taking an initial list segment. -/
noncomputable def deterministicFinsetTake {α : Type*} [DecidableEq α]
    (r : ℕ) (s : Finset α) : Finset α :=
  (s.toList.take r).toFinset

theorem deterministicFinsetTake_subset {α : Type*} [DecidableEq α]
    (r : ℕ) (s : Finset α) : deterministicFinsetTake r s ⊆ s := by
  intro a ha
  rw [deterministicFinsetTake, List.mem_toFinset] at ha
  exact Finset.mem_toList.mp (List.mem_of_mem_take ha)

theorem card_deterministicFinsetTake {α : Type*} [DecidableEq α]
    (r : ℕ) (s : Finset α) :
    (deterministicFinsetTake r s).card = min r s.card := by
  rw [deterministicFinsetTake, List.toFinset_card_of_nodup]
  · simp [Finset.length_toList]
  · exact s.nodup_toList.take

/-! ## Flexible present and absent pairs -/

/-- A coordinate-free membership description of the public flexible-pair
finset. -/
theorem mem_flexiblePairFinset_iff {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) (e : Sym2 (Fin n)) :
    e ∈ flexiblePairFinset W L U x ↔
      ¬e.IsDiag ∧ L ≤ graphonPairValue W x e ∧
        graphonPairValue W x e ≤ U := by
  induction e using Sym2.inductionOn with
  | _ i j => simp [graphonPairValue]

/-- Flexible pairs which are edges of `G`. -/
noncomputable def presentFlexibleEdgeFinset {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  flexiblePairFinset W L U x ∩ finiteGraphEdges G

/-- Flexible pairs which are nonedges of `G`. -/
noncomputable def absentFlexibleEdgeFinset {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  flexiblePairFinset W L U x \ finiteGraphEdges G

@[simp]
theorem mem_presentFlexibleEdgeFinset {n : ℕ} {W : Graphon}
    {x : Fin n → UnitInterval} {L U : ℝ} {G : SimpleGraph (Fin n)}
    {e : Sym2 (Fin n)} :
    e ∈ presentFlexibleEdgeFinset W x L U G ↔
      e ∈ flexiblePairFinset W L U x ∧ e ∈ finiteGraphEdges G := by
  simp [presentFlexibleEdgeFinset]

@[simp]
theorem mem_absentFlexibleEdgeFinset {n : ℕ} {W : Graphon}
    {x : Fin n → UnitInterval} {L U : ℝ} {G : SimpleGraph (Fin n)}
    {e : Sym2 (Fin n)} :
    e ∈ absentFlexibleEdgeFinset W x L U G ↔
      e ∈ flexiblePairFinset W L U x ∧ e ∉ finiteGraphEdges G := by
  simp [absentFlexibleEdgeFinset]

noncomputable def flexibleEdgesToDelete {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ) : Finset (Sym2 (Fin n)) :=
  deterministicFinsetTake ((finiteGraphEdges G).card - m)
    (presentFlexibleEdgeFinset W x L U G)

noncomputable def flexibleEdgesToAdd {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ) : Finset (Sym2 (Fin n)) :=
  deterministicFinsetTake (m - (finiteGraphEdges G).card)
    (absentFlexibleEdgeFinset W x L U G)

/-- Deterministically repair `G` to `m` edges by deleting an initial segment
of its present flexible pairs, or adding an initial segment of its absent
flexible pairs. -/
noncomputable def repairToExactEdgeCount {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ) : SimpleGraph (Fin n) :=
  if m ≤ (finiteGraphEdges G).card then
    G.deleteEdges (flexibleEdgesToDelete W x L U G m : Set (Sym2 (Fin n)))
  else
    G ⊔ SimpleGraph.fromEdgeSet
      (flexibleEdgesToAdd W x L U G m : Set (Sym2 (Fin n)))

theorem flexibleEdgesToDelete_subset_present {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ) :
    flexibleEdgesToDelete W x L U G m ⊆
      presentFlexibleEdgeFinset W x L U G :=
  deterministicFinsetTake_subset _ _

theorem flexibleEdgesToAdd_subset_absent {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ) :
    flexibleEdgesToAdd W x L U G m ⊆
      absentFlexibleEdgeFinset W x L U G :=
  deterministicFinsetTake_subset _ _

theorem card_flexibleEdgesToDelete {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ)
    (hEnough : (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W x L U G).card) :
    (flexibleEdgesToDelete W x L U G m).card =
      (finiteGraphEdges G).card - m := by
  rw [flexibleEdgesToDelete, card_deterministicFinsetTake, min_eq_left hEnough]

theorem card_flexibleEdgesToAdd {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ)
    (hEnough : m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W x L U G).card) :
    (flexibleEdgesToAdd W x L U G m).card =
      m - (finiteGraphEdges G).card := by
  rw [flexibleEdgesToAdd, card_deterministicFinsetTake, min_eq_left hEnough]

/-! ## Edge-set and cardinality correctness -/

theorem finiteGraphEdges_repairToExactEdgeCount {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ) :
    finiteGraphEdges (repairToExactEdgeCount W x L U G m) =
      if m ≤ (finiteGraphEdges G).card then
        finiteGraphEdges G \ flexibleEdgesToDelete W x L U G m
      else
        finiteGraphEdges G ∪ flexibleEdgesToAdd W x L U G m := by
  classical
  by_cases h : m ≤ (finiteGraphEdges G).card
  · rw [if_pos h]
    ext e
    simp [repairToExactEdgeCount, h, SimpleGraph.edgeSet_deleteEdges]
  · rw [if_neg h]
    ext e
    simp only [repairToExactEdgeCount, h, ↓reduceIte]
    constructor
    · intro he
      rw [mem_finiteGraphEdges, SimpleGraph.edgeSet_sup,
        Set.mem_union, SimpleGraph.edgeSet_fromEdgeSet] at he
      rw [Finset.mem_union]
      rcases he with he | ⟨he, -⟩
      · exact Or.inl (by simpa using he)
      · exact Or.inr (by simpa using he)
    · intro he
      rw [Finset.mem_union] at he
      rw [mem_finiteGraphEdges, SimpleGraph.edgeSet_sup,
        Set.mem_union, SimpleGraph.edgeSet_fromEdgeSet]
      rcases he with he | he
      · exact Or.inl (by simpa using he)
      · refine Or.inr ⟨by simpa using he, ?_⟩
        have hflex : e ∈ flexiblePairFinset W L U x :=
          (mem_absentFlexibleEdgeFinset.mp
            (flexibleEdgesToAdd_subset_absent W x L U G m he)).1
        exact (mem_flexiblePairFinset_iff W L U x e).mp hflex |>.1

/-- If enough present flexible pairs are available for deletion and enough
absent flexible pairs are available for addition, deterministic repair has
exactly `m` edges.  Only the branch selected by the comparison with the input
edge count is actually used. -/
theorem repairToExactEdgeCount_edge_card {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ)
    (hPresent : (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W x L U G).card)
    (hAbsent : m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W x L U G).card) :
    (finiteGraphEdges (repairToExactEdgeCount W x L U G m)).card = m := by
  classical
  rw [finiteGraphEdges_repairToExactEdgeCount]
  by_cases h : m ≤ (finiteGraphEdges G).card
  · rw [if_pos h, Finset.card_sdiff_of_subset]
    · rw [card_flexibleEdgesToDelete W x L U G m hPresent]
      omega
    · exact (flexibleEdgesToDelete_subset_present W x L U G m).trans
        (Finset.inter_subset_right)
  · rw [if_neg h, Finset.card_union_of_disjoint]
    · rw [card_flexibleEdgesToAdd W x L U G m hAbsent]
      omega
    · rw [Finset.disjoint_left]
      intro e heG heAdd
      exact (mem_absentFlexibleEdgeFinset.mp
        (flexibleEdgesToAdd_subset_absent W x L U G m heAdd)).2 heG

/-! ## Exact edit distance -/

theorem graphEditFinset_repairToExactEdgeCount {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ) :
    graphEditFinset G (repairToExactEdgeCount W x L U G m) =
      if m ≤ (finiteGraphEdges G).card then
        flexibleEdgesToDelete W x L U G m
      else
        flexibleEdgesToAdd W x L U G m := by
  classical
  by_cases h : m ≤ (finiteGraphEdges G).card
  · rw [if_pos h]
    ext e
    rw [mem_graphEditFinset]
    simp_rw [← mem_finiteGraphEdges]
    rw [finiteGraphEdges_repairToExactEdgeCount, if_pos h]
    have hsub : e ∈ flexibleEdgesToDelete W x L U G m →
        e ∈ finiteGraphEdges G := fun he ↦
      (mem_presentFlexibleEdgeFinset.mp
        (flexibleEdgesToDelete_subset_present W x L U G m he)).2
    simp only [Finset.mem_sdiff]
    tauto
  · rw [if_neg h]
    ext e
    rw [mem_graphEditFinset]
    simp_rw [← mem_finiteGraphEdges]
    rw [finiteGraphEdges_repairToExactEdgeCount, if_neg h]
    have hdisj : e ∈ flexibleEdgesToAdd W x L U G m →
        e ∉ finiteGraphEdges G := fun he ↦
      (mem_absentFlexibleEdgeFinset.mp
        (flexibleEdgesToAdd_subset_absent W x L U G m he)).2
    simp only [Finset.mem_union]
    tauto

/-- Exact repair toggles precisely the discrepancy in edge counts. -/
theorem graphEditDistance_repairToExactEdgeCount {n : ℕ} (W : Graphon)
    (x : Fin n → UnitInterval) (L U : ℝ) (G : SimpleGraph (Fin n))
    (m : ℕ)
    (hPresent : (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W x L U G).card)
    (hAbsent : m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W x L U G).card) :
    graphEditDistance G (repairToExactEdgeCount W x L U G m) =
      Nat.dist (finiteGraphEdges G).card m := by
  classical
  rw [graphEditDistance, graphEditFinset_repairToExactEdgeCount]
  by_cases h : m ≤ (finiteGraphEdges G).card
  · rw [if_pos h, card_flexibleEdgesToDelete W x L U G m hPresent,
      Nat.dist_eq_sub_of_le_right h]
  · have h' : (finiteGraphEdges G).card ≤ m := by omega
    rw [if_neg h, card_flexibleEdgesToAdd W x L U G m hAbsent,
      Nat.dist_eq_sub_of_le h']

/-! ## Preservation of positive conditional mass -/

private theorem mem_finiteGraphEdges_compl_iff {n : ℕ}
    (G : SimpleGraph (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ finiteGraphEdges Gᶜ ↔
      ¬e.IsDiag ∧ e ∉ finiteGraphEdges G := by
  induction e using Sym2.inductionOn with
  | _ i j => simp [Sym2.mk_isDiag_iff]

private theorem edgeFactor_pos_of_weight_pos {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n))
    (hpos : 0 < wRandomConditionalWeight W x G)
    (e : Sym2 (Fin n)) (he : e ∈ finiteGraphEdges G) :
    0 < graphonPairValue W x e := by
  have hproduct :
      0 < (∏ a ∈ finiteGraphEdges G, graphonPairValue W x a) *
        ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) := by
    simpa only [wRandomConditionalWeight, graphonInducedIntegrand] using hpos
  have hnonedge_nonneg :
      0 ≤ ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) :=
    Finset.prod_nonneg fun a _ ↦
      sub_nonneg.mpr (graphonPairValue_le_one W x a)
  have hedge_pos : 0 < ∏ a ∈ finiteGraphEdges G,
      graphonPairValue W x a :=
    pos_of_mul_pos_left hproduct hnonedge_nonneg
  have hne : graphonPairValue W x e ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hedge_pos.ne') e he
  exact lt_of_le_of_ne (graphonPairValue_nonneg W x e) hne.symm

private theorem nonedgeFactor_pos_of_weight_pos {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n))
    (hpos : 0 < wRandomConditionalWeight W x G)
    (e : Sym2 (Fin n)) (he : e ∈ finiteGraphEdges Gᶜ) :
    0 < 1 - graphonPairValue W x e := by
  have hproduct :
      0 < (∏ a ∈ finiteGraphEdges G, graphonPairValue W x a) *
        ∏ a ∈ finiteGraphEdges Gᶜ, (1 - graphonPairValue W x a) := by
    simpa only [wRandomConditionalWeight, graphonInducedIntegrand] using hpos
  have hedge_nonneg :
      0 ≤ ∏ a ∈ finiteGraphEdges G, graphonPairValue W x a :=
    Finset.prod_nonneg fun a _ ↦ graphonPairValue_nonneg W x a
  have hnonedge_pos : 0 < ∏ a ∈ finiteGraphEdges Gᶜ,
      (1 - graphonPairValue W x a) :=
    pos_of_mul_pos_right hproduct hedge_nonneg
  have hne : 1 - graphonPairValue W x e ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp hnonedge_pos.ne') e he
  exact lt_of_le_of_ne
    (sub_nonneg.mpr (graphonPairValue_le_one W x e)) hne.symm

/-- Toggling only pairs whose graphon values lie in a strict interior band
preserves positivity of the conditional sampling weight. -/
theorem wRandomConditionalWeight_pos_of_edit_subset_flexible {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G K : SimpleGraph (Fin n)) (hL : 0 < L) (hU : U < 1)
    (hpos : 0 < wRandomConditionalWeight W x G)
    (hEdit : graphEditFinset G K ⊆ flexiblePairFinset W L U x) :
    0 < wRandomConditionalWeight W x K := by
  unfold wRandomConditionalWeight graphonInducedIntegrand
  apply mul_pos
  · apply Finset.prod_pos
    intro e heK
    by_cases heG : e ∈ finiteGraphEdges G
    · exact edgeFactor_pos_of_weight_pos W x G hpos e heG
    · have heEdit : e ∈ graphEditFinset G K := by
        rw [mem_graphEditFinset]
        exact Or.inr ⟨by simpa only [mem_finiteGraphEdges] using heK,
          by simpa only [mem_finiteGraphEdges] using heG⟩
      have hband := (mem_flexiblePairFinset_iff W L U x e).mp (hEdit heEdit)
      exact hL.trans_le hband.2.1
  · apply Finset.prod_pos
    intro e heKc
    have heK' : e ∉ finiteGraphEdges K :=
      (mem_finiteGraphEdges_compl_iff K e).mp heKc |>.2
    by_cases heG : e ∈ finiteGraphEdges G
    · have heEdit : e ∈ graphEditFinset G K := by
        rw [mem_graphEditFinset]
        exact Or.inl ⟨by simpa only [mem_finiteGraphEdges] using heG,
          by simpa only [mem_finiteGraphEdges] using heK'⟩
      have hband := (mem_flexiblePairFinset_iff W L U x e).mp (hEdit heEdit)
      linarith [hband.2.2]
    · apply nonedgeFactor_pos_of_weight_pos W x G hpos e
      exact (mem_finiteGraphEdges_compl_iff G e).mpr
        ⟨(mem_finiteGraphEdges_compl_iff K e).mp heKc |>.1, heG⟩

/-- Deterministic exact-edge repair preserves positive conditional mass. -/
theorem wRandomConditionalWeight_repairToExactEdgeCount_pos {n : ℕ}
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ) (hL : 0 < L) (hU : U < 1)
    (hpos : 0 < wRandomConditionalWeight W x G) :
    0 < wRandomConditionalWeight W x
      (repairToExactEdgeCount W x L U G m) := by
  apply wRandomConditionalWeight_pos_of_edit_subset_flexible
    W x L U G (repairToExactEdgeCount W x L U G m) hL hU hpos
  rw [graphEditFinset_repairToExactEdgeCount]
  split_ifs
  · exact (flexibleEdgesToDelete_subset_present W x L U G m).trans
      Finset.inter_subset_left
  · exact (flexibleEdgesToAdd_subset_absent W x L U G m).trans
      Finset.sdiff_subset

/-! ## Induced-free support and cut-distance control -/

/-- Almost every latent configuration sends every positive-weight graph to
another positive-weight, hence induced-`H`-free, graph after repair. -/
theorem ae_repairToExactEdgeCount_inducedFree {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon)
    (hfree : graphonInducedDensity H W = 0) (L U : ℝ)
    (hL : 0 < L) (hU : U < 1) :
    ∀ᵐ x : Fin n → UnitInterval, ∀ (G : SimpleGraph (Fin n)) (m : ℕ),
      0 < wRandomConditionalWeight W x G →
        ¬Regularity.InducedEmbeds H
          (repairToExactEdgeCount W x L U G m) := by
  filter_upwards [ae_conditionalSupport_inducedFree H W hfree] with x hx
  intro G m hpos
  exact hx (repairToExactEdgeCount W x L U G m)
    (wRandomConditionalWeight_repairToExactEdgeCount_pos
      W x L U G m hL hU hpos)

/-- The cut-distance cost of exact-edge repair is controlled by the exact
number of toggled unordered pairs. -/
theorem cutDist_graphGraphon_repairToExactEdgeCount_le {n : ℕ}
    (hn : 0 < n) (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ)
    (hPresent : (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W x L U G).card)
    (hAbsent : m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W x L U G).card) :
    cutDist (graphGraphon G)
        (graphGraphon (repairToExactEdgeCount W x L U G m)) ≤
      2 * (Nat.dist (finiteGraphEdges G).card m : ℝ) / (n : ℝ) ^ 2 := by
  calc
    cutDist (graphGraphon G)
        (graphGraphon (repairToExactEdgeCount W x L U G m)) ≤
        2 * (graphEditDistance G
          (repairToExactEdgeCount W x L U G m) : ℝ) / (n : ℝ) ^ 2 :=
      cutDist_graphGraphon_le_edit hn G
        (repairToExactEdgeCount W x L U G m)
    _ = 2 * (Nat.dist (finiteGraphEdges G).card m : ℝ) / (n : ℝ) ^ 2 := by
      rw [graphEditDistance_repairToExactEdgeCount
        W x L U G m hPresent hAbsent]

/-- The principal deterministic repair specification: exact edge count,
exact edit cost, preservation of conditional support, and the resulting cut
bound. -/
theorem repairToExactEdgeCount_correct {n : ℕ} (hn : 0 < n)
    (W : Graphon) (x : Fin n → UnitInterval) (L U : ℝ)
    (G : SimpleGraph (Fin n)) (m : ℕ)
    (hPresent : (finiteGraphEdges G).card - m ≤
      (presentFlexibleEdgeFinset W x L U G).card)
    (hAbsent : m - (finiteGraphEdges G).card ≤
      (absentFlexibleEdgeFinset W x L U G).card)
    (hL : 0 < L) (hU : U < 1)
    (hpos : 0 < wRandomConditionalWeight W x G) :
    (finiteGraphEdges (repairToExactEdgeCount W x L U G m)).card = m ∧
      graphEditDistance G (repairToExactEdgeCount W x L U G m) =
        Nat.dist (finiteGraphEdges G).card m ∧
      0 < wRandomConditionalWeight W x
        (repairToExactEdgeCount W x L U G m) ∧
      cutDist (graphGraphon G)
          (graphGraphon (repairToExactEdgeCount W x L U G m)) ≤
        2 * (Nat.dist (finiteGraphEdges G).card m : ℝ) / (n : ℝ) ^ 2 := by
  exact ⟨repairToExactEdgeCount_edge_card W x L U G m hPresent hAbsent,
    graphEditDistance_repairToExactEdgeCount W x L U G m hPresent hAbsent,
    wRandomConditionalWeight_repairToExactEdgeCount_pos
      W x L U G m hL hU hpos,
    cutDist_graphGraphon_repairToExactEdgeCount_le
      hn W x L U G m hPresent hAbsent⟩

end InducedStars
