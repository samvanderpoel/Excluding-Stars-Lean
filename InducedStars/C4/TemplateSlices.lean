import InducedStars.C4.ColoredCounting
import DenseGraph.Regularity.ColoredEdit
import DenseGraph.FiniteModels.ForcedGraphSlices
import InducedStars.FiniteModels.RepairCounting

/-!
# Exact realization slices and bounded-error template repair

Blue pairs are forced, green pairs are forbidden, and both red and missing
pairs are optional. Missing pairs are never silently assigned a color.
Induced-C4 exclusion is transferred for complete templates, as in
`eqn:coloring-entropy-0`. All finite cardinality formulas keep their feasibility guard.
-/

noncomputable section
open Finset InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical

namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem c4Template_blue_disjoint_green (J : RegularityColoredGraph V) :
    Disjoint (J.edgeColor.labelGraph .blue) (J.edgeColor.labelGraph .green) := by
  apply SimpleGraph.disjoint_left.mpr
  intro x y hb hg
  obtain ⟨h, hc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hb
  obtain ⟨h', hc'⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hg
  have hh : EdgeColor.blue = .green := hc.symm.trans hc'
  cases hh

theorem c4Template_isColoredRealization_iff (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    DenseGraph.IsColoredRealization J G ↔
      J.edgeColor.labelGraph .blue ≤ G ∧ Disjoint (J.edgeColor.labelGraph .green) G := by
  constructor
  · intro h
    constructor
    · intro x y hblue
      obtain ⟨hxy, hc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hblue
      exact (h x y hxy).1 hc
    · apply SimpleGraph.disjoint_left.mpr
      intro x y hgreen hG
      obtain ⟨hxy, hc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hgreen
      exact (h x y hxy).2 hc hG
  · rintro ⟨hblue, hgreen⟩ x y hxy
    constructor
    · intro hc
      exact hblue ((SimpleGraph.EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hc⟩)
    · intro hc hG
      exact SimpleGraph.disjoint_left.mp hgreen x y
        ((SimpleGraph.EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hc⟩) hG

/-- The optional universe includes every missing pair as well as every red pair. -/
theorem c4Template_optionalEdges_eq (J : RegularityColoredGraph V) :
    DenseGraph.forcedGraphOptionalEdges (J.edgeColor.labelGraph .blue)
      (J.edgeColor.labelGraph .green) =
      finiteGraphEdges (J.edgeColor.labelGraph .red) ∪ finiteGraphEdges J.graphᶜ := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [DenseGraph.mem_forcedGraphOptionalEdges, Finset.mem_union,
      mk_mem_finiteGraphEdges, SimpleGraph.EdgeLabeling.labelGraph_adj, SimpleGraph.compl_adj]
    by_cases hxy : J.graph.Adj x y
    · have hne := hxy.ne
      cases hc : J.getEdgeColor x y hxy <;>
        simp_all [RegularityColoredGraph.getEdgeColor, SimpleGraph.EdgeLabeling.get]
    · simp [hxy]

theorem c4Template_redEdges_disjoint_missing (J : RegularityColoredGraph V) :
    Disjoint (finiteGraphEdges (J.edgeColor.labelGraph .red)) (finiteGraphEdges J.graphᶜ) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨hxy, _⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp
      ((mk_mem_finiteGraphEdges _ _ _).mp he)
    exact ((mk_mem_finiteGraphEdges _ _ _).mp hf).2 hxy

theorem c4Template_optionalEdges_card (J : RegularityColoredGraph V) :
    (DenseGraph.forcedGraphOptionalEdges (J.edgeColor.labelGraph .blue)
      (J.edgeColor.labelGraph .green)).card = c4ColorEdgeCount J .red + c4MissingEdgeCount J := by
  rw [c4Template_optionalEdges_eq, Finset.card_union_of_disjoint
    (c4Template_redEdges_disjoint_missing J), c4ColorEdgeCount_eq_card]
  rfl

def c4TemplateRealizationSlice (J : RegularityColoredGraph V) (m : ℕ) :
    Finset (SimpleGraph V) :=
  DenseGraph.forcedGraphSlice (J.edgeColor.labelGraph .blue) (J.edgeColor.labelGraph .green) m

@[simp] theorem mem_c4TemplateRealizationSlice (J : RegularityColoredGraph V)
    (G : SimpleGraph V) (m : ℕ) :
    G ∈ c4TemplateRealizationSlice J m ↔
      DenseGraph.IsColoredRealization J G ∧ (finiteGraphEdges G).card = m := by
  simp only [c4TemplateRealizationSlice, DenseGraph.mem_forcedGraphSlice,
    c4Template_isColoredRealization_iff, and_assoc]

/-- Exact guarded slice cardinality for partial templates. -/
theorem card_c4TemplateRealizationSlice (J : RegularityColoredGraph V) (m : ℕ) :
    (c4TemplateRealizationSlice J m).card =
      if c4ColorEdgeCount J .blue ≤ m then
        Nat.choose (c4ColorEdgeCount J .red + c4MissingEdgeCount J)
          (m - c4ColorEdgeCount J .blue) else 0 := by
  rw [c4TemplateRealizationSlice, DenseGraph.card_forcedGraphSlice _ _
    (c4Template_blue_disjoint_green J), c4Template_optionalEdges_card,
    ← c4ColorEdgeCount_eq_card]

theorem card_c4TemplateRealizationSlice_eq_guarded (J : RegularityColoredGraph V) (m : ℕ) :
    (c4TemplateRealizationSlice J m).card =
      DenseGraph.guardedEntropySliceCount (c4ColorEdgeCount J .red + c4MissingEdgeCount J)
        (c4ColorEdgeCount J .blue) m := by
  rw [card_c4TemplateRealizationSlice]
  rfl

theorem c4TemplateRealizationSlice_nonempty_iff (J : RegularityColoredGraph V) (m : ℕ) :
    (c4TemplateRealizationSlice J m).Nonempty ↔ c4ColorEdgeCount J .blue ≤ m ∧
      m ≤ c4ColorEdgeCount J .blue + (c4ColorEdgeCount J .red + c4MissingEdgeCount J) := by
  rw [← Finset.card_pos, card_c4TemplateRealizationSlice_eq_guarded,
    DenseGraph.guardedEntropySliceCount_pos_iff]

theorem c4MissingEdgeCount_eq_zero_of_complete (J : RegularityColoredGraph V)
    (hcomplete : J.graph = ⊤) : c4MissingEdgeCount J = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have hxy := (mk_mem_finiteGraphEdges _ x y).mp he
    exact hxy.2 (by rw [hcomplete]; exact hxy.1)

theorem card_c4TemplateRealizationSlice_of_complete (J : RegularityColoredGraph V)
    (hcomplete : J.graph = ⊤) (m : ℕ) :
    (c4TemplateRealizationSlice J m).card =
      if c4ColorEdgeCount J .blue ≤ m then
        Nat.choose (c4ColorEdgeCount J .red) (m - c4ColorEdgeCount J .blue) else 0 := by
  rw [card_c4TemplateRealizationSlice, c4MissingEdgeCount_eq_zero_of_complete J hcomplete,
    Nat.add_zero]

/-- Completeness is essential for transfer of induced-C4 exclusion. -/
theorem c4TemplateRealizationSlice_no_inducedC4 (J : RegularityColoredGraph V)
    (hcomplete : J.graph = ⊤) (hfree : ¬ColoredHomExists inducedC4 J)
    {G : SimpleGraph V} {m : ℕ} (hG : G ∈ c4TemplateRealizationSlice J m) :
    ¬InducedEmbeds inducedC4 G :=
  DenseGraph.not_inducedEmbeds_of_complete_realization J G inducedC4 hcomplete
    ((mem_c4TemplateRealizationSlice J G m).mp hG).1 hfree

theorem c4TemplateRealizationSlice_subset_inducedC4Free {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (m : ℕ)
    (hcomplete : J.graph = ⊤) (hfree : ¬ColoredHomExists inducedC4 J) :
    c4TemplateRealizationSlice J m ⊆ inducedC4FreeGraphFinsetWithEdges n m := by
  intro G hG
  exact mem_inducedC4FreeGraphFinsetWithEdges.mpr
    ⟨c4TemplateRealizationSlice_no_inducedC4 J hcomplete hfree hG,
      ((mem_c4TemplateRealizationSlice J G m).mp hG).2⟩

/-- Repair only forced blue and forbidden green pairs, retaining every optional
pair exactly as it occurred in the input graph. -/
def c4TemplateRepair (J : RegularityColoredGraph V) (G : SimpleGraph V) : SimpleGraph V :=
  DenseGraph.forcedGraphOfChoice (J.edgeColor.labelGraph .blue)
    (finiteGraphEdges G ∩ DenseGraph.forcedGraphOptionalEdges
      (J.edgeColor.labelGraph .blue) (J.edgeColor.labelGraph .green))

theorem c4TemplateRepair_edges (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    finiteGraphEdges (c4TemplateRepair J G) =
      finiteGraphEdges (J.edgeColor.labelGraph .blue) ∪
        (finiteGraphEdges G ∩ DenseGraph.forcedGraphOptionalEdges
          (J.edgeColor.labelGraph .blue) (J.edgeColor.labelGraph .green)) :=
  DenseGraph.finiteGraphEdges_forcedGraphOfChoice _ _ Finset.inter_subset_right

theorem c4TemplateRepair_realizes (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    DenseGraph.IsColoredRealization J (c4TemplateRepair J G) := by
  apply (c4Template_isColoredRealization_iff J _).mpr
  exact DenseGraph.forcedGraphOfChoice_constraints _ _ (c4Template_blue_disjoint_green J)
    Finset.inter_subset_right

theorem c4TemplateRepair_eq_self (J : RegularityColoredGraph V) {G : SimpleGraph V}
    (hG : DenseGraph.IsColoredRealization J G) : c4TemplateRepair J G = G := by
  obtain ⟨hb, hg⟩ := (c4Template_isColoredRealization_iff J G).mp hG
  exact DenseGraph.forcedGraphOfChoice_of_constraints _ _ _ hb hg

private theorem repair_adj (J : RegularityColoredGraph V) (G : SimpleGraph V) (x y : V) :
    (c4TemplateRepair J G).Adj x y ↔ (J.edgeColor.labelGraph .blue).Adj x y ∨
      (G.Adj x y ∧ x ≠ y ∧ ¬(J.edgeColor.labelGraph .blue).Adj x y ∧
        ¬(J.edgeColor.labelGraph .green).Adj x y) := by
  rw [← mk_mem_finiteGraphEdges, c4TemplateRepair_edges]
  simp only [Finset.mem_union, Finset.mem_inter, mk_mem_finiteGraphEdges,
    DenseGraph.mem_forcedGraphOptionalEdges]

/-- Exact repair cost: there are no edits on red or missing pairs. -/
theorem c4TemplateRepair_editFinset (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    DenseGraph.simpleGraphEditFinset G (c4TemplateRepair J G) =
      DenseGraph.coloredInconsistencyFinset G J := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [DenseGraph.mem_simpleGraphEditFinset, DenseGraph.mem_coloredInconsistencyFinset,
      SimpleGraph.mem_edgeSet, DenseGraph.coloredPairStatus_mk, SimpleGraph.top_adj, repair_adj,
      SimpleGraph.EdgeLabeling.labelGraph_adj]
    by_cases hne : x = y
    · subst y
      simp
    · by_cases hxy : J.graph.Adj x y
      · cases hc : J.getEdgeColor x y hxy <;>
          simp_all [RegularityColoredGraph.getEdgeColor, SimpleGraph.EdgeLabeling.get]
      · simp [hxy, hne]

theorem c4TemplateRepair_editDistance (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    DenseGraph.simpleGraphEditDistance G (c4TemplateRepair J G) =
      DenseGraph.coloredInconsistency G J := by
  rw [DenseGraph.simpleGraphEditDistance, c4TemplateRepair_editFinset]
  rfl

private theorem edgeCount_le_add_edit (G H : SimpleGraph V) :
    (finiteGraphEdges G).card ≤ (finiteGraphEdges H).card + DenseGraph.simpleGraphEditDistance G H := by
  have hsub : finiteGraphEdges G ⊆ finiteGraphEdges H ∪ DenseGraph.simpleGraphEditFinset G H := by
    intro e he
    by_cases hh : e ∈ finiteGraphEdges H
    · exact Finset.mem_union_left _ hh
    · apply Finset.mem_union_right
      exact DenseGraph.mem_simpleGraphEditFinset.mpr
        (Or.inl ⟨by simpa using he, by simpa using hh⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Both directions of the edge-count shift are bounded by the same exact
repair cost; natural subtraction is unnecessary. -/
theorem c4TemplateRepair_edgeCount_bounds (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    (finiteGraphEdges (c4TemplateRepair J G)).card ≤
        (finiteGraphEdges G).card + DenseGraph.coloredInconsistency G J ∧
      (finiteGraphEdges G).card ≤ (finiteGraphEdges (c4TemplateRepair J G)).card +
        DenseGraph.coloredInconsistency G J := by
  constructor
  · simpa only [DenseGraph.simpleGraphEditDistance_comm (c4TemplateRepair J G) G,
      c4TemplateRepair_editDistance] using edgeCount_le_add_edit (c4TemplateRepair J G) G
  · simpa only [c4TemplateRepair_editDistance] using edgeCount_le_add_edit G (c4TemplateRepair J G)

theorem c4TemplateRepair_edgeCount_abs_le (J : RegularityColoredGraph V) (G : SimpleGraph V) :
    |((finiteGraphEdges (c4TemplateRepair J G)).card : ℝ) - (finiteGraphEdges G).card| ≤
      DenseGraph.coloredInconsistency G J := by
  obtain ⟨h1, h2⟩ := c4TemplateRepair_edgeCount_bounds J G
  have h1R : ((finiteGraphEdges (c4TemplateRepair J G)).card : ℝ) ≤
      (finiteGraphEdges G).card + (DenseGraph.coloredInconsistency G J : ℝ) := by exact_mod_cast h1
  have h2R : ((finiteGraphEdges G).card : ℝ) ≤
      (finiteGraphEdges (c4TemplateRepair J G)).card + (DenseGraph.coloredInconsistency G J : ℝ) := by
    exact_mod_cast h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Fixed original edge count and at most `r` disagreements with the actual
forced/forbidden pairs of a partial template. -/
def c4TemplateNearSlice (J : RegularityColoredGraph V) (m r : ℕ) : Finset (SimpleGraph V) :=
  univ.filter fun G => (finiteGraphEdges G).card = m ∧ DenseGraph.coloredInconsistency G J ≤ r

@[simp] theorem mem_c4TemplateNearSlice (J : RegularityColoredGraph V)
    (G : SimpleGraph V) (m r : ℕ) :
    G ∈ c4TemplateNearSlice J m r ↔
      (finiteGraphEdges G).card = m ∧ DenseGraph.coloredInconsistency G J ≤ r := by
  simp only [c4TemplateNearSlice, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every bounded-error input has an actual feasible realization in the
two-sided repaired edge-count window. -/
theorem c4TemplateRepair_mem_window (J : RegularityColoredGraph V) {G : SimpleGraph V}
    {m r : ℕ} (hG : G ∈ c4TemplateNearSlice J m r) :
    c4TemplateRepair J G ∈ (Finset.Icc (m - r) (m + r)).biUnion
      (fun m' => c4TemplateRealizationSlice J m') := by
  obtain ⟨hm, hr⟩ := (mem_c4TemplateNearSlice J G m r).mp hG
  obtain ⟨hup, hlo⟩ := c4TemplateRepair_edgeCount_bounds J G
  apply Finset.mem_biUnion.mpr
  refine ⟨(finiteGraphEdges (c4TemplateRepair J G)).card, Finset.mem_Icc.mpr ?_, ?_⟩
  · constructor <;> omega
  · exact (mem_c4TemplateRealizationSlice J _ _).mpr ⟨c4TemplateRepair_realizes J G, rfl⟩

/-- Repair fibers lose at most one Hamming ball. The target family sums only
over actual realization slices, so infeasible repaired counts contribute zero. -/
theorem card_c4TemplateNearSlice_le_slice_sum {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (m r : ℕ) :
    (c4TemplateNearSlice J m r).card ≤
      (∑ m' ∈ Finset.Icc (m - r) (m + r), (c4TemplateRealizationSlice J m').card) *
        hammingBallVolume (completeEdgeCount n) r := by
  let S : Finset (SimpleGraph (Fin n)) := (Finset.Icc (m - r) (m + r)).biUnion
    (fun m' => c4TemplateRealizationSlice J m')
  have hDist : ∀ G ∈ c4TemplateNearSlice J m r,
      graphEditDistance G (c4TemplateRepair J G) ≤ r := by
    intro G hG
    rw [← DenseGraph.simpleGraphEditDistance_eq_graphEditDistance,
      c4TemplateRepair_editDistance]
    exact ((mem_c4TemplateNearSlice J G m r).mp hG).2
  have hcount := card_le_card_mul_hammingBallVolume_of_graphRepair
    (c4TemplateNearSlice J m r) S (c4TemplateRepair J)
    (fun G hG => c4TemplateRepair_mem_window J hG) hDist
  exact hcount.trans (Nat.mul_le_mul_right _ (Finset.card_biUnion_le))

/-- Explicit guarded binomial window bound, valid also for zero red capacity,
missing template pairs, and naturally truncated lower edge-count endpoints. -/
theorem card_c4TemplateNearSlice_le_binomial_window {n : ℕ}
    (J : RegularityColoredGraph (Fin n)) (m r : ℕ) :
    (c4TemplateNearSlice J m r).card ≤
      (∑ m' ∈ Finset.Icc (m - r) (m + r),
        if c4ColorEdgeCount J .blue ≤ m' then
          Nat.choose (c4ColorEdgeCount J .red + c4MissingEdgeCount J)
            (m' - c4ColorEdgeCount J .blue) else 0) *
        hammingBallVolume (completeEdgeCount n) r := by
  simpa only [card_c4TemplateRealizationSlice] using card_c4TemplateNearSlice_le_slice_sum J m r

end InducedStars
