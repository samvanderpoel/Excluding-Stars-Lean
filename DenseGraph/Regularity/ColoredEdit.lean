import DenseGraph.Regularity.ColoredRealization
import DenseGraph.FiniteModels.GraphEdit

/-!
# Unordered edits and realization errors of partial colored templates

Missing pairs have the status `none`; adding or removing an actual edge
costs one edit. Vertex colors have zero edit cost. Realization errors count
only a missing forced blue edge or a present forbidden green edge.
-/

noncomputable section
open Finset InducedStars InducedStars.Regularity
open scoped Classical
namespace DenseGraph

variable {V : Type*} [Fintype V]

def coloredPairStatus (J : RegularityColoredGraph V) (e : Sym2 V) : Option EdgeColor :=
  if h : e ∈ J.graph.edgeSet then some (J.edgeColor ⟨e, h⟩) else none

@[simp] theorem coloredPairStatus_mk (J : RegularityColoredGraph V) (x y : V) :
    coloredPairStatus J s(x,y) =
      if h : J.graph.Adj x y then some (J.getEdgeColor x y h) else none := rfl

def coloredEditFinset (J K : RegularityColoredGraph V) : Finset (Sym2 V) :=
  (finiteGraphEdges (⊤ : SimpleGraph V)).filter fun e ↦
    coloredPairStatus J e ≠ coloredPairStatus K e

def coloredEditDistance (J K : RegularityColoredGraph V) : ℕ :=
  (coloredEditFinset J K).card

@[simp] theorem mem_coloredEditFinset (J K : RegularityColoredGraph V) (e : Sym2 V) :
    e ∈ coloredEditFinset J K ↔ e ∈ (⊤ : SimpleGraph V).edgeSet ∧
      coloredPairStatus J e ≠ coloredPairStatus K e := by
  simp [coloredEditFinset, finiteGraphEdges]

theorem coloredEditDistance_triangle (J K L : RegularityColoredGraph V) :
    coloredEditDistance J L ≤ coloredEditDistance J K + coloredEditDistance K L := by
  apply (card_le_card (show coloredEditFinset J L ⊆
      coloredEditFinset J K ∪ coloredEditFinset K L from ?_)).trans
    (card_union_le _ _)
  intro e he
  simp only [mem_coloredEditFinset, mem_union] at he ⊢
  by_cases h : coloredPairStatus J e = coloredPairStatus K e
  · exact Or.inr ⟨he.1, fun hh ↦ he.2 (h.trans hh)⟩
  · exact Or.inl ⟨he.1, h⟩

def coloredInconsistencyFinset (G : SimpleGraph V) (J : RegularityColoredGraph V) :
    Finset (Sym2 V) :=
  (finiteGraphEdges (⊤ : SimpleGraph V)).filter fun e ↦
    (coloredPairStatus J e = some .blue ∧ e ∉ G.edgeSet) ∨
      (coloredPairStatus J e = some .green ∧ e ∈ G.edgeSet)

def coloredInconsistency (G : SimpleGraph V) (J : RegularityColoredGraph V) : ℕ :=
  (coloredInconsistencyFinset G J).card

@[simp] theorem mem_coloredInconsistencyFinset (G : SimpleGraph V)
    (J : RegularityColoredGraph V) (e : Sym2 V) :
    e ∈ coloredInconsistencyFinset G J ↔ e ∈ (⊤ : SimpleGraph V).edgeSet ∧
      ((coloredPairStatus J e = some .blue ∧ e ∉ G.edgeSet) ∨
        (coloredPairStatus J e = some .green ∧ e ∈ G.edgeSet)) := by
  simp [coloredInconsistencyFinset, finiteGraphEdges]

/-- Changing template edges costs at most one additional realization error
per changed unordered pair. -/
theorem coloredInconsistency_le_add_edit (G : SimpleGraph V)
    (J K : RegularityColoredGraph V) :
    coloredInconsistency G K ≤ coloredInconsistency G J + coloredEditDistance J K := by
  apply (card_le_card (show coloredInconsistencyFinset G K ⊆
      coloredInconsistencyFinset G J ∪ coloredEditFinset J K from ?_)).trans
    (card_union_le _ _)
  intro e he
  simp only [mem_coloredInconsistencyFinset, mem_coloredEditFinset, mem_union] at he ⊢
  by_cases h : coloredPairStatus J e = coloredPairStatus K e
  · exact Or.inl ⟨he.1, h ▸ he.2⟩
  · exact Or.inr ⟨he.1, h⟩

/-- Changing the uncolored graph costs at most one consistency error per
unordered edge toggle. -/
theorem coloredInconsistency_le_graphEdit_add (G H : SimpleGraph V)
    (J : RegularityColoredGraph V) :
    coloredInconsistency G J ≤ simpleGraphEditDistance G H + coloredInconsistency H J := by
  apply (card_le_card (show coloredInconsistencyFinset G J ⊆
      simpleGraphEditFinset G H ∪ coloredInconsistencyFinset H J from ?_)).trans
    (card_union_le _ _)
  intro e he
  simp only [mem_coloredInconsistencyFinset, mem_simpleGraphEditFinset, mem_union] at he ⊢
  tauto

theorem coloredInconsistency_eq_zero_of_realization (G : SimpleGraph V)
    (J : RegularityColoredGraph V) (h : IsColoredRealization J G) :
    coloredInconsistency G J = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    have he := (mem_coloredInconsistencyFinset G J s(x,y)).mp he
    by_cases hxy : J.graph.Adj x y
    · simp only [coloredPairStatus_mk, dif_pos hxy, Option.some.injEq,
        SimpleGraph.mem_edgeSet] at he
      rcases he.2 with hb | hg
      · exact hb.2 ((h x y hxy).1 hb.1)
      · exact (h x y hxy).2 hg.1 hg.2
    · simp [coloredPairStatus_mk, hxy] at he

/-- Every realization is at least as far away as the number of forced or
forbidden pairs violated by the original graph. No completeness is needed. -/
theorem coloredInconsistency_le_graphEdit_of_realization (G H : SimpleGraph V)
    (J : RegularityColoredGraph V) (h : IsColoredRealization J H) :
    coloredInconsistency G J ≤ simpleGraphEditDistance G H := by
  simpa only [coloredInconsistency_eq_zero_of_realization H J h, add_zero] using
    coloredInconsistency_le_graphEdit_add G H J

end DenseGraph
