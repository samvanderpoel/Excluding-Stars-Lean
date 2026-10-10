import InducedStars.Structure.Subcritical.RetainedCounts
import InducedStars.Structure.Subcritical.RetainedShift
import InducedStars.Structure.Subcritical.ProfileDefects

/-!
# Retained active models and signed defects

Paper: Definition `def:active-random-models-K1k`. The fixed model is the
existing exact-cardinality block model, not a second sampling construction.
The remainder has the nonretained subtype as its vertex type.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's active fixed-count model. -/
abbrev subcriticalActiveFixedBlockModel {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (mvec : RetainedEdgeCountVector D eta R₀) :=
  retainedEdgeChoiceModel mvec

theorem subcriticalActiveFixedBlockModel_card {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (mvec : RetainedEdgeCountVector D eta R₀) :
    Fintype.card (subcriticalActiveFixedBlockModel mvec).Sample =
      retainedEdgeCountMultiplicity mvec := retainedEdgeChoices_card mvec

@[simp] theorem subcriticalActiveFixedBlockModel_card_of_isEmpty
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    [IsEmpty (RetainedActivePair D eta R₀)]
    (mvec : RetainedEdgeCountVector D eta R₀) :
    Fintype.card (subcriticalActiveFixedBlockModel mvec).Sample = 1 := by
  rw [subcriticalActiveFixedBlockModel_card, retainedEdgeCountMultiplicity_of_isEmpty]

/-- A graph genuinely on the nonretained side. -/
abbrev SubcriticalRemainderGraph (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :=
  SimpleGraph {v : V // v ∈ D.nonretainedVertices eta R₀}

def subcriticalRemainderGraphSpanningCoe {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀) : SimpleGraph V :=
  H.spanningCoe

theorem subcriticalRemainderGraphSpanningCoe_support {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    {x y : V} (h : (subcriticalRemainderGraphSpanningCoe H).Adj x y) :
    x ∈ D.nonretainedVertices eta R₀ ∧ y ∈ D.nonretainedVertices eta R₀ := by
  rw [subcriticalRemainderGraphSpanningCoe, SimpleGraph.spanningCoe, SimpleGraph.map_adj] at h
  obtain ⟨a, b, _, rfl, rfl⟩ := h
  exact ⟨a.2, b.2⟩

theorem subcriticalRemainderGraphSpanningCoe_card {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀) :
    (finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H)).card =
      (finiteGraphEdges H).card := by
  have hL : finiteGraphEdges H.spanningCoe = H.spanningCoe.edgeFinset := by
    ext z
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hR : finiteGraphEdges H = H.edgeFinset := by
    ext z
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  change (finiteGraphEdges H.spanningCoe).card = _
  rw [hL, hR]
  exact SimpleGraph.card_edgeFinset_map
    (Function.Embedding.subtype (fun v : V ↦ v ∈ (D.nonretainedVertices eta R₀ : Set V))) H

def subcriticalRemainderGraph (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : SubcriticalRemainderGraph D eta R₀ :=
  G.induce (D.nonretainedVertices eta R₀ : Set V)

@[simp] theorem subcriticalRemainderGraph_adj (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (x y : V) :
    (subcriticalRemainderGraphSpanningCoe (subcriticalRemainderGraph G D eta R₀)).Adj x y ↔
      G.Adj x y ∧ x ∈ D.nonretainedVertices eta R₀ ∧
        y ∈ D.nonretainedVertices eta R₀ := by
  simp only [subcriticalRemainderGraphSpanningCoe, subcriticalRemainderGraph,
    SimpleGraph.spanningCoe, SimpleGraph.map_adj, SimpleGraph.induce_adj]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩; exact ⟨hab, a.2, b.2⟩
  · rintro ⟨hab, ha, hb⟩; exact ⟨⟨x, ha⟩, ⟨y, hb⟩, hab, rfl, rfl⟩

/-- Valid defects have a retained endpoint and never lie in an active block.
Within a retained part they delete a clique edge; otherwise they add an edge. -/
def IsSubcriticalRetainedDefectPattern (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) : Prop :=
  ∀ ⦃x y⦄, T.Adj x y →
    (x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) ∧
      ¬ D.ActivePair x y

theorem subcriticalRetainedIncidentDefectGraph_valid (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    IsSubcriticalRetainedDefectPattern D eta R₀
      (subcriticalRetainedIncidentDefectGraph G D eta R₀) := by
  intro x y h
  refine ⟨h.2, ?_⟩
  obtain ⟨⟨_, hdef⟩, _⟩ := (subcriticalDefectGraph_adj_iff G D).mp h.1
  exact hdef.elim (fun h ↦ D.not_activePair_of_samePart h.1) (fun h ↦ h.2.1)

theorem IsSubcriticalRetainedDefectPattern.disjoint_active
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} {T : SimpleGraph V}
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T) :
    Disjoint (finiteGraphEdges T) (retainedActiveEdgeUniverse D eta R₀) := by
  apply Finset.disjoint_left.mpr
  intro z hz ha
  induction z using Sym2.inductionOn with
  | _ x y =>
    exact (hT ((mk_mem_finiteGraphEdges T x y).mp hz)).2
      ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ x y).mp ha).1

theorem IsSubcriticalRetainedDefectPattern.disjoint_nonretained
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ} {T : SimpleGraph V}
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T) :
    Disjoint (finiteGraphEdges T) (nonretainedPotentialEdges D eta R₀) := by
  apply Finset.disjoint_left.mpr
  intro z hz ha
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hret := (hT ((mk_mem_finiteGraphEdges T x y).mp hz)).1
    obtain ⟨hx, hy, _⟩ := (mk_mem_nonretainedPotentialEdges_iff D eta R₀ x y).mp ha
    exact hret.elim ((D.mem_nonretainedVertices eta R₀ x).mp hx)
      ((D.mem_nonretainedVertices eta R₀ y).mp hy)

/-- Integer signed size: each retained clique defect has weight minus one,
all remaining edges weight plus one. -/
def subcriticalSignedDefectSize (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (T : SimpleGraph V) : ℤ :=
  (finiteGraphEdges T).card -
    2 * ((finiteGraphEdges T ∩ retainedCliquePotentialEdges D eta R₀).card : ℤ)

theorem subcriticalSignedDefectSize_eq_positive_sub_missing
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) :
    subcriticalSignedDefectSize D eta R₀ T =
      ((finiteGraphEdges T \ retainedCliquePotentialEdges D eta R₀).card : ℤ) -
        (finiteGraphEdges T ∩ retainedCliquePotentialEdges D eta R₀).card := by
  have h := Finset.card_sdiff_add_card_inter (finiteGraphEdges T)
    (retainedCliquePotentialEdges D eta R₀)
  dsimp [subcriticalSignedDefectSize]
  omega

theorem abs_subcriticalSignedDefectSize_le (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) :
    |subcriticalSignedDefectSize D eta R₀ T| ≤ (finiteGraphEdges T).card := by
  have h := Finset.card_le_card
    (Finset.inter_subset_left : finiteGraphEdges T ∩ retainedCliquePotentialEdges D eta R₀ ⊆ _)
  rw [abs_le]
  dsimp [subcriticalSignedDefectSize]
  omega

/-- Exact retained-part expansion; the intersections are precisely the
unordered edges of the induced subgraphs `T[D.part a]`. -/
theorem subcriticalSignedDefectSize_eq_sum (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) :
    subcriticalSignedDefectSize D eta R₀ T = (finiteGraphEdges T).card -
      2 * ∑ a ∈ D.retainedPartIndices eta R₀,
        ((finiteGraphEdges T ∩ retainedPartCliquePotentialEdges D a).card : ℤ) := by
  have hcard : (finiteGraphEdges T ∩ retainedCliquePotentialEdges D eta R₀).card =
      ∑ a ∈ D.retainedPartIndices eta R₀,
        (finiteGraphEdges T ∩ retainedPartCliquePotentialEdges D a).card := by
    rw [retainedCliquePotentialEdges, Finset.inter_biUnion, Finset.card_biUnion]
    intro a _ b _ hab
    exact (retainedPartCliquePotentialEdges_disjoint D hab).mono
      Finset.inter_subset_right Finset.inter_subset_right
  simp only [subcriticalSignedDefectSize, hcard, Nat.cast_sum]

theorem subcriticalRetainedIncidentDefectGraph_edges (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    finiteGraphEdges (subcriticalRetainedIncidentDefectGraph G D eta R₀) =
      retainedMissingCliqueEdges G D eta R₀ ∪ retainedPresentDefectEdges G D eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    have hsret (hs : D.SamePart x y) :
        x ∈ D.retainedVertices eta R₀ ↔ y ∈ D.retainedVertices eta R₀ := by
      obtain ⟨a, hx, hy⟩ := hs
      exact (D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a.2, hx⟩)).trans
        (D.mem_retainedVertices_iff_of_mem_componentSupport
          (D.mem_componentSupport.mpr ⟨a.2, hy⟩)).symm
    have hretsp (v : V) (hv : v ∈ D.retainedVertices eta R₀) : v ∉ D.sparse := by
      intro hsp
      exact (D.mem_nonretainedVertices eta R₀ v).mp
        (D.sparse_subset_nonretainedVertices eta R₀ hsp) hv
    simp only [mk_mem_finiteGraphEdges, subcriticalRetainedIncidentDefectGraph_adj,
      subcriticalDefectGraph_adj_iff, Finset.mem_union,
      mk_mem_retainedMissingCliqueEdges, mk_mem_retainedPresentDefectEdges]
    have hne : G.Adj x y → x ≠ y := SimpleGraph.Adj.ne
    constructor
    · rintro ⟨⟨⟨hne, hdef⟩, _⟩, hret⟩
      rcases hdef with ⟨hs, hn⟩ | ⟨hs, ha, hg⟩
      · exact Or.inl ⟨hne, hs, hret.elim id (hsret hs).mpr, hn⟩
      · exact Or.inr ⟨hg, hs, ha, hret⟩
    · rintro (⟨hne, hs, hr, hg⟩ | ⟨hg, hs, ha, hr⟩)
      · exact ⟨⟨⟨hne, Or.inl ⟨hs, hg⟩⟩, fun h ↦ hretsp x hr h.1⟩, Or.inl hr⟩
      · exact ⟨⟨⟨hne hg, Or.inr ⟨hs, ha, hg⟩⟩,
          fun h ↦ hr.elim (fun hx ↦ hretsp x hx h.1) (fun hy ↦ hretsp y hy h.2)⟩, hr⟩

theorem subcriticalSignedDefectSize_actual (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    subcriticalSignedDefectSize D eta R₀
        (subcriticalRetainedIncidentDefectGraph G D eta R₀) =
      (retainedPresentDefectCount G D eta R₀ : ℤ) -
        retainedMissingCliqueCount G D eta R₀ := by
  have hinter : (retainedMissingCliqueEdges G D eta R₀ ∪
      retainedPresentDefectEdges G D eta R₀) ∩ retainedCliquePotentialEdges D eta R₀ =
      retainedMissingCliqueEdges G D eta R₀ := by
    ext z
    simp only [retainedMissingCliqueEdges, retainedPresentDefectEdges,
      Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [subcriticalSignedDefectSize, subcriticalRetainedIncidentDefectGraph_edges,
    hinter, Finset.card_union_of_disjoint
      (retainedPresentDefectEdges_disjoint_missing G D eta R₀).symm]
  simp only [Nat.cast_add, retainedPresentDefectCount, retainedMissingCliqueCount]
  ring

theorem subcriticalRetainedPartDefectCount_eq (D : SubcriticalDivision k V)
    (T : SimpleGraph V) (a : D.PartIndex) :
    (finiteGraphEdges T ∩ retainedPartCliquePotentialEdges D a).card =
      inducedEdgeCount T (D.part a) := by
  rw [inducedEdgeCount_eq_card_inter_sym2]
  congr 1
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [Finset.mem_inter, mk_mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Finset.mk_mem_sym2_iff, mem_retainedPartCliquePotentialEdges]
    constructor
    · rintro ⟨hT, u, hu, v, hv, _, heq⟩
      have hp := (Sym2.mk_eq_mk_iff (p := (x, y)) (q := (u, v))).mp heq
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hT, hu, hv⟩
      · exact ⟨hT, hv, hu⟩
    · rintro ⟨hT, hx, hy⟩
      exact ⟨hT, x, hx, y, hy, hT.ne, rfl⟩

/-- The literal paper formula `e(T) - 2 ∑ e(T[P_a])`. -/
theorem subcriticalSignedDefectSize_eq_induced_sum (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (T : SimpleGraph V) :
    subcriticalSignedDefectSize D eta R₀ T = (finiteGraphEdges T).card -
      2 * ∑ a ∈ D.retainedPartIndices eta R₀, (inducedEdgeCount T (D.part a) : ℤ) := by
  simpa only [subcriticalRetainedPartDefectCount_eq] using
    subcriticalSignedDefectSize_eq_sum D eta R₀ T

end InducedStars
