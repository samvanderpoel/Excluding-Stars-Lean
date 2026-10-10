import InducedStars.C4.ColoredDistance

/-!
# Finite colored counts for C4 stability

Paper: Lemma `lemma:c4-stability`. All label graphs below count actual
template edges. Missing pairs are counted separately in the complement,
using the partial-template configuration facts from `C4.ColoredBasic`.
-/

noncomputable section
open Finset Set InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical

namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

def c4GreenVertices (J : RegularityColoredGraph V) : Finset V :=
  univ.filter fun v ↦ J.vertexColor v = .green

def c4BlueVertices (J : RegularityColoredGraph V) : Finset V :=
  univ.filter fun v ↦ J.vertexColor v = .blue

@[simp] theorem mem_c4GreenVertices (J : RegularityColoredGraph V) (v : V) :
    v ∈ c4GreenVertices J ↔ J.vertexColor v = .green := by simp [c4GreenVertices]

@[simp] theorem mem_c4BlueVertices (J : RegularityColoredGraph V) (v : V) :
    v ∈ c4BlueVertices J ↔ J.vertexColor v = .blue := by simp [c4BlueVertices]

theorem c4GreenVertices_disjoint_blue (J : RegularityColoredGraph V) :
    Disjoint (c4GreenVertices J) (c4BlueVertices J) := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have h := (mem_c4GreenVertices J v).mp hv
  have h' := (mem_c4BlueVertices J v).mp hw
  simp [h] at h'

theorem c4GreenVertices_union_blue (J : RegularityColoredGraph V) :
    c4GreenVertices J ∪ c4BlueVertices J = Finset.univ := by
  ext v
  cases h : J.vertexColor v <;> simp [h]

theorem c4GreenVertices_card_add_blue (J : RegularityColoredGraph V) :
    (c4GreenVertices J).card + (c4BlueVertices J).card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint (c4GreenVertices_disjoint_blue J),
    c4GreenVertices_union_blue, Finset.card_univ]

def c4VertexColorDivision (J : RegularityColoredGraph V) : C4Division V := c4GreenVertices J

@[simp] theorem c4VertexColorDivision_independent (J : RegularityColoredGraph V) :
    (c4VertexColorDivision J).independentPart = c4GreenVertices J := rfl

@[simp] theorem c4VertexColorDivision_clique (J : RegularityColoredGraph V) :
    (c4VertexColorDivision J).cliquePart = c4BlueVertices J := by
  ext v
  simp only [C4Division.mem_cliquePart, c4VertexColorDivision_independent,
    mem_c4GreenVertices, mem_c4BlueVertices]
  cases J.vertexColor v <;> simp

/-- All unordered distinct pairs within a finite set, whether or not they
are actual template edges. -/
def c4PairsWithin (S : Finset V) : Finset (Sym2 V) := S.offDiag.image Sym2.mk.uncurry

@[simp] theorem mk_mem_c4PairsWithin (S : Finset V) (x y : V) :
    s(x, y) ∈ c4PairsWithin S ↔ x ∈ S ∧ y ∈ S ∧ x ≠ y := by
  constructor
  · rintro h
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp h
    have hab' := Finset.mem_offDiag.mp hab
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab'
    · exact ⟨hab'.2.1, hab'.1, hab'.2.2.symm⟩
  · rintro ⟨hx, hy, hne⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_offDiag.mpr ⟨hx, hy, hne⟩, rfl⟩

@[simp] theorem card_c4PairsWithin (S : Finset V) :
    (c4PairsWithin S).card = Nat.choose S.card 2 := Sym2.card_image_offDiag S

def c4MissingEdgeCount (J : RegularityColoredGraph V) : ℕ :=
  (finiteGraphEdges J.graphᶜ).card

theorem c4Actual_add_missing (J : RegularityColoredGraph V) :
    (finiteGraphEdges J.graph).card + c4MissingEdgeCount J =
      Nat.choose (Fintype.card V) 2 := by
  have hdis : Disjoint (finiteGraphEdges J.graph) (finiteGraphEdges J.graphᶜ) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact ((mk_mem_finiteGraphEdges _ _ _).mp hf).2
        ((mk_mem_finiteGraphEdges _ _ _).mp he)
  have hunion : finiteGraphEdges J.graph ∪ finiteGraphEdges J.graphᶜ = c4PairsWithin univ := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Finset.mem_union, mk_mem_finiteGraphEdges, SimpleGraph.compl_adj,
        mk_mem_c4PairsWithin, Finset.mem_univ, true_and]
      exact ⟨by rintro (h | h); exact h.ne; exact h.1,
        fun h ↦ by by_cases ha : J.graph.Adj x y; exact Or.inl ha; exact Or.inr ⟨h, ha⟩⟩
  rw [c4MissingEdgeCount, ← Finset.card_union_of_disjoint hdis, hunion,
    card_c4PairsWithin, Finset.card_univ]

theorem c4MissingEdgeCount_eq_sub (J : RegularityColoredGraph V) :
    c4MissingEdgeCount J = Nat.choose (Fintype.card V) 2 - (finiteGraphEdges J.graph).card := by
  have h := c4Actual_add_missing J
  omega

theorem c4ColorEdges_disjoint (J : RegularityColoredGraph V) {c d : EdgeColor} (hcd : c ≠ d) :
    Disjoint (finiteGraphEdges (J.edgeColor.labelGraph c))
      (finiteGraphEdges (J.edgeColor.labelGraph d)) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  induction e using Sym2.inductionOn with
  | _ x y =>
    obtain ⟨h, hc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp
      ((mk_mem_finiteGraphEdges _ _ _).mp he)
    obtain ⟨h', hd⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp
      ((mk_mem_finiteGraphEdges _ _ _).mp hf)
    exact hcd (hc.symm.trans hd)

theorem c4ColorEdgeCounts_add_missing (J : RegularityColoredGraph V) :
    c4ColorEdgeCount J .red + c4ColorEdgeCount J .green + c4ColorEdgeCount J .blue +
      c4MissingEdgeCount J = Nat.choose (Fintype.card V) 2 := by
  have hunion : (finiteGraphEdges (J.edgeColor.labelGraph .red) ∪
      finiteGraphEdges (J.edgeColor.labelGraph .green)) ∪
      finiteGraphEdges (J.edgeColor.labelGraph .blue) = finiteGraphEdges J.graph := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Finset.mem_union, mk_mem_finiteGraphEdges, SimpleGraph.EdgeLabeling.labelGraph_adj]
      constructor
      · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h
      · intro h
        cases hc : J.getEdgeColor x y h with
        | red => exact Or.inl (Or.inl ⟨h, hc⟩)
        | green => exact Or.inl (Or.inr ⟨h, hc⟩)
        | blue => exact Or.inr ⟨h, hc⟩
  have hdis := Finset.disjoint_union_left.mpr
    ⟨c4ColorEdges_disjoint J (by decide : EdgeColor.red ≠ .blue),
      c4ColorEdges_disjoint J (by decide : EdgeColor.green ≠ .blue)⟩
  have hc := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint
    (c4ColorEdges_disjoint J (by decide : EdgeColor.red ≠ .green))] at hc
  rw [c4ColorEdgeCount_eq_card, c4ColorEdgeCount_eq_card, c4ColorEdgeCount_eq_card, hc]
  exact c4Actual_add_missing J

theorem c4Free_red_endpoints_cross (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) {x y : V}
    (hred : (J.edgeColor.labelGraph .red).Adj x y) :
    (x ∈ c4GreenVertices J ∧ y ∈ c4BlueVertices J) ∨
      (y ∈ c4GreenVertices J ∧ x ∈ c4BlueVertices J) := by
  obtain ⟨hxy, hc⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj x y).mp hred
  cases hx : J.vertexColor x <;> cases hy : J.vertexColor y
  · have hg := c4Free_green_green_edge J hfree hx hy hxy
    have he : EdgeColor.red = .green := hc.symm.trans hg
    cases he
  · exact Or.inl ⟨by simp [hx], by simp [hy]⟩
  · exact Or.inr ⟨by simp [hy], by simp [hx]⟩
  · exact False.elim ((c4Free_blue_blue_edge_not_red J hfree hx hy hxy) hc)

theorem c4Free_red_edges_subset_cross (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    finiteGraphEdges (J.edgeColor.labelGraph .red) ⊆
      c4CrossPotentialEdges (c4VertexColorDivision J) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
    simpa only [mk_mem_c4CrossPotentialEdges, c4VertexColorDivision_independent,
      c4VertexColorDivision_clique] using c4Free_red_endpoints_cross J hfree
        ((mk_mem_finiteGraphEdges _ _ _).mp he)

theorem c4Free_redCount_le_crossCapacity (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    c4ColorEdgeCount J .red ≤ (c4GreenVertices J).card * (c4BlueVertices J).card := by
  rw [c4ColorEdgeCount_eq_card]
  simpa using Finset.card_le_card (c4Free_red_edges_subset_cross J hfree)

def c4GreenInsideBlueEdges (J : RegularityColoredGraph V) : Finset (Sym2 V) :=
  finiteGraphEdges (J.edgeColor.labelGraph .green) ∩ c4PairsWithin (c4BlueVertices J)

def c4NonredCrossEdges (J : RegularityColoredGraph V) : Finset (Sym2 V) :=
  (finiteGraphEdges (J.edgeColor.labelGraph .green) ∪
    finiteGraphEdges (J.edgeColor.labelGraph .blue)) ∩
      c4CrossPotentialEdges (c4VertexColorDivision J)

theorem c4Free_greenCount_add_missing_ge (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    Nat.choose (c4GreenVertices J).card 2 + (c4GreenInsideBlueEdges J).card ≤
      c4ColorEdgeCount J .green + c4MissingEdgeCount J := by
  rw [c4ColorEdgeCount_eq_card]
  have hdis : Disjoint (c4PairsWithin (c4GreenVertices J)) (c4GreenInsideBlueEdges J) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hx := (mk_mem_c4PairsWithin _ _ _).mp he
      have hy := (mk_mem_c4PairsWithin _ _ _).mp (Finset.mem_inter.mp hf).2
      exact Finset.disjoint_left.mp (c4GreenVertices_disjoint_blue J) hx.1 hy.1
  have hsub : c4PairsWithin (c4GreenVertices J) ∪ c4GreenInsideBlueEdges J ⊆
      finiteGraphEdges (J.edgeColor.labelGraph .green) ∪ finiteGraphEdges J.graphᶜ := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · induction e using Sym2.inductionOn with
      | _ x y =>
        obtain ⟨hx, hy, hne⟩ := (mk_mem_c4PairsWithin _ _ _).mp he
        by_cases hxy : J.graph.Adj x y
        · apply Finset.mem_union_left
          exact (mk_mem_finiteGraphEdges _ _ _).mpr
            ((SimpleGraph.EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy,
              c4Free_green_green_edge J hfree ((mem_c4GreenVertices J x).mp hx)
                ((mem_c4GreenVertices J y).mp hy) hxy⟩)
        · exact Finset.mem_union_right _ ((mk_mem_finiteGraphEdges _ _ _).mpr ⟨hne, hxy⟩)
    · exact Finset.mem_union_left _ (Finset.mem_inter.mp he).1
  calc
    Nat.choose (c4GreenVertices J).card 2 + (c4GreenInsideBlueEdges J).card =
        (c4PairsWithin (c4GreenVertices J) ∪ c4GreenInsideBlueEdges J).card := by
      rw [Finset.card_union_of_disjoint hdis, card_c4PairsWithin]
    _ ≤ _ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem c4Free_redCount_add_nonredCross_le (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    c4ColorEdgeCount J .red + (c4NonredCrossEdges J).card ≤
      (c4GreenVertices J).card * (c4BlueVertices J).card := by
  have hdis : Disjoint (finiteGraphEdges (J.edgeColor.labelGraph .red))
      (c4NonredCrossEdges J) :=
    (Finset.disjoint_union_right.mpr
      ⟨c4ColorEdges_disjoint J (by decide), c4ColorEdges_disjoint J (by decide)⟩).mono_right
        (Finset.inter_subset_left)
  have hsub : finiteGraphEdges (J.edgeColor.labelGraph .red) ∪ c4NonredCrossEdges J ⊆
      c4CrossPotentialEdges (c4VertexColorDivision J) :=
    Finset.union_subset (c4Free_red_edges_subset_cross J hfree) Finset.inter_subset_right
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis, card_c4CrossPotentialEdges,
    c4VertexColorDivision_independent, c4VertexColorDivision_clique] at hc
  simpa only [c4ColorEdgeCount_eq_card] using hc

def c4RedNeighbors (J : RegularityColoredGraph V) (v : V) : Finset V :=
  univ.filter fun w ↦ (J.edgeColor.labelGraph .red).Adj v w

@[simp] theorem mem_c4RedNeighbors (J : RegularityColoredGraph V) (v w : V) :
    w ∈ c4RedNeighbors J v ↔ (J.edgeColor.labelGraph .red).Adj v w := by
  simp [c4RedNeighbors]

def c4RedDegree (J : RegularityColoredGraph V) (v : V) : ℕ := (c4RedNeighbors J v).card

theorem c4Free_redNeighbors_subset_blue (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) {v : V} (hv : v ∈ c4GreenVertices J) :
    c4RedNeighbors J v ⊆ c4BlueVertices J := by
  intro w hw
  rcases c4Free_red_endpoints_cross J hfree ((mem_c4RedNeighbors J v w).mp hw) with h | h
  · exact h.2
  · exact False.elim (Finset.disjoint_left.mp (c4GreenVertices_disjoint_blue J) hv h.2)

/-- Every red edge has exactly one green endpoint, so the sum is not divided
by two. The finite union proof counts actual unordered edges. -/
theorem c4Free_redCount_eq_sum_green_degrees (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    c4ColorEdgeCount J .red = ∑ v ∈ c4GreenVertices J, c4RedDegree J v := by
  let row (v : V) : Finset (Sym2 V) := (c4RedNeighbors J v).image fun w ↦ s(v, w)
  have hrows : finiteGraphEdges (J.edgeColor.labelGraph .red) =
      (c4GreenVertices J).biUnion row := by
    ext e
    constructor
    · intro he
      induction e using Sym2.inductionOn with
      | _ x y =>
        have hxy := (mk_mem_finiteGraphEdges _ _ _).mp he
        rcases c4Free_red_endpoints_cross J hfree hxy with h | h
        · exact Finset.mem_biUnion.mpr ⟨x, h.1,
            Finset.mem_image.mpr ⟨y, (mem_c4RedNeighbors J x y).mpr hxy, rfl⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨y, h.1,
            Finset.mem_image.mpr ⟨x, (mem_c4RedNeighbors J y x).mpr hxy.symm,
              Sym2.eq_swap⟩⟩
    · intro he
      obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      exact (mk_mem_finiteGraphEdges _ _ _).mpr ((mem_c4RedNeighbors J v w).mp hw)
  have hdis : (c4GreenVertices J : Set V).PairwiseDisjoint row := by
    intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨b, hb, heq⟩ := Finset.mem_image.mp hf
    rcases Sym2.eq_iff.mp heq with ⟨h, _⟩ | ⟨h, _⟩
    · exact hvw h.symm
    · have haB := c4Free_redNeighbors_subset_blue J hfree hv ha
      exact Finset.disjoint_left.mp (c4GreenVertices_disjoint_blue J) hw (h ▸ haB)
  rw [c4ColorEdgeCount_eq_card, hrows, Finset.card_biUnion hdis]
  apply Finset.sum_congr rfl
  intro v hv
  dsimp [row, c4RedDegree]
  rw [Finset.card_image_iff.mpr]
  intro a ha b hb heq
  rcases Sym2.eq_iff.mp heq with ⟨_, hab⟩ | ⟨hvb, hav⟩
  · exact hab
  · exact hav.trans hvb

/-- All distinct pairs of red neighbors of a green vertex are either blue
actual edges or genuinely missing pairs. -/
theorem c4Free_redDegree_choose_le_blue_add_missing (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) {v : V} (hv : v ∈ c4GreenVertices J) :
    Nat.choose (c4RedDegree J v) 2 ≤ c4ColorEdgeCount J .blue + c4MissingEdgeCount J := by
  have hsub : c4PairsWithin (c4RedNeighbors J v) ⊆
      finiteGraphEdges (J.edgeColor.labelGraph .blue) ∪ finiteGraphEdges J.graphᶜ := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hx, hy, hne⟩ := (mk_mem_c4PairsWithin _ _ _).mp he
      obtain ⟨hvx, hcx⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj v x).mp
        ((mem_c4RedNeighbors J v x).mp hx)
      obtain ⟨hvy, hcy⟩ := (SimpleGraph.EdgeLabeling.labelGraph_adj v y).mp
        ((mem_c4RedNeighbors J v y).mp hy)
      by_cases hxy : J.graph.Adj x y
      · apply Finset.mem_union_left
        exact (mk_mem_finiteGraphEdges _ _ _).mpr
          ((SimpleGraph.EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy,
            c4Free_green_red_neighbors_edge_blue J hfree ((mem_c4GreenVertices J v).mp hv)
              hvx hvy hxy hcx hcy⟩)
      · exact Finset.mem_union_right _ ((mk_mem_finiteGraphEdges _ _ _).mpr ⟨hne, hxy⟩)
  rw [c4ColorEdgeCount_eq_card]
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa only [card_c4PairsWithin, c4RedDegree, c4MissingEdgeCount] using hc

theorem c4Free_redDegree_choose_lt_bStar_add_missing (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) {v : V} (hv : v ∈ c4GreenVertices J)
    {bStar : ℕ} (hbStar : c4ColorEdgeCount J .blue < Nat.choose (bStar + 1) 2) :
    Nat.choose (c4RedDegree J v) 2 < Nat.choose (bStar + 1) 2 + c4MissingEdgeCount J :=
  (c4Free_redDegree_choose_le_blue_add_missing J hfree hv).trans_lt (Nat.add_lt_add_right hbStar _)

/-- Completing missing pairs, recoloring green edges within the blue side,
and recoloring nonred cut edges produces the split coloring on the original
vertex-color partition. Vertex recoloring is unnecessary. -/
theorem c4Free_coloredEdit_le_badCounts (J : RegularityColoredGraph V)
    (hfree : ¬ColoredHomExists inducedC4 J) :
    DenseGraph.coloredEditDistance J (c4SplitColoring (c4VertexColorDivision J)) ≤
      c4MissingEdgeCount J + (c4GreenInsideBlueEdges J).card + (c4NonredCrossEdges J).card := by
  have hsub : DenseGraph.coloredEditFinset J (c4SplitColoring (c4VertexColorDivision J)) ⊆
      (finiteGraphEdges J.graphᶜ ∪ c4GreenInsideBlueEdges J) ∪ c4NonredCrossEdges J := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      obtain ⟨hne, hchange⟩ := (DenseGraph.mem_coloredEditFinset _ _ _).mp he
      change x ≠ y at hne
      by_cases hxy : J.graph.Adj x y
      · have hneq : J.getEdgeColor x y hxy ≠
            (if x ∈ c4GreenVertices J ∧ y ∈ c4GreenVertices J then EdgeColor.green
              else if x ∉ c4GreenVertices J ∧ y ∉ c4GreenVertices J then .blue else .red) := by
          simpa [DenseGraph.coloredPairStatus_mk, c4SplitColoring_complete, hxy, hne,
            c4SplitColoring_edgeColor] using hchange
        have hmem (c : EdgeColor) (hc : J.getEdgeColor x y hxy = c) :
            s(x, y) ∈ finiteGraphEdges (J.edgeColor.labelGraph c) :=
          (mk_mem_finiteGraphEdges _ _ _).mpr
            ((SimpleGraph.EdgeLabeling.labelGraph_adj x y).mpr ⟨hxy, hc⟩)
        have hcross (h : (x ∈ c4GreenVertices J ∧ y ∈ c4BlueVertices J) ∨
            (y ∈ c4GreenVertices J ∧ x ∈ c4BlueVertices J))
            (hc : J.getEdgeColor x y hxy ≠ .red) :
            s(x, y) ∈ c4NonredCrossEdges J := by
          refine Finset.mem_inter.mpr ⟨?_, ?_⟩
          · cases hec : J.getEdgeColor x y hxy with
            | red => exact False.elim (hc hec)
            | green => exact Finset.mem_union_left _ (hmem .green hec)
            | blue => exact Finset.mem_union_right _ (hmem .blue hec)
          · simpa only [mk_mem_c4CrossPotentialEdges, c4VertexColorDivision_independent,
              c4VertexColorDivision_clique] using h
        cases hx : J.vertexColor x <;> cases hy : J.vertexColor y
        · have hg := c4Free_green_green_edge J hfree hx hy hxy
          exact False.elim (hneq (by simpa [hx, hy] using hg))
        · apply Finset.mem_union_right
          exact hcross (Or.inl ⟨by simp [hx], by simp [hy]⟩) (by simpa [hx, hy] using hneq)
        · apply Finset.mem_union_right
          exact hcross (Or.inr ⟨by simp [hy], by simp [hx]⟩) (by simpa [hx, hy] using hneq)
        · have hnred := c4Free_blue_blue_edge_not_red J hfree hx hy hxy
          have hgreen : J.getEdgeColor x y hxy = .green := by
            cases hc : J.getEdgeColor x y hxy with
            | green => rfl
            | red => exact False.elim (hnred hc)
            | blue => exact False.elim (hneq (by simpa [hx, hy] using hc))
          apply Finset.mem_union_left
          apply Finset.mem_union_right
          exact Finset.mem_inter.mpr ⟨hmem .green hgreen,
            (mk_mem_c4PairsWithin _ _ _).mpr ⟨by simp [hx], by simp [hy], hne⟩⟩
      · apply Finset.mem_union_left
        apply Finset.mem_union_left
        exact (mk_mem_finiteGraphEdges _ _ _).mpr ⟨hne, hxy⟩
  calc
    DenseGraph.coloredEditDistance J (c4SplitColoring (c4VertexColorDivision J)) ≤
        ((finiteGraphEdges J.graphᶜ ∪ c4GreenInsideBlueEdges J) ∪ c4NonredCrossEdges J).card :=
      Finset.card_le_card hsub
    _ ≤ (finiteGraphEdges J.graphᶜ ∪ c4GreenInsideBlueEdges J).card +
        (c4NonredCrossEdges J).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (Finset.card_union_le _ _) _

end InducedStars
