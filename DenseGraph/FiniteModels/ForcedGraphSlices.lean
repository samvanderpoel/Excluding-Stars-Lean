import DenseGraph.FiniteModels.GraphEdit

/-!
# Fixed-edge slices with forced and forbidden unordered pairs

All formulas retain the lower feasibility guard. The optional universe
contains every pair that is neither forced nor forbidden.
-/

noncomputable section
open Finset InducedStars
open scoped Classical
namespace DenseGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

def forcedGraphOptionalEdges (B H : SimpleGraph V) : Finset (Sym2 V) :=
  finiteGraphEdges (⊤ : SimpleGraph V) \ (finiteGraphEdges B ∪ finiteGraphEdges H)

@[simp] theorem mem_forcedGraphOptionalEdges (B H : SimpleGraph V) (x y : V) :
    s(x,y) ∈ forcedGraphOptionalEdges B H ↔ x ≠ y ∧ ¬B.Adj x y ∧ ¬H.Adj x y := by
  simp [forcedGraphOptionalEdges, not_or, and_assoc]

def forcedGraphOfChoice (B : SimpleGraph V) (C : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (↑(finiteGraphEdges B ∪ C) : Set (Sym2 V))

theorem finiteGraphEdges_forcedGraphOfChoice (B H : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ forcedGraphOptionalEdges B H) :
    finiteGraphEdges (forcedGraphOfChoice B C) = finiteGraphEdges B ∪ C := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    rw [mk_mem_finiteGraphEdges, forcedGraphOfChoice, SimpleGraph.fromEdgeSet_adj]
    change (s(x,y) ∈ finiteGraphEdges B ∪ C ∧ x ≠ y) ↔ _
    constructor
    · exact And.left
    · intro he
      refine ⟨he, ?_⟩
      rcases mem_union.mp he with he | he
      · exact ((mk_mem_finiteGraphEdges B x y).mp he).ne
      · exact ((mem_forcedGraphOptionalEdges B H x y).mp (hC he)).1

theorem forcedGraphOptionalEdges_disjoint (B H : SimpleGraph V) :
    Disjoint (finiteGraphEdges B) (forcedGraphOptionalEdges B H) := by
  apply disjoint_left.mpr
  intro e he hf
  exact (mem_sdiff.mp hf).2 (mem_union_left _ he)

theorem forcedGraphOfChoice_edgeCount (B H : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ forcedGraphOptionalEdges B H) :
    (finiteGraphEdges (forcedGraphOfChoice B C)).card = (finiteGraphEdges B).card + C.card := by
  rw [finiteGraphEdges_forcedGraphOfChoice B H hC,
    card_union_of_disjoint ((forcedGraphOptionalEdges_disjoint B H).mono_right hC)]

theorem forcedGraphOfChoice_recover (B H : SimpleGraph V)
    {C : Finset (Sym2 V)} (hC : C ⊆ forcedGraphOptionalEdges B H) :
    finiteGraphEdges (forcedGraphOfChoice B C) ∩ forcedGraphOptionalEdges B H = C := by
  rw [finiteGraphEdges_forcedGraphOfChoice B H hC]
  ext e
  simp only [mem_inter, mem_union]
  constructor
  · rintro ⟨h | h, he⟩
    · exact False.elim (disjoint_left.mp (forcedGraphOptionalEdges_disjoint B H) h he)
    · exact h
  · intro h; exact ⟨Or.inr h, hC h⟩

theorem forcedGraphOfChoice_injectiveOn (B H : SimpleGraph V) :
    Set.InjOn (forcedGraphOfChoice B) {C | C ⊆ forcedGraphOptionalEdges B H} := by
  intro C hC E hE heq
  have hh := congrArg (fun G ↦ finiteGraphEdges G ∩ forcedGraphOptionalEdges B H) heq
  simpa only [forcedGraphOfChoice_recover B H hC, forcedGraphOfChoice_recover B H hE] using hh

theorem forcedGraphOfChoice_constraints (B H : SimpleGraph V) (hBH : Disjoint B H)
    {C : Finset (Sym2 V)} (hC : C ⊆ forcedGraphOptionalEdges B H) :
    B ≤ forcedGraphOfChoice B C ∧ Disjoint H (forcedGraphOfChoice B C) := by
  constructor
  · intro x y hxy
    rw [← mk_mem_finiteGraphEdges, finiteGraphEdges_forcedGraphOfChoice B H hC]
    exact mem_union_left _ ((mk_mem_finiteGraphEdges B x y).mpr hxy)
  · apply SimpleGraph.disjoint_left.mpr
    intro x y hH hG
    have he := (mk_mem_finiteGraphEdges _ x y).mpr hG
    rw [finiteGraphEdges_forcedGraphOfChoice B H hC] at he
    rcases mem_union.mp he with he | he
    · exact SimpleGraph.disjoint_left.mp hBH x y ((mk_mem_finiteGraphEdges B x y).mp he) hH
    · exact ((mem_forcedGraphOptionalEdges B H x y).mp (hC he)).2.2 hH

theorem forcedGraph_edges_decompose (B H G : SimpleGraph V)
    (hB : B ≤ G) (hH : Disjoint H G) :
    finiteGraphEdges G = finiteGraphEdges B ∪
      (finiteGraphEdges G ∩ forcedGraphOptionalEdges B H) := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, mem_union, mem_inter, mem_forcedGraphOptionalEdges]
    constructor
    · intro hG
      by_cases hb : B.Adj x y
      · exact Or.inl hb
      · exact Or.inr ⟨hG, hG.ne, hb, fun hh ↦ SimpleGraph.disjoint_left.mp hH x y hh hG⟩
    · rintro (h | h)
      · exact hB h
      · exact h.1

theorem forcedGraphOfChoice_of_constraints (B H G : SimpleGraph V)
    (hB : B ≤ G) (hH : Disjoint H G) :
    forcedGraphOfChoice B (finiteGraphEdges G ∩ forcedGraphOptionalEdges B H) = G := by
  ext x y
  rw [← mk_mem_finiteGraphEdges, finiteGraphEdges_forcedGraphOfChoice B H inter_subset_right,
    ← forcedGraph_edges_decompose B H G hB hH, mk_mem_finiteGraphEdges]

def forcedGraphSlice (B H : SimpleGraph V) (m : ℕ) : Finset (SimpleGraph V) :=
  univ.filter fun G ↦ B ≤ G ∧ Disjoint H G ∧ (finiteGraphEdges G).card = m

@[simp] theorem mem_forcedGraphSlice (B H G : SimpleGraph V) (m : ℕ) :
    G ∈ forcedGraphSlice B H m ↔ B ≤ G ∧ Disjoint H G ∧ (finiteGraphEdges G).card = m := by
  simp [forcedGraphSlice]

theorem forcedGraphSlice_eq_image (B H : SimpleGraph V) (hBH : Disjoint B H) (m : ℕ) :
    forcedGraphSlice B H m = if (finiteGraphEdges B).card ≤ m then
      ((forcedGraphOptionalEdges B H).powersetCard (m-(finiteGraphEdges B).card)).image
        (forcedGraphOfChoice B) else ∅ := by
  by_cases hm : (finiteGraphEdges B).card ≤ m
  · rw [if_pos hm]
    ext G
    constructor
    · intro hG
      obtain ⟨hB, hH, he⟩ := (mem_forcedGraphSlice B H G m).mp hG
      have hcard := forcedGraphOfChoice_edgeCount B H
        (C := finiteGraphEdges G ∩ forcedGraphOptionalEdges B H) inter_subset_right
      rw [forcedGraphOfChoice_of_constraints B H G hB hH, he] at hcard
      exact mem_image.mpr ⟨_, mem_powersetCard.mpr ⟨inter_subset_right, by omega⟩,
        forcedGraphOfChoice_of_constraints B H G hB hH⟩
    · rintro hG
      obtain ⟨C, hC, rfl⟩ := mem_image.mp hG
      obtain ⟨hC, hc⟩ := mem_powersetCard.mp hC
      obtain ⟨hB, hH⟩ := forcedGraphOfChoice_constraints B H hBH hC
      refine (mem_forcedGraphSlice _ _ _ _).mpr ⟨hB, hH, ?_⟩
      rw [forcedGraphOfChoice_edgeCount B H hC, hc]
      omega
  · rw [if_neg hm]
    apply eq_empty_iff_forall_notMem.mpr
    intro G hG
    obtain ⟨hB, _, he⟩ := (mem_forcedGraphSlice B H G m).mp hG
    have hs : finiteGraphEdges B ⊆ finiteGraphEdges G := by
      intro e he
      induction e using Sym2.inductionOn with
      | _ x y => exact (mk_mem_finiteGraphEdges G x y).mpr (hB
          ((mk_mem_finiteGraphEdges B x y).mp he))
    have hc := card_le_card hs
    omega

/-- Exact guarded binomial count; no divisibility or density condition. -/
theorem card_forcedGraphSlice (B H : SimpleGraph V) (hBH : Disjoint B H) (m : ℕ) :
    (forcedGraphSlice B H m).card = if (finiteGraphEdges B).card ≤ m then
      Nat.choose (forcedGraphOptionalEdges B H).card (m-(finiteGraphEdges B).card) else 0 := by
  rw [forcedGraphSlice_eq_image B H hBH m]
  split_ifs with hm
  · rw [card_image_iff.mpr, card_powersetCard]
    intro C hC E hE heq
    exact forcedGraphOfChoice_injectiveOn B H (mem_powersetCard.mp hC).1
      (mem_powersetCard.mp hE).1 heq
  · rfl

end DenseGraph
