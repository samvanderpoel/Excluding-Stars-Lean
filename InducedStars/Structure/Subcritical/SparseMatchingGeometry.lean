import DenseGraph.Combinatorics.MatchingCounting
import InducedStars.FiniteModels.GraphFamilies
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Isolated matching extensions of induced-star-free graphs

These finite lemmas keep the added matching as an actual labeled graph.  They
are the geometric and recovery ingredients for both matching-transfer counts.
-/

noncomputable section

namespace InducedStars

open DenseGraph

variable {V W : Type*} [Fintype V] [DecidableEq V]

local instance sparseMatchingGeometryEdgeSetFintype (G : SimpleGraph V) :
    Fintype G.edgeSet := Fintype.ofFinite _

/-- The graph carried by a finite edge family. -/
def sparseMatchingGraph (E : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 V))

theorem sparseMatchingGraph_edgeFinset (E : Finset (Sym2 V))
    (hE : IsEdgeMatching ⊤ E) : (sparseMatchingGraph E).edgeFinset = E := by
  classical
  apply Finset.coe_injective
  rw [SimpleGraph.coe_edgeFinset]
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    change (s(x, y) ∈ E ∧ x ≠ y) ↔ s(x, y) ∈ E
    exact ⟨And.left, fun h ↦ ⟨h, hE.1 _ h⟩⟩

theorem sparseMatchingGraph_neighbor_unique (E : Finset (Sym2 V))
    (hE : IsEdgeMatching ⊤ E) {x y z : V}
    (hxy : (sparseMatchingGraph E).Adj x y)
    (hxz : (sparseMatchingGraph E).Adj x z) : y = z := by
  have he : s(x, y) = s(x, z) := by
    by_contra hne
    have hd := hE.2 hxy.1 hxz.1 hne
    exact Set.disjoint_left.mp hd (show x ∈ (s(x, y) : Set V) by simp)
      (show x ∈ (s(x, z) : Set V) by simp)
  exact Sym2.congr_right.mp he

/-- Adding a graph of maximum degree one on isolated vertices preserves the
induced-star-free property.  All vertices keep their original labels. -/
theorem inducedStarFree_sup_isolated_matching {k : ℕ} (hk : 2 ≤ k)
    (G M : SimpleGraph V)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    (hM : ∀ x y z, M.Adj x y → M.Adj x z → y = z)
    (hiso : ∀ x y z, M.Adj x y → ¬G.Adj x z) :
    ¬Regularity.InducedEmbeds (inducedStar k) (G ⊔ M) := by
  rintro ⟨f⟩
  have hcenter : ∀ w, ¬M.Adj (f 0) w := by
    intro w hw
    let a : Fin (k + 1) := ⟨1, by omega⟩
    let b : Fin (k + 1) := ⟨2, by omega⟩
    have ha := f.map_rel_iff.mpr (inducedStar_center_adj_of_ne
      (show a ≠ 0 by simp [a]))
    have hb := f.map_rel_iff.mpr (inducedStar_center_adj_of_ne
      (show b ≠ 0 by simp [b]))
    have hma : M.Adj (f 0) (f a) := ha.elim (fun h ↦ (hiso _ _ _ hw h).elim) id
    have hmb : M.Adj (f 0) (f b) := hb.elim (fun h ↦ (hiso _ _ _ hw h).elim) id
    have hab := f.injective (hM _ _ _ hma hmb)
    have := congrArg Fin.val hab
    norm_num [a, b] at this
  have hnoM : ∀ i w, ¬M.Adj (f i) w := by
    intro i w h
    by_cases hi : i = 0
    · exact hcenter w (hi ▸ h)
    · have hstar := f.map_rel_iff.mpr (inducedStar_center_adj_of_ne hi)
      have hG : G.Adj (f 0) (f i) := hstar.elim id (fun h ↦ (hcenter _ h).elim)
      exact hiso _ _ _ h hG.symm
  apply hfree
  exact ⟨{
    toFun := f
    inj' := f.injective
    map_rel_iff' := by
      intro i j
      constructor
      · intro h
        exact f.map_rel_iff.mp (Or.inl h)
      · intro h
        exact (f.map_rel_iff.mpr h).elim id (fun hh ↦ (hnoM _ _ hh).elim) }⟩

/-- Injective relabeling and adding isolated vertices preserve star-freeness. -/
theorem inducedStarFree_map {k : ℕ} (hk : 1 ≤ k) (G : SimpleGraph V)
    (e : V ↪ W) (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G) :
    ¬Regularity.InducedEmbeds (inducedStar k) (G.map e) := by
  rintro ⟨f⟩
  have hrange : ∀ i, ∃ v, e v = f i := by
    intro i
    have hadj : ∃ j, (inducedStar k).Adj i j := by
      by_cases hi : i = 0
      · subst i
        exact ⟨⟨1, by omega⟩, inducedStar_center_adj_of_ne (by simp)⟩
      · exact ⟨0, (inducedStar_center_adj_of_ne hi).symm⟩
    obtain ⟨j, hj⟩ := hadj
    obtain ⟨v, w, _, hv, _⟩ :=
      (SimpleGraph.map_adj e G _ _).mp (f.map_rel_iff.mpr hj)
    exact ⟨v, hv⟩
  choose g hg using hrange
  apply hfree
  exact ⟨{
    toFun := g
    inj' := by intro i j h; apply f.injective; rw [← hg i, ← hg j, h]
    map_rel_iff' := by
      intro i j
      change G.Adj (g i) (g j) ↔ (inducedStar k).Adj i j
      rw [← SimpleGraph.map_adj_apply (f := e), hg i, hg j]
      exact f.map_rel_iff }⟩

/-- A mapped matching still has at most one neighbor at every vertex. -/
theorem sparseMatchingGraph_map_neighbor_unique
    (E : Finset (Sym2 V)) (hE : IsEdgeMatching ⊤ E) (e : V ↪ W)
    {x y z : W} (hxy : ((sparseMatchingGraph E).map e).Adj x y)
    (hxz : ((sparseMatchingGraph E).map e).Adj x z) : y = z := by
  obtain ⟨a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj e _ _ _).mp hxy
  obtain ⟨a', c, hac, ha', hc⟩ := (SimpleGraph.map_adj e _ _ _).mp hxz
  have haa : a = a' := e.injective (ha.trans ha'.symm)
  subst a'
  have hbc := sparseMatchingGraph_neighbor_unique E hE hab hac
  rw [← hb, ← hc, hbc]

/-- Removing the marked added matching recovers the original graph exactly. -/
theorem sup_isolated_matching_deleteEdges (G M : SimpleGraph V)
    (hiso : ∀ x y z, M.Adj x y → ¬G.Adj x z) :
    (G ⊔ M).deleteEdges M.edgeSet = G := by
  classical
  ext x y
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hG | hM, hn⟩
    · exact hG
    · exact (hn hM).elim
  · intro hG
    exact ⟨Or.inl hG, fun hM ↦ hiso _ _ _ hM hG⟩

end InducedStars
