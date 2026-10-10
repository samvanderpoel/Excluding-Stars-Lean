import InducedStars.EdgeColoring.Extremal
import InducedStars.Graphon.Star
import InducedStars.Regularity.Type
import Mathlib.Tactic

/-!
# Complete colorings attached to regularity Types

This file implements the complete red--green--blue coloring used in the
preparation for the graphon Mantel inequality.  Actual edges of a colored
reduced graph retain their color, while reduced nonedges are colored blue.

The finite obstruction has `k` vertices, whereas the forbidden induced star
has `k + 1` vertices.  The bridge below is therefore deliberately
noninjective and uses the vertex colors of the Type in three exhaustive
cases.
-/

noncomputable section

namespace InducedStars

open Regularity

namespace Regularity.RegularityColoredGraph

universe u

variable {V : Type u}

/-- Complete an arbitrary regularity-colored graph by coloring its nonedges
blue.  Existing red, green, and blue edge labels are retained verbatim. -/
noncomputable def completeColoring (J : RegularityColoredGraph V) : ColoredGraph V := by
  classical
  exact SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if h : J.graph.Adj x y then J.getEdgeColor x y h else .blue)
    (by
      intro x y _
      by_cases hxy : J.graph.Adj x y
      · have hyx : J.graph.Adj y x := hxy.symm
        simp only [hxy, hyx, dite_true]
        simpa only [proof_irrel_heq] using J.getEdgeColor_comm x y hxy
      · have hyx : ¬J.graph.Adj y x := fun h ↦ hxy h.symm
        simp only [hxy, hyx, dite_false])

/-- Red in the completed coloring means exactly an actual red edge. -/
@[simp] theorem completeColoring_color_eq_red_iff [DecidableEq V]
    (J : RegularityColoredGraph V) (x y : V) :
    J.completeColoring.color x y = .red ↔
      ∃ h : J.graph.Adj x y, J.getEdgeColor x y h = .red := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ColoredGraph.color_eq_get _ hxy]
    change (if h' : J.graph.Adj x y then J.getEdgeColor x y h' else .blue) = .red ↔ _
    by_cases h : J.graph.Adj x y
    · simp [completeColoring, h]
    · simp [completeColoring, h]

/-- Green in the completed coloring means exactly an actual green edge. -/
@[simp] theorem completeColoring_color_eq_green_iff [DecidableEq V]
    (J : RegularityColoredGraph V) (x y : V) :
    J.completeColoring.color x y = .green ↔
      ∃ h : J.graph.Adj x y, J.getEdgeColor x y h = .green := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ColoredGraph.color_eq_get _ hxy]
    change (if h' : J.graph.Adj x y then J.getEdgeColor x y h' else .blue) = .green ↔ _
    by_cases h : J.graph.Adj x y
    · simp [completeColoring, h]
    · simp [completeColoring, h]

/-- Blue in the completed coloring means either a reduced nonedge or an
actual blue reduced edge.  In particular, this also covers the diagonal. -/
@[simp] theorem completeColoring_color_eq_blue_iff [DecidableEq V]
    (J : RegularityColoredGraph V) (x y : V) :
    J.completeColoring.color x y = .blue ↔
      ¬J.graph.Adj x y ∨
        ∃ h : J.graph.Adj x y, J.getEdgeColor x y h = .blue := by
  classical
  by_cases hxy : x = y
  · subst y
    simp
  · rw [ColoredGraph.color_eq_get _ hxy]
    change (if h' : J.graph.Adj x y then J.getEdgeColor x y h' else .blue) = .blue ↔ _
    by_cases h : J.graph.Adj x y
    · simp [completeColoring, h]
    · simp [completeColoring, h]

/-- A red completed pair supports an edge of a colored homomorphism. -/
theorem mapsEdge_of_completeColoring_red [DecidableEq V]
    {W : Type*} (J : RegularityColoredGraph V) (phi : W → V) {x y : W}
    (hred : J.completeColoring.color (phi x) (phi y) = .red) :
    J.MapsEdge phi x y := by
  right
  obtain ⟨hadj, hcolor⟩ :=
    (J.completeColoring_color_eq_red_iff (phi x) (phi y)).mp hred
  exact ⟨hadj, Or.inl hcolor⟩

/-- A red or green completed pair supports a nonedge of a colored
homomorphism. -/
theorem mapsNonedge_of_completeColoring_leafColor [DecidableEq V]
    {W : Type*} (J : RegularityColoredGraph V) (phi : W → V) {x y : W}
    (hleaf : (J.completeColoring.color (phi x) (phi y)).IsLeafColor) :
    J.MapsNonedge phi x y := by
  right
  rcases hleaf with hred | hgreen
  · obtain ⟨hadj, hcolor⟩ :=
      (J.completeColoring_color_eq_red_iff (phi x) (phi y)).mp hred
    exact ⟨hadj, Or.inl hcolor⟩
  · obtain ⟨hadj, hcolor⟩ :=
      (J.completeColoring_color_eq_green_iff (phi x) (phi y)).mp hgreen
    exact ⟨hadj, Or.inr hcolor⟩

end Regularity.RegularityColoredGraph

namespace Regularity

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {eta delta : ℝ} {ell : ℕ}

/-- The paper's complete red--green--blue coloring associated with a Type. -/
noncomputable def typeCompleteColoring (T : RegularityType G eta delta ell) :
    ColoredGraph (Fin T.partition.clusterCount) :=
  T.coloredGraph.completeColoring

@[simp] theorem typeCompleteColoring_color_eq_red_iff
    (T : RegularityType G eta delta ell)
    (i j : Fin T.partition.clusterCount) :
    (typeCompleteColoring T).color i j = .red ↔
      ∃ h : T.coloredGraph.graph.Adj i j,
        T.coloredGraph.getEdgeColor i j h = .red :=
  T.coloredGraph.completeColoring_color_eq_red_iff i j

@[simp] theorem typeCompleteColoring_color_eq_green_iff
    (T : RegularityType G eta delta ell)
    (i j : Fin T.partition.clusterCount) :
    (typeCompleteColoring T).color i j = .green ↔
      ∃ h : T.coloredGraph.graph.Adj i j,
        T.coloredGraph.getEdgeColor i j h = .green :=
  T.coloredGraph.completeColoring_color_eq_green_iff i j

@[simp] theorem typeCompleteColoring_color_eq_blue_iff
    (T : RegularityType G eta delta ell)
    (i j : Fin T.partition.clusterCount) :
    (typeCompleteColoring T).color i j = .blue ↔
      ¬T.coloredGraph.graph.Adj i j ∨
        ∃ h : T.coloredGraph.graph.Adj i j,
          T.coloredGraph.getEdgeColor i j h = .blue :=
  T.coloredGraph.completeColoring_color_eq_blue_iff i j

namespace RegularityColoredGraph

universe w

variable {X : Type w} [DecidableEq X]

/-- The only collision of `Fin.predAbove p` between distinct inputs occurs
over its pivot. -/
private theorem predAbove_eq_pivot_of_eq_of_ne {n : ℕ} (p : Fin n)
    {i j : Fin (n + 1)} (hij : i ≠ j)
    (heq : p.predAbove i = p.predAbove j) :
    p.predAbove i = p := by
  by_contra hp
  have hi : i ≠ p.castSucc := by
    intro hi
    subst i
    exact hp (Fin.predAbove_castSucc_self p)
  have hj : j ≠ p.castSucc := by
    intro hj
    subst j
    exact hp (heq.trans (Fin.predAbove_castSucc_self p))
  have hs := congrArg p.castSucc.succAbove heq
  rw [Fin.succAbove_predAbove hi, Fin.succAbove_predAbove hj] at hs
  exact hij hs

/-- Case 1 of the forbidden-pattern extension: duplicate exactly one green
pattern leaf and biject the remaining source leaves to the remaining pattern
leaves. -/
private theorem coloredHom_inducedStar_of_green_leaf {n : ℕ}
    (J : RegularityColoredGraph X) (e : Fin (n + 1) ↪ X)
    (center a : Fin (n + 1)) (ha : a ≠ center)
    (haGreen : J.vertexColor (e a) = .green)
    (hcenterRed : ∀ x, x ≠ center →
      J.completeColoring.color (e center) (e x) = .red)
    (hleaf : ∀ x y, x ≠ center → y ≠ center → x ≠ y →
      (J.completeColoring.color (e x) (e y)).IsLeafColor) :
    ColoredHomExists (inducedStar (n + 1)) J := by
  classical
  obtain ⟨p, hp⟩ := Fin.exists_succAbove_eq ha
  let leafMap : Fin (n + 1) → Fin (n + 1) := fun i ↦
    center.succAbove (p.predAbove i)
  let phi : Fin ((n + 1) + 1) → X :=
    Fin.cases (e center) (fun i ↦ e (leafMap i))
  have hleafMap_ne (i : Fin (n + 1)) : leafMap i ≠ center := by
    exact Fin.succAbove_ne center (p.predAbove i)
  refine ⟨phi, ?_⟩
  intro x y hxy
  constructor
  · intro hadj
    rcases (inducedStar_adj.mp hadj).2 with hx | hy
    · subst x
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy.symm
      apply J.mapsEdge_of_completeColoring_red phi
      simpa [phi] using hcenterRed (leafMap i) (hleafMap_ne i)
    · subst y
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy
      apply J.mapsEdge_of_completeColoring_red phi
      rw [J.completeColoring.color_comm]
      simpa [phi] using hcenterRed (leafMap i) (hleafMap_ne i)
  · intro hnonedge
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      exact hnonedge (inducedStar_center_adj_of_ne hxy.symm)
    have hy0 : y ≠ 0 := by
      intro hy
      subst y
      exact hnonedge (inducedStar_center_adj_of_ne hxy).symm
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hx0
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hy0
    have hij : i ≠ j := by
      intro hij
      exact hxy (congrArg Fin.succ hij)
    by_cases himage : leafMap i = leafMap j
    · left
      have hpred : p.predAbove i = p.predAbove j := by
        apply Fin.succAbove_right_injective
        simpa only [leafMap] using himage
      have hip : p.predAbove i = p :=
        predAbove_eq_pivot_of_eq_of_ne p hij hpred
      have hia : leafMap i = a := by
        simp only [leafMap, hip, hp]
      constructor
      · simpa [phi, himage]
      · simpa [phi, hia] using haGreen
    · apply J.mapsNonedge_of_completeColoring_leafColor phi
      simpa [phi] using
        hleaf (leafMap i) (leafMap j) (hleafMap_ne i) (hleafMap_ne j) himage

/-- Case 2 of the forbidden-pattern extension: collapse the source center
and one source leaf at a blue pattern center, then biject the remaining
source leaves to all pattern leaves. -/
private theorem coloredHom_inducedStar_of_blue_center {n : ℕ}
    (J : RegularityColoredGraph X) (e : Fin (n + 1) ↪ X)
    (center : Fin (n + 1))
    (hcenterBlue : J.vertexColor (e center) = .blue)
    (hcenterRed : ∀ x, x ≠ center →
      J.completeColoring.color (e center) (e x) = .red)
    (hleaf : ∀ x y, x ≠ center → y ≠ center → x ≠ y →
      (J.completeColoring.color (e x) (e y)).IsLeafColor) :
    ColoredHomExists (inducedStar (n + 1)) J := by
  classical
  let leafMap : Fin (n + 1) → Fin (n + 1) := fun i ↦
    if hi : i = 0 then center else center.succAbove (i.pred hi)
  let phi : Fin ((n + 1) + 1) → X :=
    Fin.cases (e center) (fun i ↦ e (leafMap i))
  have hleafMap_zero : leafMap 0 = center := by
    simp [leafMap]
  have hleafMap_ne {i : Fin (n + 1)} (hi : i ≠ 0) :
      leafMap i ≠ center := by
    simp only [leafMap, hi, dite_false]
    exact Fin.succAbove_ne center (i.pred hi)
  have hleafMap_injective {i j : Fin (n + 1)} (hi : i ≠ 0) (hj : j ≠ 0)
      (himage : leafMap i = leafMap j) : i = j := by
    simp only [leafMap, hi, hj, dite_false] at himage
    have hpred : i.pred hi = j.pred hj :=
      Fin.succAbove_right_injective himage
    have hsucc := congrArg Fin.succ hpred
    simpa using hsucc
  have hphi_center : phi 0 = e center := rfl
  have hphi_leaf (i : Fin (n + 1)) : phi i.succ = e (leafMap i) := rfl
  have hphi_leaf_zero : phi (0 : Fin (n + 1)).succ = e center := by
    rw [hphi_leaf, hleafMap_zero]
  refine ⟨phi, ?_⟩
  intro x y hxy
  constructor
  · intro hadj
    rcases (inducedStar_adj.mp hadj).2 with hx | hy
    · subst x
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy.symm
      by_cases hi : i = 0
      · left
        subst i
        constructor
        · exact hphi_center.trans hphi_leaf_zero.symm
        · rw [hphi_center]
          exact hcenterBlue
      · apply J.mapsEdge_of_completeColoring_red phi
        simpa [phi] using hcenterRed (leafMap i) (hleafMap_ne hi)
    · subst y
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy
      by_cases hi : i = 0
      · left
        subst i
        constructor
        · exact hphi_leaf_zero.trans hphi_center.symm
        · rw [hphi_leaf_zero]
          exact hcenterBlue
      · apply J.mapsEdge_of_completeColoring_red phi
        rw [J.completeColoring.color_comm]
        simpa [phi] using hcenterRed (leafMap i) (hleafMap_ne hi)
  · intro hnonedge
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      exact hnonedge (inducedStar_center_adj_of_ne hxy.symm)
    have hy0 : y ≠ 0 := by
      intro hy
      subst y
      exact hnonedge (inducedStar_center_adj_of_ne hxy).symm
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hx0
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hy0
    have hij : i ≠ j := by
      intro hij
      exact hxy (congrArg Fin.succ hij)
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro hj
        exact hij hj.symm
      apply J.mapsNonedge_of_completeColoring_leafColor phi
      apply Or.inl
      rw [hphi_leaf_zero, hphi_leaf]
      exact hcenterRed (leafMap j) (hleafMap_ne hj)
    · by_cases hj : j = 0
      · subst j
        apply J.mapsNonedge_of_completeColoring_leafColor phi
        apply Or.inl
        rw [hphi_leaf_zero, hphi_leaf, J.completeColoring.color_comm]
        exact hcenterRed (leafMap i) (hleafMap_ne hi)
      · have himage : leafMap i ≠ leafMap j := by
          intro himage
          exact hij (hleafMap_injective hi hj himage)
        apply J.mapsNonedge_of_completeColoring_leafColor phi
        simpa [phi] using
          hleaf (leafMap i) (leafMap j) (hleafMap_ne hi) (hleafMap_ne hj) himage

/-- Case 3 of the forbidden-pattern extension: collapse the source center
and one source leaf at a blue pattern leaf, then collapse all remaining
source leaves at the green pattern center. -/
private theorem coloredHom_inducedStar_of_green_center {n : ℕ} (hn : 0 < n)
    (J : RegularityColoredGraph X) (e : Fin (n + 1) ↪ X)
    (center : Fin (n + 1))
    (hcenterGreen : J.vertexColor (e center) = .green)
    (hleavesBlue : ∀ x, x ≠ center → J.vertexColor (e x) = .blue)
    (hcenterRed : ∀ x, x ≠ center →
      J.completeColoring.color (e center) (e x) = .red) :
    ColoredHomExists (inducedStar (n + 1)) J := by
  classical
  let p : Fin n := ⟨0, hn⟩
  let a : Fin (n + 1) := center.succAbove p
  have ha : a ≠ center := Fin.succAbove_ne center p
  have haBlue : J.vertexColor (e a) = .blue := hleavesBlue a ha
  let leafMap : Fin (n + 1) → Fin (n + 1) := fun i ↦
    if i = 0 then a else center
  let phi : Fin ((n + 1) + 1) → X :=
    Fin.cases (e a) (fun i ↦ e (leafMap i))
  have hleafMap_zero : leafMap 0 = a := by simp [leafMap]
  have hleafMap_of_ne {i : Fin (n + 1)} (hi : i ≠ 0) :
      leafMap i = center := by simp [leafMap, hi]
  have hphi_center : phi 0 = e a := rfl
  have hphi_leaf (i : Fin (n + 1)) : phi i.succ = e (leafMap i) := rfl
  have hphi_leaf_zero : phi (0 : Fin (n + 1)).succ = e a := by
    rw [hphi_leaf, hleafMap_zero]
  refine ⟨phi, ?_⟩
  intro x y hxy
  constructor
  · intro hadj
    rcases (inducedStar_adj.mp hadj).2 with hx | hy
    · subst x
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy.symm
      by_cases hi : i = 0
      · subst i
        left
        constructor
        · exact hphi_center.trans hphi_leaf_zero.symm
        · rw [hphi_center]
          exact haBlue
      · apply J.mapsEdge_of_completeColoring_red phi
        rw [hphi_center, hphi_leaf, hleafMap_of_ne hi,
          J.completeColoring.color_comm]
        exact hcenterRed a ha
    · subst y
      obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hxy
      by_cases hi : i = 0
      · subst i
        left
        constructor
        · exact hphi_leaf_zero.trans hphi_center.symm
        · rw [hphi_leaf_zero]
          exact haBlue
      · apply J.mapsEdge_of_completeColoring_red phi
        rw [hphi_leaf, hleafMap_of_ne hi, hphi_center]
        exact hcenterRed a ha
  · intro hnonedge
    have hx0 : x ≠ 0 := by
      intro hx
      subst x
      exact hnonedge (inducedStar_center_adj_of_ne hxy.symm)
    have hy0 : y ≠ 0 := by
      intro hy
      subst y
      exact hnonedge (inducedStar_center_adj_of_ne hxy).symm
    obtain ⟨i, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hx0
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq_of_ne_zero hy0
    have hij : i ≠ j := by
      intro hij
      exact hxy (congrArg Fin.succ hij)
    by_cases hi : i = 0
    · subst i
      have hj : j ≠ 0 := by
        intro hj
        exact hij hj.symm
      apply J.mapsNonedge_of_completeColoring_leafColor phi
      apply Or.inl
      rw [hphi_leaf_zero, hphi_leaf, hleafMap_of_ne hj,
        J.completeColoring.color_comm]
      exact hcenterRed a ha
    · by_cases hj : j = 0
      · subst j
        apply J.mapsNonedge_of_completeColoring_leafColor phi
        apply Or.inl
        rw [hphi_leaf, hleafMap_of_ne hi, hphi_leaf_zero]
        exact hcenterRed a ha
      · left
        constructor
        · rw [hphi_leaf, hleafMap_of_ne hi, hphi_leaf, hleafMap_of_ne hj]
        · rw [hphi_leaf, hleafMap_of_ne hi]
          exact hcenterGreen

/-- A forbidden `k`-vertex configuration in a completed regularity-colored
graph produces a colored homomorphism from the `(k + 1)`-vertex induced
star.  The map is intentionally noninjective; its construction is split
according to the green/blue vertex colors of the forbidden configuration.
Paper: the forbidden-pattern argument in `prop:graphon-char-fixed-gamma`. -/
theorem coloredHom_inducedStar_of_forbiddenConfig {k : ℕ} (hk : 3 ≤ k)
    (J : RegularityColoredGraph X) (e : Fin k ↪ X)
    (hforbidden : (J.completeColoring.pullback e).IsForbiddenPattern) :
    ColoredHomExists (inducedStar k) J := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hn : 0 < n := by omega
  rcases hforbidden with ⟨center, hred, hleaf⟩
  have hcenterRed (x : Fin (n + 1)) (hx : x ≠ center) :
      J.completeColoring.color (e center) (e x) = .red := by
    simpa only [ColoredGraph.pullback_color] using hred x hx
  have hleaf' (x y : Fin (n + 1)) (hx : x ≠ center)
      (hy : y ≠ center) (hxy : x ≠ y) :
      (J.completeColoring.color (e x) (e y)).IsLeafColor := by
    simpa only [ColoredGraph.pullback_color] using hleaf x y hx hy hxy
  by_cases hgreenLeaf : ∃ a : Fin (n + 1),
      a ≠ center ∧ J.vertexColor (e a) = .green
  · obtain ⟨a, ha, haGreen⟩ := hgreenLeaf
    exact coloredHom_inducedStar_of_green_leaf J e center a ha haGreen
      hcenterRed hleaf'
  · have hleavesBlue : ∀ x : Fin (n + 1), x ≠ center →
        J.vertexColor (e x) = .blue := by
      intro x hx
      cases hcolor : J.vertexColor (e x) with
      | green => exact (hgreenLeaf ⟨x, hx, hcolor⟩).elim
      | blue => rfl
    by_cases hcenterBlue : J.vertexColor (e center) = .blue
    · exact coloredHom_inducedStar_of_blue_center J e center hcenterBlue
        hcenterRed hleaf'
    · have hcenterGreen : J.vertexColor (e center) = .green := by
        cases hcolor : J.vertexColor (e center) with
        | green => rfl
        | blue => exact (hcenterBlue hcolor).elim
      exact coloredHom_inducedStar_of_green_center hn J e center hcenterGreen
        hleavesBlue hcenterRed

end RegularityColoredGraph

/-- The complete coloring attached to an induced-`K_{1,k}`-free Type is a
member of the finite forbidden-pattern class `Ck k`, by extending its
`k`-vertex pattern noninjectively to an induced star. -/
theorem typeCompleteColoring_mem_Ck {k : ℕ} (hk : 3 ≤ k)
    (T : RegularityType G eta delta (k + 1))
    (hfree : ¬InducedEmbeds (inducedStar k) G) :
    typeCompleteColoring T ∈ ColoredGraph.Ck k T.partition.clusterCount := by
  rw [ColoredGraph.mem_Ck_iff]
  intro hcontains
  rcases hcontains with ⟨e, he⟩
  apply hfree
  apply T.inducedEmbedding (k + 1) le_rfl (inducedStar k)
  apply RegularityColoredGraph.coloredHom_inducedStar_of_forbiddenConfig hk
      T.coloredGraph e
  change ((typeCompleteColoring T).pullback e).IsForbiddenPattern at he
  exact he

end Regularity

namespace ColoredGraph

open Finset

/-- Ordered pairs whose total color is `c`.  For blue this includes every
diagonal pair, in accordance with the project's blue diagonal sentinel. -/
def orderedColorPairs {q : ℕ} (C : ColoredGraph (Fin q)) (c : EdgeColor) :
    Finset (Fin q × Fin q) :=
  Finset.univ.filter fun ij ↦ C.color ij.1 ij.2 = c

@[simp] theorem mem_orderedColorPairs {q : ℕ} (C : ColoredGraph (Fin q))
    (c : EdgeColor) (i j : Fin q) :
    (i, j) ∈ C.orderedColorPairs c ↔ C.color i j = c := by
  simp [orderedColorPairs]

/-- Away from blue, ordered colored pairs are exactly the darts of the
corresponding color graph. -/
theorem orderedColorPairs_eq_adj_filter_of_ne_blue {q : ℕ}
    (C : ColoredGraph (Fin q)) {c : EdgeColor} (hc : c ≠ .blue) :
    C.orderedColorPairs c =
      Finset.univ.filter fun ij ↦ (C.colorGraph c).Adj ij.1 ij.2 := by
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [orderedColorPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    colorGraph_adj]
  constructor
  · intro hcolor
    refine ⟨?_, hcolor⟩
    intro hij
    subst j
    rw [C.color_self i] at hcolor
    exact hc hcolor.symm
  · exact fun h ↦ h.2

/-- Every unordered red edge contributes its two orientations. -/
theorem card_orderedRedPairs {q : ℕ} (C : ColoredGraph (Fin q)) :
    #(C.orderedColorPairs .red) = 2 * C.edgeCount .red := by
  rw [C.orderedColorPairs_eq_adj_filter_of_ne_blue (by decide)]
  simpa only [edgeCount, edgeFinset] using
    (C.redGraph.two_mul_card_edgeFinset).symm

/-- Every unordered green edge contributes its two orientations. -/
theorem card_orderedGreenPairs {q : ℕ} (C : ColoredGraph (Fin q)) :
    #(C.orderedColorPairs .green) = 2 * C.edgeCount .green := by
  rw [C.orderedColorPairs_eq_adj_filter_of_ne_blue (by decide)]
  simpa only [edgeCount, edgeFinset] using
    (C.greenGraph.two_mul_card_edgeFinset).symm

/-- The diagonal ordered pairs on `Fin q`. -/
def diagonalPairs (q : ℕ) : Finset (Fin q × Fin q) :=
  Finset.univ.image fun i ↦ (i, i)

@[simp] theorem mem_diagonalPairs {q : ℕ} (i j : Fin q) :
    (i, j) ∈ diagonalPairs q ↔ i = j := by
  constructor
  · rintro h
    obtain ⟨x, _hx, hpair⟩ := Finset.mem_image.mp h
    exact (congrArg Prod.fst hpair).symm.trans (congrArg Prod.snd hpair)
  · intro hij
    subst j
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

@[simp] theorem card_diagonalPairs (q : ℕ) : #(diagonalPairs q) = q := by
  unfold diagonalPairs
  rw [Finset.card_image_of_injective Finset.univ]
  · simp
  · intro i j hij
    exact congrArg Prod.fst hij

/-- Blue ordered pairs split into the actual blue darts and the diagonal. -/
theorem orderedBluePairs_eq_diagonal_union_adj_filter {q : ℕ}
    (C : ColoredGraph (Fin q)) :
    C.orderedColorPairs .blue = diagonalPairs q ∪
      Finset.univ.filter fun ij ↦ C.blueGraph.Adj ij.1 ij.2 := by
  ext ij
  rcases ij with ⟨i, j⟩
  simp only [orderedColorPairs, Finset.mem_union, mem_diagonalPairs,
    Finset.mem_filter, Finset.mem_univ, true_and, colorGraph_adj]
  constructor
  · intro hblue
    by_cases hij : i = j
    · exact Or.inl hij
    · exact Or.inr ⟨hij, hblue⟩
  · rintro (hij | ⟨_hij, hblue⟩)
    · subst j
      exact C.color_self i
    · exact hblue

/-- Every unordered blue edge contributes two orientations, and the total
blue accessor contributes the `q` diagonal pairs as well. -/
theorem card_orderedBluePairs {q : ℕ} (C : ColoredGraph (Fin q)) :
    #(C.orderedColorPairs .blue) = 2 * C.edgeCount .blue + q := by
  let E : Finset (Fin q × Fin q) :=
    Finset.univ.filter fun ij ↦ C.blueGraph.Adj ij.1 ij.2
  have hdisjoint : Disjoint (diagonalPairs q) E := by
    rw [Finset.disjoint_left]
    intro ij hdiag hedge
    have hij : ij.1 = ij.2 := (mem_diagonalPairs ij.1 ij.2).mp hdiag
    have hadj : C.blueGraph.Adj ij.1 ij.2 := (Finset.mem_filter.mp hedge).2
    exact hadj.ne hij
  have hE : #E = 2 * C.edgeCount .blue := by
    simpa only [E, edgeCount, edgeFinset] using
      (C.blueGraph.two_mul_card_edgeFinset).symm
  rw [C.orderedBluePairs_eq_diagonal_union_adj_filter]
  change #(diagonalPairs q ∪ E) = _
  rw [Finset.card_union_of_disjoint hdisjoint, card_diagonalPairs, hE,
    Nat.add_comm]

/-- The normalized area of the red off-diagonal cells of a finite
coloring. -/
noncomputable def normalizedRedArea {q : ℕ} (C : ColoredGraph (Fin q)) : ℝ :=
  2 * (C.edgeCount .red : ℝ) / (q : ℝ) ^ 2

/-- The normalized area of the blue off-diagonal cells together with all
diagonal cells. -/
noncomputable def normalizedBlueDiagonalArea {q : ℕ}
    (C : ColoredGraph (Fin q)) : ℝ :=
  2 * (C.edgeCount .blue : ℝ) / (q : ℝ) ^ 2 + 1 / (q : ℝ)

theorem normalizedRedArea_nonneg {q : ℕ} (C : ColoredGraph (Fin q)) :
    0 ≤ C.normalizedRedArea := by
  exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)

theorem normalizedBlueDiagonalArea_nonneg {q : ℕ}
    (C : ColoredGraph (Fin q)) :
    0 ≤ C.normalizedBlueDiagonalArea := by
  apply add_nonneg
  · exact div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (sq_nonneg _)
  · exact div_nonneg zero_le_one (Nat.cast_nonneg _)

/-- The red normalized area is the number of ordered red cells divided by
the total number of ordered cells. -/
theorem normalizedRedArea_eq_card_orderedRedPairs {q : ℕ}
    (C : ColoredGraph (Fin q)) :
    C.normalizedRedArea =
      (#(C.orderedColorPairs .red) : ℝ) / (q : ℝ) ^ 2 := by
  rw [card_orderedRedPairs]
  simp only [normalizedRedArea, Nat.cast_mul, Nat.cast_ofNat]

/-- For positive order, the blue-plus-diagonal normalized area is the
number of ordered blue cells divided by the total number of ordered cells. -/
theorem normalizedBlueDiagonalArea_eq_card_orderedBluePairs {q : ℕ}
    (C : ColoredGraph (Fin q)) (hq : 0 < q) :
    C.normalizedBlueDiagonalArea =
      (#(C.orderedColorPairs .blue) : ℝ) / (q : ℝ) ^ 2 := by
  rw [card_orderedBluePairs]
  push_cast
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  unfold normalizedBlueDiagonalArea
  field_simp

/-- Exact normalized form of the finite `k`th-order Mantel inequality. -/
theorem normalizedRedArea_le_delta_mul_normalizedBlueDiagonalArea
    {k q : ℕ} (hk : 3 ≤ k) (hq : 0 < q)
    {C : ColoredGraph (Fin q)} (hC : C ∈ Ck k q) :
    C.normalizedRedArea ≤
      (delta k : ℝ) * C.normalizedBlueDiagonalArea := by
  have hmantel := kthOrderMantel hk hC
  have hmantelReal :
      (C.edgeCount .red : ℝ) -
          (delta k : ℝ) * (C.edgeCount .blue : ℝ) ≤
        ((delta k * q / 2 : ℕ) : ℝ) := by
    calc
      (C.edgeCount .red : ℝ) -
          (delta k : ℝ) * (C.edgeCount .blue : ℝ) =
          (objective k C : ℝ) := by simp [objective]
      _ ≤ ((delta k * q / 2 : ℕ) : ℝ) := by
        have hmantelCast :
            (objective k C : ℝ) ≤
              (((delta k * q / 2 : ℕ) : ℤ) : ℝ) :=
          (Int.cast_le).2 hmantel
        simpa only [Int.cast_natCast] using hmantelCast
  have hfloorNat : 2 * (delta k * q / 2) ≤ delta k * q := by omega
  have hfloorReal :
      2 * ((delta k * q / 2 : ℕ) : ℝ) ≤
        (delta k : ℝ) * (q : ℝ) := by
    exact_mod_cast hfloorNat
  have hcounts :
      2 * (C.edgeCount .red : ℝ) ≤
        (delta k : ℝ) * (2 * (C.edgeCount .blue : ℝ) + (q : ℝ)) := by
    nlinarith
  have hqReal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hqSq : 0 < (q : ℝ) ^ 2 := sq_pos_of_pos hqReal
  unfold normalizedRedArea normalizedBlueDiagonalArea
  calc
    2 * (C.edgeCount .red : ℝ) / (q : ℝ) ^ 2 ≤
        ((delta k : ℝ) *
          (2 * (C.edgeCount .blue : ℝ) + (q : ℝ))) / (q : ℝ) ^ 2 :=
      (div_le_div_iff_of_pos_right hqSq).2 hcounts
    _ = (delta k : ℝ) *
        (2 * (C.edgeCount .blue : ℝ) / (q : ℝ) ^ 2 + 1 / (q : ℝ)) := by
      field_simp

end ColoredGraph

end InducedStars
