import InducedStars.C4.Basic
import DenseGraph.Regularity.ColoredRealization

/-!
# Finite forbidden colored configurations for the four-cycle

Paper: the opening configuration deductions in Lemma `lemma:c4-stability`.
Every deduction below concerns actual edges of the possibly partial template.
The displayed maps retain the possibly noninjective colored-homomorphism
semantics; no missing pair receives an implicit color.
-/

namespace InducedStars
open Regularity RegularityColoredGraph

variable {V : Type*}

local instance : DecidableRel inducedC4.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.cycleGraph 4).Adj)

private theorem c4MapsEdge_symm (J : RegularityColoredGraph V)
    {f : Fin 4 → V} {i j : Fin 4} (h : J.MapsEdge f i j) : J.MapsEdge f j i := by
  rcases h with ⟨heq, hc⟩ | ⟨he, hc⟩
  · exact Or.inl ⟨heq.symm, heq ▸ hc⟩
  · exact Or.inr ⟨he.symm, by rw [J.getEdgeColor_comm (f i) (f j) he]; exact hc⟩

private theorem c4MapsNonedge_symm (J : RegularityColoredGraph V)
    {f : Fin 4 → V} {i j : Fin 4} (h : J.MapsNonedge f i j) : J.MapsNonedge f j i := by
  rcases h with ⟨heq, hc⟩ | ⟨he, hc⟩
  · exact Or.inl ⟨heq.symm, heq ▸ hc⟩
  · exact Or.inr ⟨he.symm, by rw [J.getEdgeColor_comm (f i) (f j) he]; exact hc⟩

private theorem c4_adj_cases (x y : Fin 4) : inducedC4.Adj x y ↔
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 3) ∨
    (x = 3 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 2 ∧ y = 1) ∨
    (x = 3 ∧ y = 2) ∨ (x = 0 ∧ y = 3) := by
  revert x y
  decide

private theorem c4_nonadj_cases (x y : Fin 4) : x ≠ y ∧ ¬inducedC4.Adj x y ↔
    (x = 0 ∧ y = 2) ∨ (x = 1 ∧ y = 3) ∨
    (x = 2 ∧ y = 0) ∨ (x = 3 ∧ y = 1) := by
  revert x y
  decide

/-- Checking the six unordered source pairs suffices for a colored C4 map. -/
theorem c4_isColoredHom_of_sixPairs (J : RegularityColoredGraph V) (f : Fin 4 → V)
    (h01 : J.MapsEdge f 0 1) (h12 : J.MapsEdge f 1 2)
    (h23 : J.MapsEdge f 2 3) (h30 : J.MapsEdge f 3 0)
    (h02 : J.MapsNonedge f 0 2) (h13 : J.MapsNonedge f 1 3) :
    IsColoredHom inducedC4 J f := by
  intro x y hxy
  constructor
  · intro hadj
    rcases (c4_adj_cases x y).mp hadj with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | exact h01 | exact h12 | exact h23 | exact h30
      | exact c4MapsEdge_symm J h01 | exact c4MapsEdge_symm J h12
      | exact c4MapsEdge_symm J h23 | exact c4MapsEdge_symm J h30
  · intro hnon
    rcases (c4_nonadj_cases x y).mp ⟨hxy, hnon⟩ with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | exact h02 | exact h13
      | exact c4MapsNonedge_symm J h02 | exact c4MapsNonedge_symm J h13

/-- Two green vertices joined by a red or blue edge receive the two
independent sides of the cycle: the explicit map is `![a,b,a,b]`. -/
theorem c4_coloredHom_of_green_green_edge
    (J : RegularityColoredGraph V) {a b : V}
    (ha : J.vertexColor a = .green) (hb : J.vertexColor b = .green)
    (hab : J.graph.Adj a b)
    (hc : J.getEdgeColor a b hab = .red ∨ J.getEdgeColor a b hab = .blue) :
    ColoredHomExists inducedC4 J := by
  let f : Fin 4 → V := ![a, b, a, b]
  have he : J.MapsEdge f 0 1 := Or.inr ⟨hab, hc⟩
  refine ⟨f, c4_isColoredHom_of_sixPairs J f he ?_ ?_ ?_ ?_ ?_⟩
  · exact c4MapsEdge_symm J he
  · exact he
  · exact c4MapsEdge_symm J he
  · exact Or.inl ⟨rfl, ha⟩
  · exact Or.inl ⟨rfl, hb⟩

/-- Two adjacent blue collapsed pairs, `![a,a,b,b]`, give the forbidden
red edge between blue vertices. -/
theorem c4_coloredHom_of_blue_blue_red
    (J : RegularityColoredGraph V) {a b : V}
    (ha : J.vertexColor a = .blue) (hb : J.vertexColor b = .blue)
    (hab : J.graph.Adj a b) (hc : J.getEdgeColor a b hab = .red) :
    ColoredHomExists inducedC4 J := by
  let f : Fin 4 → V := ![a, a, b, b]
  have he : J.MapsEdge f 1 2 := Or.inr ⟨hab, Or.inl hc⟩
  have hn : J.MapsNonedge f 0 2 := Or.inr ⟨hab, Or.inl hc⟩
  refine ⟨f, c4_isColoredHom_of_sixPairs J f ?_ he ?_ ?_ hn ?_⟩
  · exact Or.inl ⟨rfl, ha⟩
  · exact Or.inl ⟨rfl, hb⟩
  · exact c4MapsEdge_symm J he
  · exact hn

/-- Map opposite cycle vertices to a green root: `![v,x,v,y]`. -/
theorem c4_coloredHom_of_green_red_triangle
    (J : RegularityColoredGraph V) {v x y : V}
    (hv : J.vertexColor v = .green)
    (hvx : J.graph.Adj v x) (hvy : J.graph.Adj v y) (hxy : J.graph.Adj x y)
    (hcx : J.getEdgeColor v x hvx = .red) (hcy : J.getEdgeColor v y hvy = .red)
    (hcxy : J.getEdgeColor x y hxy = .red ∨ J.getEdgeColor x y hxy = .green) :
    ColoredHomExists inducedC4 J := by
  let f : Fin 4 → V := ![v, x, v, y]
  have hx : J.MapsEdge f 0 1 := Or.inr ⟨hvx, Or.inl hcx⟩
  have hy : J.MapsEdge f 2 3 := Or.inr ⟨hvy, Or.inl hcy⟩
  refine ⟨f, c4_isColoredHom_of_sixPairs J f hx ?_ hy ?_ ?_ ?_⟩
  · exact c4MapsEdge_symm J hx
  · exact c4MapsEdge_symm J hy
  · exact Or.inl ⟨rfl, hv⟩
  · exact Or.inr ⟨hxy, hcxy⟩

/-- Map adjacent cycle vertices to a blue root: `![v,v,x,y]`. -/
theorem c4_coloredHom_of_blue_red_triangle
    (J : RegularityColoredGraph V) {v x y : V}
    (hv : J.vertexColor v = .blue)
    (hvx : J.graph.Adj v x) (hvy : J.graph.Adj v y) (hxy : J.graph.Adj x y)
    (hcx : J.getEdgeColor v x hvx = .red) (hcy : J.getEdgeColor v y hvy = .red)
    (hcxy : J.getEdgeColor x y hxy = .red ∨ J.getEdgeColor x y hxy = .blue) :
    ColoredHomExists inducedC4 J := by
  let f : Fin 4 → V := ![v, v, x, y]
  have hy : J.MapsEdge f 0 3 := Or.inr ⟨hvy, Or.inl hcy⟩
  refine ⟨f, c4_isColoredHom_of_sixPairs J f ?_ ?_ ?_ ?_ ?_ ?_⟩
  · exact Or.inl ⟨rfl, hv⟩
  · exact Or.inr ⟨hvx, Or.inl hcx⟩
  · exact Or.inr ⟨hxy, hcxy⟩
  · exact c4MapsEdge_symm J hy
  · exact Or.inr ⟨hvx, Or.inl hcx⟩
  · exact Or.inr ⟨hvy, Or.inl hcy⟩

/-- Every actual edge between green vertices is green. -/
theorem c4Free_green_green_edge
    (J : RegularityColoredGraph V) (hfree : ¬ColoredHomExists inducedC4 J)
    {a b : V} (ha : J.vertexColor a = .green) (hb : J.vertexColor b = .green)
    (hab : J.graph.Adj a b) : J.getEdgeColor a b hab = .green := by
  cases hc : J.getEdgeColor a b hab with
  | green => rfl
  | red => exact False.elim (hfree (c4_coloredHom_of_green_green_edge J ha hb hab (Or.inl hc)))
  | blue => exact False.elim (hfree (c4_coloredHom_of_green_green_edge J ha hb hab (Or.inr hc)))

/-- An actual edge between blue vertices cannot be red. -/
theorem c4Free_blue_blue_edge_not_red
    (J : RegularityColoredGraph V) (hfree : ¬ColoredHomExists inducedC4 J)
    {a b : V} (ha : J.vertexColor a = .blue) (hb : J.vertexColor b = .blue)
    (hab : J.graph.Adj a b) : J.getEdgeColor a b hab ≠ .red :=
  fun hc ↦ hfree (c4_coloredHom_of_blue_blue_red J ha hb hab hc)

/-- Actual edges between red neighbors of a green root are blue. -/
theorem c4Free_green_red_neighbors_edge_blue
    (J : RegularityColoredGraph V) (hfree : ¬ColoredHomExists inducedC4 J)
    {v x y : V} (hv : J.vertexColor v = .green)
    (hvx : J.graph.Adj v x) (hvy : J.graph.Adj v y) (hxy : J.graph.Adj x y)
    (hcx : J.getEdgeColor v x hvx = .red) (hcy : J.getEdgeColor v y hvy = .red) :
    J.getEdgeColor x y hxy = .blue := by
  cases hc : J.getEdgeColor x y hxy with
  | blue => rfl
  | red => exact False.elim (hfree (c4_coloredHom_of_green_red_triangle
      J hv hvx hvy hxy hcx hcy (Or.inl hc)))
  | green => exact False.elim (hfree (c4_coloredHom_of_green_red_triangle
      J hv hvx hvy hxy hcx hcy (Or.inr hc)))

/-- Actual edges between red neighbors of a blue root are green. -/
theorem c4Free_blue_red_neighbors_edge_green
    (J : RegularityColoredGraph V) (hfree : ¬ColoredHomExists inducedC4 J)
    {v x y : V} (hv : J.vertexColor v = .blue)
    (hvx : J.graph.Adj v x) (hvy : J.graph.Adj v y) (hxy : J.graph.Adj x y)
    (hcx : J.getEdgeColor v x hvx = .red) (hcy : J.getEdgeColor v y hvy = .red) :
    J.getEdgeColor x y hxy = .green := by
  cases hc : J.getEdgeColor x y hxy with
  | green => rfl
  | red => exact False.elim (hfree (c4_coloredHom_of_blue_red_triangle
      J hv hvx hvy hxy hcx hcy (Or.inl hc)))
  | blue => exact False.elim (hfree (c4_coloredHom_of_blue_red_triangle
      J hv hvx hvy hxy hcx hcy (Or.inr hc)))

/-- The four-cycle with every vertex and every actual edge blue. Its two
missing diagonal pairs are genuinely uncolored, not green. -/
def c4BluePartialTemplate : RegularityColoredGraph (Fin 4) where
  graph := inducedC4
  vertexColor := fun _ ↦ .blue
  edgeColor := SimpleGraph.EdgeLabeling.mk (fun _ _ _ ↦ .blue) (by intros; rfl)

/-- A nonedge of the source cannot map anywhere in an all-blue partial
template, either collapsed or on an actual edge. -/
theorem c4BluePartialTemplate_no_coloredHom :
    ¬ColoredHomExists inducedC4 c4BluePartialTemplate := by
  rintro ⟨f, hf⟩
  have h := hf.map_nonedge (by decide : (0 : Fin 4) ≠ 2)
    (by decide : ¬inducedC4.Adj 0 2)
  rcases h with ⟨_, hc⟩ | ⟨he, hc⟩
  · cases hc
  · rcases hc with hc | hc <;> cases hc

/-- The blue-only realization of this partial template is exactly C4. -/
theorem c4BluePartialTemplate_blue_realization (x y : Fin 4) :
    inducedC4.Adj x y ↔ ∃ h : c4BluePartialTemplate.graph.Adj x y,
      c4BluePartialTemplate.getEdgeColor x y h = .blue := by
  constructor
  · intro h
    exact ⟨h, rfl⟩
  · rintro ⟨h, _⟩
    exact h

theorem c4BluePartialTemplate_realizes_C4 :
    DenseGraph.IsColoredRealization c4BluePartialTemplate inducedC4 := by
  intro x y h
  exact ⟨fun _ ↦ h, fun hc ↦ by cases hc⟩

/-- Thus partial-template colored exclusion does not imply induced exclusion
in its blue-only realization. -/
theorem c4BluePartialTemplate_realization_contains_C4 :
    InducedEmbeds inducedC4 inducedC4 := by
  exact ⟨RelEmbedding.refl _⟩

end InducedStars
