import DenseGraph.Regularity.ColoredRealization
import Mathlib.Data.Finset.Basic

/-!
# Colored blow-ups with an exceptional set

Each active fiber is a clique colored by its reduced vertex. Different
active fibers inherit precisely the actual reduced edges and their colors.
Inactive vertices are green and isolated in the template, not assigned any
implicit edge color. Colored maps from graphs without isolated vertices
project to the reduced template.
-/

noncomputable section
open InducedStars InducedStars.Regularity InducedStars.Regularity.RegularityColoredGraph
open scoped Classical
namespace DenseGraph

variable {V I W : Type*}

def vertexToEdgeColor : TypeVertexColor → EdgeColor
  | .green => .green
  | .blue => .blue

@[simp] theorem vertexToEdgeColor_eq_blue (c : TypeVertexColor) :
    vertexToEdgeColor c = .blue ↔ c = .blue := by cases c <;> simp [vertexToEdgeColor]

@[simp] theorem vertexToEdgeColor_eq_green (c : TypeVertexColor) :
    vertexToEdgeColor c = .green ↔ c = .green := by cases c <;> simp [vertexToEdgeColor]

@[simp] theorem vertexToEdgeColor_ne_red (c : TypeVertexColor) :
    vertexToEdgeColor c ≠ .red := by cases c <;> simp [vertexToEdgeColor]

def coloredBlowUpGraph (J : RegularityColoredGraph I) (f : V → I) (S : Set V) :
    SimpleGraph V where
  Adj x y := x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ (f x = f y ∨ J.graph.Adj (f x) (f y))
  symm := ⟨by
    rintro x y ⟨hne, hx, hy, h | h⟩
    · exact ⟨hne.symm, hy, hx, Or.inl h.symm⟩
    · exact ⟨hne.symm, hy, hx, Or.inr h.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def coloredBlowUpLabel (J : RegularityColoredGraph I) (f : V → I) (S : Set V)
    (x y : V) (h : (coloredBlowUpGraph J f S).Adj x y) : EdgeColor :=
  if heq : f x = f y then vertexToEdgeColor (J.vertexColor (f x))
  else J.getEdgeColor (f x) (f y) (h.2.2.2.resolve_left heq)

theorem coloredBlowUpLabel_comm (J : RegularityColoredGraph I) (f : V → I) (S : Set V)
    (x y : V) (h : (coloredBlowUpGraph J f S).Adj x y) :
    coloredBlowUpLabel J f S y x h.symm = coloredBlowUpLabel J f S x y h := by
  by_cases heq : f x = f y
  · simp [coloredBlowUpLabel, heq]
  · simp only [coloredBlowUpLabel, dif_neg heq, dif_neg (Ne.symm heq)]
    exact J.getEdgeColor_comm _ _ _

def coloredBlowUp (J : RegularityColoredGraph I) (f : V → I) (S : Set V) :
    RegularityColoredGraph V where
  graph := coloredBlowUpGraph J f S
  vertexColor x := if x ∈ S then J.vertexColor (f x) else .green
  edgeColor := SimpleGraph.EdgeLabeling.mk (coloredBlowUpLabel J f S)
    (coloredBlowUpLabel_comm J f S)

@[simp] theorem coloredBlowUp_adj (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) (x y : V) :
    (coloredBlowUp J f S).graph.Adj x y ↔
      x ≠ y ∧ x ∈ S ∧ y ∈ S ∧ (f x = f y ∨ J.graph.Adj (f x) (f y)) := Iff.rfl

@[simp] theorem coloredBlowUp_vertexColor (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) (x : V) :
    (coloredBlowUp J f S).vertexColor x =
      if x ∈ S then J.vertexColor (f x) else .green := rfl

@[simp] theorem coloredBlowUp_edgeColor (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) (x y : V) (h : (coloredBlowUp J f S).graph.Adj x y) :
    (coloredBlowUp J f S).getEdgeColor x y h = coloredBlowUpLabel J f S x y h := rfl

theorem coloredBlowUp_mapsEdge_active (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) {phi : W → V} {x y : W}
    (h : (coloredBlowUp J f S).MapsEdge phi x y) : phi x ∈ S := by
  rcases h with ⟨_, hc⟩ | ⟨he, _⟩
  · by_contra hx
    simp [hx] at hc
  · exact he.2.1

/-- Projection of a colored map whose image lies in the active fibers. -/
theorem coloredHom_project_blowUp (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) {H : SimpleGraph W} {phi : W → V}
    (hphi : IsColoredHom H (coloredBlowUp J f S) phi)
    (hactive : ∀ x, phi x ∈ S) : IsColoredHom H J (f ∘ phi) := by
  intro x y hxy
  constructor
  · intro hadj
    rcases hphi.map_edge hadj with ⟨heq, hc⟩ | ⟨he, hc⟩
    · refine Or.inl ⟨congrArg f heq, ?_⟩
      simpa only [coloredBlowUp_vertexColor, if_pos (hactive x), Function.comp_apply] using hc
    · by_cases heq : f (phi x) = f (phi y)
      · refine Or.inl ⟨heq, ?_⟩
        simpa only [coloredBlowUp_edgeColor, coloredBlowUpLabel, dif_pos heq,
          vertexToEdgeColor_ne_red, false_or, vertexToEdgeColor_eq_blue, Function.comp_apply] using hc
      · refine Or.inr ⟨he.2.2.2.resolve_left heq, ?_⟩
        simpa only [coloredBlowUp_edgeColor, coloredBlowUpLabel, dif_neg heq, Function.comp_apply] using hc
  · intro hnon
    rcases hphi.map_nonedge hxy hnon with ⟨heq, hc⟩ | ⟨he, hc⟩
    · refine Or.inl ⟨congrArg f heq, ?_⟩
      simpa only [coloredBlowUp_vertexColor, if_pos (hactive x), Function.comp_apply] using hc
    · by_cases heq : f (phi x) = f (phi y)
      · refine Or.inl ⟨heq, ?_⟩
        simpa only [coloredBlowUp_edgeColor, coloredBlowUpLabel, dif_pos heq,
          vertexToEdgeColor_ne_red, false_or, vertexToEdgeColor_eq_green, Function.comp_apply] using hc
      · refine Or.inr ⟨he.2.2.2.resolve_left heq, ?_⟩
        simpa only [coloredBlowUp_edgeColor, coloredBlowUpLabel, dif_neg heq, Function.comp_apply] using hc

/-- No isolated source vertex can be sent to an exceptional isolated green
vertex. This is the exact projection needed by lifted regularity types. -/
theorem coloredHomExists_project_blowUp (J : RegularityColoredGraph I) (f : V → I)
    (S : Set V) (H : SimpleGraph W) (hH : ∀ x, ∃ y, H.Adj x y)
    (h : ColoredHomExists H (coloredBlowUp J f S)) : ColoredHomExists H J := by
  obtain ⟨phi, hphi⟩ := h
  refine ⟨f ∘ phi, coloredHom_project_blowUp J f S hphi ?_⟩
  intro x
  obtain ⟨y, hxy⟩ := hH x
  exact coloredBlowUp_mapsEdge_active J f S (hphi.map_edge hxy)

end DenseGraph
