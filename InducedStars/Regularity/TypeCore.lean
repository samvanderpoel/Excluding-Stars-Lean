import DenseGraph.Regularity.Inputs
import InducedStars.ColoredGraph
import InducedStars.Regularity.Basic
import InducedStars.Regularity.Embedding
import Mathlib.Tactic

/-!
# Colored regularity types: axiom-free core

This file formalizes the colored reduced graphs and colored homomorphisms in
the paper's regularity section. Unlike `InducedStars.ColoredGraph`, a
`RegularityColoredGraph` has an arbitrary underlying simple graph and labels
only its actual edges.  The uniform decoration theorem takes the published
homogeneous-subpartition result through an explicit theorem-valued input.
-/

open Finset
open scoped SimpleGraph

namespace InducedStars.Regularity

universe u v w z

/-- The two colors allowed on vertices of a regularity type. -/
inductive TypeVertexColor where
  | green
  | blue
  deriving DecidableEq, Repr

/-- A simple graph with green/blue vertices and red/green/blue actual edges.
Nonedges are outside the domain of `edgeColor` and receive no label. -/
structure RegularityColoredGraph (V : Type u) where
  graph : SimpleGraph V
  vertexColor : V → TypeVertexColor
  edgeColor : SimpleGraph.EdgeLabeling graph EdgeColor

namespace RegularityColoredGraph

variable {V : Type u} {W : Type v} {J : RegularityColoredGraph V}
  {H : SimpleGraph W} {φ : W → V}

/-- Retrieve the color of an actual edge. -/
abbrev getEdgeColor (J : RegularityColoredGraph V) (x y : V)
    (h : J.graph.Adj x y) : EdgeColor :=
  J.edgeColor.get x y h

theorem getEdgeColor_comm (J : RegularityColoredGraph V) (x y : V)
    (h : J.graph.Adj x y) :
    J.getEdgeColor y x h.symm = J.getEdgeColor x y h :=
  SimpleGraph.EdgeLabeling.get_comm x y h.symm

/-- The allowed image behavior of an edge of the source graph. -/
def MapsEdge (J : RegularityColoredGraph V) (φ : W → V) (x y : W) : Prop :=
  (φ x = φ y ∧ J.vertexColor (φ x) = .blue) ∨
    ∃ h : J.graph.Adj (φ x) (φ y),
      J.getEdgeColor (φ x) (φ y) h = .red ∨
        J.getEdgeColor (φ x) (φ y) h = .blue

/-- The allowed image behavior of a distinct nonedge of the source graph. -/
def MapsNonedge (J : RegularityColoredGraph V) (φ : W → V) (x y : W) : Prop :=
  (φ x = φ y ∧ J.vertexColor (φ x) = .green) ∨
    ∃ h : J.graph.Adj (φ x) (φ y),
      J.getEdgeColor (φ x) (φ y) h = .red ∨
        J.getEdgeColor (φ x) (φ y) h = .green

/-- Paper: Definition 2.8 / the colored homomorphism in
`subsec:colored-graphs`.

The map is not required to be injective. The separate `x ≠ y` hypothesis
implements the coherent simple-graph reading of the published nonedge clause. -/
def IsColoredHom (H : SimpleGraph W) (J : RegularityColoredGraph V)
    (φ : W → V) : Prop :=
  ∀ ⦃x y : W⦄, x ≠ y →
    (H.Adj x y → J.MapsEdge φ x y) ∧
      (¬H.Adj x y → J.MapsNonedge φ x y)

/-- Existence of a (possibly noninjective) colored homomorphism. -/
def ColoredHomExists (H : SimpleGraph W) (J : RegularityColoredGraph V) : Prop :=
  ∃ φ : W → V, IsColoredHom H J φ

theorem IsColoredHom.map_edge (hφ : IsColoredHom H J φ)
    {x y : W} (hxy : H.Adj x y) : J.MapsEdge φ x y := by
  exact (hφ hxy.ne).1 hxy

theorem IsColoredHom.map_nonedge (hφ : IsColoredHom H J φ)
    {x y : W} (hne : x ≠ y) (hxy : ¬H.Adj x y) : J.MapsNonedge φ x y := by
  exact (hφ hne).2 hxy

theorem IsColoredHom.edge_of_ne (hφ : IsColoredHom H J φ)
    {x y : W} (hxy : H.Adj x y) (himage : φ x ≠ φ y) :
    ∃ h : J.graph.Adj (φ x) (φ y),
      J.getEdgeColor (φ x) (φ y) h = .red ∨
        J.getEdgeColor (φ x) (φ y) h = .blue := by
  rcases hφ.map_edge hxy with hcollapse | hedge
  · exact (himage hcollapse.1).elim
  · exact hedge

theorem IsColoredHom.nonedge_of_ne (hφ : IsColoredHom H J φ)
    {x y : W} (hne : x ≠ y) (hxy : ¬H.Adj x y) (himage : φ x ≠ φ y) :
    ∃ h : J.graph.Adj (φ x) (φ y),
      J.getEdgeColor (φ x) (φ y) h = .red ∨
        J.getEdgeColor (φ x) (φ y) h = .green := by
  rcases hφ.map_nonedge hne hxy with hcollapse | hedge
  · exact (himage hcollapse.1).elim
  · exact hedge

theorem IsColoredHom.edge_of_eq (hφ : IsColoredHom H J φ)
    {x y : W} (hxy : H.Adj x y) (himage : φ x = φ y) :
    J.vertexColor (φ x) = .blue := by
  rcases hφ.map_edge hxy with hcollapse | hedge
  · exact hcollapse.2
  · exact (hedge.choose.ne himage).elim

theorem IsColoredHom.nonedge_of_eq (hφ : IsColoredHom H J φ)
    {x y : W} (hne : x ≠ y) (hxy : ¬H.Adj x y) (himage : φ x = φ y) :
    J.vertexColor (φ x) = .green := by
  rcases hφ.map_nonedge hne hxy with hcollapse | hedge
  · exact hcollapse.2
  · exact (hedge.choose.ne himage).elim

theorem IsColoredHom.image_adj_of_ne (hφ : IsColoredHom H J φ)
    {x y : W} (hne : x ≠ y) (himage : φ x ≠ φ y) :
    J.graph.Adj (φ x) (φ y) := by
  by_cases hxy : H.Adj x y
  · exact (hφ.edge_of_ne hxy himage).choose
  · exact (hφ.nonedge_of_ne hne hxy himage).choose

/-- Colored homomorphisms restrict along induced graph embeddings. -/
theorem IsColoredHom.comp_embedding {X : Type w} {H' : SimpleGraph X}
    (hφ : IsColoredHom H J φ) (e : H' ↪g H) :
    IsColoredHom H' J (φ ∘ e) := by
  intro x y hxy
  have hexy : e x ≠ e y := e.injective.ne hxy
  have h := hφ hexy
  constructor
  · intro hadj
    simpa [Function.comp_apply, MapsEdge] using h.1 (e.map_rel_iff.mpr hadj)
  · intro hnonedge
    apply h.2
    intro hadj
    exact hnonedge (e.map_rel_iff.mp hadj)

/-- An isomorphism of regularity colored graphs preserves the underlying
graph, both vertex colors, and the labels of actual edges. -/
structure Iso (J : RegularityColoredGraph V) (J' : RegularityColoredGraph W) where
  graphIso : J.graph ≃g J'.graph
  map_vertexColor : ∀ x, J'.vertexColor (graphIso x) = J.vertexColor x
  map_edgeColor : ∀ x y (h : J.graph.Adj x y),
    J'.getEdgeColor (graphIso x) (graphIso y) (graphIso.map_rel_iff.mpr h) =
      J.getEdgeColor x y h

/-- A colored homomorphism can be transported through an isomorphism of its
regularity-colored target. -/
theorem IsColoredHom.map_iso {J' : RegularityColoredGraph W}
    (hφ : IsColoredHom H J φ) (e : Iso J J') :
    IsColoredHom H J' (e.graphIso ∘ φ) := by
  intro x y hxy
  constructor
  · intro hadj
    rcases hφ.map_edge hadj with hcollapse | ⟨himage, hcolor⟩
    · left
      constructor
      · exact congrArg e.graphIso hcollapse.1
      · change J'.vertexColor (e.graphIso (φ x)) = .blue
        exact (e.map_vertexColor (φ x)).trans hcollapse.2
    · right
      let himage' : J'.graph.Adj (e.graphIso (φ x)) (e.graphIso (φ y)) :=
        e.graphIso.map_rel_iff.mpr himage
      refine ⟨himage', ?_⟩
      have htransport := e.map_edgeColor (φ x) (φ y) himage
      rcases hcolor with hred | hblue
      · left
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' = .red
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' =
            J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hred
      · right
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' = .blue
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' =
            J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hblue
  · intro hnonedge
    rcases hφ.map_nonedge hxy hnonedge with hcollapse | ⟨himage, hcolor⟩
    · left
      constructor
      · exact congrArg e.graphIso hcollapse.1
      · change J'.vertexColor (e.graphIso (φ x)) = .green
        exact (e.map_vertexColor (φ x)).trans hcollapse.2
    · right
      let himage' : J'.graph.Adj (e.graphIso (φ x)) (e.graphIso (φ y)) :=
        e.graphIso.map_rel_iff.mpr himage
      refine ⟨himage', ?_⟩
      have htransport := e.map_edgeColor (φ x) (φ y) himage
      rcases hcolor with hred | hgreen
      · left
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' = .red
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' =
            J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hred
      · right
        change J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' = .green
        have ht : J'.getEdgeColor (e.graphIso (φ x)) (e.graphIso (φ y)) himage' =
            J.getEdgeColor (φ x) (φ y) himage := by
          simpa only [himage'] using htransport
        exact ht.trans hgreen

/-- A colored homomorphism can be transported through an isomorphism of its
ordinary source graph. -/
theorem IsColoredHom.comp_iso {X : Type z} {H' : SimpleGraph X}
    (hφ : IsColoredHom H J φ) (e : H' ≃g H) :
    IsColoredHom H' J (φ ∘ e) :=
  hφ.comp_embedding e.toEmbedding

end RegularityColoredGraph

section ReducedGraph

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ}

/-- The paper's threshold rule for colors of regular reduced edges. -/
noncomputable def densityEdgeColor (δ density : ℝ) : EdgeColor :=
  if density < δ then .green
  else if density ≤ 1 - δ then .red
  else .blue

theorem densityEdgeColor_eq_green_iff {δ density : ℝ}
    (_hδ : δ ≤ 1 / 2) :
    densityEdgeColor δ density = .green ↔ density < δ := by
  classical
  by_cases h : density < δ
  · simp [densityEdgeColor, h]
  · by_cases h₂ : density ≤ 1 - δ <;> simp [densityEdgeColor, h, h₂]

theorem densityEdgeColor_eq_red_iff {δ density : ℝ}
    (_hδ : δ ≤ 1 / 2) :
    densityEdgeColor δ density = .red ↔ δ ≤ density ∧ density ≤ 1 - δ := by
  classical
  by_cases h₁ : density < δ
  · have hnot : ¬(δ ≤ density ∧ density ≤ 1 - δ) := fun h =>
      (not_lt_of_ge h.1) h₁
    simp [densityEdgeColor, h₁, hnot]
  · have hd : δ ≤ density := le_of_not_gt h₁
    by_cases h₂ : density ≤ 1 - δ
    · simp [densityEdgeColor, h₁, h₂, hd]
    · simp [densityEdgeColor, h₁, h₂, hd]

theorem densityEdgeColor_eq_blue_iff {δ density : ℝ}
    (hδ : δ ≤ 1 / 2) :
    densityEdgeColor δ density = .blue ↔ 1 - δ < density := by
  classical
  by_cases h₁ : density < δ
  · have hnot : ¬(1 - δ < density) := by linarith
    simp [densityEdgeColor, h₁, hnot]
  · by_cases h₂ : density ≤ 1 - δ
    · have hnot : ¬(1 - δ < density) := not_lt_of_ge h₂
      simp [densityEdgeColor, h₁, h₂, hnot]
    · have hgt : 1 - δ < density := lt_of_not_ge h₂
      simp [densityEdgeColor, h₁, h₂, hgt]

/-- Edge labels of the reduced graph, obtained from cluster densities. -/
noncomputable def densityEdgeLabeling (P : RegularPartition G ε) (δ : ℝ) :
    SimpleGraph.EdgeLabeling P.regularPairGraph EdgeColor :=
  SimpleGraph.EdgeLabeling.mk
    (fun i j _ => densityEdgeColor δ (graphDensity G (P.clusters i) (P.clusters j)))
    (by
      intro i j _
      simp only [graphDensity_comm G (P.clusters j) (P.clusters i)])

/-- The colored reduced graph belonging to a regular partition and a choice
of green/blue vertex labels. -/
noncomputable def reducedColoredGraph (P : RegularPartition G ε) (δ : ℝ)
    (vertexColor : Fin P.clusterCount → TypeVertexColor) :
    RegularityColoredGraph (Fin P.clusterCount) where
  graph := P.regularPairGraph
  vertexColor := vertexColor
  edgeColor := densityEdgeLabeling P δ

@[simp]
theorem reducedColoredGraph_graph (P : RegularPartition G ε) (δ : ℝ)
    (vertexColor : Fin P.clusterCount → TypeVertexColor) :
    (reducedColoredGraph P δ vertexColor).graph = P.regularPairGraph :=
  rfl

@[simp]
theorem reducedColoredGraph_vertexColor (P : RegularPartition G ε) (δ : ℝ)
    (vertexColor : Fin P.clusterCount → TypeVertexColor) (i) :
    (reducedColoredGraph P δ vertexColor).vertexColor i = vertexColor i :=
  rfl

@[simp]
theorem reducedColoredGraph_getEdgeColor (P : RegularPartition G ε) (δ : ℝ)
    (vertexColor : Fin P.clusterCount → TypeVertexColor) (i j)
    (h : P.regularPairGraph.Adj i j) :
    (reducedColoredGraph P δ vertexColor).getEdgeColor i j h =
      densityEdgeColor δ (graphDensity G (P.clusters i) (P.clusters j)) :=
  rfl

theorem edgeColor_eq_green_iff (P : RegularPartition G ε) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (vertexColor) {i j} (h : P.regularPairGraph.Adj i j) :
    (reducedColoredGraph P δ vertexColor).getEdgeColor i j h = .green ↔
      graphDensity G (P.clusters i) (P.clusters j) < δ := by
  rw [reducedColoredGraph_getEdgeColor, densityEdgeColor_eq_green_iff hδ]

theorem edgeColor_eq_red_iff (P : RegularPartition G ε) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (vertexColor) {i j} (h : P.regularPairGraph.Adj i j) :
    (reducedColoredGraph P δ vertexColor).getEdgeColor i j h = .red ↔
      δ ≤ graphDensity G (P.clusters i) (P.clusters j) ∧
        graphDensity G (P.clusters i) (P.clusters j) ≤ 1 - δ := by
  rw [reducedColoredGraph_getEdgeColor, densityEdgeColor_eq_red_iff hδ]

theorem edgeColor_eq_blue_iff (P : RegularPartition G ε) {δ : ℝ}
    (hδ : δ ≤ 1 / 2) (vertexColor) {i j} (h : P.regularPairGraph.Adj i j) :
    (reducedColoredGraph P δ vertexColor).getEdgeColor i j h = .blue ↔
      1 - δ < graphDensity G (P.clusters i) (P.clusters j) := by
  rw [reducedColoredGraph_getEdgeColor, densityEdgeColor_eq_blue_iff hδ]

end ReducedGraph

section SelectedConfiguration

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Select one homogeneous child for each source vertex, using its source
index as a child index.  This is the fibre-selection step in the published
proof of BTW Lemma 2.9; `Fin.castLE` is injective, so vertices collapsed to
the same parent receive distinct children. -/
noncomputable def selectedEmbeddingConfiguration
    {η δ μ ε' : ℝ} {ℓ f : ℕ} (P : RegularPartition G η)
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hμ : 0 < μ) (hε' : 0 < ε')
    (hηδ : η ≤ δ / 2) (hημ : η ≤ μ)
    (hημε' : η ≤ μ * ε') (h2η : 2 * η ≤ ε')
    (S : ∀ i, HomogeneousSubpartition G (P.clusters i) μ ε' ℓ)
    (hparent : ∀ i, μ⁻¹ ≤ ((P.clusters i).card : ℝ))
    (vertexColor : Fin P.clusterCount → TypeVertexColor)
    (hsparse : ∀ i, vertexColor i = .green → (S i).IsSparse)
    (hdense : ∀ i, vertexColor i = .blue → (S i).IsDense)
    (hf : f ≤ ℓ) (H : SimpleGraph (Fin f)) (φ : Fin f → Fin P.clusterCount)
    (hφ : RegularityColoredGraph.IsColoredHom H
      (reducedColoredGraph P δ vertexColor) φ) :
    InducedEmbeddingConfiguration G H ε' (δ / 2) where
  parts x := (S (φ x)).parts (Fin.castLE hf x)
  parts_pairwiseDisjoint := by
    intro x _ y _ hxy
    by_cases himage : φ x = φ y
    · have hparts : (S (φ x)).parts = (S (φ y)).parts :=
        congrArg (fun i => (S i).parts) himage
      have hchild : Fin.castLE hf x ≠ Fin.castLE hf y :=
        fun h => hxy (Fin.castLE_injective hf h)
      change Disjoint ((S (φ x)).parts (Fin.castLE hf x))
        ((S (φ y)).parts (Fin.castLE hf y))
      rw [← hparts]
      exact (S (φ x)).parts_disjoint hchild
    · exact (P.clusters_disjoint himage).mono
        ((S (φ x)).parts_subset _) ((S (φ y)).parts_subset _)
  parts_nonempty x := (S (φ x)).parts_nonempty hμ (hparent (φ x)) _
  regular := by
    intro x y hxy
    by_cases himage : φ x = φ y
    · have hparts : (S (φ x)).parts = (S (φ y)).parts :=
        congrArg (fun i => (S i).parts) himage
      have hchild : Fin.castLE hf x ≠ Fin.castLE hf y :=
        fun h => hxy (Fin.castLE_injective hf h)
      simpa only [← hparts] using (S (φ x)).regular hchild
    · have hadj : P.regularPairGraph.Adj (φ x) (φ y) :=
        hφ.image_adj_of_ne hxy himage
      have hparentReg : IsRegularPair G η (P.clusters (φ x)) (P.clusters (φ y)) :=
        (P.regularPairGraph_adj (φ x) (φ y)).mp hadj |>.2
      exact hparentReg.slice G
        ((S (φ x)).parts_subset _) ((S (φ y)).parts_subset _)
        ((S (φ x)).card_lower _) ((S (φ y)).card_lower _)
        hμ.le hε'.le hημε' h2η
  edge_density := by
    intro x y hxy
    by_cases himage : φ x = φ y
    · have hparts : (S (φ x)).parts = (S (φ y)).parts :=
        congrArg (fun i => (S i).parts) himage
      have hchild : Fin.castLE hf x ≠ Fin.castLE hf y :=
        fun h => hxy.ne (Fin.castLE_injective hf h)
      have hblue : vertexColor (φ x) = .blue := by
        simpa only [reducedColoredGraph_vertexColor] using hφ.edge_of_eq hxy himage
      have hd := hdense (φ x) hblue hchild
      have hd' : 1 / 2 ≤
          graphDensity G ((S (φ x)).parts (Fin.castLE hf x))
            ((S (φ y)).parts (Fin.castLE hf y)) := by
        simpa only [← hparts] using hd
      linarith
    · obtain ⟨hadj, hcolor⟩ := hφ.edge_of_ne hxy himage
      have hparentReg : IsRegularPair G η (P.clusters (φ x)) (P.clusters (φ y)) :=
        (P.regularPairGraph_adj (φ x) (φ y)).mp hadj |>.2
      have hclose := hparentReg.density_subsets G
        (A' := (S (φ x)).parts (Fin.castLE hf x))
        (B' := (S (φ y)).parts (Fin.castLE hf y))
        ((S (φ x)).parts_subset (Fin.castLE hf x))
        ((S (φ y)).parts_subset (Fin.castLE hf y))
        ((S (φ x)).card_lower (Fin.castLE hf x))
        ((S (φ y)).card_lower (Fin.castLE hf y)) hημ
      have hlower :
          graphDensity G (P.clusters (φ x)) (P.clusters (φ y)) -
              graphDensity G ((S (φ x)).parts (Fin.castLE hf x))
                ((S (φ y)).parts (Fin.castLE hf y)) ≤ η := by
        exact (le_abs_self _).trans (by simpa [abs_sub_comm] using hclose)
      rcases hcolor with hred | hblue
      · have hp := (edgeColor_eq_red_iff P hδhalf.le vertexColor hadj).mp hred
        linarith
      · have hp := (edgeColor_eq_blue_iff P hδhalf.le vertexColor hadj).mp hblue
        linarith
  nonedge_density := by
    intro x y hxy hnonedge
    by_cases himage : φ x = φ y
    · have hparts : (S (φ x)).parts = (S (φ y)).parts :=
        congrArg (fun i => (S i).parts) himage
      have hchild : Fin.castLE hf x ≠ Fin.castLE hf y :=
        fun h => hxy (Fin.castLE_injective hf h)
      have hgreen : vertexColor (φ x) = .green := by
        simpa only [reducedColoredGraph_vertexColor] using
          hφ.nonedge_of_eq hxy hnonedge himage
      have hs := hsparse (φ x) hgreen hchild
      have hs' :
          graphDensity G ((S (φ x)).parts (Fin.castLE hf x))
            ((S (φ y)).parts (Fin.castLE hf y)) < 1 / 2 := by
        simpa only [← hparts] using hs
      linarith
    · obtain ⟨hadj, hcolor⟩ := hφ.nonedge_of_ne hxy hnonedge himage
      have hparentReg : IsRegularPair G η (P.clusters (φ x)) (P.clusters (φ y)) :=
        (P.regularPairGraph_adj (φ x) (φ y)).mp hadj |>.2
      have hclose := hparentReg.density_subsets G
        (A' := (S (φ x)).parts (Fin.castLE hf x))
        (B' := (S (φ y)).parts (Fin.castLE hf y))
        ((S (φ x)).parts_subset (Fin.castLE hf x))
        ((S (φ y)).parts_subset (Fin.castLE hf y))
        ((S (φ x)).card_lower (Fin.castLE hf x))
        ((S (φ y)).card_lower (Fin.castLE hf y)) hημ
      have hupper :
          graphDensity G ((S (φ x)).parts (Fin.castLE hf x))
                ((S (φ y)).parts (Fin.castLE hf y)) -
              graphDensity G (P.clusters (φ x)) (P.clusters (φ y)) ≤ η :=
        (le_abs_self _).trans hclose
      rcases hcolor with hred | hgreen
      · have hp := (edgeColor_eq_red_iff P hδhalf.le vertexColor hadj).mp hred
        linarith
      · have hp := (edgeColor_eq_green_iff P hδhalf.le vertexColor hadj).mp hgreen
        linarith

end SelectedConfiguration

section UniformDecoration

/-- The uniform selected-image argument, parameterized by a locally proved
cluster-family embedding lemma and an explicit homogeneous-subpartition input.

The returned tolerance and natural cluster-size threshold depend only on
`(δ, ℓ)` and the supplied `(δ / 2, ℓ)` embedding tolerance.  In particular,
neither depends on the total number of clusters in the input partition.
This is the proof-local uniformity hidden in the published proof of BTW Lemma
2.9 and made explicit in paper Lemma `lemma:type-lemma`. -/
theorem existsTypeVertexColors_of_largeRegularPartition_of_embedding_withInput
    (input : DenseGraph.HomogeneousSubpartitionInput.{u})
    (δ : ℝ) (ℓ : ℕ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (εEmbed : ℝ) (hεEmbed : 0 < εEmbed)
    (hembed : ∀ (f : ℕ), f ≤ ℓ →
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (H : SimpleGraph (Fin f)),
          InducedEmbeddingConfiguration G H εEmbed (δ / 2) →
            InducedEmbeds H G) :
    ∃ εStar : ℝ, 0 < εStar ∧ ∃ clusterSizeThreshold : ℕ,
      ∀ (η : ℝ), 0 < η → η < εStar →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj]
          (P : RegularPartition G η),
            clusterSizeThreshold ≤ P.clusterSize →
              ∃ vertexColor : Fin P.clusterCount → TypeVertexColor,
                ∀ (f : ℕ), f ≤ ℓ → ∀ H : SimpleGraph (Fin f),
                  RegularityColoredGraph.ColoredHomExists H
                      (reducedColoredGraph P δ vertexColor) →
                    InducedEmbeds H G := by
  classical
  let εChild : ℝ := min εEmbed 1
  have hεChild : 0 < εChild := by
    simp only [εChild, lt_min_iff]
    exact ⟨hεEmbed, zero_lt_one⟩
  have hεChildEmbed : εChild ≤ εEmbed := min_le_left _ _
  have hεChildOne : εChild ≤ 1 := min_le_right _ _
  obtain ⟨μ, hμ, hsubpartition⟩ :=
    input.inside ℓ εChild hεChild
  let εStar : ℝ := min (δ / 2) (min (μ * εChild) (εChild / 2))
  have hεStar : 0 < εStar := by
    simp only [εStar, lt_min_iff]
    exact ⟨by positivity, mul_pos hμ hεChild, by positivity⟩
  let clusterSizeThreshold : ℕ := ⌈μ⁻¹⌉₊
  refine ⟨εStar, hεStar, clusterSizeThreshold, ?_⟩
  intro η hη hηStar V _ _ G _ P hcluster
  have hηδ : η ≤ δ / 2 :=
    (le_of_lt hηStar).trans (min_le_left _ _)
  have hημεChild : η ≤ μ * εChild :=
    (le_of_lt hηStar).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηεChildHalf : η ≤ εChild / 2 :=
    (le_of_lt hηStar).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hημ : η ≤ μ := by
    calc
      η ≤ μ * εChild := hημεChild
      _ ≤ μ * 1 := by gcongr
      _ = μ := mul_one μ
  have h2η : 2 * η ≤ εChild := by linarith
  have hparent : ∀ i, μ⁻¹ ≤ ((P.clusters i).card : ℝ) := by
    intro i
    calc
      μ⁻¹ ≤ (clusterSizeThreshold : ℝ) := Nat.le_ceil _
      _ ≤ (P.clusterSize : ℝ) := by exact_mod_cast hcluster
      _ = ((P.clusters i).card : ℝ) := by rw [P.cluster_card_eq i]
  have hexists : ∀ i, ∃ S : HomogeneousSubpartition
      G (P.clusters i) μ εChild ℓ, S.IsSparse ∨ S.IsDense := by
    intro i
    exact hsubpartition G (P.clusters i) (hparent i)
  choose S hS using hexists
  let vertexColor : Fin P.clusterCount → TypeVertexColor := fun i =>
    if (S i).IsSparse then .green else .blue
  have hsparse : ∀ i, vertexColor i = .green → (S i).IsSparse := by
    intro i hi
    by_cases hs : (S i).IsSparse
    · exact hs
    · simp [vertexColor, hs] at hi
  have hdense : ∀ i, vertexColor i = .blue → (S i).IsDense := by
    intro i hi
    by_cases hs : (S i).IsSparse
    · simp [vertexColor, hs] at hi
    · exact (hS i).resolve_left hs
  refine ⟨vertexColor, ?_⟩
  intro f hf H hhom
  obtain ⟨φ, hφ⟩ := hhom
  let Cchild := selectedEmbeddingConfiguration P hδ hδhalf hμ hεChild
    hηδ hημ hημεChild h2η S hparent vertexColor hsparse hdense hf H φ hφ
  exact hembed f hf G H (Cchild.mono hεChildEmbed)

/-- The axiom-free uniform vertex-decoration conclusion needed by the later
Type Lemma, parameterized by the exact homogeneous-subpartition input.

For fixed `(δ, ℓ)`, both the parent regularity tolerance and the lower bound
on every nonexceptional cluster size are chosen before the input partition;
in particular, neither depends on its total number of clusters.  The proof
combines the supplied BTW-shaped input with the locally proved cluster-family
embedding theorem without adding an assumption for the paper-local adapter. -/
theorem existsTypeVertexColors_of_largeRegularPartition_withInput
    (input : DenseGraph.HomogeneousSubpartitionInput.{u})
    (δ : ℝ) (ℓ : ℕ) (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    ∃ εStar : ℝ, 0 < εStar ∧ ∃ clusterSizeThreshold : ℕ,
      ∀ (η : ℝ), 0 < η → η < εStar →
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj]
          (P : RegularPartition G η),
            clusterSizeThreshold ≤ P.clusterSize →
              ∃ vertexColor : Fin P.clusterCount → TypeVertexColor,
                ∀ (f : ℕ), f ≤ ℓ → ∀ H : SimpleGraph (Fin f),
                  RegularityColoredGraph.ColoredHomExists H
                      (reducedColoredGraph P δ vertexColor) →
                    InducedEmbeds H G := by
  classical
  obtain ⟨εEmbed, hεEmbed, hembed⟩ :=
    exists_inducedEmbedding_tolerance (δ / 2) (by positivity) (by linarith) ℓ
  exact existsTypeVertexColors_of_largeRegularPartition_of_embedding_withInput
    input δ ℓ hδ hδhalf εEmbed hεEmbed (by
      intro f hf V _ _ G _ H C
      exact hembed f hf G H C)

end UniformDecoration

section PaperType

variable {V : Type u} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Paper: Definition `dfn:type`.

The reduced graph and all its edge labels are canonical functions of the
partition and `δ`; only the green/blue vertex decoration is additional data.
The last field is exactly the paper's induced-embedding conclusion for every
graph on at most `ℓ` vertices. -/
structure RegularityType (ε δ : ℝ) (ℓ : ℕ) where
  epsilon_pos : 0 < ε
  epsilon_lt_half : ε < 1 / 2
  delta_pos : 0 < δ
  delta_lt_half : δ < 1 / 2
  partition : RegularPartition G ε
  vertexColor : Fin partition.clusterCount → TypeVertexColor
  inducedEmbedding :
    ∀ (f : ℕ), f ≤ ℓ → ∀ H : SimpleGraph (Fin f),
      RegularityColoredGraph.ColoredHomExists H
          (reducedColoredGraph partition δ vertexColor) →
        InducedEmbeds H G

namespace RegularityType

variable {G : SimpleGraph V} [DecidableRel G.Adj] {ε δ : ℝ} {ℓ : ℕ}

/-- The colored reduced graph carried by a paper Type. -/
noncomputable abbrev coloredGraph (T : RegularityType G ε δ ℓ) :=
  reducedColoredGraph T.partition δ T.vertexColor

end RegularityType

end PaperType

/-- Induced containment is invariant under isomorphisms of source and host. -/
theorem inducedEmbeds_congr {V : Type u} {W : Type v} {X : Type w} {Y : Type z}
    {A : SimpleGraph V} {A' : SimpleGraph W}
    {B : SimpleGraph X} {B' : SimpleGraph Y}
    (eA : A ≃g A') (eB : B ≃g B') :
    InducedEmbeds A B ↔ InducedEmbeds A' B' := by
  constructor
  · intro h
    exact eA.symm.isIndContained.trans (h.trans eB.isIndContained)
  · intro h
    exact eA.isIndContained.trans (h.trans eB.symm.isIndContained)

end InducedStars.Regularity
