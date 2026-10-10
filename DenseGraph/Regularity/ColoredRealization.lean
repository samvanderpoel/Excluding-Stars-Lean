import InducedStars.Regularity.TypeCore

/-!
# Realizations of complete colored templates

Missing pairs in a partial template impose no colored-homomorphism condition.
The realization implication therefore explicitly assumes completeness.
-/

namespace DenseGraph
open InducedStars InducedStars.Regularity

variable {V W : Type*}

/-- Actual blue pairs are edges and actual green pairs are nonedges.
Red pairs impose no constraint. For a partial template this condition alone
does not transfer induced-subgraph exclusion. -/
def IsColoredRealization (J : RegularityColoredGraph V) (G : SimpleGraph V) : Prop :=
  ∀ x y (h : J.graph.Adj x y),
    (J.getEdgeColor x y h = .blue → G.Adj x y) ∧
      (J.getEdgeColor x y h = .green → ¬G.Adj x y)

/-- An actual induced embedding in a realization of a complete colored
template gives a colored homomorphism, with exactly the same vertex map. -/
theorem coloredHom_of_embedding_of_complete
    (J : RegularityColoredGraph V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hcomplete : J.graph = ⊤) (hreal : IsColoredRealization J G)
    (f : H ↪g G) : RegularityColoredGraph.IsColoredHom H J f := by
  intro x y hxy
  have hJ : J.graph.Adj (f x) (f y) := by
    rw [hcomplete]
    exact f.injective.ne hxy
  constructor
  · intro hedge
    apply Or.inr
    refine ⟨hJ, ?_⟩
    cases hc : J.getEdgeColor (f x) (f y) hJ with
    | red => exact Or.inl rfl
    | blue => exact Or.inr rfl
    | green => exact False.elim ((hreal _ _ hJ).2 hc (f.map_rel_iff.mpr hedge))
  · intro hnonedge
    apply Or.inr
    refine ⟨hJ, ?_⟩
    cases hc : J.getEdgeColor (f x) (f y) hJ with
    | red => exact Or.inl rfl
    | green => exact Or.inr rfl
    | blue => exact False.elim (hnonedge (f.map_rel_iff.mp ((hreal _ _ hJ).1 hc)))

theorem coloredHomExists_of_inducedEmbeds_of_complete
    (J : RegularityColoredGraph V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hcomplete : J.graph = ⊤) (hreal : IsColoredRealization J G)
    (hembed : InducedEmbeds H G) : RegularityColoredGraph.ColoredHomExists H J := by
  obtain ⟨f⟩ := hembed
  exact ⟨f, coloredHom_of_embedding_of_complete J G H hcomplete hreal f⟩

theorem not_inducedEmbeds_of_complete_realization
    (J : RegularityColoredGraph V) (G : SimpleGraph V) (H : SimpleGraph W)
    (hcomplete : J.graph = ⊤) (hreal : IsColoredRealization J G)
    (hfree : ¬RegularityColoredGraph.ColoredHomExists H J) : ¬InducedEmbeds H G :=
  fun hembed ↦ hfree (coloredHomExists_of_inducedEmbeds_of_complete J G H
    hcomplete hreal hembed)

end DenseGraph
