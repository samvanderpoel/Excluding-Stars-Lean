import InducedStars.PriorInstances
import InducedStars.Regularity.TypeCore

/-!
# Prior-literature compatibility layer for colored regularity types

This module supplies the project's published Böttcher--Taraz--Würfl input to
the axiom-free construction in `InducedStars.Regularity.TypeCore`.  The public
theorem names and signatures below are retained for downstream compatibility.
-/

namespace InducedStars.Regularity

universe u

/-- Compatibility form of the uniform selected-image argument, using the
project's published homogeneous-subpartition input. -/
theorem existsTypeVertexColors_of_largeRegularPartition_of_embedding
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
                    InducedEmbeds H G :=
  existsTypeVertexColors_of_largeRegularPartition_of_embedding_withInput
    PriorInstances.homogeneousSubpartitionInput
    δ ℓ hδ hδhalf εEmbed hεEmbed hembed

/-- The uniform vertex-decoration conclusion needed by the later Type Lemma.

For fixed `(δ, ℓ)`, both the parent regularity tolerance and the lower bound
on every nonexceptional cluster size are chosen before the input partition;
in particular, neither depends on its total number of clusters.  This keeps
the original project-facing statement while supplying the published BTW
Lemma 2.5 input through `InducedStars.PriorInstances`. -/
theorem existsTypeVertexColors_of_largeRegularPartition
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
                    InducedEmbeds H G :=
  existsTypeVertexColors_of_largeRegularPartition_withInput
    PriorInstances.homogeneousSubpartitionInput δ ℓ hδ hδhalf

end InducedStars.Regularity
