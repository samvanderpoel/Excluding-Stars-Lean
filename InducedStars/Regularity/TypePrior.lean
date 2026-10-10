import InducedStars.PriorInstances
import InducedStars.Regularity.TypeCore

/-!
# Published input for colored regularity types

This module supplies the published Böttcher--Taraz--Würfl homogeneous
subpartition input to the construction in `InducedStars.Regularity.TypeCore`.
The resulting uniform vertex-decoration theorem is used in the proof of
`lemma:type-lemma`.
-/

namespace InducedStars.Regularity

universe u

/-- The uniform vertex-decoration conclusion needed by the later Type Lemma.

For fixed `(δ, ℓ)`, both the parent regularity tolerance and the lower bound
on every nonexceptional cluster size are chosen before the input partition;
in particular, neither depends on its total number of clusters. The published
Böttcher--Taraz--Würfl Lemma 2.5 input is supplied through
`InducedStars.PriorInstances`. -/
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
