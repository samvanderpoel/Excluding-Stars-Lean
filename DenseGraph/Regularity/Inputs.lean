import InducedStars.Regularity.Basic

/-!
# Abstract inputs for induced regularity

This module records the exact theorem-valued input needed by the colored
regularity-type construction.  It contains no project-specific assumptions;
projects supply a value of `HomogeneousSubpartitionInput` from their chosen
source.
-/

open Finset

namespace DenseGraph

open InducedStars.Regularity

universe u

/-- The exact global homogeneous-subpartition conclusion used from
Böttcher--Taraz--Würfl Lemma 2.5.

This is data, not an axiom or a typeclass.  Keeping it as an explicit
theorem-valued input makes the regularity-type core independent of any
particular prior-literature module. -/
structure HomogeneousSubpartitionInput : Prop where
  homogeneousSubpartition :
    ∀ (q : ℕ) (ε : ℝ), 0 < ε →
      ∃ μ : ℝ, 0 < μ ∧
        ∀ {V : Type u} [Fintype V] [DecidableEq V]
          (G : SimpleGraph V) [DecidableRel G.Adj],
            μ⁻¹ ≤ (Fintype.card V : ℝ) →
              ∃ S : HomogeneousSubpartition G Finset.univ μ ε q,
                S.IsSparse ∨ S.IsDense

namespace HomogeneousSubpartitionInput

/-- Apply a global homogeneous-subpartition input to the graph induced by a
finite parent set, then transport the resulting subpartition back to the
ambient graph.  This is the axiom-free subtype adapter formerly tied directly
to the project's prior-literature declaration. -/
theorem inside (input : HomogeneousSubpartitionInput.{u})
    (q : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (parent : Finset V),
          μ⁻¹ ≤ (parent.card : ℝ) →
            ∃ S : HomogeneousSubpartition G parent μ ε q,
              S.IsSparse ∨ S.IsDense := by
  obtain ⟨μ, hμ, hglobal⟩ := input.homogeneousSubpartition q ε hε
  refine ⟨μ, hμ, ?_⟩
  intro V _ _ G _ parent hparent
  have hcard : Fintype.card ↥(↑parent : Set V) = parent.card := by
    change Fintype.card ↥parent = parent.card
    exact Fintype.card_coe parent
  obtain ⟨S, hS⟩ := hglobal (G.induce (↑parent : Set V)) (by
    rw [hcard]
    exact hparent)
  refine ⟨InducedStars.Regularity.liftHomogeneousSubpartition G parent S, ?_⟩
  rcases hS with hS | hS
  · exact Or.inl ((InducedStars.Regularity.liftHomogeneousSubpartition_isSparse_iff
      G parent S).mpr hS)
  · exact Or.inr ((InducedStars.Regularity.liftHomogeneousSubpartition_isDense_iff
      G parent S).mpr hS)

end HomogeneousSubpartitionInput

end DenseGraph
