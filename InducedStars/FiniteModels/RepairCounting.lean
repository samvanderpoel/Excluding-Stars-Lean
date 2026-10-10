import InducedStars.FiniteModels.EntropyAsymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Counting through a bounded-distance repair map

This file isolates the finite counting argument used after exact-edge repair.
A map from a graph family `A` into a target family `B` has fibers contained
in graph Hamming balls whenever every input is within a fixed edit radius of
its image.  Summing the fiber bounds gives the standard multiplicative loss.
-/

noncomputable section

open Set
open scoped BigOperators

namespace InducedStars

/-- The inputs in `A` which a repair map sends to the graph `K`. -/
noncomputable def graphRepairFiber {n : ℕ} (A : Finset (SimpleGraph (Fin n)))
    (repair : SimpleGraph (Fin n) → SimpleGraph (Fin n))
    (K : SimpleGraph (Fin n)) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact A.filter fun G ↦ repair G = K

@[simp]
theorem mem_graphRepairFiber {n : ℕ}
    {A : Finset (SimpleGraph (Fin n))}
    {repair : SimpleGraph (Fin n) → SimpleGraph (Fin n)}
    {G K : SimpleGraph (Fin n)} :
    G ∈ graphRepairFiber A repair K ↔ G ∈ A ∧ repair G = K := by
  classical
  simp [graphRepairFiber]

/-- Every fiber of a radius-`r` graph repair map is bounded by the standard
Hamming-ball volume. -/
theorem graphRepairFiber_card_le_hammingBallVolume {n r : ℕ}
    (A : Finset (SimpleGraph (Fin n)))
    (repair : SimpleGraph (Fin n) → SimpleGraph (Fin n))
    (hDist : ∀ G ∈ A, graphEditDistance G (repair G) ≤ r)
    (K : SimpleGraph (Fin n)) :
    (graphRepairFiber A repair K).card ≤
      hammingBallVolume (completeEdgeCount n) r := by
  classical
  calc
    (graphRepairFiber A repair K).card ≤ (graphHammingBall K r).card := by
      apply Finset.card_le_card
      intro G hG
      rw [mem_graphRepairFiber] at hG
      rw [mem_graphHammingBall, graphEditDistance_comm, ← hG.2]
      exact hDist G hG.1
    _ ≤ hammingBallVolume (completeEdgeCount n) r := by
      exact graphHammingBall_card_le_hammingBallVolume K

/-- A bounded-distance repair map into `B` loses at most one graph Hamming
ball per target graph. -/
theorem card_le_card_mul_hammingBallVolume_of_graphRepair {n r : ℕ}
    (A B : Finset (SimpleGraph (Fin n)))
    (repair : SimpleGraph (Fin n) → SimpleGraph (Fin n))
    (hMap : ∀ G ∈ A, repair G ∈ B)
    (hDist : ∀ G ∈ A, graphEditDistance G (repair G) ≤ r) :
    A.card ≤ B.card * hammingBallVolume (completeEdgeCount n) r := by
  classical
  let fiber : SimpleGraph (Fin n) → Finset (SimpleGraph (Fin n)) :=
    graphRepairFiber A repair
  calc
    A.card ≤ (B.biUnion fiber).card := by
      apply Finset.card_le_card
      intro G hG
      apply Finset.mem_biUnion.mpr
      exact ⟨repair G, hMap G hG,
        (mem_graphRepairFiber).mpr ⟨hG, rfl⟩⟩
    _ ≤ B.card * hammingBallVolume (completeEdgeCount n) r := by
      apply Finset.card_biUnion_le_card_mul
      intro K hK
      exact graphRepairFiber_card_le_hammingBallVolume A repair hDist K

end InducedStars
