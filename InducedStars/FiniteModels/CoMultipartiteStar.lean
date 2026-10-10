import DenseGraph.FiniteModels.Multipartite
import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.Graphon.Star
import InducedStars.Regularity.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Co-multipartite graphs exclude large induced stars

This is the project-specific bridge from the reusable finite partition
notion to the canonical induced star.  With only `k - 1` clique parts, two
of the `k` leaves of any proposed induced copy must lie in the same clique,
contradicting their required nonadjacency.
-/

noncomputable section

namespace InducedStars

universe u

open DenseGraph

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every co-`(k-1)`-partite finite graph is induced-`K_{1,k}`-free. -/
theorem coMultipartite_not_inducedEmbeds_inducedStar
    {k : ℕ} (hk : 1 ≤ k) {G : SimpleGraph V}
    (hG : IsCoMultipartite G (k - 1)) :
    ¬Regularity.InducedEmbeds (inducedStar k) G := by
  rintro ⟨f⟩
  rcases hG with ⟨C⟩
  let label : Fin k → Fin (k - 1) := fun i ↦
    C.partIndex (f i.succ)
  have hcard : Fintype.card (Fin (k - 1)) < Fintype.card (Fin k) := by
    simp only [Fintype.card_fin]
    omega
  obtain ⟨i, j, hij, hlabel⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt label hcard
  have hi : f i.succ ∈ C.parts (label i) :=
    C.mem_partIndex (f i.succ)
  have hj0 : f j.succ ∈ C.parts (label j) :=
    C.mem_partIndex (f j.succ)
  have hj : f j.succ ∈ C.parts (label i) := by
    rw [hlabel]
    exact hj0
  have hverts : f i.succ ≠ f j.succ :=
    f.injective.ne ((Fin.succ_injective k).ne hij)
  have hadjG : G.Adj (f i.succ) (f j.succ) :=
    C.isClique (label i) hi hj hverts
  have hadjStar : (inducedStar k).Adj i.succ j.succ :=
    f.map_rel_iff.mp hadjG
  exact inducedStar_leaf_nonadj_leaf i j hadjStar

/-- Membership form for the standard finite induced-free family. -/
theorem coMultipartite_mem_inducedFreeGraphFinset
    {k n : ℕ} (hk : 1 ≤ k) {G : SimpleGraph (Fin n)}
    (hG : IsCoMultipartite G (k - 1)) :
    G ∈ inducedFreeGraphFinset (inducedStar k) n := by
  rw [mem_inducedFreeGraphFinset]
  exact coMultipartite_not_inducedEmbeds_inducedStar hk hG

end InducedStars
