import InducedStars.FiniteModels.Normalization
import InducedStars.Graphon.Densities
import InducedStars.Regularity.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# General finite labeled graph families

This file records the reusable finite combinatorial layer for an arbitrary
forbidden induced graph `H`.  Graphs are labeled on `Fin n`; there is no
quotient by graph isomorphism.
-/

namespace InducedStars

/-- A finite vertex type gives every graph a finite edge type.  This local
instance lets the finite-model files use Mathlib's canonical `edgeFinset`
notation without adding a project-wide typeclass choice. -/
noncomputable local instance graphFamiliesEdgeSetFintype {n : ℕ}
    (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-! ## Edge counts -/

/-- A labeled graph on `Fin n` has at most `n.choose 2` edges. -/
theorem card_edgeFinset_le_completeEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    G.edgeFinset.card ≤ completeEdgeCount n := by
  classical
  simpa [completeEdgeCount] using
    (SimpleGraph.card_edgeFinset_le_card_choose_two (G := G))

/-- The neutral edge finset used by the graphon layer has the same elements,
and hence the same cardinality, as Mathlib's `edgeFinset`. -/
theorem finiteGraphEdges_card_eq_edgeFinset_card {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (finiteGraphEdges G).card = G.edgeFinset.card := by
  congr 1

/-! ## Induced-free labeled graph families -/

/-- The finite family of all labeled `H`-induced-free graphs on `Fin n`. -/
noncomputable def inducedFreeGraphFinset {h : ℕ}
    (H : SimpleGraph (Fin h)) (n : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun G ↦ ¬Regularity.InducedEmbeds H G

@[simp] theorem mem_inducedFreeGraphFinset {h n : ℕ}
    {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)} :
    G ∈ inducedFreeGraphFinset H n ↔ ¬Regularity.InducedEmbeds H G := by
  classical
  simp [inducedFreeGraphFinset]

/-- The finite family of all labeled `H`-induced-free graphs on `Fin n`
having exactly `m` edges. -/
noncomputable def inducedFreeGraphFinsetWithEdges {h : ℕ}
    (H : SimpleGraph (Fin h)) (n m : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (inducedFreeGraphFinset H n).filter fun G ↦ G.edgeFinset.card = m

@[simp] theorem mem_inducedFreeGraphFinsetWithEdges {h n m : ℕ}
    {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)} :
    G ∈ inducedFreeGraphFinsetWithEdges H n m ↔
      ¬Regularity.InducedEmbeds H G ∧ G.edgeFinset.card = m := by
  classical
  simp [inducedFreeGraphFinsetWithEdges]

/-- Instance-free membership form using the neutral finite edge set. -/
theorem mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges {h n m : ℕ}
    {H : SimpleGraph (Fin h)} {G : SimpleGraph (Fin n)} :
    G ∈ inducedFreeGraphFinsetWithEdges H n m ↔
      ¬Regularity.InducedEmbeds H G ∧ (finiteGraphEdges G).card = m := by
  rw [mem_inducedFreeGraphFinsetWithEdges,
    finiteGraphEdges_card_eq_edgeFinset_card]

/-- The number of labeled `H`-induced-free graphs on `Fin n` with exactly
`m` edges. -/
noncomputable def inducedFreeGraphCountWithEdges {h : ℕ}
    (H : SimpleGraph (Fin h)) (n m : ℕ) : ℕ :=
  (inducedFreeGraphFinsetWithEdges H n m).card

@[simp] theorem inducedFreeGraphCountWithEdges_eq_card {h n m : ℕ}
    (H : SimpleGraph (Fin h)) :
    inducedFreeGraphCountWithEdges H n m =
      (inducedFreeGraphFinsetWithEdges H n m).card :=
  rfl

end InducedStars
