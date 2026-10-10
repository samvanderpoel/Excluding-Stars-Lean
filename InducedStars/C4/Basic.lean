import DenseGraph.FiniteModels.SplitGraphs
import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.FiniteModels.Uniform

/-!
# Canonical induced-C4 and exact split-graph families

All families are labeled on `Fin n` and use exactly `m` unordered edges.
The split predicate retains a genuine independent/clique partition.
-/

noncomputable section
namespace InducedStars
open DenseGraph

/-- The canonical four-cycle, in Mathlib's cyclic `Fin 4` labeling. -/
def inducedC4 : SimpleGraph (Fin 4) := SimpleGraph.cycleGraph 4

instance : DecidableRel inducedC4.Adj := by
  unfold inducedC4
  infer_instance

@[simp] theorem inducedC4_eq_cycleGraph : inducedC4 = SimpleGraph.cycleGraph 4 := rfl

theorem splitGraph_not_inducedEmbeds_C4 {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : IsSplitGraph G) : ¬Regularity.InducedEmbeds inducedC4 G :=
  hG.no_induced_cycleFour

def inducedC4FreeGraphFinsetWithEdges (n m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  inducedFreeGraphFinsetWithEdges inducedC4 n m

def inducedC4FreeGraphCountWithEdges (n m : ℕ) : ℕ :=
  (inducedC4FreeGraphFinsetWithEdges n m).card

/-- Exact split family; the edge set is the same neutral finite set used by
the graphon and generic induced-free counting layers. -/
def splitGraphFinsetWithEdges (n m : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun G ↦ IsSplitGraph G ∧ (finiteGraphEdges G).card = m

def splitGraphCountWithEdges (n m : ℕ) : ℕ := (splitGraphFinsetWithEdges n m).card

@[simp] theorem mem_inducedC4FreeGraphFinsetWithEdges {n m : ℕ}
    {G : SimpleGraph (Fin n)} : G ∈ inducedC4FreeGraphFinsetWithEdges n m ↔
      ¬Regularity.InducedEmbeds inducedC4 G ∧ (finiteGraphEdges G).card = m :=
  mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges

@[simp] theorem mem_splitGraphFinsetWithEdges {n m : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ splitGraphFinsetWithEdges n m ↔ IsSplitGraph G ∧ (finiteGraphEdges G).card = m := by
  classical
  simp [splitGraphFinsetWithEdges]

theorem splitGraphFinsetWithEdges_subset_inducedC4Free (n m : ℕ) :
    splitGraphFinsetWithEdges n m ⊆ inducedC4FreeGraphFinsetWithEdges n m := by
  intro G hG
  obtain ⟨hG, hm⟩ := mem_splitGraphFinsetWithEdges.mp hG
  exact mem_inducedC4FreeGraphFinsetWithEdges.mpr ⟨splitGraph_not_inducedEmbeds_C4 hG, hm⟩

theorem splitGraphCountWithEdges_le_inducedC4Free (n m : ℕ) :
    splitGraphCountWithEdges n m ≤ inducedC4FreeGraphCountWithEdges n m :=
  Finset.card_le_card (splitGraphFinsetWithEdges_subset_inducedC4Free n m)

end InducedStars
