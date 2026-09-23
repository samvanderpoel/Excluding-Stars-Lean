import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.Graphon.Star

/-!
# Induced-star finite graph-family compatibility

The general labeled induced-`H`-free family and normalization APIs live in
`FiniteModels.GraphFamiliesCore` and `FiniteModels.Normalization`.  This
historical import path retains the induced-star specializations, so all
existing declarations remain available to downstream files.
-/

namespace InducedStars

attribute [local instance] graphFamiliesEdgeSetFintype

/-! ## Induced-star specializations -/

/-- Labeled induced-`K_{1,k}`-free graphs with exactly `m` edges. -/
noncomputable abbrev inducedStarFreeGraphFinsetWithEdges (k n m : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  inducedFreeGraphFinsetWithEdges (inducedStar k) n m

/-- The labeled count of induced-`K_{1,k}`-free graphs with exactly `m`
edges. -/
noncomputable abbrev inducedStarFreeGraphCountWithEdges (k n m : ℕ) : ℕ :=
  inducedFreeGraphCountWithEdges (inducedStar k) n m

@[simp] theorem mem_inducedStarFreeGraphFinsetWithEdges {k n m : ℕ}
    {G : SimpleGraph (Fin n)} :
    G ∈ inducedStarFreeGraphFinsetWithEdges k n m ↔
      ¬Regularity.InducedEmbeds (inducedStar k) G ∧
        G.edgeFinset.card = m := by
  exact mem_inducedFreeGraphFinsetWithEdges

end InducedStars
