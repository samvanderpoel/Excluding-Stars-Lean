import InducedStars.Graphon.MatrixInducedDensity
import Mathlib.Combinatorics.SimpleGraph.Star

/-!
# The canonical induced star and the fixed-density variational sets

The paper's `K_{1,k}` is represented by Mathlib's star graph on `Fin (k+1)`,
centered at `0`.  Thus it has one center and exactly `k` leaves.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## The star `K_{1,k}` -/

/-- The canonical copy of the paper's `K_{1,k}`: center `0` and leaves
`Fin.succ i`, for `i : Fin k`. -/
def inducedStar (k : ℕ) : SimpleGraph (Fin (k + 1)) :=
  SimpleGraph.starGraph 0

/-- Transparent adjacency characterization of the canonical induced star. -/
@[simp] theorem inducedStar_adj {k : ℕ} {i j : Fin (k + 1)} :
    (inducedStar k).Adj i j ↔ i ≠ j ∧ (i = 0 ∨ j = 0) := by
  exact SimpleGraph.starGraph_adj

/-- The paper's `K_{1,k}` has `k+1` vertices. -/
@[simp] theorem inducedStar_vertexCount (k : ℕ) :
    Fintype.card (Fin (k + 1)) = k + 1 := by
  simp

/-- Every designated leaf is adjacent to the center. -/
theorem inducedStar_center_adj_leaf {k : ℕ} (i : Fin k) :
    (inducedStar k).Adj 0 i.succ := by
  rw [inducedStar_adj]
  exact ⟨(Fin.succ_ne_zero i).symm, Or.inl rfl⟩

/-- The center is adjacent to every non-center vertex. -/
theorem inducedStar_center_adj_of_ne {k : ℕ} {v : Fin (k + 1)} (hv : v ≠ 0) :
    (inducedStar k).Adj 0 v := by
  rw [inducedStar_adj]
  exact ⟨hv.symm, Or.inl rfl⟩

/-- Two designated leaves are never adjacent. -/
theorem inducedStar_leaf_nonadj_leaf {k : ℕ} (i j : Fin k) :
    ¬(inducedStar k).Adj i.succ j.succ := by
  simp

/-- The canonical induced star is connected. -/
theorem inducedStar_connected (k : ℕ) : (inducedStar k).Connected := by
  exact SimpleGraph.connected_starGraph 0

/-! ## Fixed-density feasible and optimizer sets -/

/-- Graphons with edge density `γ` and zero induced `K_{1,k}` density. -/
def fixedDensityFeasible (k : ℕ) (γ : ℝ) : Set Graphon :=
  {W | graphonInducedDensity (inducedStar k) W = 0 ∧ graphonEdgeDensity W = γ}

@[simp] theorem mem_fixedDensityFeasible {k : ℕ} {γ : ℝ} {W : Graphon} :
    W ∈ fixedDensityFeasible k γ ↔
      graphonInducedDensity (inducedStar k) W = 0 ∧ graphonEdgeDensity W = γ :=
  Iff.rfl

/-- A fixed-density optimizer is a feasible graphon whose entropy dominates
that of every other feasible graphon.  This definition does not presuppose
that an optimizer exists. -/
def IsFixedDensityOptimizer (k : ℕ) (γ : ℝ) (W : Graphon) : Prop :=
  W ∈ fixedDensityFeasible k γ ∧
    ∀ U ∈ fixedDensityFeasible k γ, graphonEntropy U ≤ graphonEntropy W

/-- The set of entropy maximizers in the fixed-density feasible set. -/
def fixedDensityOptimizers (k : ℕ) (γ : ℝ) : Set Graphon :=
  {W | IsFixedDensityOptimizer k γ W}

@[simp] theorem mem_fixedDensityOptimizers {k : ℕ} {γ : ℝ} {W : Graphon} :
    W ∈ fixedDensityOptimizers k γ ↔ IsFixedDensityOptimizer k γ W :=
  Iff.rfl

theorem IsFixedDensityOptimizer.feasible {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W) :
    W ∈ fixedDensityFeasible k γ :=
  hW.1

theorem IsFixedDensityOptimizer.entropy_le {k : ℕ} {γ : ℝ} {W : Graphon}
    (hW : IsFixedDensityOptimizer k γ W) {U : Graphon}
    (hU : U ∈ fixedDensityFeasible k γ) :
    graphonEntropy U ≤ graphonEntropy W :=
  hW.2 U hU

end InducedStars
