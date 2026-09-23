import InducedStars.FiniteModels.EntropyAsymptotics
import Mathlib.Tactic

/-!
# Canonical exact-edge sequences

The floor sequence in this file converts a real edge density into an exact
number of unordered edges.  Its normalization is `n.choose 2`, matching both
the finite `G(n,p)` law and the fixed-density enumeration theorem.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The canonical exact edge count obtained by flooring a fraction of all
unordered vertex pairs. -/
def floorEdgeCountSequence (γ : ℝ) (n : ℕ) : ℕ :=
  ⌊γ * (completeEdgeCount n : ℝ)⌋₊

theorem floorEdgeCountSequence_le_completeEdgeCount
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) (n : ℕ) :
    floorEdgeCountSequence γ n ≤ completeEdgeCount n := by
  have hnonneg : 0 ≤ γ * (completeEdgeCount n : ℝ) :=
    mul_nonneg hγ.1 (Nat.cast_nonneg _)
  have hfloor :
      (floorEdgeCountSequence γ n : ℝ) ≤
        γ * (completeEdgeCount n : ℝ) := by
    exact Nat.floor_le hnonneg
  have hmul :
      γ * (completeEdgeCount n : ℝ) ≤
        (completeEdgeCount n : ℝ) := by
    calc
      γ * (completeEdgeCount n : ℝ) ≤
          1 * (completeEdgeCount n : ℝ) :=
        mul_le_mul_of_nonneg_right hγ.2 (Nat.cast_nonneg _)
      _ = (completeEdgeCount n : ℝ) := one_mul _
  have hcast :
      (floorEdgeCountSequence γ n : ℝ) ≤
        (completeEdgeCount n : ℝ) :=
    hfloor.trans hmul
  exact_mod_cast hcast

/-- The floored exact-edge sequence has the prescribed asymptotic density. -/
theorem floorEdgeCountSequence_hasAsymptoticEdgeDensity
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) :
    HasAsymptoticEdgeDensity (floorEdgeCountSequence γ) γ := by
  exact (tendsto_nat_floor_mul_div_atTop hγ.1).comp
    tendsto_completeEdgeCount_cast_atTop

end InducedStars
