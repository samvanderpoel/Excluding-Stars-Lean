import InducedStars.Analysis.Entropy
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Finite graph normalizations

This file is the canonical low-level home of the unordered-pair
normalization used by the finite graph models.  It is independent of any
forbidden graph, graphon variational problem, or probability law.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

/-- The number of unordered pairs of distinct vertices in an `n`-vertex
graph.  Thus every possible edge is counted exactly once. -/
def completeEdgeCount (n : ℕ) : ℕ :=
  Nat.choose n 2

/-- Base-two logarithm normalized by the number of unordered pairs at graph
order `n`.  The project's logarithm is totalized at zero, so callers must
separately establish positivity before using logarithm identities. -/
noncomputable abbrev normalizedLogAtGraphOrder (n : ℕ) (x : ℝ) : ℝ :=
  log2 x / (completeEdgeCount n : ℝ)

/-- The normalized base-two logarithm of a finite labeled graph count. -/
noncomputable def normalizedLogGraphCount (n count : ℕ) : ℝ :=
  normalizedLogAtGraphOrder n (count : ℝ)

/-- The normalized base-two logarithm of a finite graph-event probability. -/
noncomputable def normalizedLogProbability (n : ℕ) (x : ℝ) : ℝ :=
  normalizedLogAtGraphOrder n x

/-- The edge-count sequence `m` has asymptotic density `γ` when
`m n / n.choose 2` tends to `γ`. -/
def HasAsymptoticEdgeDensity (m : ℕ → ℕ) (γ : ℝ) : Prop :=
  Tendsto
    (fun n ↦ (m n : ℝ) / (completeEdgeCount n : ℝ))
    atTop (nhds γ)

/-- The conversion factor from normalization by unordered pairs to the
ordered-square graphon normalization tends to one. -/
theorem completeEdgeCount_orderedSquareFactor_tendsto_one :
    Tendsto
      (fun n : ℕ ↦
        2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  have hsub : Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / (n : ℝ))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hinv)
  apply hsub.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn ↦ hn⟩] with n hn
  rw [completeEdgeCount, Nat.cast_choose_two]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp

end InducedStars
