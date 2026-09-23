import InducedStars.Graphon.Metric

/-!
# Elementary uniqueness of cut-distance limits

The cut distance is a pseudometric on graphons.  This file records the only
limit-uniqueness statement needed by the two branches of the fixed-density
optimizer classification: two limits of one graphon sequence have cut
distance zero.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

/-- If one graphon sequence tends to both `U` and `V` in cut distance, then
`U` and `V` have cut distance zero. -/
theorem cutDist_eq_zero_of_common_approximation
    {X : ℕ → Graphon} {U V : Graphon}
    (hU : Tendsto (fun m ↦ cutDist (X m) U) atTop (𝓝 0))
    (hV : Tendsto (fun m ↦ cutDist (X m) V) atTop (𝓝 0)) :
    cutDist U V = 0 := by
  have hUpper : Tendsto
      (fun m ↦ cutDist U (X m) + cutDist (X m) V) atTop (𝓝 0) := by
    have hU' : Tendsto (fun m ↦ cutDist U (X m)) atTop (𝓝 0) := by
      apply hU.congr'
      filter_upwards [] with m
      exact cutDist_comm (X m) U
    simpa using hU'.add hV
  have hZero : Tendsto (fun _ : ℕ ↦ cutDist U V) atTop (𝓝 0) := by
    apply squeeze_zero
    · intro m
      exact cutDist_nonneg U V
    · intro m
      exact cutDist_triangle U (X m) V
    · exact hUpper
  exact tendsto_nhds_unique tendsto_const_nhds hZero

end InducedStars
