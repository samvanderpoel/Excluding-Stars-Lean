import InducedStars.FiniteModels.EntropyAsymptotics
import Mathlib.Tactic

/-!
# Exact-edge repair scale

The graphon cut cost of changing a fraction `eta` of the unordered pairs is
`eta` in the limit.  This file records the exact bridge between the
`n.choose 2` repair radius and the ordered-square graphon normalization.
-/

noncomputable section

open Filter Topology

namespace InducedStars

/-- Twice the fractional edit radius divided by `n²` tends to the prescribed
unordered-pair fraction. -/
theorem fractionalEditRadius_orderedSquare_tendsto
    (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto
      (fun n : ℕ ↦
        2 * (fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
          (n : ℝ) ^ 2)
      atTop (nhds eta) := by
  have hratio := fractionalEditRadius_ratio_tendsto eta heta
  have hfactor := completeEdgeCount_orderedSquareFactor_tendsto_one
  have hprod : Tendsto
      (fun n : ℕ ↦
        ((fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
            (completeEdgeCount n : ℝ)) *
          (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2))
      atTop (nhds (eta * 1)) := hratio.mul hfactor
  have heq : ∀ᶠ n : ℕ in atTop,
      ((fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
          (completeEdgeCount n : ℝ)) *
        (2 * (completeEdgeCount n : ℝ) / (n : ℝ) ^ 2) =
      2 * (fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
        (n : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hN : (completeEdgeCount n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hn).ne'
    field_simp
  simpa only [mul_one] using hprod.congr' heq

/-- Eventual upper control of the exact graphon cut penalty. -/
theorem eventually_fractionalEditRadius_orderedSquare_lt
    {eta bound : ℝ} (heta : 0 ≤ eta) (hbound : eta < bound) :
    ∀ᶠ n : ℕ in atTop,
      2 * (fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
          (n : ℝ) ^ 2 < bound :=
  (fractionalEditRadius_orderedSquare_tendsto eta heta).eventually
    (Iio_mem_nhds hbound)

end InducedStars
