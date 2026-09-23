import InducedStars.Structure.Critical.WindowBasic
import DenseGraph.Combinatorics.TwoSidedBinomial

/-!
# The signed density drift in the critical window

The cancellation at `pK k` has a nonzero derivative.  Its signed first-order
term is retained here; estimating its absolute value alone would lose the
location of the transition.
-/

noncomputable section

namespace InducedStars

/-- The derivative magnitude of the logarithmic critical balance. -/
def criticalWindowLogSlope (k : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) / (1 - pK k) + 1 / pK k

theorem criticalWindowLogSlope_eq
    {k : ℕ} (hk : 3 ≤ k) :
    criticalWindowLogSlope k =
      ((k - 1 : ℕ) : ℝ) * gammaK k / (pK k * (1 - pK k)) := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hrel : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show k - 1 = k - 2 + 1 by omega)
  rw [criticalWindowLogSlope, mul_comm ((k - 1 : ℕ) : ℝ) (gammaK k),
    gammaK_mul_denominator k hk]
  rw [hrel]
  field_simp
  ring

/-- The logarithmic balance has a signed linear expansion with a uniform
quadratic remainder on a fixed neighborhood of the critical cross density. -/
theorem abs_criticalWindowLogBalance_add_slope_le
    {k : ℕ} (hk : 3 ≤ k) {q : ℝ}
    (hq0 : |q - pK k| ≤ pK k / 2)
    (hq1 : |q - pK k| ≤ (1 - pK k) / 2) :
    |((k - 1 : ℕ) : ℝ) * Real.log (1 - q) - Real.log q +
      criticalWindowLogSlope k * (q - pK k)| ≤
      (2 * ((k - 1 : ℕ) : ℝ) / (1 - pK k) ^ 2 + 2 / (pK k) ^ 2) *
        (q - pK k) ^ 2 := by
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp' := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have h0 := DenseGraph.abs_log_shift_sub_linear_le hp hq0
  have h1 := DenseGraph.abs_log_shift_sub_linear_le hp'
    (show |-(q - pK k)| ≤ (1 - pK k) / 2 by simpa only [abs_neg] using hq1)
  rw [show pK k + (q - pK k) = q by ring] at h0
  rw [show 1 - pK k + -(q - pK k) = 1 - q by ring, neg_sq] at h1
  have hr : (0 : ℝ) ≤ (k - 1 : ℕ) := Nat.cast_nonneg _
  have h1' := mul_le_mul_of_nonneg_left h1 hr
  rw [← abs_of_nonneg hr, ← abs_mul] at h1'
  have hh := (abs_sub
    (((k - 1 : ℕ) : ℝ) *
      (Real.log (1 - q) - Real.log (1 - pK k) - -(q - pK k) / (1 - pK k)))
    (Real.log q - Real.log (pK k) - (q - pK k) / pK k)).trans
      (add_le_add h1' h0)
  rw [log_pK_eq k, abs_of_nonneg hr] at hh
  unfold criticalWindowLogSlope
  convert hh using 1 <;> congr 1 <;> ring

/-- The signed window term has the completion-expansion coefficient in
the natural-log parameterization. -/
theorem criticalWindowLogSlope_mul_window_scale
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    criticalWindowLogSlope k * a / (k - 2 : ℕ) =
      a / criticalWindowThreshold k := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hd : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  have hg := gammaK_pos hk
  rw [criticalWindowLogSlope_eq hk]
  unfold criticalWindowThreshold
  field_simp

end InducedStars
