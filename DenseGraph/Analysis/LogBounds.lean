import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Elementary logarithm bounds

A finite Lipschitz estimate on a positive half-line supports the current
binomial-ratio and local-tail estimates.
-/

noncomputable section

namespace DenseGraph

/-- The logarithm is `1/lambda`-Lipschitz on the positive half-line
`[lambda,∞)`.  This elementary finite form is convenient when replacing an
exact binomial density by its limiting value. -/
theorem abs_log_sub_log_le_div_of_lower
    {lambda x y : ℝ} (hlambda : 0 < lambda)
    (hx : lambda ≤ x) (hy : lambda ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / lambda := by
  have hx0 : 0 < x := hlambda.trans_le hx
  have hy0 : 0 < y := hlambda.trans_le hy
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    calc
      Real.log y - Real.log x = Real.log (y / x) := by
        rw [Real.log_div hy0.ne' hx0.ne']
      _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      _ = (y - x) / x := by field_simp
      _ ≤ (y - x) / lambda :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hlambda hx
  · have hlog : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hlog),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    calc
      Real.log x - Real.log y = Real.log (x / y) := by
        rw [Real.log_div hx0.ne' hy0.ne']
      _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      _ = (x - y) / y := by field_simp
      _ ≤ (x - y) / lambda :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hlambda hy

end DenseGraph
