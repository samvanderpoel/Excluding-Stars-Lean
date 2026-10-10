import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# A superlinear logarithmic gain absorbs polynomial and linear costs

All logarithms are natural. The constants are fixed before the order tends
to infinity; no quantitative convergence assumption is involved.
-/

open Filter Topology
namespace DenseGraph

theorem eventually_linear_sub_mul_log_le {c : ℝ} (hc : 0 < c) (C A : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * n - c * n * Real.log n ≤ -A * n := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop ((C + A) / c))] with n hn
  have h := (div_le_iff₀ hc).mp hn
  have hmul := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

theorem tendsto_polynomial_mul_exp_linear_sub_mul_log {c : ℝ}
    (hc : 0 < c) (C : ℝ) (d : ℕ) :
    Tendsto (fun n : ℕ ↦ (n : ℝ)^d * Real.exp (C*n-c*n*Real.log n))
      atTop (𝓝 0) := by
  apply squeeze_zero' (g := fun n : ℕ ↦ (n : ℝ)^d * Real.exp (-(n : ℝ)))
  · exact Eventually.of_forall fun n ↦ by positivity
  · filter_upwards [eventually_linear_sub_mul_log_le hc C 1] with n hn
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa using hn)) (by positivity)
  · exact (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop)

theorem tendsto_linear_mul_exp_linear_sub_mul_log {c : ℝ}
    (hc : 0 < c) (C Q : ℝ) :
    Tendsto (fun n : ℕ ↦ (Q*n+1)*Real.exp (C*n-c*n*Real.log n))
      atTop (𝓝 0) := by
  have h := ((tendsto_polynomial_mul_exp_linear_sub_mul_log hc C 1).const_mul Q).add
    (tendsto_polynomial_mul_exp_linear_sub_mul_log hc C 0)
  simpa only [pow_one, pow_zero, one_mul, mul_add, add_mul, mul_assoc, mul_zero,
    zero_add] using h

end DenseGraph
