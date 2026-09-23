import InducedStars.Structure.Supercritical.FixedPatternAggregation
import DenseGraph.Combinatorics.ExponentialSums

/-!
# The divisionwise supercritical fixed-defect estimate
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedTotalAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## The positive matching-number series -/

/-- The remaining five-sixteenths of the matching exponent absorb the
number of possible positive matching sizes, leaving the required half-rate. -/
theorem eventually_sum_Icc_exp_neg_thirteen_sixteenths_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∑ h ∈ Finset.Icc 1 n,
          Real.exp (-((13 * c / 16) * (h : ℝ) * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (n : ℝ))) := by
  have hrem := DenseGraph.eventually_sum_Icc_exp_neg_mul_le
    (show 0 < 5 * c / 16 by positivity)
  filter_upwards [hrem, eventually_ge_atTop 1] with n hremN hn
  have hterm (h : ℕ) (hh : h ∈ Finset.Icc 1 n) :
      Real.exp (-((13 * c / 16) * (h : ℝ) * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (n : ℝ))) *
          Real.exp (-((5 * c / 16) * (h : ℝ) * (n : ℝ))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hhR : (1 : ℝ) ≤ h := by
      exact_mod_cast (Finset.mem_Icc.mp hh).1
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hhR)
      (mul_nonneg hc.le hn0)]
  calc
    ∑ h ∈ Finset.Icc 1 n,
        Real.exp (-((13 * c / 16) * (h : ℝ) * (n : ℝ))) ≤
      ∑ h ∈ Finset.Icc 1 n,
        Real.exp (-((c / 2) * (n : ℝ))) *
          Real.exp (-((5 * c / 16) * (h : ℝ) * (n : ℝ))) := by
      exact Finset.sum_le_sum fun h hh ↦ hterm h hh
    _ = Real.exp (-((c / 2) * (n : ℝ))) *
        (∑ h ∈ Finset.Icc 1 n,
          Real.exp (-((5 * c / 16) * (h : ℝ) * (n : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-((c / 2) * (n : ℝ))) *
        Real.exp (-(((5 * c / 16) / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hremN (Real.exp_nonneg _)
    _ ≤ Real.exp (-((c / 2) * (n : ℝ))) := by
      apply mul_le_of_le_one_right (Real.exp_nonneg _)
      rw [Real.exp_le_one_iff]
      have : 0 ≤ ((5 * c / 16) / 2) * (n : ℝ) := by positivity
      linarith

end InducedStars
