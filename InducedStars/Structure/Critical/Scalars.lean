import InducedStars.Analysis.ScalarOptimization
import Mathlib.Tactic

/-!
# The Gaussian gap at the critical density

The binomial Chernoff penalty exceeds the quadratic contribution from the
critical likelihood ratio. All logarithms in exponential weights are natural.
-/

noncomputable section
namespace InducedStars

/-- The critical Bernoulli parameter is strictly below one half. -/
theorem critical_pK_lt_half {k : ℕ} (hk : 3 ≤ k) :
    pK k < (1 / 2 : ℝ) := by
  apply (pK_lt_iff_pow_lt (by omega : 2 ≤ k) (by norm_num : (1 / 2 : ℝ) < 1)).2
  have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) (show 2 ≤ k - 1 by omega)
  norm_num at hpow ⊢
  linarith

/-- Gap between the Chernoff exponent and the critical likelihood ratio. -/
def criticalSparseQuadraticGap (k : ℕ) : ℝ :=
  pK k - (1 / 2 : ℝ) * Real.log (1 / (1 - pK k))

theorem criticalSparseQuadraticGap_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSparseQuadraticGap k := by
  have hp := pK_pos (k := k) (by omega)
  have hpHalf := critical_pK_lt_half hk
  have hq : 0 < 1 - pK k := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / (1 - pK k) by positivity)
  have heq : 1 / (1 - pK k) - 1 = pK k / (1 - pK k) := by
    field_simp
    ring
  rw [heq] at hlog
  have hratio : pK k / (1 - pK k) < 2 * pK k := by
    apply (div_lt_iff₀ hq).2
    nlinarith
  unfold criticalSparseQuadraticGap
  linarith

/-- A fixed reserve in the Gaussian remainder penalty. -/
def criticalSparsePenaltyConstant (k : ℕ) : ℝ :=
  criticalSparseQuadraticGap k / 8

theorem criticalSparsePenaltyConstant_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSparsePenaltyConstant k := by
  exact div_pos (criticalSparseQuadraticGap_pos hk) (by norm_num)

end InducedStars
