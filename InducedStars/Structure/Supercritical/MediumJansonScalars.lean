import Mathlib

/-!
# Scalar bounds for a quadratic Janson penalty

This file isolates the elementary real-algebra calculation that turns a
degree-`k` lower bound for the Janson expectation and a degree-`2k - 2`
upper bound for the dependency sum into a positive quadratic exponent.
-/

namespace InducedStars

noncomputable section

/-- An explicit quadratic penalty extracted from expectation coefficient
`a` and dependency coefficient `b`. -/
def mediumJansonQuadraticPenalty (a b : ℝ) : ℝ :=
  min (a / 2) (a ^ 2 / (4 * b))

/-- The explicit Janson penalty is positive whenever both input
coefficients are positive. -/
theorem mediumJansonQuadraticPenalty_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 < mediumJansonQuadraticPenalty a b := by
  unfold mediumJansonQuadraticPenalty
  exact lt_min (div_pos ha (by norm_num))
    (div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hb))

/-- The expectation branch of the quadratic minimum. -/
theorem mediumJansonQuadraticPenalty_mul_sq_le_mu_half
    {k n : ℕ} {a b μ : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (ha : 0 < a)
    (hμ : a * (n : ℝ) ^ k ≤ μ) :
    mediumJansonQuadraticPenalty a b * (n : ℝ) ^ 2 ≤ μ / 2 := by
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ k :=
    pow_le_pow_right₀ hn_real (by omega)
  have hc : mediumJansonQuadraticPenalty a b ≤ a / 2 := by
    exact min_le_left _ _
  calc
    mediumJansonQuadraticPenalty a b * (n : ℝ) ^ 2 ≤
        (a / 2) * (n : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_right hc (pow_nonneg (by positivity) _)
    _ ≤ (a / 2) * (n : ℝ) ^ k := by
      exact mul_le_mul_of_nonneg_left hpow (div_nonneg ha.le (by norm_num))
    _ = (a * (n : ℝ) ^ k) / 2 := by ring
    _ ≤ μ / 2 := by linarith

/-- The dependency branch of the quadratic minimum.  The conclusion is
stated in precisely the form consumed by the local Janson application. -/
theorem mediumJansonQuadraticPenalty_mul_sq_le_mu_sq_div_delta
    {k n : ℕ} {a b μ Δ : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hμ : a * (n : ℝ) ^ k ≤ μ)
    (hΔ : Δ ≤ b * (n : ℝ) ^ (2 * k - 2)) (hΔpos : 0 < Δ) :
    mediumJansonQuadraticPenalty a b * (n : ℝ) ^ 2 ≤
      μ ^ 2 / (4 * Δ) := by
  let x : ℝ := n
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hc : mediumJansonQuadraticPenalty a b ≤ a ^ 2 / (4 * b) := by
    exact min_le_right _ _
  have hc0 : 0 ≤ mediumJansonQuadraticPenalty a b :=
    (mediumJansonQuadraticPenalty_pos ha hb).le
  have hbase0 : 0 ≤ a * x ^ k :=
    mul_nonneg ha.le (pow_nonneg hx0 _)
  have hμsq : (a * x ^ k) ^ 2 ≤ μ ^ 2 := by
    exact pow_le_pow_left₀ hbase0 hμ 2
  have hpowAdd : x ^ 2 * x ^ (2 * k - 2) = x ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowMul : (x ^ k) ^ 2 = x ^ (2 * k) := by
    rw [← pow_mul]
    congr 1
    omega
  have hscaled :
      mediumJansonQuadraticPenalty a b * x ^ 2 * (4 * Δ) ≤
        (a ^ 2 / (4 * b)) * x ^ 2 *
          (4 * (b * x ^ (2 * k - 2))) := by
    gcongr
  have hidentity :
      (a ^ 2 / (4 * b)) * x ^ 2 *
          (4 * (b * x ^ (2 * k - 2))) = (a * x ^ k) ^ 2 := by
    calc
      (a ^ 2 / (4 * b)) * x ^ 2 *
          (4 * (b * x ^ (2 * k - 2))) =
          a ^ 2 * (x ^ 2 * x ^ (2 * k - 2)) := by
            field_simp [ne_of_gt hb]
      _ = a ^ 2 * x ^ (2 * k) := by rw [hpowAdd]
      _ = (a * x ^ k) ^ 2 := by rw [mul_pow, hpowMul]
  apply (le_div_iff₀ (mul_pos (by norm_num) hΔpos)).2
  change mediumJansonQuadraticPenalty a b * x ^ 2 * (4 * Δ) ≤ μ ^ 2
  exact hscaled.trans (hidentity.trans_le hμsq)

end

end InducedStars
