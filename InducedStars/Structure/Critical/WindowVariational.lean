import InducedStars.Structure.Critical.WindowBasic

/-!
# The critical-window remainder variational problem

After normalization by `log(n)^2`, the clean remainder-size counts have a
quadratic exponent.  Its unique maximizer and its boundary behavior give
the two regimes in the current critical theorem.
-/

noncomputable section

namespace InducedStars

/-- The logarithmic-window exponent for a remainder of order `x * log n`. -/
def criticalWindowRate (k : ℕ) (a x : ℝ) : ℝ :=
  (1 - a / criticalWindowThreshold k) * x -
    (gammaK k / criticalWindowThreshold k) * x ^ 2

/-- Completing the square identifies the exact remainder coefficient. -/
theorem criticalWindowRate_eq_peak_sub_square
    {k : ℕ} (hk : 3 ≤ k) (a x : ℝ) :
    criticalWindowRate k a x =
      criticalWindowRate k a (criticalWindowRemainderCoefficient k a) -
        (gammaK k / criticalWindowThreshold k) *
          (x - criticalWindowRemainderCoefficient k a) ^ 2 := by
  have ht := (criticalWindowThreshold_pos hk).ne'
  have hg := (gammaK_pos hk).ne'
  unfold criticalWindowRate criticalWindowRemainderCoefficient
  field_simp
  ring

/-- Below the transition, the maximizer lies in the allowed nonnegative range. -/
theorem criticalWindowRemainderCoefficient_nonneg
    {k : ℕ} (hk : 3 ≤ k) {a : ℝ} (ha : a ≤ criticalWindowThreshold k) :
    0 ≤ criticalWindowRemainderCoefficient k a := by
  have hg := gammaK_pos hk
  exact div_nonneg (sub_nonneg.mpr ha) (by positivity)

/-- The variational gap is explicitly quadratic in distance from the maximizer. -/
theorem criticalWindowRate_le_peak_sub_gap
    {k : ℕ} (hk : 3 ≤ k) (a x : ℝ) {eta : ℝ}
    (heta : 0 ≤ eta) (haway : eta ≤ |x - criticalWindowRemainderCoefficient k a|) :
    criticalWindowRate k a x ≤
      criticalWindowRate k a (criticalWindowRemainderCoefficient k a) -
        (gammaK k / criticalWindowThreshold k) * eta ^ 2 := by
  rw [criticalWindowRate_eq_peak_sub_square hk]
  have hsq := pow_le_pow_left₀ heta haway 2
  rw [sq_abs] at hsq
  have hbeta : 0 ≤ gammaK k / criticalWindowThreshold k :=
    div_nonneg (gammaK_pos hk).le (criticalWindowThreshold_pos hk).le
  nlinarith [mul_le_mul_of_nonneg_left hsq hbeta]

/-- Above the transition the boundary maximizer is zero, with a strictly
negative linear term for every positive remainder size. -/
theorem criticalWindowRate_le_neg_linear
    {k : ℕ} (hk : 3 ≤ k) {a x : ℝ} :
    criticalWindowRate k a x ≤ -(a / criticalWindowThreshold k - 1) * x := by
  unfold criticalWindowRate
  have hquad : 0 ≤ gammaK k / criticalWindowThreshold k * x ^ 2 :=
    mul_nonneg (div_nonneg (gammaK_pos hk).le (criticalWindowThreshold_pos hk).le)
      (sq_nonneg x)
  linarith

theorem criticalWindowSupercriticalLinearGap_pos
    {k : ℕ} (hk : 3 ≤ k) {a : ℝ} (ha : criticalWindowThreshold k < a) :
    0 < a / criticalWindowThreshold k - 1 := by
  apply sub_pos.mpr
  exact (one_lt_div (criticalWindowThreshold_pos hk)).mpr ha

end InducedStars
