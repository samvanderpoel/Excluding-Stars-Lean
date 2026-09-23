import InducedStars.Analysis.ScalarOptimization
import Mathlib.Tactic

/-!
# Scalar constants for the critical sparse-set penalty

The logarithm in the critical gap is the natural logarithm.
-/

noncomputable section

namespace InducedStars

/-- The natural-log quadratic coefficient in the critical binomial
expansion. -/
noncomputable def criticalQuadraticCoefficient (k : ℕ) : ℝ :=
  ((k - 1 : ℕ) : ℝ) /
      (((k - 2 : ℕ) : ℝ) * (1 - pK k)) -
    ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) +
    1 / (pK k * ((k - 1 : ℕ) : ℝ) * ((k - 2 : ℕ) : ℝ))

/-- The sparse-summation gap uses `Real.log`, hence natural
logarithms, because it occurs inside a `Real.exp` exponent. -/
noncomputable def criticalSparseQuadraticGap (k : ℕ) : ℝ :=
  criticalQuadraticCoefficient k -
    (1 / 2 : ℝ) * Real.log (1 / (1 - pK k))

private theorem criticalQuadraticCoefficient_sub_rational_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalQuadraticCoefficient k -
      pK k / (2 * (1 - pK k)) := by
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  let d : ℝ := ((k - 2 : ℕ) : ℝ)
  let p : ℝ := pK k
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (show 0 < k - 1 by omega)
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast (show 0 < k - 2 by omega)
  have hdOne : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast (show 1 ≤ k - 2 by omega)
  have hp : 0 < p := by
    dsimp [p]
    exact pK_pos (by omega)
  have hpOne : p < 1 := by
    dsimp [p]
    exact pK_lt_one (by omega)
  have hq : 0 < 1 - p := sub_pos.mpr hpOne
  have hrd : r = d + 1 := by
    dsimp [r, d]
    norm_num [Nat.cast_sub (show 1 ≤ k by omega),
      Nat.cast_sub (show 2 ≤ k by omega)]
    ring
  have hprod : 0 ≤ p * d * (d - 1) := by positivity
  have hnum :
      0 < 2 * r ^ 2 - p * r * d - 2 * d ^ 2 * (1 - p) := by
    rw [hrd]
    nlinarith
  have hmain :
      0 < (2 * r ^ 2 - p * r * d - 2 * d ^ 2 * (1 - p)) /
        (2 * r * d * (1 - p)) := by positivity
  have hinv : 0 < 1 / (p * r * d) := by positivity
  have hidAlias :
      r / (d * (1 - p)) - d / r + 1 / (p * r * d) -
          p / (2 * (1 - p)) =
        (2 * r ^ 2 - p * r * d - 2 * d ^ 2 * (1 - p)) /
            (2 * r * d * (1 - p)) +
          1 / (p * r * d) := by
    field_simp [hr.ne', hd.ne', hp.ne', hq.ne']
    ring
  have hid :
      criticalQuadraticCoefficient k - pK k / (2 * (1 - pK k)) =
        (2 * r ^ 2 - p * r * d - 2 * d ^ 2 * (1 - p)) /
            (2 * r * d * (1 - p)) +
          1 / (p * r * d) := by
    simpa [criticalQuadraticCoefficient, r, d, p] using hidAlias
  rw [hid]
  positivity

/-- The critical quadratic coefficient is positive for every `k ≥ 3`. -/
theorem criticalQuadraticCoefficient_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalQuadraticCoefficient k := by
  have hmargin := criticalQuadraticCoefficient_sub_rational_pos hk
  have hp : 0 < pK k := pK_pos (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega))
  have : 0 < pK k / (2 * (1 - pK k)) := by positivity
  linarith

/-- Positivity of the natural-log critical gap. -/
theorem criticalSparseQuadraticGap_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSparseQuadraticGap k := by
  have hp : 0 < pK k := pK_pos (by omega)
  have hpOne : pK k < 1 := pK_lt_one (by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr hpOne
  have hx : 0 < 1 / (1 - pK k) := by positivity
  have hxne : 1 / (1 - pK k) ≠ 1 := by
    intro h
    field_simp [hq.ne'] at h
    linarith
  have hlog0 := Real.log_lt_sub_one_of_pos hx hxne
  have hratio :
      1 / (1 - pK k) - 1 = pK k / (1 - pK k) := by
    field_simp
    ring
  rw [hratio] at hlog0
  have hmargin := criticalQuadraticCoefficient_sub_rational_pos hk
  have hhalf :
      (1 / 2 : ℝ) * Real.log (1 / (1 - pK k)) <
        pK k / (2 * (1 - pK k)) := by
    have hmul := mul_lt_mul_of_pos_left hlog0 (by norm_num : (0 : ℝ) < 1 / 2)
    calc
      (1 / 2 : ℝ) * Real.log (1 / (1 - pK k)) <
          (1 / 2 : ℝ) * (pK k / (1 - pK k)) := hmul
      _ = pK k / (2 * (1 - pK k)) := by
        field_simp [hq.ne']
  unfold criticalSparseQuadraticGap
  linarith

/-- A fixed positive fraction of the corrected critical sparse gap, used to
absorb finite Taylor and rounding errors. -/
noncomputable def criticalSparsePenaltyConstant (k : ℕ) : ℝ :=
  criticalSparseQuadraticGap k / 8

/-- Positivity of the final critical sparse-set penalty constant. -/
theorem criticalSparsePenaltyConstant_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSparsePenaltyConstant k := by
  unfold criticalSparsePenaltyConstant
  exact div_pos (criticalSparseQuadraticGap_pos hk) (by norm_num)

end InducedStars
