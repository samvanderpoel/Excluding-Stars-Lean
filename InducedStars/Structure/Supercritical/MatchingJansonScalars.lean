import InducedStars.Structure.Supercritical.MatchingParameters
import InducedStars.Structure.Supercritical.MediumJansonScalars
import Mathlib.Tactic

/-!
# Scalar bounds for the supercritical matching Janson penalty

If a homogeneous matching has `q` edges, the matching construction produces
Janson expectation of order `q * n^(k-1)` and dependency sum of order
`q * n^(2k-3)`.  This file contains the elementary calculation turning those
two estimates into an exponent of order `q * n`.  It is deliberately
independent of the concrete candidate representation.
-/

namespace InducedStars

noncomputable section

/-- The linear matching penalty extracted from expectation coefficient `a`
and dependency coefficient `b`. -/
def matchingJansonLinearPenalty (a b : ℝ) : ℝ :=
  min (a / 2) (a ^ 2 / (4 * b))

theorem matchingJansonLinearPenalty_pos {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    0 < matchingJansonLinearPenalty a b := by
  unfold matchingJansonLinearPenalty
  exact lt_min (div_pos ha (by norm_num))
    (div_pos (sq_pos_of_pos ha) (mul_pos (by norm_num) hb))

/-- The expectation branch of the matching Janson minimum. -/
theorem matchingJansonLinearPenalty_mul_matching_mul_n_le_mu_half
    {k n q : ℕ} {a b μ : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (ha : 0 < a)
    (hμ : a * (q : ℝ) * (n : ℝ) ^ (k - 1) ≤ μ) :
    matchingJansonLinearPenalty a b * (q : ℝ) * (n : ℝ) ≤ μ / 2 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hpow : (n : ℝ) ≤ (n : ℝ) ^ (k - 1) := by
    simpa using pow_le_pow_right₀ hnR (show 1 ≤ k - 1 by omega)
  have hc : matchingJansonLinearPenalty a b ≤ a / 2 := min_le_left _ _
  calc
    matchingJansonLinearPenalty a b * (q : ℝ) * (n : ℝ) ≤
        (a / 2) * (q : ℝ) * (n : ℝ) := by gcongr
    _ ≤ (a / 2) * (q : ℝ) * (n : ℝ) ^ (k - 1) := by
      gcongr
    _ = (a * (q : ℝ) * (n : ℝ) ^ (k - 1)) / 2 := by ring
    _ ≤ μ / 2 := by linarith

/-- The dependency branch of the matching Janson minimum. -/
theorem matchingJansonLinearPenalty_mul_matching_mul_n_le_mu_sq_div_delta
    {k n q : ℕ} {a b μ Δ : ℝ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b)
    (hμ : a * (q : ℝ) * (n : ℝ) ^ (k - 1) ≤ μ)
    (hΔ : Δ ≤ b * (q : ℝ) * (n : ℝ) ^ (2 * k - 3))
    (hΔpos : 0 < Δ) :
    matchingJansonLinearPenalty a b * (q : ℝ) * (n : ℝ) ≤
      μ ^ 2 / (4 * Δ) := by
  let x : ℝ := n
  let y : ℝ := q
  have hx : 1 ≤ x := by
    dsimp [x]
    exact_mod_cast hn
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hy0 : 0 ≤ y := by positivity
  have hc : matchingJansonLinearPenalty a b ≤ a ^ 2 / (4 * b) :=
    min_le_right _ _
  have hc0 : 0 ≤ matchingJansonLinearPenalty a b :=
    (matchingJansonLinearPenalty_pos ha hb).le
  have hbase0 : 0 ≤ a * y * x ^ (k - 1) := by positivity
  have hμsq : (a * y * x ^ (k - 1)) ^ 2 ≤ μ ^ 2 :=
    pow_le_pow_left₀ hbase0 (by simpa [x, y] using hμ) 2
  have hpowAdd : x * x ^ (2 * k - 3) = x ^ (2 * k - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpowMul : (x ^ (k - 1)) ^ 2 = x ^ (2 * k - 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hscaled :
      matchingJansonLinearPenalty a b * y * x * (4 * Δ) ≤
        (a ^ 2 / (4 * b)) * y * x *
          (4 * (b * y * x ^ (2 * k - 3))) := by
    gcongr
  have hidentity :
      (a ^ 2 / (4 * b)) * y * x *
          (4 * (b * y * x ^ (2 * k - 3))) =
        (a * y * x ^ (k - 1)) ^ 2 := by
    calc
      (a ^ 2 / (4 * b)) * y * x *
          (4 * (b * y * x ^ (2 * k - 3))) =
          a ^ 2 * y ^ 2 * (x * x ^ (2 * k - 3)) := by
            field_simp [ne_of_gt hb]
      _ = a ^ 2 * y ^ 2 * x ^ (2 * k - 2) := by rw [hpowAdd]
      _ = (a * y * x ^ (k - 1)) ^ 2 := by
        rw [mul_pow, mul_pow, hpowMul]
  apply (le_div_iff₀ (mul_pos (by norm_num) hΔpos)).2
  change matchingJansonLinearPenalty a b * y * x * (4 * Δ) ≤ μ ^ 2
  exact hscaled.trans (hidentity.trans_le hμsq)

/-- Paper-facing matching penalty for candidate-abundance coefficient
`candidateRate` and any proved positive dependency coefficient. -/
def supercriticalMatchingBernoulliPenalty
    (k : ℕ) (gamma candidateRate dependencyCoefficient : ℝ) : ℝ :=
  matchingJansonLinearPenalty
    (candidateRate * supercriticalMatchingEventProbabilityFloor k gamma)
    dependencyCoefficient

theorem supercriticalMatchingBernoulliPenalty_pos
    {k : ℕ} (hk : 3 ≤ k)
    {gamma candidateRate dependencyCoefficient : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (hcandidate : 0 < candidateRate)
    (hdependency : 0 < dependencyCoefficient) :
    0 < supercriticalMatchingBernoulliPenalty
      k gamma candidateRate dependencyCoefficient := by
  apply matchingJansonLinearPenalty_pos
  · exact mul_pos hcandidate
      (supercriticalMatchingEventProbabilityFloor_pos hk hgamma)
  · exact hdependency

/-- Final fixed-count matching rate.  The denominator is exactly twice the
`4(k-1)` loss between the selected homogeneous matching and the support-
incident matching number, leaving the other half for conditioning. -/
def supercriticalMatchingFixedPenalty
    (k : ℕ) (gamma candidateRate dependencyCoefficient : ℝ) : ℝ :=
  supercriticalMatchingBernoulliPenalty
      k gamma candidateRate dependencyCoefficient /
    (8 * ((k - 1 : ℕ) : ℝ))

theorem supercriticalMatchingFixedPenalty_pos
    {k : ℕ} (hk : 3 ≤ k)
    {gamma candidateRate dependencyCoefficient : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (hcandidate : 0 < candidateRate)
    (hdependency : 0 < dependencyCoefficient) :
    0 < supercriticalMatchingFixedPenalty
      k gamma candidateRate dependencyCoefficient := by
  unfold supercriticalMatchingFixedPenalty
  have hk1Nat : 0 < k - 1 := by omega
  have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hk1Nat
  exact div_pos
    (supercriticalMatchingBernoulliPenalty_pos
      hk hgamma hcandidate hdependency) (mul_pos (by norm_num) hk1)

/-- The final rate spends exactly half of the matching Janson exponent when
`h(T) ≤ 4(k-1)q`. -/
theorem twice_supercriticalMatchingFixedPenalty_mul_scale
    {k : ℕ} (hk : 3 ≤ k)
    {gamma candidateRate dependencyCoefficient : ℝ} :
    2 * supercriticalMatchingFixedPenalty
        k gamma candidateRate dependencyCoefficient *
        (4 * ((k - 1 : ℕ) : ℝ)) =
      supercriticalMatchingBernoulliPenalty
        k gamma candidateRate dependencyCoefficient := by
  unfold supercriticalMatchingFixedPenalty
  have hk1Nat : 0 < k - 1 := by omega
  have hk1 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hk1Nat
  field_simp [ne_of_gt hk1]
  ring

end

end InducedStars
