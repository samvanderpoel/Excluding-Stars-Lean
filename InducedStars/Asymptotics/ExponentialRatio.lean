import InducedStars.FiniteModels.Normalization
import Mathlib.Tactic

/-!
# Converting normalized base-two gaps to exponential ratio bounds

This file isolates the elementary conversion used by the rough-structure
theorems.  The finite models are normalized by the number
`completeEdgeCount n = n.choose 2` of unordered pairs, whereas their final
probability bounds are conventionally written as `exp (-C * n ^ 2)`.

The project's `log2` is totalized at zero.  Consequently the ratio proof
splits off a zero numerator before applying logarithm identities; the
denominator is always assumed strictly positive.
-/

noncomputable section

namespace InducedStars

/-- For every `n ≥ 2`, the number of unordered vertex pairs is at least a
quarter of the ordered square. -/
theorem quarter_square_le_completeEdgeCount {n : ℕ} (hn : 2 ≤ n) :
    (n : ℝ) ^ 2 / 4 ≤ (completeEdgeCount n : ℝ) := by
  rw [completeEdgeCount, Nat.cast_choose_two]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ n by positivity)
    (sub_nonneg.mpr hnR)]

/-- Orientation of `quarter_square_le_completeEdgeCount` matching the usual
written inequality `n.choose 2 ≥ n² / 4`. -/
theorem completeEdgeCount_ge_quarter_square {n : ℕ} (hn : 2 ≤ n) :
    (completeEdgeCount n : ℝ) ≥ (n : ℝ) ^ 2 / 4 :=
  quarter_square_le_completeEdgeCount hn

/-- A gap of `c` between normalized base-two logarithms gives a ratio bound
on the exact binomial scale.  The numerator is merely nonnegative: when it
is zero the conclusion follows directly, avoiding any use of `log 0`.

No sign assumption on `c` is needed for this exact-scale conversion. -/
theorem ratio_le_exp_neg_completeEdgeCount_of_normalizedLog_gap
    {n : ℕ} (hn : 2 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b)
    (hgap : normalizedLogProbability n a ≤
      normalizedLogProbability n b - c) :
    a / b ≤ Real.exp
      (-c * Real.log 2 * (completeEdgeCount n : ℝ)) := by
  rcases ha.eq_or_lt with ha0 | ha
  · rw [← ha0, zero_div]
    exact Real.exp_pos _ |>.le
  · have hN : 0 < (completeEdgeCount n : ℝ) := by
      exact_mod_cast Nat.choose_pos hn
    unfold normalizedLogProbability normalizedLogAtGraphOrder at hgap
    have hnormalized :
        log2 a / (completeEdgeCount n : ℝ) -
            log2 b / (completeEdgeCount n : ℝ) ≤ -c := by
      linarith
    have hlog2 :
        log2 a - log2 b ≤
          -c * (completeEdgeCount n : ℝ) := by
      have hdiv :
          (log2 a - log2 b) / (completeEdgeCount n : ℝ) ≤ -c := by
        simpa only [sub_div] using hnormalized
      exact (div_le_iff₀ hN).mp hdiv
    have hlog :
        Real.log a - Real.log b ≤
          (-c * (completeEdgeCount n : ℝ)) * Real.log 2 := by
      have hdiv :
          (Real.log a - Real.log b) / Real.log 2 ≤
            -c * (completeEdgeCount n : ℝ) := by
        simpa only [log2, sub_div] using hlog2
      exact (div_le_iff₀ realLogTwo_pos).mp hdiv
    calc
      a / b = Real.exp (Real.log a) / Real.exp (Real.log b) := by
        rw [Real.exp_log ha, Real.exp_log hb]
      _ = Real.exp (Real.log a - Real.log b) :=
        (Real.exp_sub _ _).symm
      _ ≤ Real.exp
          ((-c * (completeEdgeCount n : ℝ)) * Real.log 2) :=
        Real.exp_le_exp.mpr hlog
      _ = Real.exp
          (-c * Real.log 2 * (completeEdgeCount n : ℝ)) := by
        congr 1
        ring

/-- Public `n²`-scale conversion.  If the numerator is nonnegative, the
denominator is positive, and their normalized base-two logarithms have a
positive gap `c`, then their ratio is at most
`exp (-(c * log 2 / 4) * n²)`.

The displayed exponential constant is strictly positive because `c > 0`
and `Real.log 2 > 0`. -/
theorem ratio_le_exp_neg_square_of_normalizedLog_gap
    {n : ℕ} (hn : 2 ≤ n) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c)
    (hgap : normalizedLogProbability n a ≤
      normalizedLogProbability n b - c) :
    a / b ≤ Real.exp
      (-(c * Real.log 2 / 4) * (n : ℝ) ^ 2) := by
  have hbinomial :=
    ratio_le_exp_neg_completeEdgeCount_of_normalizedLog_gap
      hn ha hb hgap
  apply hbinomial.trans
  apply Real.exp_le_exp.mpr
  have hcoefficient : 0 ≤ c * Real.log 2 :=
    mul_nonneg hc.le realLogTwo_pos.le
  have hscaled := mul_le_mul_of_nonneg_left
    (quarter_square_le_completeEdgeCount hn) hcoefficient
  calc
    -c * Real.log 2 * (completeEdgeCount n : ℝ) =
        -(c * Real.log 2 * (completeEdgeCount n : ℝ)) := by ring
    _ ≤ -(c * Real.log 2 * ((n : ℝ) ^ 2 / 4)) :=
      neg_le_neg hscaled
    _ = -(c * Real.log 2 / 4) * (n : ℝ) ^ 2 := by ring

end InducedStars
