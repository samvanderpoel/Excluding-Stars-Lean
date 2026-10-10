import DenseGraph.Combinatorics.MatchingCoefficientBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential growth from an isolated matching

An elementary factorial-product estimate leaves an `exp(c n log n)` gain
even after a `4^q` marked-inverse overhead.  All logarithms are natural.
-/

namespace DenseGraph

theorem exp_half_log_le_labeledMatchingCoefficient {t q : ℕ}
    (hqt : 2 * q ≤ t) (hq : 4 ≤ q) :
    Real.exp ((q : ℝ) / 2 * Real.log ((q : ℝ) / 4)) ≤
      (labeledMatchingCoefficient t q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hhpos : (0 : ℝ) < (q / 2 : ℕ) := by exact_mod_cast (by omega : 0 < q / 2)
  have hbase : (q : ℝ) / 4 ≤ (q / 2 : ℕ) := by
    have hh : (q : ℝ) ≤ 4 * (q / 2 : ℕ) := by exact_mod_cast (by omega : q ≤ 4 * (q / 2))
    linarith
  have hpower : (q : ℝ) / 2 ≤ (q - q / 2 : ℕ) := by
    have hh : (q : ℝ) ≤ 2 * (q - q / 2 : ℕ) := by
      exact_mod_cast (by omega : q ≤ 2 * (q - q / 2))
    linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (q : ℝ) / 4) hbase
  have hlognonneg : 0 ≤ Real.log ((q : ℝ) / 4) := by
    apply Real.log_nonneg
    have : (4 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  calc
    _ ≤ Real.exp (((q - q / 2 : ℕ) : ℝ) * Real.log ((q / 2 : ℕ) : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul hpower hlog hlognonneg (by positivity))
    _ = (((q / 2 : ℕ) : ℝ) ^ (q - q / 2)) := by
      rw [Real.exp_nat_mul, Real.exp_log hhpos]
    _ ≤ _ := by exact_mod_cast half_pow_le_labeledMatchingCoefficient hqt

/-- The gain survives the worst-case `4^q` inverse marking multiplicity.
The explicit threshold is inessential and avoids all asymptotic factorial
machinery. -/
theorem four_pow_mul_exp_le_labeledMatchingCoefficient {t q : ℕ}
    (hqt : 2 * q ≤ t) (hq : 4096 ≤ q) :
    (4 : ℝ) ^ q * Real.exp ((q : ℝ) / 4 * Real.log q) ≤
      (labeledMatchingCoefficient t q : ℝ) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlog : 6 * Real.log 4 ≤ Real.log q := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 4096)
      (show (4096 : ℝ) ≤ q by exact_mod_cast hq)
    have he : Real.log (4096 : ℝ) = 6 * Real.log 4 := by
      rw [show (4096 : ℝ) = 4 ^ 6 by norm_num, Real.log_pow]
      norm_num
    rwa [he] at hh
  have hp : (4 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hp, ← Real.exp_add]
  refine (Real.exp_le_exp.mpr ?_).trans (exp_half_log_le_labeledMatchingCoefficient hqt (by omega))
  rw [Real.log_div hqpos.ne' (by norm_num : (4 : ℝ) ≠ 0)]
  nlinarith [mul_nonneg hqpos.le (sub_nonneg.mpr hlog)]

/-- Uniform exponential gain for every matching size at least `a*n`.
The threshold depends only on the positive constant `a`, not on `q` or the
number `t` of available vertices. -/
theorem eventually_matchingCoefficient_exponential_gain (a : ℝ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ q t : ℕ,
      a * n ≤ q → 2 * q ≤ t →
        (4 : ℝ) ^ q * Real.exp ((a / 8) * n * Real.log n) ≤
          (labeledMatchingCoefficient t q : ℝ) := by
  have hnat : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hscale : Filter.Tendsto (fun n : ℕ ↦ a * n) Filter.atTop Filter.atTop :=
    hnat.const_mul_atTop ha
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hnat
  filter_upwards [hscale.eventually (Filter.eventually_ge_atTop (4096 : ℝ)),
    hlog.eventually (Filter.eventually_ge_atTop (-2 * Real.log a)),
    Filter.eventually_ge_atTop (1 : ℕ)] with n hlarge hloglarge hn
  intro q t hq hqt
  have hqbig : 4096 ≤ q := by exact_mod_cast hlarge.trans hq
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogq : Real.log (n : ℝ) / 2 ≤ Real.log (q : ℝ) := by
    have hh := Real.log_le_log (mul_pos ha hnpos) hq
    rw [Real.log_mul ha.ne' hnpos.ne'] at hh
    linarith
  have hmul : (a / 8) * n * Real.log n ≤ (q : ℝ) / 4 * Real.log q := by
    calc
      _ = (a * n / 4) * (Real.log n / 2) := by ring
      _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right hq (by norm_num)) hlogq
        (by positivity : 0 ≤ Real.log (n : ℝ) / 2) (by positivity)
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hmul) (by positivity)).trans
    (four_pow_mul_exp_le_labeledMatchingCoefficient hqt hqbig)

end DenseGraph
