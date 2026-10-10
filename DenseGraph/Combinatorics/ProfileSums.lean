import DenseGraph.Combinatorics.ExponentialSums

/-!
# Polynomial complexity weights with linear exponential penalties

A finite collection with complexity r may have `(n+1)^(A*(r+1)+B)`
encodings. One uniform polynomial reserve pays both that factor and the
number of complexity levels. The results are independent of graph theory.
-/

noncomputable section
open Filter Finset
open scoped BigOperators

namespace DenseGraph

/-- Every fixed power of n+1 is eventually below any prescribed positive
linear exponential. This is a specialization of the existing polynomial
absorption estimate, not an additional asymptotic assumption. -/
theorem eventually_natCast_add_one_pow_le_exp_mul
    (P : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ P ≤ Real.exp (c * n) := by
  filter_upwards [eventually_pow_succ_mul_exp_neg_le_of_le_two_mul P hc] with n hn
  have h := hn n (by omega) le_rfl
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (c * n)).le
  have heq : Real.exp (-(c * n)) * Real.exp (c * n) = 1 := by
    rw [← Real.exp_add]
    simp
  have hp : ((n : ℝ) + 1) ^ P ≤ Real.exp ((3 * c / 4) * n) := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, heq, mul_one,
      ← Real.exp_add, show -((c / 4) * (n : ℝ)) + c * n = (3 * c / 4) * n by ring]
      using hmul
  exact hp.trans (Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) ≤ n by positivity]))

/-- Natural-log version of the preceding eventual polynomial reserve. -/
theorem eventually_natCast_mul_log_add_one_le_mul
    (P : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, (P : ℝ) * Real.log ((n : ℝ) + 1) ≤ c * n := by
  filter_upwards [eventually_natCast_add_one_pow_le_exp_mul P hc] with n hn
  have hlog := (Real.log_le_iff_le_exp (by positivity :
    (0 : ℝ) < ((n : ℝ) + 1) ^ P)).mpr hn
  simpa only [Real.log_pow] using hlog

/-- Finite complexity summation with one explicit polynomial reserve.
The rate 32 leaves room for both the per-level encoding and the number of
levels. The empty interval at n=0 is included. -/
theorem sum_profileComplexity_pow_mul_exp_le
    (A B n : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hpoly : ((n : ℝ) + 1) ^ (2 * A + B + 2) ≤ Real.exp (c * n)) :
    ∑ r ∈ Finset.Icc 1 (2 * n),
      ((n : ℝ) + 1) ^ (A * (r + 1) + B) *
        Real.exp (-(32 * c) * r * n) ≤ Real.exp (-c * n) := by
  have hbase : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hpolySmall : ((n : ℝ) + 1) ^ (2 * A + B) ≤ Real.exp (c * n) :=
    (pow_le_pow_right₀ hbase (by omega : 2 * A + B ≤ 2 * A + B + 2)).trans hpoly
  have hcount : (2 : ℝ) * n ≤ Real.exp (c * n) := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      _ ≤ ((n : ℝ) + 1) ^ (2 * A + B + 2) :=
        pow_le_pow_right₀ hbase (by omega)
      _ ≤ _ := hpoly
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 (2 * n)) :
      ((n : ℝ) + 1) ^ (A * (r + 1) + B) *
        Real.exp (-(32 * c) * r * n) ≤ Real.exp (-(31 * c) * n) := by
    have hrOne : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hexponent : A * (r + 1) + B ≤ (2 * A + B) * r := by nlinarith
    have hpower : ((n : ℝ) + 1) ^ (A * (r + 1) + B) ≤
        (Real.exp (c * n)) ^ r := by
      calc
        _ ≤ ((n : ℝ) + 1) ^ ((2 * A + B) * r) :=
          pow_le_pow_right₀ hbase hexponent
        _ = (((n : ℝ) + 1) ^ (2 * A + B)) ^ r := pow_mul _ _ _
        _ ≤ _ := pow_le_pow_left₀ (by positivity) hpolySmall r
    calc
      _ ≤ (Real.exp (c * n)) ^ r * Real.exp (-(32 * c) * r * n) :=
        mul_le_mul_of_nonneg_right hpower (Real.exp_pos _).le
      _ = Real.exp (-(31 * c) * r * n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hrReal : (1 : ℝ) ≤ r := by exact_mod_cast hrOne
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrReal (by positivity : 0 ≤ 31 * c))
          (Nat.cast_nonneg n)
        nlinarith only [hh]
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 (2 * n), Real.exp (-(31 * c) * n) :=
      Finset.sum_le_sum hterm
    _ = (2 : ℝ) * n * Real.exp (-(31 * c) * n) := by
      simp [Nat.card_Icc]
    _ ≤ Real.exp (c * n) * Real.exp (-(31 * c) * n) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (-(30 * c) * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hc (Nat.cast_nonneg n)]

/-- Natural-log form of the finite reserve, convenient for synchronizing
the order thresholds in a scalar parameter package. -/
theorem sum_profileComplexity_pow_mul_exp_le_of_log_reserve
    (A B n : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hlog : ((2 * A + B + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1) ≤ c * n) :
    ∑ r ∈ Finset.Icc 1 (2 * n),
      ((n : ℝ) + 1) ^ (A * (r + 1) + B) *
        Real.exp (-(32 * c) * r * n) ≤ Real.exp (-c * n) := by
  apply sum_profileComplexity_pow_mul_exp_le A B n hc
  calc
    _ = Real.exp (((2 * A + B + 2 : ℕ) : ℝ) * Real.log ((n : ℝ) + 1)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    _ ≤ _ := Real.exp_le_exp.mpr hlog

/-- The explicit polynomial reserve is eventually available, uniformly in
every complexity level. -/
theorem eventually_sum_profileComplexity_pow_mul_exp_le
    (A B : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∑ r ∈ Finset.Icc 1 (2 * n),
        ((n : ℝ) + 1) ^ (A * (r + 1) + B) *
          Real.exp (-(32 * c) * r * n) ≤ Real.exp (-c * n) := by
  filter_upwards [eventually_natCast_add_one_pow_le_exp_mul (2 * A + B + 2) hc]
    with n hn
  exact sum_profileComplexity_pow_mul_exp_le A B n hc.le hn

end DenseGraph
