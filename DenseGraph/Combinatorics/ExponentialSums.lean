import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Elementary exponential summation estimates

This file collects finite estimates used when a fixed combinatorial overhead
has to be absorbed by a linear exponential penalty.  The statements are
independent of graph theory.
-/

noncomputable section

open Filter Finset
open scoped BigOperators

namespace DenseGraph

/-- Every fixed linear function is eventually bounded by an exponential of
arbitrarily small positive linear rate. -/
theorem eventually_natCast_mul_le_exp_mul
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (r : ℝ) * (n : ℝ) ≤ Real.exp (c * (n : ℝ)) := by
  have hlittle :
      (fun x : ℝ ↦ (r : ℝ) * x ^ (1 : ℕ)) =o[atTop]
        (fun x : ℝ ↦ Real.exp (c * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop 1 hc).const_mul_left (r : ℝ)
  have hgrowth := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
  filter_upwards [hgrowth] with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg] using hn

/-- A fixed polynomial in `q` is absorbed uniformly by a linear exponential
penalty when `q` lies between `n / 2` and `n`.  The output deliberately keeps
one quarter of the original rate in the ambient parameter `n`. -/
theorem eventually_pow_succ_mul_exp_neg_le_of_le_two_mul
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ, n ≤ 2 * q → q ≤ n →
      (((q + 1 : ℕ) : ℝ) ^ r) * Real.exp (-(c * (q : ℝ))) ≤
        Real.exp (-((c / 4) * (n : ℝ))) := by
  have hcHalf : 0 < c / 2 := half_pos hc
  have hlittle :
      (fun x : ℝ ↦ (2 : ℝ) ^ r * x ^ r) =o[atTop]
        (fun x : ℝ ↦ Real.exp ((c / 2) * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop r hcHalf).const_mul_left ((2 : ℝ) ^ r)
  have hgrowth : ∀ᶠ q : ℕ in atTop,
      (2 : ℝ) ^ r * (q : ℝ) ^ r ≤ Real.exp ((c / 2) * (q : ℝ)) := by
    have hbound := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
    filter_upwards [hbound] with q hq
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hq
  rw [eventually_atTop] at hgrowth
  obtain ⟨Q, hQ⟩ := hgrowth
  filter_upwards [eventually_ge_atTop (2 * Q), eventually_ge_atTop 2] with
      n hnQ hnTwo
  intro q hnq _hqn
  have hQq : Q ≤ q := by omega
  have hqOne : 1 ≤ q := by omega
  have hpoly : (((q + 1 : ℕ) : ℝ) ^ r) ≤
      (2 : ℝ) ^ r * (q : ℝ) ^ r := by
    have hqAdd : q + 1 ≤ 2 * q := by omega
    calc
      (((q + 1 : ℕ) : ℝ) ^ r) ≤ (((2 * q : ℕ) : ℝ) ^ r) := by
        exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqAdd) r
      _ = (2 : ℝ) ^ r * (q : ℝ) ^ r := by
        push_cast
        rw [mul_pow]
  have hoverhead : (((q + 1 : ℕ) : ℝ) ^ r) ≤
      Real.exp ((c / 2) * (q : ℝ)) := hpoly.trans (hQ q hQq)
  calc
    (((q + 1 : ℕ) : ℝ) ^ r) * Real.exp (-(c * (q : ℝ))) ≤
        Real.exp ((c / 2) * (q : ℝ)) *
          Real.exp (-(c * (q : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hoverhead (Real.exp_pos _).le
    _ = Real.exp (-((c / 2) * (q : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((c / 4) * (n : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have hnqReal : (n : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hnq
      nlinarith

/-- A fixed-base exponential overhead is absorbed by a quadratic exponential
penalty.  The threshold depends only on the base and the positive rate. -/
theorem eventually_pow_mul_exp_neg_sq_le
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ((r ^ n : ℕ) : ℝ) * Real.exp (-(c * (n : ℝ) ^ 2)) ≤
        Real.exp (-((c / 2) * (n : ℝ) ^ 2)) := by
  filter_upwards [eventually_natCast_mul_le_exp_mul (r + 1) (half_pos hc),
      eventually_ge_atTop 1] with n hnExp hnPos
  have hr : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * n := by
    calc
      (r : ℝ) ≤ (r + 1 : ℕ) := by norm_num
      _ ≤ ((r + 1 : ℕ) : ℝ) * n := by
        nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hnPos]
  have hrExp : ((r ^ n : ℕ) : ℝ) ≤
      (Real.exp ((c / 2) * (n : ℝ))) ^ n := by
    push_cast
    exact pow_le_pow_left₀ (by positivity) (hr.trans hnExp) n
  calc
    ((r ^ n : ℕ) : ℝ) * Real.exp (-(c * (n : ℝ) ^ 2)) ≤
        (Real.exp ((c / 2) * (n : ℝ))) ^ n *
          Real.exp (-(c * (n : ℝ) ^ 2)) := by gcongr
    _ = Real.exp (-((c / 2) * (n : ℝ) ^ 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- A binomial choice factor and a fixed multiplicity are absorbed uniformly
in every positive value of the chosen cardinality. -/
theorem eventually_mul_choose_mul_exp_neg_le
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ n →
      ((r * n.choose s : ℕ) : ℝ) *
          Real.exp (-(c * (s : ℝ) * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (s : ℝ) * (n : ℝ))) := by
  have hcHalf : 0 < c / 2 := half_pos hc
  filter_upwards [eventually_natCast_mul_le_exp_mul (r + 1) hcHalf,
      eventually_ge_atTop 1] with n hnExp hnPos s hs _hsn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hr0 : (0 : ℝ) ≤ r := by positivity
  have hrOne : (1 : ℝ) ≤ (r + 1 : ℕ) := by norm_num
  have hrPow : (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ s := by
    calc
      (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by norm_num
      _ = (((r + 1 : ℕ) : ℝ) ^ 1) := by simp
      _ ≤ (((r + 1 : ℕ) : ℝ) ^ s) :=
        pow_le_pow_right₀ hrOne hs
  have hchoose : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by
    exact_mod_cast Nat.choose_le_pow n s
  have hoverhead : ((r * n.choose s : ℕ) : ℝ) ≤
      (((r + 1 : ℕ) : ℝ) * (n : ℝ)) ^ s := by
    rw [Nat.cast_mul, mul_pow]
    exact mul_le_mul hrPow hchoose (by positivity) (by positivity)
  have hpowExp :
      (((r + 1 : ℕ) : ℝ) * (n : ℝ)) ^ s ≤
        (Real.exp ((c / 2) * (n : ℝ))) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hnExp s
  calc
    ((r * n.choose s : ℕ) : ℝ) *
          Real.exp (-(c * (s : ℝ) * (n : ℝ))) ≤
        (Real.exp ((c / 2) * (n : ℝ))) ^ s *
          Real.exp (-(c * (s : ℝ) * (n : ℝ))) := by
      gcongr
      exact hoverhead.trans hpowExp
    _ = Real.exp (-((c / 2) * (s : ℝ) * (n : ℝ))) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

/-- A finite positive-index exponential series keeps a linear exponential
penalty.  The loss of one half in the exponent conveniently absorbs the
number of summands. -/
theorem eventually_sum_Icc_exp_neg_mul_le
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∑ h ∈ Finset.Icc 1 n,
          Real.exp (-(c * (h : ℝ) * (n : ℝ))) ≤
        Real.exp (-((c / 2) * (n : ℝ))) := by
  have hcHalf : 0 < c / 2 := half_pos hc
  filter_upwards [eventually_natCast_mul_le_exp_mul 1 hcHalf,
      eventually_ge_atTop 1] with n hnExp hnPos
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hterm (h : ℕ) (hh : h ∈ Finset.Icc 1 n) :
      Real.exp (-(c * (h : ℝ) * (n : ℝ))) ≤
        Real.exp (-(c * (n : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast (Finset.mem_Icc.mp hh).1
    have hch : c ≤ c * (h : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hh1 hc.le
    have hchn := mul_le_mul_of_nonneg_right hch hn0
    linarith
  calc
    ∑ h ∈ Finset.Icc 1 n,
          Real.exp (-(c * (h : ℝ) * (n : ℝ))) ≤
        ∑ _h ∈ Finset.Icc 1 n, Real.exp (-(c * (n : ℝ))) := by
      exact Finset.sum_le_sum fun h hh ↦ hterm h hh
    _ = (n : ℝ) * Real.exp (-(c * (n : ℝ))) := by
      simp [Nat.card_Icc, hnPos]
    _ ≤ Real.exp ((c / 2) * (n : ℝ)) *
        Real.exp (-(c * (n : ℝ))) := by
      gcongr
      simpa using hnExp
    _ = Real.exp (-((c / 2) * (n : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Summing the binomially many preimages over every positive sparse size
still leaves a positive linear exponential penalty. -/
theorem eventually_sum_mul_choose_mul_exp_neg_le
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∑ s ∈ Finset.Icc 1 n,
          ((r * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ))) ≤
        Real.exp (-((c / 4) * (n : ℝ))) := by
  have hcHalf : 0 < c / 2 := half_pos hc
  filter_upwards [eventually_mul_choose_mul_exp_neg_le r hc,
      eventually_sum_Icc_exp_neg_mul_le hcHalf] with n hnTerm hnSum
  calc
    ∑ s ∈ Finset.Icc 1 n,
          ((r * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ))) ≤
        ∑ s ∈ Finset.Icc 1 n,
          Real.exp (-((c / 2) * (s : ℝ) * (n : ℝ))) := by
      apply Finset.sum_le_sum
      intro s hs
      exact hnTerm s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    _ ≤ Real.exp (-(((c / 2) / 2) * (n : ℝ))) := hnSum
    _ = Real.exp (-((c / 4) * (n : ℝ))) := by ring_nf

end DenseGraph
