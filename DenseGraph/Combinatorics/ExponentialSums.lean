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

/-! ### Gaussian sparse-size sums -/

/-- A common sparse-size summand: a fixed polynomial factor, a choice of the
sparse set, and a Gaussian penalty with linear and logarithmic losses. -/
def sparseGaussianWeight
    (r : ℕ) (c C : ℝ) (n s : ℕ) : ℝ :=
  (((n + 1 : ℕ) : ℝ) ^ r) * (n.choose s : ℝ) *
    Real.exp
      (-c * (s : ℝ) ^ 2 + C * (s : ℝ) +
        C * Real.log ((n + 1 : ℕ) : ℝ))

theorem sparseGaussianWeight_nonneg
    (r : ℕ) (c C : ℝ) (n s : ℕ) :
    0 ≤ sparseGaussianWeight r c C n s := by
  unfold sparseGaussianWeight
  positivity

/-- Turn the combinatorial overhead in `sparseGaussianWeight` into its
natural-log exponent. -/
theorem sparseGaussianWeight_le_exp
    (r : ℕ) (c C : ℝ) (n s : ℕ) :
    sparseGaussianWeight r c C n s ≤
      Real.exp
        (-c * (s : ℝ) ^ 2 +
          (((s : ℝ) + C + (r : ℝ)) *
            Real.log ((n + 1 : ℕ) : ℝ)) +
          C * (s : ℝ)) := by
  have hX : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hnle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
  have hchoose : (n.choose s : ℝ) ≤
      (((n + 1 : ℕ) : ℝ) ^ s) := by
    calc
      (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by
        exact_mod_cast Nat.choose_le_pow n s
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ s) :=
        pow_le_pow_left₀ (by positivity) hnle s
  calc
    sparseGaussianWeight r c C n s ≤
        (((n + 1 : ℕ) : ℝ) ^ r) *
          (((n + 1 : ℕ) : ℝ) ^ s) *
          Real.exp
            (-c * (s : ℝ) ^ 2 + C * (s : ℝ) +
              C * Real.log ((n + 1 : ℕ) : ℝ)) := by
      unfold sparseGaussianWeight
      gcongr
    _ = Real.exp
        (-c * (s : ℝ) ^ 2 +
          (((s : ℝ) + C + (r : ℝ)) *
            Real.log ((n + 1 : ℕ) : ℝ)) +
          C * (s : ℝ)) := by
      rw [show (((n + 1 : ℕ) : ℝ) ^ r) =
          Real.exp ((r : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) by
        rw [Real.exp_nat_mul, Real.exp_log hX],
        show (((n + 1 : ℕ) : ℝ) ^ s) =
          Real.exp ((s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) by
        rw [Real.exp_nat_mul, Real.exp_log hX],
        ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

private theorem sparseGaussianWeight_le_exp_neg_half_sq
    (r : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {n s : ℕ}
    (hlog : 1 ≤ Real.log ((n + 1 : ℕ) : ℝ))
    (hcut :
      2 * (1 + 2 * C + (r : ℝ)) *
          Real.log ((n + 1 : ℕ) : ℝ) ≤
        c * (s : ℝ)) :
    sparseGaussianWeight r c C n s ≤
      Real.exp (-(c / 2) * (s : ℝ) ^ 2) := by
  have hs0 : (0 : ℝ) ≤ s := by positivity
  have hs1 : (1 : ℝ) ≤ s := by
    have hD : 1 ≤ 1 + 2 * C + (r : ℝ) := by
      have : 0 ≤ (r : ℝ) := by positivity
      linarith
    have hleft : 0 <
        2 * (1 + 2 * C + (r : ℝ)) *
          Real.log ((n + 1 : ℕ) : ℝ) := by positivity
    have : 0 < c * (s : ℝ) := by nlinarith
    have hsne : s ≠ 0 := by
      intro hs
      subst s
      norm_num at this
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hsne
  apply (sparseGaussianWeight_le_exp r c C n s).trans
  apply Real.exp_le_exp.mpr
  have hCa : C * (s : ℝ) ≤
      C * (s : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg hC hs0]
  have hconst : (C + (r : ℝ)) *
        Real.log ((n + 1 : ℕ) : ℝ) ≤
      (C + (r : ℝ)) * (s : ℝ) *
        Real.log ((n + 1 : ℕ) : ℝ) := by
    have : 0 ≤ C + (r : ℝ) := by positivity
    nlinarith [mul_nonneg this (sub_nonneg.mpr hs1),
      Real.log_natCast_nonneg (n + 1)]
  have hquad :
      (1 + 2 * C + (r : ℝ)) * (s : ℝ) *
          Real.log ((n + 1 : ℕ) : ℝ) ≤
        (c / 2) * (s : ℝ) ^ 2 := by
    nlinarith
  nlinarith

/-- Finite Gaussian-cutoff estimate with the complete binomial and
polynomial overhead.  The cutoff condition is linear in `log (n+1)`; the
right-hand side is a genuine Gaussian tail bound. -/
theorem gaussian_cutoff_sparse_sum_le
    (r : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    {n a : ℕ}
    (hlog : 1 ≤ Real.log ((n + 1 : ℕ) : ℝ))
    (hcut :
      2 * (1 + 2 * C + (r : ℝ)) *
          Real.log ((n + 1 : ℕ) : ℝ) ≤
        c * (a : ℝ)) :
    ∑ s ∈ Finset.Icc a n, sparseGaussianWeight r c C n s ≤
      ((n + 1 : ℕ) : ℝ) *
        Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
  have hterm (s : ℕ) (hs : s ∈ Finset.Icc a n) :
      sparseGaussianWeight r c C n s ≤
        Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
    have has : (a : ℝ) ≤ s := by
      exact_mod_cast (Finset.mem_Icc.mp hs).1
    have hcuts :
        2 * (1 + 2 * C + (r : ℝ)) *
            Real.log ((n + 1 : ℕ) : ℝ) ≤
          c * (s : ℝ) :=
      hcut.trans (mul_le_mul_of_nonneg_left has hc.le)
    refine (sparseGaussianWeight_le_exp_neg_half_sq r hc hC hlog hcuts).trans ?_
    apply Real.exp_le_exp.mpr
    have hsq : (a : ℝ) ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith
    nlinarith
  calc
    ∑ s ∈ Finset.Icc a n, sparseGaussianWeight r c C n s ≤
        ∑ _s ∈ Finset.Icc a n,
          Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
      exact Finset.sum_le_sum fun s hs ↦ hterm s hs
    _ = ((Finset.Icc a n).card : ℝ) *
          Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by simp
    _ ≤ ((n + 1 : ℕ) : ℝ) *
          Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
      gcongr
      have hcard := Finset.card_le_card
        (show Finset.Icc a n ⊆ Finset.Iic n from fun x hx ↦
          Finset.mem_Iic.mpr (Finset.mem_Icc.mp hx).2)
      exact_mod_cast (show (Finset.Icc a n).card ≤ n + 1 by simpa using hcard)

/-- There is a logarithmic cutoff above which the complete Gaussian sparse
sum tends to zero.  This is the asymptotic form of
`gaussian_cutoff_sparse_sum_le`. -/
theorem exists_gaussian_cutoff_sparse_sum_tendsto_zero
    (r : ℕ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto
        (fun n : ℕ ↦
          ∑ s ∈ Finset.Icc
              (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))) n,
            sparseGaussianWeight r c C n s)
        atTop (nhds 0) := by
  let D : ℝ := 1 + 2 * C + (r : ℝ)
  let L : ℝ := 2 * D / c
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have hL : 0 < L := by
    dsimp [L]
    positivity
  refine ⟨L, hL, ?_⟩
  have hX : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hlogTop :
      Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX
  have hinv :
      Tendsto (fun n : ℕ ↦ 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hX
  apply squeeze_zero'
  · filter_upwards with n
    exact Finset.sum_nonneg fun s _ ↦ sparseGaussianWeight_nonneg r c C n s
  · filter_upwards [hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
      hlogTop.eventually
        (eventually_ge_atTop (4 / (c * L ^ 2)))] with n hlog hlarge
    let a : ℕ := Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))
    have hceil :
        L * Real.log ((n + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by
      exact Nat.le_ceil _
    have hcut :
        2 * (1 + 2 * C + (r : ℝ)) *
            Real.log ((n + 1 : ℕ) : ℝ) ≤
          c * (a : ℝ) := by
      calc
        2 * (1 + 2 * C + (r : ℝ)) *
            Real.log ((n + 1 : ℕ) : ℝ) =
          c * (L * Real.log ((n + 1 : ℕ) : ℝ)) := by
            dsimp [L, D]
            field_simp
        _ ≤ c * (a : ℝ) := mul_le_mul_of_nonneg_left hceil hc.le
    have hfinite := gaussian_cutoff_sparse_sum_le r hc hC hlog hcut
    have ha0 : 0 ≤ (a : ℝ) := by positivity
    have hLlog0 :
        0 ≤ L * Real.log ((n + 1 : ℕ) : ℝ) := by positivity
    have hasq :
        (L * Real.log ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ (a : ℝ) ^ 2 := by
      nlinarith
    have hdecay :
        Real.log ((n + 1 : ℕ) : ℝ) -
            (c / 2) * (a : ℝ) ^ 2 ≤
          -Real.log ((n + 1 : ℕ) : ℝ) := by
      have hcL : 0 < c * L ^ 2 := by positivity
      have hquad :
          4 * Real.log ((n + 1 : ℕ) : ℝ) ≤
            c * L ^ 2 * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := by
        have := mul_le_mul_of_nonneg_right hlarge
          (Real.log_natCast_nonneg (n + 1))
        field_simp [hcL.ne'] at this
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hasq (by positivity : 0 ≤ c / 2)]
    calc
      ∑ s ∈ Finset.Icc
              (Nat.ceil (L * Real.log ((n + 1 : ℕ) : ℝ))) n,
            sparseGaussianWeight r c C n s ≤
          ((n + 1 : ℕ) : ℝ) *
            Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
        simpa [a] using hfinite
      _ = Real.exp
          (Real.log ((n + 1 : ℕ) : ℝ) -
            (c / 2) * (a : ℝ) ^ 2) := by
        calc
          ((n + 1 : ℕ) : ℝ) * Real.exp (-(c / 2) * (a : ℝ) ^ 2) =
              Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) *
                Real.exp (-(c / 2) * (a : ℝ) ^ 2) := by
            rw [Real.exp_log (by positivity :
              (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
          _ = Real.exp
              (Real.log ((n + 1 : ℕ) : ℝ) +
                (-(c / 2) * (a : ℝ) ^ 2)) := (Real.exp_add _ _).symm
          _ = Real.exp
              (Real.log ((n + 1 : ℕ) : ℝ) -
                (c / 2) * (a : ℝ) ^ 2) := by ring
      _ ≤ Real.exp (-Real.log ((n + 1 : ℕ) : ℝ)) :=
        Real.exp_le_exp.mpr hdecay
      _ = 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [Real.exp_neg, Real.exp_log (by positivity :
          (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
        ring
  · exact hinv

/-- A finite all-sparse-size bound obtained by completing the square.  Its
logarithm is quadratic in `log (n+1)`, hence sublinear in `n`. -/
theorem all_sparse_gaussian_sum_le_log_quadratic
    (r : ℕ) {c C : ℝ} (hc : 0 < c) :
    ∑ s ∈ Finset.Icc 0 n, sparseGaussianWeight r c C n s ≤
      ((n + 1 : ℕ) : ℝ) * Real.exp
        ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
          (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hterm (s : ℕ) :
      sparseGaussianWeight r c C n s ≤
        Real.exp
          ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
            (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    refine (sparseGaussianWeight_le_exp r c C n s).trans ?_
    apply Real.exp_le_exp.mpr
    have h4c : 0 < 4 * c := by positivity
    have hsquare := sq_nonneg
      (2 * c * (s : ℝ) -
        (Real.log ((n + 1 : ℕ) : ℝ) + C))
    have hcomplete :
        -c * (s : ℝ) ^ 2 +
            (Real.log ((n + 1 : ℕ) : ℝ) + C) * (s : ℝ) ≤
          (Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) := by
      apply (le_div_iff₀ h4c).2
      nlinarith
    nlinarith
  calc
    ∑ s ∈ Finset.Icc 0 n, sparseGaussianWeight r c C n s ≤
        ∑ _s ∈ Finset.Icc 0 n,
          Real.exp
            ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
              (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun s _hs ↦ hterm s
    _ = ((n + 1 : ℕ) : ℝ) * Real.exp
        ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
          (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) := by
      simp [Nat.card_Icc]

/-- The full sparse-size sum is subexponential: every prescribed positive
linear exponential eventually dominates it. -/
theorem eventually_subexponential_all_sparse_sum_le
    (r : ℕ) {c C eta : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop,
      ∑ s ∈ Finset.Icc 0 n, sparseGaussianWeight r c C n s ≤
        Real.exp (eta * (n : ℝ)) := by
  let A : ℝ :=
    1 / (4 * c) + (1 + C + (r : ℝ) + C / (2 * c)) +
      C ^ 2 / (4 * c)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hX : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hlogTop :
      Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX
  have hsmall :
      (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ) ^ 2) =o[atTop]
        (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) :=
    Real.isLittleO_pow_log_id_atTop.comp_tendsto hX
  have heps : 0 < eta / (2 * A) := by positivity
  filter_upwards [hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
      hsmall.bound heps, eventually_ge_atTop 1] with n hlog hsmalln hn
  have hXpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
    Real.log_natCast_nonneg (n + 1)
  have hsquare :
      Real.log ((n + 1 : ℕ) : ℝ) ^ 2 ≤
        (eta / (2 * A)) * ((n + 1 : ℕ) : ℝ) := by
    have hsq0 : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
    have hX0 : 0 ≤ ((n + 1 : ℕ) : ℝ) := hXpos.le
    simpa only [Real.norm_eq_abs, abs_of_nonneg hsq0,
      abs_of_nonneg hX0] using hsmalln
  have hXle : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show n + 1 ≤ 2 * n by omega)
  have hAsquare :
      A * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 ≤
        eta * (n : ℝ) := by
    have := mul_le_mul_of_nonneg_left hsquare hA.le
    field_simp [hA.ne'] at this
    nlinarith
  have hexponent :
      Real.log ((n + 1 : ℕ) : ℝ) +
          (Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
          (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ) ≤
        eta * (n : ℝ) := by
    have hlogSq :
        Real.log ((n + 1 : ℕ) : ℝ) ≤
          Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have honeSq :
        1 ≤ Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have hc4 : 0 < 4 * c := by positivity
    have hc2 : 0 < 2 * c := by positivity
    have hcoeff1 : 0 ≤ 1 + C + (r : ℝ) + C / (2 * c) := by positivity
    have hcoeff2 : 0 ≤ C ^ 2 / (4 * c) := by positivity
    have hexpand :
        Real.log ((n + 1 : ℕ) : ℝ) +
            (Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
            (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ) =
          (1 / (4 * c)) * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 +
            (1 + C + (r : ℝ) + C / (2 * c)) *
              Real.log ((n + 1 : ℕ) : ℝ) +
            C ^ 2 / (4 * c) := by
      field_simp
      ring
    have hboundA :
        Real.log ((n + 1 : ℕ) : ℝ) +
            (Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
            (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ) ≤
          A * Real.log ((n + 1 : ℕ) : ℝ) ^ 2 := by
      rw [hexpand]
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left hlogSq hcoeff1,
        mul_le_mul_of_nonneg_left honeSq hcoeff2]
    exact hboundA.trans hAsquare
  calc
    ∑ s ∈ Finset.Icc 0 n, sparseGaussianWeight r c C n s ≤
        ((n + 1 : ℕ) : ℝ) * Real.exp
          ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
            (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) :=
      all_sparse_gaussian_sum_le_log_quadratic r hc
    _ = Real.exp
        (Real.log ((n + 1 : ℕ) : ℝ) +
          ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
            (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ))) := by
      calc
        ((n + 1 : ℕ) : ℝ) * Real.exp
            ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
              (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) =
          Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) * Real.exp
            ((Real.log ((n + 1 : ℕ) : ℝ) + C) ^ 2 / (4 * c) +
              (C + (r : ℝ)) * Real.log ((n + 1 : ℕ) : ℝ)) := by
            rw [Real.exp_log hXpos]
        _ = _ := (Real.exp_add _ _).symm
    _ ≤ Real.exp (eta * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith

end DenseGraph
