import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
import DenseGraph.Combinatorics.BinomialEntropy

/-!
# Second-order comparison of nearby binomial coefficients

This file gives a finite, non-asymptotic comparison between
`Nat.choose (N - K) (M + L)` and `Nat.choose N M`.  Its cubic error is
explicit.  The proof uses the entropy sandwich and the elementary Taylor
remainder estimate for `Real.log`; it does not use Stirling's formula.
-/

noncomputable section

namespace DenseGraph

open Finset

/-- The logarithm is `1/lambda`-Lipschitz on the positive half-line
`[lambda,∞)`.  This elementary finite form is convenient when replacing an
exact binomial density by its limiting value. -/
theorem abs_log_sub_log_le_div_of_lower
    {lambda x y : ℝ} (hlambda : 0 < lambda)
    (hx : lambda ≤ x) (hy : lambda ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / lambda := by
  have hx0 : 0 < x := hlambda.trans_le hx
  have hy0 : 0 < y := hlambda.trans_le hy
  rcases le_total x y with hxy | hyx
  · have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
    calc
      Real.log y - Real.log x = Real.log (y / x) := by
        rw [Real.log_div hy0.ne' hx0.ne']
      _ ≤ y / x - 1 := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
      _ = (y - x) / x := by field_simp
      _ ≤ (y - x) / lambda :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hlambda hx
  · have hlog : Real.log y ≤ Real.log x := Real.log_le_log hy0 hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hlog),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    calc
      Real.log x - Real.log y = Real.log (x / y) := by
        rw [Real.log_div hx0.ne' hy0.ne']
      _ ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
      _ = (x - y) / y := by field_simp
      _ ≤ (x - y) / lambda :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hlambda hy

/-- The elementary cubic remainder used below.  On `[0,1)` it bounds the
error after the quadratic Taylor polynomial of `log (1 - x)`. -/
def logOneSubCubicRemainder (x : ℝ) : ℝ :=
  x ^ 3 / (1 - x)

private theorem abs_log_one_sub_secondOrder_le
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |x + x ^ 2 / 2 + Real.log (1 - x)| ≤
      logOneSubCubicRemainder x := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := x) (by simpa [abs_of_nonneg hx0] using hx1) 2
  norm_num [logOneSubCubicRemainder, abs_of_nonneg hx0,
    Finset.sum_range_succ] at h ⊢
  exact h

private theorem log_one_sub_secondOrder_upper
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log (1 - x) ≤
      -x - x ^ 2 / 2 + logOneSubCubicRemainder x := by
  have h := abs_log_one_sub_secondOrder_le hx0 hx1
  linarith [le_abs_self (x + x ^ 2 / 2 + Real.log (1 - x))]

private theorem log_one_sub_secondOrder_lower
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -x - x ^ 2 / 2 - logOneSubCubicRemainder x ≤
      Real.log (1 - x) := by
  have h := abs_log_one_sub_secondOrder_le hx0 hx1
  have hneg := (neg_le_of_abs_le h)
  linarith

private theorem log_one_add_secondOrder_lower
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x - x ^ 2 / 2 - logOneSubCubicRemainder x ≤
      Real.log (1 + x) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -x) (by simpa [abs_of_nonneg hx0] using hx1) 2
  norm_num [abs_of_nonneg hx0, Finset.sum_range_succ] at h
  have hneg := neg_le_of_abs_le h
  unfold logOneSubCubicRemainder
  linarith

/-- Closed logarithmic form of the entropy perspective, valid in the
interior of a binomial slice. -/
theorem binomialEntropyPerspective_eq_log_formula
    {N M : ℕ} (hM : 0 < M) (hMN : M < N) :
    binomialEntropyPerspective N M =
      (N : ℝ) * Real.log (N : ℝ) -
        (M : ℝ) * Real.log (M : ℝ) -
          ((N - M : ℕ) : ℝ) * Real.log ((N - M : ℕ) : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hM.trans hMN
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hsub : (0 : ℝ) < (N - M : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hMN
  have hratio :
      1 - (M : ℝ) / (N : ℝ) =
        ((N - M : ℕ) : ℝ) / (N : ℝ) := by
    rw [Nat.cast_sub hMN.le]
    field_simp
  rw [binomialEntropyPerspective, Real.binEntropy,
    Real.log_inv, Real.log_inv, Real.log_div hMR.ne' hN.ne',
    hratio, Real.log_div hsub.ne' hN.ne']
  rw [Nat.cast_sub hMN.le]
  field_simp
  ring

/-- The closed real-valued entropy perspective.  On `0 < M < N`, this is
equal to `N * Real.binEntropy (M / N)`. -/
def realBinomialEntropyPerspective (N M : ℝ) : ℝ :=
  N * Real.log N - M * Real.log M - (N - M) * Real.log (N - M)

/-- Explicit third-order error for simultaneously deleting `K` capacity
coordinates and adding `L` selected coordinates.  The three occurrences of
`logOneSubCubicRemainder` are bounded Taylor remainders; consequently this
quantity is genuinely cubic whenever the three displayed ratios stay in a
compact subinterval of `[0,1)`. -/
def binomialSecondOrderCubicRemainder
    (N M K L : ℝ) : ℝ :=
  K ^ 3 / (2 * N ^ 2) + L ^ 3 / (2 * M ^ 2) -
      (K + L) ^ 3 / (2 * (N - M) ^ 2) +
    (N - K) * logOneSubCubicRemainder (K / N) +
    (M + L) * logOneSubCubicRemainder (L / M) +
    (N - M - (K + L)) *
      logOneSubCubicRemainder ((K + L) / (N - M))

private theorem logOneSubCubicRemainder_le_two_mul_cube
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    logOneSubCubicRemainder x ≤ 2 * x ^ 3 := by
  have hden : 0 < 1 - x := by linarith
  rw [logOneSubCubicRemainder, div_le_iff₀ hden]
  have hpow : 0 ≤ x ^ 3 := pow_nonneg hx0 3
  have hprod := mul_nonpos_of_nonneg_of_nonpos hpow (show 2 * x - 1 ≤ 0 by linarith)
  nlinarith

private theorem binomialSecondOrderCubicRemainder_le_separated
    {N M K L : ℝ}
    (hM : 0 < M) (hMN : M < N)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    binomialSecondOrderCubicRemainder N M K L ≤
      3 * K ^ 3 / N ^ 2 + 4 * L ^ 3 / M ^ 2 +
        2 * (K + L) ^ 3 / (N - M) ^ 2 := by
  have hN : 0 < N := hM.trans hMN
  have hA : 0 < N - M := sub_pos.mpr hMN
  have hNK : 0 ≤ N - K := by linarith
  have hML : 0 ≤ M + L := by linarith
  have hAd : 0 ≤ N - M - (K + L) := by linarith
  have htK0 : 0 ≤ K / N := by positivity
  have htL0 : 0 ≤ L / M := by positivity
  have htd0 : 0 ≤ (K + L) / (N - M) := by positivity
  have htKhalf : K / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hN]
    nlinarith
  have htLhalf : L / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hM]
    nlinarith
  have htdhalf : (K + L) / (N - M) ≤ 1 / 2 := by
    rw [div_le_iff₀ hA]
    nlinarith
  have hRN0 : 0 ≤ logOneSubCubicRemainder (K / N) := by
    unfold logOneSubCubicRemainder
    exact div_nonneg (pow_nonneg htK0 3) (by linarith)
  have hRM0 : 0 ≤ logOneSubCubicRemainder (L / M) := by
    unfold logOneSubCubicRemainder
    exact div_nonneg (pow_nonneg htL0 3) (by linarith)
  have hRA0 : 0 ≤
      logOneSubCubicRemainder ((K + L) / (N - M)) := by
    unfold logOneSubCubicRemainder
    exact div_nonneg (pow_nonneg htd0 3) (by linarith)
  have hRN :
      (N - K) * logOneSubCubicRemainder (K / N) ≤
        2 * K ^ 3 / N ^ 2 := by
    calc
      (N - K) * logOneSubCubicRemainder (K / N) ≤
          N * logOneSubCubicRemainder (K / N) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hRN0
      _ ≤ N * (2 * (K / N) ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (logOneSubCubicRemainder_le_two_mul_cube htK0 htKhalf) hN.le
      _ = 2 * K ^ 3 / N ^ 2 := by
        field_simp
  have hRM :
      (M + L) * logOneSubCubicRemainder (L / M) ≤
        3 * L ^ 3 / M ^ 2 := by
    have hMLbound : M + L ≤ (3 / 2 : ℝ) * M := by linarith
    calc
      (M + L) * logOneSubCubicRemainder (L / M) ≤
          ((3 / 2 : ℝ) * M) * logOneSubCubicRemainder (L / M) := by
        gcongr
      _ ≤ ((3 / 2 : ℝ) * M) * (2 * (L / M) ^ 3) := by
        gcongr
        exact logOneSubCubicRemainder_le_two_mul_cube htL0 htLhalf
      _ = 3 * L ^ 3 / M ^ 2 := by
        field_simp
  have hRA :
      (N - M - (K + L)) *
          logOneSubCubicRemainder ((K + L) / (N - M)) ≤
        2 * (K + L) ^ 3 / (N - M) ^ 2 := by
    calc
      (N - M - (K + L)) *
          logOneSubCubicRemainder ((K + L) / (N - M)) ≤
          (N - M) *
            logOneSubCubicRemainder ((K + L) / (N - M)) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hRA0
      _ ≤ (N - M) * (2 * ((K + L) / (N - M)) ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (logOneSubCubicRemainder_le_two_mul_cube htd0 htdhalf) hA.le
      _ = 2 * (K + L) ^ 3 / (N - M) ^ 2 := by
        field_simp
  have hneg :
      -(K + L) ^ 3 / (2 * (N - M) ^ 2) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (pow_nonneg (add_nonneg hK hL) 3))
      (by positivity)
  have hKterm : 0 ≤ K ^ 3 / N ^ 2 := by positivity
  have hLterm : 0 ≤ L ^ 3 / M ^ 2 := by positivity
  unfold binomialSecondOrderCubicRemainder
  ring_nf at hRN hRM hRA hneg hKterm hLterm ⊢
  linarith

/-- Compact-band form of the cubic-remainder bound.  This is uniform in all
four perturbation variables: only the fixed lower density `lambda` enters
the constant. -/
theorem binomialSecondOrderCubicRemainder_le_of_compact_band
    {lambda N M K L : ℝ}
    (hlambda : 0 < lambda)
    (hM : 0 < M) (hMN : M < N)
    (hLower : lambda * N ≤ M)
    (hUpper : M ≤ (1 - lambda) * N)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    binomialSecondOrderCubicRemainder N M K L ≤
      (3 + 6 / lambda ^ 2) * (K + L) ^ 3 / N ^ 2 := by
  have hN : 0 < N := hM.trans hMN
  have hA : 0 < N - M := sub_pos.mpr hMN
  have hsep := binomialSecondOrderCubicRemainder_le_separated
    hM hMN hK hL hKhalf hLhalf hdhalf
  have hKsum : K ≤ K + L := by linarith
  have hLsum : L ≤ K + L := by linarith
  have hKpow : K ^ 3 ≤ (K + L) ^ 3 :=
    pow_le_pow_left₀ hK hKsum 3
  have hLpow : L ^ 3 ≤ (K + L) ^ 3 :=
    pow_le_pow_left₀ hL hLsum 3
  have hxK :
      K ^ 3 / N ^ 2 ≤ (K + L) ^ 3 / N ^ 2 := by
    exact div_le_div_of_nonneg_right hKpow (sq_nonneg N)
  have hlambdaN : 0 < lambda * N := mul_pos hlambda hN
  have hlambdaSq : 0 < lambda ^ 2 * N ^ 2 := by positivity
  have hMSq : lambda ^ 2 * N ^ 2 ≤ M ^ 2 := by
    have := mul_self_le_mul_self hlambdaN.le hLower
    nlinarith
  have hAShift : lambda * N ≤ N - M := by
    nlinarith
  have hASq : lambda ^ 2 * N ^ 2 ≤ (N - M) ^ 2 := by
    have := mul_self_le_mul_self hlambdaN.le hAShift
    nlinarith
  have hxL :
      L ^ 3 / M ^ 2 ≤
        (K + L) ^ 3 / (lambda ^ 2 * N ^ 2) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hM) hlambdaSq]
    calc
      L ^ 3 * (lambda ^ 2 * N ^ 2) ≤
          (K + L) ^ 3 * (lambda ^ 2 * N ^ 2) := by
        gcongr
      _ ≤ (K + L) ^ 3 * M ^ 2 := by
        gcongr
  have hxA :
      (K + L) ^ 3 / (N - M) ^ 2 ≤
        (K + L) ^ 3 / (lambda ^ 2 * N ^ 2) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hA) hlambdaSq]
    exact mul_le_mul_of_nonneg_left hASq (pow_nonneg (add_nonneg hK hL) 3)
  calc
    binomialSecondOrderCubicRemainder N M K L ≤
        3 * K ^ 3 / N ^ 2 + 4 * L ^ 3 / M ^ 2 +
          2 * (K + L) ^ 3 / (N - M) ^ 2 := hsep
    _ ≤ 3 * ((K + L) ^ 3 / N ^ 2) +
        6 * ((K + L) ^ 3 / (lambda ^ 2 * N ^ 2)) := by
      ring_nf at hxK hxL hxA ⊢
      linarith
    _ = (3 + 6 / lambda ^ 2) * (K + L) ^ 3 / N ^ 2 := by
      field_simp

private theorem realBinomialEntropyPerspective_sub_secondOrder_le
    {N M K L : ℝ}
    (hM : 0 < M) (hMN : M < N)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    realBinomialEntropyPerspective (N - K) (M + L) -
        realBinomialEntropyPerspective N M ≤
      K * Real.log ((N - M) / N) +
        L * Real.log ((N - M) / M) -
        (K + L) ^ 2 / (2 * (N - M)) +
        K ^ 2 / (2 * N) - L ^ 2 / (2 * M) +
        binomialSecondOrderCubicRemainder N M K L := by
  have hN : 0 < N := hM.trans hMN
  have hA : 0 < N - M := sub_pos.mpr hMN
  have hNK : 0 < N - K := by linarith
  have hML : 0 < M + L := by linarith
  have hAd : 0 < N - M - (K + L) := by linarith
  have htK0 : 0 ≤ K / N := div_nonneg hK hN.le
  have htK1 : K / N < 1 := (div_lt_one hN).2 (by linarith)
  have htL0 : 0 ≤ L / M := div_nonneg hL hM.le
  have htL1 : L / M < 1 := (div_lt_one hM).2 (by linarith)
  have htd0 : 0 ≤ (K + L) / (N - M) :=
    div_nonneg (add_nonneg hK hL) hA.le
  have htd1 : (K + L) / (N - M) < 1 :=
    (div_lt_one hA).2 (by linarith)
  have hlogNK :
      Real.log (N - K) =
        Real.log N + Real.log (1 - K / N) := by
    rw [show N - K = N * (1 - K / N) by field_simp]
    exact Real.log_mul hN.ne' (by positivity)
  have hlogML :
      Real.log (M + L) =
        Real.log M + Real.log (1 + L / M) := by
    rw [show M + L = M * (1 + L / M) by field_simp]
    exact Real.log_mul hM.ne' (by positivity)
  have hlogAd :
      Real.log (N - M - (K + L)) =
        Real.log (N - M) +
          Real.log (1 - (K + L) / (N - M)) := by
    rw [show N - M - (K + L) =
        (N - M) * (1 - (K + L) / (N - M)) by field_simp]
    exact Real.log_mul hA.ne' (by positivity)
  have hshiftA : N - K - (M + L) = N - M - (K + L) := by ring
  have hexact :
      realBinomialEntropyPerspective (N - K) (M + L) -
          realBinomialEntropyPerspective N M =
        K * Real.log ((N - M) / N) +
          L * Real.log ((N - M) / M) +
          (N - K) * Real.log (1 - K / N) -
          (M + L) * Real.log (1 + L / M) -
          (N - M - (K + L)) *
            Real.log (1 - (K + L) / (N - M)) := by
    rw [realBinomialEntropyPerspective, realBinomialEntropyPerspective,
      hlogNK, hlogML, hshiftA, hlogAd,
      Real.log_div hA.ne' hN.ne', Real.log_div hA.ne' hM.ne']
    ring
  have htermN := mul_le_mul_of_nonneg_left
    (log_one_sub_secondOrder_upper htK0 htK1) hNK.le
  have htermM := neg_le_neg (mul_le_mul_of_nonneg_left
    (log_one_add_secondOrder_lower htL0 htL1) hML.le)
  have htermA := neg_le_neg (mul_le_mul_of_nonneg_left
    (log_one_sub_secondOrder_lower htd0 htd1) hAd.le)
  rw [hexact]
  unfold binomialSecondOrderCubicRemainder
  calc
    K * Real.log ((N - M) / N) +
          L * Real.log ((N - M) / M) +
          (N - K) * Real.log (1 - K / N) -
          (M + L) * Real.log (1 + L / M) -
          (N - M - (K + L)) *
            Real.log (1 - (K + L) / (N - M)) ≤
        K * Real.log ((N - M) / N) +
          L * Real.log ((N - M) / M) +
          (N - K) *
            (- (K / N) - (K / N) ^ 2 / 2 +
              logOneSubCubicRemainder (K / N)) -
          (M + L) *
            (L / M - (L / M) ^ 2 / 2 -
              logOneSubCubicRemainder (L / M)) -
          (N - M - (K + L)) *
            (-((K + L) / (N - M)) -
              ((K + L) / (N - M)) ^ 2 / 2 -
              logOneSubCubicRemainder ((K + L) / (N - M))) := by
      linarith
    _ = K * Real.log ((N - M) / N) +
        L * Real.log ((N - M) / M) -
        (K + L) ^ 2 / (2 * (N - M)) +
        K ^ 2 / (2 * N) - L ^ 2 / (2 * M) +
        (K ^ 3 / (2 * N ^ 2) + L ^ 3 / (2 * M ^ 2) -
          (K + L) ^ 3 / (2 * (N - M) ^ 2) +
          (N - K) * logOneSubCubicRemainder (K / N) +
          (M + L) * logOneSubCubicRemainder (L / M) +
          (N - M - (K + L)) *
            logOneSubCubicRemainder ((K + L) / (N - M))) := by
      field_simp
      ring

/-- The explicit cubic error in the natural-number binomial comparison. -/
def binomialSecondOrderCubicError (N M K L : ℕ) : ℝ :=
  binomialSecondOrderCubicRemainder (N : ℝ) (M : ℝ) (K : ℝ) (L : ℝ)

/-- Natural-number interface to the compact-band cubic bound.  In
particular, the error is at most an explicit constant depending only on
`lambda` times `(K+L)^3/N^2`. -/
theorem binomialSecondOrderCubicError_le_of_compact_band
    {lambda : ℝ} {N M K L : ℕ}
    (hlambda : 0 < lambda)
    (hM : 0 < M) (hMN : M < N)
    (hLower : lambda * (N : ℝ) ≤ (M : ℝ))
    (hUpper : (M : ℝ) ≤ (1 - lambda) * (N : ℝ))
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    binomialSecondOrderCubicError N M K L ≤
      (3 + 6 / lambda ^ 2) * ((K + L : ℕ) : ℝ) ^ 3 / (N : ℝ) ^ 2 := by
  have hdhalfR :
      2 * ((K : ℝ) + (L : ℝ)) ≤ (N : ℝ) - (M : ℝ) := by
    calc
      2 * ((K : ℝ) + (L : ℝ)) = ((2 * (K + L) : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast hdhalf
      _ = (N : ℝ) - (M : ℝ) := by rw [Nat.cast_sub hMN.le]
  have h := binomialSecondOrderCubicRemainder_le_of_compact_band
    hlambda (by exact_mod_cast hM) (by exact_mod_cast hMN)
    hLower hUpper (by positivity) (by positivity)
    (by exact_mod_cast hKhalf) (by exact_mod_cast hLhalf) hdhalfR
  simpa [binomialSecondOrderCubicError, Nat.cast_add] using h

/-- Second-order perturbation of the entropy perspective.  The half-range
hypotheses make all three logarithmic Taylor expansions uniform and, in
particular, imply that the shifted binomial slice is admissible. -/
theorem binomialEntropyPerspective_sub_capacity_add_selected_secondOrder_le
    {N M K L : ℕ}
    (hM : 0 < M) (hMN : M < N)
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    binomialEntropyPerspective (N - K) (M + L) -
        binomialEntropyPerspective N M ≤
      (K : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (N : ℝ)) +
        (L : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (M : ℝ)) -
        ((K + L : ℕ) : ℝ) ^ 2 /
          (2 * ((N - M : ℕ) : ℝ)) +
        (K : ℝ) ^ 2 / (2 * (N : ℝ)) -
        (L : ℝ) ^ 2 / (2 * (M : ℝ)) +
        binomialSecondOrderCubicError N M K L := by
  have hKle : K ≤ N := by omega
  have hdle : K + L ≤ N - M := by omega
  have hshift : M + L < N - K := by omega
  have hshiftPos : 0 < M + L := by omega
  have hdhalfR :
      2 * ((K : ℝ) + (L : ℝ)) ≤ (N : ℝ) - (M : ℝ) := by
    calc
      2 * ((K : ℝ) + (L : ℝ)) = ((2 * (K + L) : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast hdhalf
      _ = (N : ℝ) - (M : ℝ) := by rw [Nat.cast_sub hMN.le]
  have hanalytic := realBinomialEntropyPerspective_sub_secondOrder_le
    (N := (N : ℝ)) (M := (M : ℝ)) (K := (K : ℝ)) (L := (L : ℝ))
    (by exact_mod_cast hM) (by exact_mod_cast hMN)
    (by positivity) (by positivity)
    (by exact_mod_cast hKhalf) (by exact_mod_cast hLhalf)
    hdhalfR
  rw [binomialEntropyPerspective_eq_log_formula hshiftPos hshift,
    binomialEntropyPerspective_eq_log_formula hM hMN]
  simpa [realBinomialEntropyPerspective, binomialSecondOrderCubicError,
    Nat.cast_sub hKle, Nat.cast_sub hMN.le, Nat.cast_sub hshift.le,
    Nat.cast_add] using hanalytic

/-- A reusable finite second-order comparison for a simultaneous capacity
decrease and selected-count increase.  All logarithms are natural.  The
term `binomialSecondOrderCubicError` is the explicit Taylor remainder; no
asymptotic notation or Stirling estimate is hidden in the statement. -/
theorem choose_sub_capacity_add_selected_secondOrder_le
    {N M K L : ℕ}
    (hM : 0 < M) (hMN : M < N)
    (hKhalf : 2 * K ≤ N)
    (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    (Nat.choose (N - K) (M + L) : ℝ) ≤
      (Nat.choose N M : ℝ) * Real.exp
        ((K : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (N : ℝ)) +
          (L : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (M : ℝ)) -
          ((K + L : ℕ) : ℝ) ^ 2 /
            (2 * ((N - M : ℕ) : ℝ)) +
          (K : ℝ) ^ 2 / (2 * (N : ℝ)) -
          (L : ℝ) ^ 2 / (2 * (M : ℝ)) +
          binomialSecondOrderCubicError N M K L +
          Real.log ((N + 1 : ℕ) : ℝ)) := by
  have hshift : M + L < N - K := by omega
  have hbasePos : (0 : ℝ) < Nat.choose N M := by
    exact_mod_cast Nat.choose_pos hMN.le
  have hshiftPos : (0 : ℝ) < Nat.choose (N - K) (M + L) := by
    exact_mod_cast Nat.choose_pos hshift.le
  have hupper := log_choose_upper_binEntropy hshift.le
  have hlower := log_choose_lower_binEntropy hMN.le
  have hsecond :=
    binomialEntropyPerspective_sub_capacity_add_selected_secondOrder_le
      hM hMN hKhalf hLhalf hdhalf
  have hlog :
      Real.log (Nat.choose (N - K) (M + L) : ℝ) ≤
        Real.log (Nat.choose N M : ℝ) +
          ((K : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (N : ℝ)) +
            (L : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (M : ℝ)) -
            ((K + L : ℕ) : ℝ) ^ 2 /
              (2 * ((N - M : ℕ) : ℝ)) +
            (K : ℝ) ^ 2 / (2 * (N : ℝ)) -
            (L : ℝ) ^ 2 / (2 * (M : ℝ)) +
            binomialSecondOrderCubicError N M K L +
            Real.log ((N + 1 : ℕ) : ℝ)) := by
    linarith
  calc
    (Nat.choose (N - K) (M + L) : ℝ) =
        Real.exp (Real.log (Nat.choose (N - K) (M + L) : ℝ)) := by
      rw [Real.exp_log hshiftPos]
    _ ≤ Real.exp
        (Real.log (Nat.choose N M : ℝ) +
          ((K : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (N : ℝ)) +
            (L : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (M : ℝ)) -
            ((K + L : ℕ) : ℝ) ^ 2 /
              (2 * ((N - M : ℕ) : ℝ)) +
            (K : ℝ) ^ 2 / (2 * (N : ℝ)) -
            (L : ℝ) ^ 2 / (2 * (M : ℝ)) +
            binomialSecondOrderCubicError N M K L +
            Real.log ((N + 1 : ℕ) : ℝ))) :=
      Real.exp_le_exp.mpr hlog
    _ = (Nat.choose N M : ℝ) * Real.exp
        ((K : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (N : ℝ)) +
          (L : ℝ) * Real.log (((N - M : ℕ) : ℝ) / (M : ℝ)) -
          ((K + L : ℕ) : ℝ) ^ 2 /
            (2 * ((N - M : ℕ) : ℝ)) +
          (K : ℝ) ^ 2 / (2 * (N : ℝ)) -
          (L : ℝ) ^ 2 / (2 * (M : ℝ)) +
          binomialSecondOrderCubicError N M K L +
          Real.log ((N + 1 : ℕ) : ℝ)) := by
      rw [Real.exp_add, Real.exp_log hbasePos]

end DenseGraph
