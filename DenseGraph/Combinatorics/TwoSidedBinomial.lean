import DenseGraph.Combinatorics.BinomialStirling

/-!
# Two-sided second-order binomial ratios

A signed Taylor estimate for `x * log x`, combined with the bounded
Stirling correction, gives both sides of the second-order binomial
comparison.  The finite error is cubic in the changes and bounded in the
Stirling coordinates.
-/

noncomputable section

namespace DenseGraph

private theorem abs_log_one_add_secondOrder_le
    {z : ℝ} (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - z + z ^ 2 / 2| ≤ 2 * |z| ^ 3 := by
  have hzlt : |-z| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -z) hzlt 2
  norm_num [Finset.sum_range_succ, abs_neg] at h
  have hden : 0 < 1 - |z| := by linarith
  have hbound : |z| ^ 3 / (1 - |z|) ≤ 2 * |z| ^ 3 := by
    apply (div_le_iff₀ hden).2
    nlinarith [pow_nonneg (abs_nonneg z) 3]
  convert h.trans hbound using 1 <;> congr 1 <;> ring

/-- Signed first-order logarithmic expansion with a quadratic remainder. -/
theorem abs_log_shift_sub_linear_le
    {x h : ℝ} (hx : 0 < x) (hh : |h| ≤ x / 2) :
    |Real.log (x + h) - Real.log x - h / x| ≤ 2 * h ^ 2 / x ^ 2 := by
  have hz : |h / x| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
    linarith
  have hunit : 0 < 1 + h / x := by linarith [(abs_le.mp hz).1]
  have hlog : Real.log (x + h) = Real.log x + Real.log (1 + h / x) := by
    rw [show x + h = x * (1 + h / x) by field_simp]
    exact Real.log_mul hx.ne' hunit.ne'
  have ht := abs_log_one_add_secondOrder_le hz
  have hc : 2 * |h / x| ^ 3 ≤ (h / x) ^ 2 := by
    have hsq : 0 ≤ |h / x| ^ 2 := sq_nonneg _
    have hh' := mul_le_mul_of_nonneg_right hz hsq
    rw [sq_abs] at hh'
    nlinarith [sq_abs (h / x)]
  rw [hlog]
  have htr := abs_le.mp ht
  rw [abs_le]
  rw [show 2 * h ^ 2 / x ^ 2 = 2 * (h / x) ^ 2 by ring]
  constructor <;> linarith [sq_nonneg (h / x)]

/-- Signed second-order Taylor estimate for the factorial entropy term.
The bound is uniform whenever the relative change is at most one half. -/
theorem abs_mul_log_shift_secondOrder_le
    {x h : ℝ} (hx : 0 < x) (hh : |h| ≤ x / 2) :
    |(x + h) * Real.log (x + h) - x * Real.log x -
      h * (Real.log x + 1) - h ^ 2 / (2 * x)| ≤
      4 * |h| ^ 3 / x ^ 2 := by
  have hh' := abs_le.mp hh
  have hxh : 0 < x + h := by linarith
  have hz : |h / x| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
    linarith
  have ht := abs_log_one_add_secondOrder_le hz
  have hlog : Real.log (x + h) = Real.log x + Real.log (1 + h / x) := by
    rw [show x + h = x * (1 + h / x) by field_simp]
    exact Real.log_mul hx.ne' (ne_of_gt (by linarith [(abs_le.mp hz).1]))
  have hid :
      (x + h) * Real.log (x + h) - x * Real.log x -
        h * (Real.log x + 1) - h ^ 2 / (2 * x) =
      (x + h) * (Real.log (1 + h / x) - h / x + (h / x) ^ 2 / 2) -
        h ^ 3 / (2 * x ^ 2) := by
    rw [hlog]
    field_simp
    ring
  rw [hid]
  have hrem :
      |(x + h) * (Real.log (1 + h / x) - h / x + (h / x) ^ 2 / 2)| ≤
        3 * |h| ^ 3 / x ^ 2 := by
    rw [abs_mul, abs_of_pos hxh]
    calc
      (x + h) * |Real.log (1 + h / x) - h / x + (h / x) ^ 2 / 2| ≤
          (x + h) * (2 * |h / x| ^ 3) := mul_le_mul_of_nonneg_left ht hxh.le
      _ ≤ (3 * x / 2) * (2 * |h / x| ^ 3) := by gcongr; linarith
      _ = 3 * |h| ^ 3 / x ^ 2 := by
        rw [abs_div, abs_of_pos hx]
        field_simp
  have hcube : |h ^ 3 / (2 * x ^ 2)| = |h| ^ 3 / (2 * x ^ 2) := by
    rw [abs_div, abs_pow, abs_of_pos (by positivity : 0 < 2 * x ^ 2)]
  calc
    _ ≤ |(x + h) * (Real.log (1 + h / x) - h / x + (h / x) ^ 2 / 2)| +
        |h ^ 3 / (2 * x ^ 2)| := abs_sub _ _
    _ ≤ 3 * |h| ^ 3 / x ^ 2 + |h| ^ 3 / (2 * x ^ 2) := by
      rw [hcube]
      exact add_le_add hrem (le_refl _)
    _ ≤ 4 * |h| ^ 3 / x ^ 2 := by
      have hnn : 0 ≤ |h| ^ 3 / x ^ 2 := by positivity
      ring_nf at hnn ⊢
      linarith

/-- The second-order entropy expression for a capacity loss `K` and a
selected-count increase `L`. -/
def binomialSecondOrderMain (N M K L : ℝ) : ℝ :=
  K * Real.log ((N - M) / N) + L * Real.log ((N - M) / M) -
    (K + L) ^ 2 / (2 * (N - M)) + K ^ 2 / (2 * N) - L ^ 2 / (2 * M)

/-- A positive cubic error that bounds both signs of the Taylor remainder. -/
def binomialSecondOrderAbsoluteError (N M K L : ℝ) : ℝ :=
  4 * (K ^ 3 / N ^ 2 + L ^ 3 / M ^ 2 + (K + L) ^ 3 / (N - M) ^ 2)

/-- Two-sided entropy Taylor estimate, with all perturbation guards explicit. -/
theorem abs_realBinomialEntropyPerspective_sub_secondOrder_le
    {N M K L : ℝ} (hM : 0 < M) (hMN : M < N)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hKhalf : 2 * K ≤ N) (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    |realBinomialEntropyPerspective (N - K) (M + L) -
        realBinomialEntropyPerspective N M - binomialSecondOrderMain N M K L| ≤
      binomialSecondOrderAbsoluteError N M K L := by
  have hN := hM.trans hMN
  have hD : 0 < N - M := sub_pos.mpr hMN
  have hsum : 0 ≤ K + L := add_nonneg hK hL
  have hn := abs_mul_log_shift_secondOrder_le hN
    (show |-K| ≤ N / 2 by rw [abs_neg, abs_of_nonneg hK]; linarith)
  have hm := abs_mul_log_shift_secondOrder_le hM
    (show |L| ≤ M / 2 by rw [abs_of_nonneg hL]; linarith)
  have hd := abs_mul_log_shift_secondOrder_le hD
    (show |-(K + L)| ≤ (N - M) / 2 by
      rw [abs_neg, abs_of_nonneg hsum]; linarith)
  simp only [abs_neg, abs_of_nonneg hK, abs_of_nonneg hL, abs_of_nonneg hsum] at hn hm hd
  have hnr := abs_le.mp hn
  have hmr := abs_le.mp hm
  have hdr := abs_le.mp hd
  unfold realBinomialEntropyPerspective binomialSecondOrderMain binomialSecondOrderAbsoluteError
  rw [Real.log_div hD.ne' hN.ne', Real.log_div hD.ne' hM.ne']
  rw [abs_le]
  have harg : N - K - (M + L) = N - M + -(K + L) := by ring
  rw [harg]
  simp only [neg_sq, ← sub_eq_add_neg] at hnr hdr ⊢
  ring_nf at hnr hmr hdr ⊢
  constructor <;> linarith only [hnr.1, hnr.2, hmr.1, hmr.2, hdr.1, hdr.2]

/-- The entropy comparison also allows either sign of the two changes.
This form avoids natural-subtraction choices in asymptotic applications. -/
theorem abs_realBinomialEntropyPerspective_signed_secondOrder_le
    {N M K L : ℝ} (hM : 0 < M) (hMN : M < N)
    (hKhalf : |K| ≤ N / 2) (hLhalf : |L| ≤ M / 2)
    (hdhalf : |K + L| ≤ (N - M) / 2) :
    |realBinomialEntropyPerspective (N - K) (M + L) -
        realBinomialEntropyPerspective N M - binomialSecondOrderMain N M K L| ≤
      4 * (|K| ^ 3 / N ^ 2 + |L| ^ 3 / M ^ 2 + |K + L| ^ 3 / (N - M) ^ 2) := by
  have hN := hM.trans hMN
  have hD : 0 < N - M := sub_pos.mpr hMN
  have hn := abs_mul_log_shift_secondOrder_le hN
    (show |-K| ≤ N / 2 by simpa only [abs_neg] using hKhalf)
  have hm := abs_mul_log_shift_secondOrder_le hM hLhalf
  have hd := abs_mul_log_shift_secondOrder_le hD
    (show |-(K + L)| ≤ (N - M) / 2 by simpa only [abs_neg] using hdhalf)
  simp only [abs_neg] at hn hd
  have hnr := abs_le.mp hn
  have hmr := abs_le.mp hm
  have hdr := abs_le.mp hd
  unfold realBinomialEntropyPerspective binomialSecondOrderMain
  rw [Real.log_div hD.ne' hN.ne', Real.log_div hD.ne' hM.ne', abs_le]
  have harg : N - K - (M + L) = N - M + -(K + L) := by ring
  rw [harg]
  simp only [neg_sq, ← sub_eq_add_neg] at hnr hdr ⊢
  ring_nf at hnr hmr hdr ⊢
  constructor <;> linarith only [hnr.1, hnr.2, hmr.1, hmr.2, hdr.1, hdr.2]

/-- Arbitrary signed differences between two nearby interior binomial
slices, with a uniform constant Stirling error. -/
theorem abs_log_choose_signed_secondOrder_le
    {N M N' M' : ℕ} (hM : 0 < M) (hMN : M < N)
    (hM' : 0 < M') (hM'N' : M' < N')
    (hK : |(N : ℝ) - N'| ≤ (N : ℝ) / 2)
    (hL : |(M' : ℝ) - M| ≤ (M : ℝ) / 2)
    (hD : |((N : ℝ) - N') + ((M' : ℝ) - M)| ≤ ((N : ℝ) - M) / 2) :
    |Real.log (Nat.choose N' M' : ℝ) - Real.log (Nat.choose N M : ℝ) -
      binomialSecondOrderMain N M ((N : ℝ) - N') ((M' : ℝ) - M)| ≤
      4 * (|(N : ℝ) - N'| ^ 3 / (N : ℝ) ^ 2 +
        |(M' : ℝ) - M| ^ 3 / (M : ℝ) ^ 2 +
        |((N : ℝ) - N') + ((M' : ℝ) - M)| ^ 3 / ((N : ℝ) - M) ^ 2) + 4 := by
  have ht := abs_realBinomialEntropyPerspective_signed_secondOrder_le
    (show (0 : ℝ) < M by exact_mod_cast hM)
    (show (M : ℝ) < N by exact_mod_cast hMN) hK hL hD
  simp only [sub_sub_cancel, add_sub_cancel] at ht
  have he :
      |binomialEntropyPerspective N' M' - binomialEntropyPerspective N M -
          binomialSecondOrderMain N M ((N : ℝ) - N') ((M' : ℝ) - M)| ≤
        4 * (|(N : ℝ) - N'| ^ 3 / (N : ℝ) ^ 2 +
          |(M' : ℝ) - M| ^ 3 / (M : ℝ) ^ 2 +
          |((N : ℝ) - N') + ((M' : ℝ) - M)| ^ 3 / ((N : ℝ) - M) ^ 2) := by
    rw [binomialEntropyPerspective_eq_log_formula hM' hM'N',
      binomialEntropyPerspective_eq_log_formula hM hMN]
    simpa only [realBinomialEntropyPerspective, Nat.cast_sub hMN.le,
      Nat.cast_sub hM'N'.le] using ht
  have hk := abs_le.mp hK
  have hl := abs_le.mp hL
  have hd := abs_le.mp hD
  have hs := abs_log_choose_ratio_sub_entropy_le_four hM hMN hM' hM'N'
    (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) N])
    (by linarith) (by linarith [Nat.cast_nonneg (α := ℝ) M])
    (by rw [Nat.cast_sub hMN.le, Nat.cast_sub hM'N'.le]; linarith)
    (by rw [Nat.cast_sub hMN.le, Nat.cast_sub hM'N'.le]; linarith)
  rw [abs_le] at he hs ⊢
  constructor <;> linarith

/-- Sharp finite two-sided binomial ratio.  The `4` is an absolute
Stirling-prefactor error, so no logarithmic capacity loss remains. -/
theorem abs_log_choose_sub_capacity_add_selected_secondOrder_le
    {N M K L : ℕ} (hM : 0 < M) (hMN : M < N)
    (hKhalf : 2 * K ≤ N) (hLhalf : 2 * L ≤ M)
    (hdhalf : 2 * (K + L) ≤ N - M) :
    |Real.log (Nat.choose (N - K) (M + L) : ℝ) -
        Real.log (Nat.choose N M : ℝ) -
        binomialSecondOrderMain N M K L| ≤
      binomialSecondOrderAbsoluteError N M K L + 4 := by
  have hKle : K ≤ N := by omega
  have hshift : M + L < N - K := by omega
  have hshiftPos : 0 < M + L := by omega
  have hmr : (0 : ℝ) < M := by exact_mod_cast hM
  have hmnr : (M : ℝ) < N := by exact_mod_cast hMN
  have hkr : 2 * (K : ℝ) ≤ N := by exact_mod_cast hKhalf
  have hlr : 2 * (L : ℝ) ≤ M := by exact_mod_cast hLhalf
  have hdr : 2 * ((K : ℝ) + L) ≤ (N : ℝ) - M := by
    have h : (2 * (K + L) : ℝ) ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast hdhalf
    simpa only [Nat.cast_sub hMN.le] using h
  have ht := abs_realBinomialEntropyPerspective_sub_secondOrder_le hmr hmnr
    (Nat.cast_nonneg (α := ℝ) K) (Nat.cast_nonneg (α := ℝ) L) hkr hlr hdr
  have he :
      |binomialEntropyPerspective (N - K) (M + L) -
          binomialEntropyPerspective N M - binomialSecondOrderMain N M K L| ≤
        binomialSecondOrderAbsoluteError N M K L := by
    rw [binomialEntropyPerspective_eq_log_formula hshiftPos hshift,
      binomialEntropyPerspective_eq_log_formula hM hMN]
    simpa only [realBinomialEntropyPerspective, Nat.cast_sub hKle,
      Nat.cast_sub hMN.le, Nat.cast_sub hshift.le, Nat.cast_add] using ht
  have hs := abs_log_choose_ratio_sub_entropy_le_four hM hMN hshiftPos hshift
    (by rw [Nat.cast_sub hKle]; linarith)
    (by rw [Nat.cast_sub hKle]; linarith [Nat.cast_nonneg (α := ℝ) K])
    (by rw [Nat.cast_add]; linarith [Nat.cast_nonneg (α := ℝ) L])
    (by rw [Nat.cast_add]; linarith)
    (by rw [Nat.cast_sub hshift.le, Nat.cast_sub hKle, Nat.cast_sub hMN.le, Nat.cast_add]; linarith)
    (by rw [Nat.cast_sub hshift.le, Nat.cast_sub hKle, Nat.cast_sub hMN.le, Nat.cast_add]
        linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) L])
  rw [abs_le] at he hs ⊢
  constructor <;> linarith

end DenseGraph
