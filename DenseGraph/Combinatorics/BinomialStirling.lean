import DenseGraph.Combinatorics.SecondOrderBinomial
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Binomial ratios with a bounded Stirling error

The entropy sandwich loses a logarithm of the capacity.  Ratios of nearby
interior binomial coefficients instead have a bounded error, because their
Stirling prefactors cancel.  The estimates below retain this cancellation
and control both sides of the ratio.
-/

noncomputable section

namespace DenseGraph

/-- The logarithms of the positive-index Stirling sequence differ by at most
`1/12`, uniformly in both indices. -/
theorem abs_log_stirlingSeq_sub_le
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    |Real.log (Stirling.stirlingSeq m) - Real.log (Stirling.stirlingSeq n)| ≤
      (1 / 12 : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hml := Stirling.log_stirlingSeq_bounded_aux m
  have hnl := Stirling.log_stirlingSeq_bounded_aux n
  have hmu := Stirling.log_stirlingSeq'_antitone (show 0 ≤ m by omega)
  have hnu := Stirling.log_stirlingSeq'_antitone (show 0 ≤ n by omega)
  simp only [Function.comp_apply, Nat.succ_eq_add_one, zero_add] at hmu hnu
  rw [abs_le]
  constructor <;> linarith

/-- Exact logarithmic factorial identity, with its Stirling correction
separated from the main term. -/
theorem log_factorial_eq_stirling_correction
    {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) =
      (n : ℝ) * Real.log (n : ℝ) - n +
        (1 / 2 : ℝ) * Real.log (n : ℝ) +
        (1 / 2 : ℝ) * Real.log 2 + Real.log (Stirling.stirlingSeq n) := by
  have h := Stirling.log_stirlingSeq_formula n
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnR,
    Real.log_div hnR (Real.exp_ne_zero _), Real.log_exp] at h
  linarith

/-- The exact logarithm of an interior binomial coefficient. -/
theorem log_choose_eq_stirling_correction
    {N M : ℕ} (hM : 0 < M) (hMN : M < N) :
    Real.log (Nat.choose N M : ℝ) =
      binomialEntropyPerspective N M +
        (Real.log (N : ℝ) - Real.log (M : ℝ) -
          Real.log ((N - M : ℕ) : ℝ)) / 2 -
        Real.log 2 / 2 + Real.log (Stirling.stirlingSeq N) -
        Real.log (Stirling.stirlingSeq M) -
        Real.log (Stirling.stirlingSeq (N - M)) := by
  have hN : 0 < N := hM.trans hMN
  have hD : 0 < N - M := Nat.sub_pos_of_lt hMN
  have hc : (Nat.choose N M : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hMN.le).ne'
  have hmf : (M.factorial : ℝ) ≠ 0 := by positivity
  have hdf : ((N - M).factorial : ℝ) ≠ 0 := by positivity
  have hprod :
      (Nat.choose N M : ℝ) * M.factorial * (N - M).factorial = N.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hMN.le
  have hlog := congrArg Real.log hprod
  rw [Real.log_mul (mul_ne_zero hc hmf) hdf, Real.log_mul hc hmf] at hlog
  rw [log_factorial_eq_stirling_correction hM,
    log_factorial_eq_stirling_correction hD,
    log_factorial_eq_stirling_correction hN] at hlog
  rw [binomialEntropyPerspective_eq_log_formula hM hMN]
  rw [Nat.cast_sub hMN.le] at hlog ⊢
  linarith

/-- A two-sided comparison of logarithmic binomial ratios with their entropy
and square-root prefactors.  The error is independent of the capacities. -/
theorem abs_log_choose_ratio_sub_entropy_prefactor_le
    {N M N' M' : ℕ} (hM : 0 < M) (hMN : M < N)
    (hM' : 0 < M') (hM'N' : M' < N') :
    |(Real.log (Nat.choose N' M' : ℝ) - Real.log (Nat.choose N M : ℝ)) -
      (binomialEntropyPerspective N' M' - binomialEntropyPerspective N M +
        ((Real.log (N' : ℝ) - Real.log (N : ℝ)) -
          (Real.log (M' : ℝ) - Real.log (M : ℝ)) -
          (Real.log ((N' - M' : ℕ) : ℝ) - Real.log ((N - M : ℕ) : ℝ))) / 2)| ≤
      (1 / 4 : ℝ) := by
  have hN := abs_log_stirlingSeq_sub_le (hM'.trans hM'N') (hM.trans hMN)
  have hsel := abs_log_stirlingSeq_sub_le hM' hM
  have hmiss := abs_log_stirlingSeq_sub_le
    (Nat.sub_pos_of_lt hM'N') (Nat.sub_pos_of_lt hMN)
  rw [log_choose_eq_stirling_correction hM' hM'N',
    log_choose_eq_stirling_correction hM hMN]
  have hbound := (abs_sub
    (Real.log (Stirling.stirlingSeq N') - Real.log (Stirling.stirlingSeq N) -
      (Real.log (Stirling.stirlingSeq M') - Real.log (Stirling.stirlingSeq M)))
    (Real.log (Stirling.stirlingSeq (N' - M')) -
      Real.log (Stirling.stirlingSeq (N - M)))).trans
    (add_le_add (abs_sub
      (Real.log (Stirling.stirlingSeq N') - Real.log (Stirling.stirlingSeq N))
      (Real.log (Stirling.stirlingSeq M') - Real.log (Stirling.stirlingSeq M))) (le_refl _))
  convert hbound.trans (show
    |Real.log (Stirling.stirlingSeq N') - Real.log (Stirling.stirlingSeq N)| +
      |Real.log (Stirling.stirlingSeq M') - Real.log (Stirling.stirlingSeq M)| +
      |Real.log (Stirling.stirlingSeq (N' - M')) -
        Real.log (Stirling.stirlingSeq (N - M))| ≤ (1 / 4 : ℝ) by linarith) using 1 <;>
    congr 1 <;> ring

/-- Dropping the explicit prefactor costs only the logarithms of the three
relative coordinate changes, rather than a logarithm of the capacity. -/
theorem abs_log_choose_ratio_sub_entropy_le
    {N M N' M' : ℕ} (hM : 0 < M) (hMN : M < N)
    (hM' : 0 < M') (hM'N' : M' < N') :
    |(Real.log (Nat.choose N' M' : ℝ) - Real.log (Nat.choose N M : ℝ)) -
      (binomialEntropyPerspective N' M' - binomialEntropyPerspective N M)| ≤
      (|Real.log (N' : ℝ) - Real.log (N : ℝ)| +
        |Real.log (M' : ℝ) - Real.log (M : ℝ)| +
        |Real.log ((N' - M' : ℕ) : ℝ) - Real.log ((N - M : ℕ) : ℝ)|) / 2 +
      (1 / 4 : ℝ) := by
  have h := abs_log_choose_ratio_sub_entropy_prefactor_le hM hMN hM' hM'N'
  have hp := (abs_sub
    (Real.log (N' : ℝ) - Real.log (N : ℝ) -
      (Real.log (M' : ℝ) - Real.log (M : ℝ)))
    (Real.log ((N' - M' : ℕ) : ℝ) - Real.log ((N - M : ℕ) : ℝ))).trans
    (add_le_add (abs_sub
      (Real.log (N' : ℝ) - Real.log (N : ℝ))
      (Real.log (M' : ℝ) - Real.log (M : ℝ))) (le_refl _))
  have hhalf := mul_le_mul_of_nonneg_right hp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [abs_le] at h ⊢
  have hp' := abs_le.mp hp
  constructor <;> linarith

/-- A relative factor-two change in a positive argument changes its logarithm
by at most two. -/
theorem abs_log_sub_log_le_two_of_ratio
    {x y : ℝ} (hx : 0 < x) (hlower : x / 2 ≤ y) (hupper : y ≤ 2 * x) :
    |Real.log y - Real.log x| ≤ 2 := by
  have h := abs_log_sub_log_le_div_of_lower
    (show 0 < x / 2 by positivity) hlower (show x / 2 ≤ x by linarith)
  have hdist : |y - x| ≤ x := by rw [abs_le]; constructor <;> linarith
  apply h.trans
  apply (div_le_iff₀ (show 0 < x / 2 by positivity)).2
  linarith

/-- Constant-error entropy comparison for two interior slices whose three
factorial arguments change by at most a factor of two. -/
theorem abs_log_choose_ratio_sub_entropy_le_four
    {N M N' M' : ℕ} (hM : 0 < M) (hMN : M < N)
    (hM' : 0 < M') (hM'N' : M' < N')
    (hNlo : (N : ℝ) / 2 ≤ N') (hNhi : (N' : ℝ) ≤ 2 * N)
    (hMlo : (M : ℝ) / 2 ≤ M') (hMhi : (M' : ℝ) ≤ 2 * M)
    (hDlo : ((N - M : ℕ) : ℝ) / 2 ≤ (N' - M' : ℕ))
    (hDhi : ((N' - M' : ℕ) : ℝ) ≤ 2 * (N - M : ℕ)) :
    |(Real.log (Nat.choose N' M' : ℝ) - Real.log (Nat.choose N M : ℝ)) -
      (binomialEntropyPerspective N' M' - binomialEntropyPerspective N M)| ≤ 4 := by
  have h := abs_log_choose_ratio_sub_entropy_le hM hMN hM' hM'N'
  have hn := abs_log_sub_log_le_two_of_ratio
    (show (0 : ℝ) < N by exact_mod_cast hM.trans hMN) hNlo hNhi
  have hm := abs_log_sub_log_le_two_of_ratio
    (show (0 : ℝ) < M by exact_mod_cast hM) hMlo hMhi
  have hd := abs_log_sub_log_le_two_of_ratio
    (show (0 : ℝ) < (N - M : ℕ) by exact_mod_cast Nat.sub_pos_of_lt hMN) hDlo hDhi
  linarith

end DenseGraph
