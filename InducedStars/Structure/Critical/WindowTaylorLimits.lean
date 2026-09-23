import InducedStars.Structure.Critical.WindowScales

/-!
# Vanishing signed binomial expansion error
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- The constant-error signed binomial expansion is asymptotically exact
on the squared-logarithm scale.  The hypotheses are the explicit interior
and half-capacity guards of the finite expansion. -/
theorem criticalWindowSignedBinomial_remainder_tendsto_zero
    {N M N' M' : ℕ → ℕ} {c d b e : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c - d ≠ 0)
    (hN : Tendsto (fun n ↦ (N n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hM : Tendsto (fun n ↦ (M n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 d))
    (hK : Tendsto (fun n ↦ ((N n : ℝ) - N' n) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 b))
    (hL : Tendsto (fun n ↦ ((M' n : ℝ) - M n) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 e))
    (hguard : ∀ᶠ n : ℕ in atTop,
      0 < M n ∧ M n < N n ∧ 0 < M' n ∧ M' n < N' n ∧
      |(N n : ℝ) - N' n| ≤ (N n : ℝ) / 2 ∧
      |(M' n : ℝ) - M n| ≤ (M n : ℝ) / 2 ∧
      |((N n : ℝ) - N' n) + ((M' n : ℝ) - M n)| ≤
        ((N n : ℝ) - M n) / 2) :
    Tendsto (fun n ↦
      (Real.log (Nat.choose (N' n) (M' n) : ℝ) - Real.log (Nat.choose (N n) (M n) : ℝ) -
        DenseGraph.binomialSecondOrderMain (N n) (M n)
          ((N n : ℝ) - N' n) ((M' n : ℝ) - M n)) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_
    (criticalWindowSecondOrderError_tendsto_zero hc hd hcd hN hM hK hL)
  filter_upwards [hguard] with n hn
  rcases hn with ⟨hM0, hMN, hM'0, hM'N', hK', hL', hKL'⟩
  rw [abs_div, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ)))]
  exact div_le_div_of_nonneg_right
    (DenseGraph.abs_log_choose_signed_secondOrder_le hM0 hMN hM'0 hM'N' hK' hL' hKL')
    (sq_nonneg _)

end InducedStars
