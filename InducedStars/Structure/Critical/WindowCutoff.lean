import InducedStars.Structure.Critical.WindowCoarseProbability
import InducedStars.Structure.Critical.WindowPrefactors

/-!
# Converting the coarse integer cutoff to a logarithmic size bound
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem eventually_criticalWindowCutoff_div_log_le
    {L : ℝ} (hL : 0 ≤ L) :
    ∀ᶠ n : ℕ in atTop,
      (criticalLogarithmicSparseCutoff L n : ℝ) / Real.log (n : ℝ) ≤ L + 1 := by
  filter_upwards [eventually_ge_atTop 1,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_ge_atTop (L * Real.log 2 + 1))]
    with n hn hl hlarge
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hnext : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 1 by omega))
  have hceil := Nat.ceil_lt_add_one (mul_nonneg hL hnext)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
    (show (n : ℝ) + 1 ≤ 2 * n by linarith)
  rw [Real.log_mul (by norm_num) hnpos.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hL
  apply (div_le_iff₀ hl).mpr
  unfold criticalLogarithmicSparseCutoff
  simp only [Nat.cast_add, Nat.cast_one] at hceil ⊢
  nlinarith

theorem eventually_criticalWindowFullCount_pos
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < (criticalWindowInducedStarFreeGraphFinset k n a).card := by
  filter_upwards [eventually_criticalWindowCoPartiteCount_pos k hk a] with n hn
  exact hn.trans_le (criticalWindowCoPartiteCount_le_fullCount hk a)

end InducedStars
