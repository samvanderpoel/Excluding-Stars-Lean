import InducedStars.Structure.Critical.WindowScales

/-!
# Normalization for positive remainder sizes

Normalization by `s log n` retains the negative linear term even for a
single exceptional vertex.  The absolute constant in the two-sided
Stirling estimate is essential on this scale.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

theorem criticalWindowPositiveScale_inv_tendsto_zero
    {s : ℕ → ℕ} (hs : ∀ᶠ n : ℕ in atTop, 1 ≤ s n) :
    Tendsto (fun n ↦ (1 : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ (tendsto_const_nhds.div_atTop hlog :
    Tendsto (fun n : ℕ ↦ (1 : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
  · filter_upwards [hs, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hl
    positivity
  · filter_upwards [hs, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hl
    have hnR : (1 : ℝ) ≤ s n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le hl (by nlinarith)

theorem criticalWindowPositiveQuadraticTerm_tendsto
    {s : ℕ → ℕ} {N K : ℕ → ℝ} {c b x : ℝ} (hc : c ≠ 0)
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hK : Tendsto (fun n ↦ K n / ((s n : ℝ) * n)) atTop (𝓝 b)) :
    Tendsto (fun n ↦ (K n) ^ 2 / (2 * N n) / ((s n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 ((b ^ 2 / (2 * c)) * x)) := by
  have h := ((hK.pow 2).div ((tendsto_const_nhds (x := (2 : ℝ))).mul hN)
    (mul_ne_zero (by norm_num) hc)).mul hs
  apply h.congr'
  filter_upwards [hspos, eventually_ge_atTop 1] with n hsn hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsR : (s n : ℝ) ≠ 0 := by exact_mod_cast (show s n ≠ 0 by omega)
  dsimp only [Pi.div_apply]
  field_simp <;> ring

theorem criticalWindowPositiveCubicTerm_tendsto_zero
    {s : ℕ → ℕ} {N K : ℕ → ℝ} {c b x : ℝ} (hc : c ≠ 0)
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hK : Tendsto (fun n ↦ K n / ((s n : ℝ) * n)) atTop (𝓝 b)) :
    Tendsto (fun n ↦ |K n| ^ 3 / (N n) ^ 2 / ((s n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h := (((hK.abs.pow 3).div (hN.pow 2) (pow_ne_zero _ hc)).mul (hs.pow 2)).mul hlog
  simp only [mul_zero] at h
  apply h.congr'
  have hlogpos := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hspos, eventually_ge_atTop 1, hlogpos] with n hsn hn hl
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : (0 : ℝ) < s n := by exact_mod_cast (show 0 < s n by omega)
  change 0 < Real.log (n : ℝ) at hl
  dsimp only [Pi.div_apply]
  rw [abs_div, abs_mul, abs_of_pos hsR, abs_of_pos hnR]
  field_simp <;> ring

/-- Conversion of the edge-count normalization on the positive-size scale. -/
theorem criticalWindowPositiveEdgeCount_logSq_tendsto
    {s t : ℕ → ℕ} {x z : ℝ}
    (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (ht : Tendsto (fun n ↦ (t n : ℝ) / ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 z)) :
    Tendsto (fun n ↦ (t n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 (z * x)) := by
  apply (ht.mul hs).congr'
  filter_upwards [hspos] with n hn
  have hsR : (s n : ℝ) ≠ 0 := by exact_mod_cast (show s n ≠ 0 by omega)
  field_simp <;> ring

/-- A logarithmic-size times vertex-order scale tends to infinity for every
positive remainder sequence. -/
theorem criticalWindowPositiveSize_order_tendsto_atTop
    {s : ℕ → ℕ} (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n) :
    Tendsto (fun n ↦ (s n : ℝ) * n) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [hspos] with n hn
  have hsR : (1 : ℝ) ≤ s n := by exact_mod_cast hn
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem criticalWindowPositiveScale_tendsto_atTop
    {s : ℕ → ℕ} (hspos : ∀ᶠ n : ℕ in atTop, 1 ≤ s n) :
    Tendsto (fun n ↦ (s n : ℝ) * Real.log (n : ℝ)) atTop atTop := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop_mono' atTop ?_ hlog
  filter_upwards [hspos, hlog.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hl
  have hsR : (1 : ℝ) ≤ s n := by exact_mod_cast hn
  nlinarith

end InducedStars
