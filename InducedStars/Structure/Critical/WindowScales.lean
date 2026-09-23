import InducedStars.Structure.Critical.WindowBasic
import DenseGraph.Combinatorics.TwoSidedBinomial

/-!
# Normalization of the critical-window Taylor terms

On the logarithmic remainder scale, the cubic error vanishes and the
second-order entropy term has a finite limit.  These statements retain
signed perturbations and can be applied to every sequence of remainder
sizes in a bounded logarithmic range.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

private theorem critical_log_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop

/-- A cubic Taylor remainder is negligible on the squared-logarithm scale. -/
theorem criticalWindowCubicTerm_tendsto_zero
    {N K : ℕ → ℝ} {c b : ℝ} (hc : c ≠ 0)
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hK : Tendsto (fun n ↦ K n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 b)) :
    Tendsto (fun n ↦ |K n| ^ 3 / (N n) ^ 2 / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hmain := ((hK.abs.pow 3).div (hN.pow 2) (pow_ne_zero _ hc)).mul
    critical_log_div_nat_tendsto_zero
  simp only [mul_zero] at hmain
  apply hmain.congr'
  have hnz : ∀ᶠ n : ℕ in atTop, N n ≠ 0 := by
    filter_upwards [hN.eventually_ne hc] with n hn
    intro h
    simp only [h, zero_div] at hn
    exact hn rfl
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hnz, hlog, eventually_ge_atTop 1] with n hn hl hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  dsimp only [Pi.div_apply]
  change 0 < Real.log (n : ℝ) at hl
  rw [abs_div, abs_mul, abs_of_pos hnR, abs_of_pos hl]
  field_simp <;> ring

/-- The normalized quadratic term depends only on the normalized capacity
and perturbation limits. -/
theorem criticalWindowQuadraticTerm_tendsto
    {N K : ℕ → ℝ} {c b : ℝ} (hc : c ≠ 0)
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hK : Tendsto (fun n ↦ K n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 b)) :
    Tendsto (fun n ↦ (K n) ^ 2 / (2 * N n) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 (b ^ 2 / (2 * c))) := by
  have hmain := (hK.pow 2).div ((tendsto_const_nhds (x := (2 : ℝ))).mul hN)
    (mul_ne_zero (by norm_num) hc)
  apply hmain.congr'
  have hnz : ∀ᶠ n : ℕ in atTop, N n ≠ 0 := by
    filter_upwards [hN.eventually_ne hc] with n hn
    intro h
    simp only [h, zero_div] at hn
    exact hn rfl
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hnz, hlog, eventually_ge_atTop 1] with n hn hl hn1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp only [Pi.div_apply]
  field_simp <;> ring

/-- The complete signed cubic error vanishes after logarithmic normalization. -/
theorem criticalWindowSecondOrderError_tendsto_zero
    {N M K L : ℕ → ℝ} {c d b e : ℝ}
    (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c - d ≠ 0)
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hM : Tendsto (fun n ↦ M n / (n : ℝ) ^ 2) atTop (𝓝 d))
    (hK : Tendsto (fun n ↦ K n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 b))
    (hL : Tendsto (fun n ↦ L n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 e)) :
    Tendsto (fun n ↦
      (4 * (|K n| ^ 3 / (N n) ^ 2 + |L n| ^ 3 / (M n) ^ 2 +
        |K n + L n| ^ 3 / (N n - M n) ^ 2) + 4) / Real.log (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hNM : Tendsto (fun n ↦ (N n - M n) / (n : ℝ) ^ 2) atTop (𝓝 (c - d)) := by
    simpa only [sub_div] using hN.sub hM
  have hKL : Tendsto (fun n ↦ (K n + L n) / ((n : ℝ) * Real.log (n : ℝ)))
      atTop (𝓝 (b + e)) := by simpa only [add_div] using hK.add hL
  have h1 := criticalWindowCubicTerm_tendsto_zero hc hN hK
  have h2 := criticalWindowCubicTerm_tendsto_zero hd hM hL
  have h3 := criticalWindowCubicTerm_tendsto_zero hcd hNM hKL
  have hlogTop : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h4 : Tendsto (fun n : ℕ ↦ (4 : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlogTop)
  convert (((h1.add h2).add h3).const_mul 4).add h4 using 1
  · ext n
    ring
  · norm_num

/-- A logarithmic first-order perturbation is negligible relative to the
quadratic reference capacity. -/
theorem criticalWindowPerturbation_div_sq_tendsto_zero
    {K : ℕ → ℝ} {b : ℝ}
    (hK : Tendsto (fun n ↦ K n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 b)) :
    Tendsto (fun n ↦ K n / (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := hK.mul critical_log_div_nat_tendsto_zero
  simp only [mul_zero] at h
  apply h.congr'
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hlog] with n hn
  change 0 < Real.log (n : ℝ) at hn
  field_simp <;> ring

/-- Positivity of a nonzero quadratic-scale limit gives eventual positivity
of the unnormalized quantity. -/
theorem eventually_pos_of_criticalWindowQuadraticScale
    {N : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c)) :
    ∀ᶠ n : ℕ in atTop, 0 < N n := by
  have h := hN.eventually (Ioi_mem_nhds hc)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact (div_pos_iff_of_pos_right (sq_pos_of_pos hnR)).mp hn

/-- The half-capacity guards in the finite expansion eventually hold for
every logarithmic-scale signed perturbation. -/
theorem eventually_abs_le_half_of_criticalWindowScales
    {N K : ℕ → ℝ} {c b : ℝ} (hc : 0 < c)
    (hN : Tendsto (fun n ↦ N n / (n : ℝ) ^ 2) atTop (𝓝 c))
    (hK : Tendsto (fun n ↦ K n / ((n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 b)) :
    ∀ᶠ n : ℕ in atTop, |K n| ≤ N n / 2 := by
  have h := (criticalWindowPerturbation_div_sq_tendsto_zero hK).abs.eventually_lt
    (hN.div_const 2) (by simpa only [abs_zero] using half_pos hc)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))] at hn
  have heq : N n / (n : ℝ) ^ 2 / 2 = (N n / 2) / (n : ℝ) ^ 2 := by ring
  rw [heq] at hn
  exact ((div_lt_div_iff_of_pos_right (sq_pos_of_pos hnR)).mp hn).le

/-- A subquadratic sequence admits a global quadratic envelope with an
arbitrarily small leading coefficient and a finite constant term. -/
theorem exists_global_subquadratic_envelope
    {f : ℕ → ℝ}
    (hf : Tendsto (fun n ↦ f n / (n : ℝ) ^ 2) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |f n| ≤ epsilon * (n : ℝ) ^ 2 + C := by
  have h := hf.abs.eventually (Iio_mem_nhds (by simpa only [abs_zero] using hepsilon))
  rcases eventually_atTop.1 (h.and (eventually_ge_atTop 1)) with ⟨N, hN⟩
  refine ⟨∑ n ∈ Finset.range N, |f n|, Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := (hN n hn).2; omega)
    have hsmall := (hN n hn).1
    rw [abs_div, abs_of_nonneg (sq_nonneg (n : ℝ))] at hsmall
    have hlt := (div_lt_iff₀ (sq_pos_of_pos hnR)).mp hsmall
    exact hlt.le.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)))
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hn)
    have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.range N) ↦ abs_nonneg (f j)) hmem
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg hepsilon.le (sq_nonneg _)))

/-- Subquadratic errors remain negligible under every logarithmic-size
substitution, including bounded and oscillating remainder orders. -/
theorem subquadratic_comp_logarithmicScale_tendsto_zero
    {f : ℕ → ℝ} {s : ℕ → ℕ} {x : ℝ}
    (hf : Tendsto (fun n ↦ f n / (n : ℝ) ^ 2) atTop (𝓝 0))
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ f (s n) / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro epsilon hepsilon
  let delta := epsilon / (2 * (x ^ 2 + 1))
  have hd : 0 < delta := by dsimp [delta]; positivity
  rcases exists_global_subquadratic_envelope hf hd with ⟨C, hC, hbound⟩
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun n : ℕ ↦ C / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hlog)
  have hu := ((hs.pow 2).const_mul delta).add hconst
  simp only [add_zero] at hu
  have hdsmall : delta * x ^ 2 < epsilon := by
    have hx : 0 < 2 * (x ^ 2 + 1) := by positivity
    have heq : delta * x ^ 2 = epsilon * x ^ 2 / (2 * (x ^ 2 + 1)) := by
      dsimp [delta]
      ring
    rw [heq]
    apply (div_lt_iff₀ hx).2
    nlinarith [sq_nonneg x]
  have hu' := hu.eventually (Iio_mem_nhds hdsmall)
  filter_upwards [hu'] with n hn
  simp only [Real.dist_eq, sub_zero, abs_div, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ)))]
  have h := div_le_div_of_nonneg_right (hbound (s n)) (sq_nonneg (Real.log (n : ℝ)))
  calc
    |f (s n)| / Real.log (n : ℝ) ^ 2 ≤
        (delta * (s n : ℝ) ^ 2 + C) / Real.log (n : ℝ) ^ 2 := h
    _ = delta * ((s n : ℝ) / Real.log (n : ℝ)) ^ 2 + C / Real.log (n : ℝ) ^ 2 := by ring
    _ < epsilon := hn

end InducedStars
