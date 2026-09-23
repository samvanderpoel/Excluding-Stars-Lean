import InducedStars.Structure.Critical.WindowRowBounds

/-!
# Concentration at the logarithmic remainder-size maximizer
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

/-- A Gaussian penalty in `log n` dominates the number of possible
remainder sizes. -/
theorem criticalWindow_logGaussian_linear_tendsto_zero
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) * Real.exp (-d * Real.log (n : ℝ) ^ 2))
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := hinv.add (hinv.pow 2)
    simp only [zero_pow (by omega : 2 ≠ 0), add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp <;> ring
  have hlog := criticalWindowLog_nat_tendsto_atTop
  have hlarge := (hlog.const_mul_atTop hd).eventually (eventually_ge_atTop (2 : ℝ))
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by positivity) ?_ hu
  filter_upwards [hlarge, hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop 1] with n hn hl hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : Real.exp (-2 * Real.log (n : ℝ)) = 1 / (n : ℝ) ^ 2 := by
    rw [show -2 * Real.log (n : ℝ) = -(Real.log (n : ℝ) + Real.log (n : ℝ)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log hnR]
    ring
  have he := Real.exp_le_exp.mpr (show -d * Real.log (n : ℝ) ^ 2 ≤
      -2 * Real.log (n : ℝ) by nlinarith)
  rw [hexp] at he
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left he
    (by positivity : 0 ≤ (n : ℝ) + 1)

/-- Total cardinal mass of bounded-logarithmic clean assemblies whose
exceptional size stays away from the predicted maximizer. -/
def criticalWindowOffPeakAssemblyMass (k : ℕ) (a L epsilon : ℝ) (n : ℕ) : ℝ :=
  ∑ s ∈ (Finset.range (n + 1)).filter (fun s : ℕ ↦
      (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
        epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|),
    ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ)

/-- Below and at the transition, the actual bounded-logarithmic assembly
mass concentrates at the unique quadratic maximizer. -/
theorem criticalWindowOffPeakAssemblyMass_div_total_tendsto_zero
    {k : ℕ} (hk : 3 ≤ k) {a L epsilon : ℝ}
    (ha : a ≤ criticalWindowThreshold k) (hL : 0 ≤ L) (hepsilon : 0 < epsilon) :
    Tendsto (fun n ↦ criticalWindowOffPeakAssemblyMass k a L epsilon n /
      ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ)) atTop (𝓝 0) := by
  classical
  let x := criticalWindowRemainderCoefficient k a
  let d := gammaK k / criticalWindowThreshold k * epsilon ^ 2
  have hx : 0 ≤ x := criticalWindowRemainderCoefficient_nonneg hk ha
  have hd : 0 < d := mul_pos (div_pos (gammaK_pos hk) (criticalWindowThreshold_pos hk))
    (sq_pos_of_pos hepsilon)
  let s0 : ℕ → ℕ := fun n ↦ ⌊x * Real.log (n : ℝ)⌋₊
  have hs0 : Tendsto (fun n ↦ (s0 n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x) :=
    DenseGraph.natFloor_mul_div_tendsto criticalWindowLog_nat_tendsto_atTop hx
  obtain ⟨C, hC, hupper⟩ := exists_criticalWindowAssembly_upper_rate_uniform hk a L hL
    (by positivity : 0 < d / 4)
  obtain ⟨B, hB, hlower⟩ := exists_criticalWindowTotal_lower_rate hk a hx hs0
    (by positivity : 0 < d / 4)
  have hbound : ∀ᶠ n : ℕ in atTop,
      criticalWindowOffPeakAssemblyMass k a L epsilon n /
          ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) ≤
        C * B * (((n : ℝ) + 1) * Real.exp (-(d / 2) * Real.log (n : ℝ) ^ 2)) := by
    filter_upwards [hupper, hlower, eventually_criticalWindowReferenceMass_pos hk a]
      with n hupper hlower hR
    let R := criticalWindowReferenceMass k a n
    let V := Real.exp ((criticalWindowRate k a x - d / 4) * Real.log (n : ℝ) ^ 2)
    let U := Real.exp ((criticalWindowRate k a x - d + d / 4) * Real.log (n : ℝ) ^ 2)
    have htotal : (0 : ℝ) < (criticalWindowInducedStarFreeGraphFinset k n a).card :=
      lt_of_lt_of_le (mul_pos (mul_pos (inv_pos.mpr hB) hR) (Real.exp_pos _)) hlower
    have hU : 0 ≤ C * R * U := by dsimp [R, U]; positivity
    have hnum : criticalWindowOffPeakAssemblyMass k a L epsilon n ≤
        ((n : ℝ) + 1) * (C * R * U) := by
      unfold criticalWindowOffPeakAssemblyMass
      calc
        _ ≤ ∑ _s ∈ (Finset.range (n + 1)).filter (fun s : ℕ ↦
            (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
              epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|),
            C * R * U := by
          apply Finset.sum_le_sum
          intro s hs
          obtain ⟨hmem, hsize, haway⟩ := Finset.mem_filter.mp hs
          have hsn : s ≤ n := by have := Finset.mem_range.mp hmem; omega
          have hr := criticalWindowRate_le_peak_sub_gap hk a ((s : ℝ) / Real.log (n : ℝ))
            hepsilon.le haway
          have he : Real.exp ((criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)) + d / 4) *
              Real.log (n : ℝ) ^ 2) ≤ U := by
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            change _ ≤ criticalWindowRate k a x - d + d / 4
            dsimp [x, d]
            linarith
          exact (hupper s hsn hsize).trans (mul_le_mul_of_nonneg_left he (mul_pos hC hR).le)
        _ = (((Finset.range (n + 1)).filter (fun s : ℕ ↦
            (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
              epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|)).card : ℝ) *
            (C * R * U) := by simp
        _ ≤ ((n : ℝ) + 1) * (C * R * U) := by
          apply mul_le_mul_of_nonneg_right ?_ hU
          exact_mod_cast (show ((Finset.range (n + 1)).filter (fun s : ℕ ↦
            (s : ℝ) / Real.log (n : ℝ) ≤ L ∧
              epsilon ≤ |(s : ℝ) / Real.log (n : ℝ) - criticalWindowRemainderCoefficient k a|)).card ≤ n + 1 by
            simpa only [Finset.card_range] using Finset.card_filter_le (Finset.range (n + 1)) _)
    have hE : U = Real.exp (-(d / 2) * Real.log (n : ℝ) ^ 2) * V := by
      dsimp [U, V]
      rw [← Real.exp_add]
      congr 1
      ring
    have hnonneg : 0 ≤ C * B * (((n : ℝ) + 1) * Real.exp (-(d / 2) * Real.log (n : ℝ) ^ 2)) := by positivity
    apply (div_le_iff₀ htotal).mpr
    have hm := mul_le_mul_of_nonneg_left hlower hnonneg
    have hid : ((n : ℝ) + 1) * (C * R * U) =
        C * B * (((n : ℝ) + 1) * Real.exp (-(d / 2) * Real.log (n : ℝ) ^ 2)) *
          (B⁻¹ * R * V) := by
      rw [hE]
      field_simp <;> ring
    exact hnum.trans (hid.le.trans hm)
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by
    unfold criticalWindowOffPeakAssemblyMass
    positivity) hbound
  simpa only [mul_zero] using (criticalWindow_logGaussian_linear_tendsto_zero
    (by positivity : 0 < d / 2)).const_mul (C * B)

end InducedStars
