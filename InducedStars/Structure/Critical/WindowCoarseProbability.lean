import InducedStars.Structure.Critical.WindowCoarseTotals
import InducedStars.Structure.Critical.WindowCoarseFamilies
import InducedStars.Structure.Critical.WindowCoarseSeries
import InducedStars.Structure.Supercritical.ReferenceFiber

/-!
# Probability assembly for the coarse critical-window reduction

The finite three-way decomposition is divided by the actual induced-star-free
count.  The co-partite count supplies a positive lower bound for that
denominator, so the clean logarithmic tail and the linearly penalized defect
sum both vanish.
-/

noncomputable section
open Filter Set Topology
open scoped BigOperators
namespace InducedStars

/-- The failure proportion for a literal assembly with the logarithmic cutoff. -/
def criticalWindowSmallAssemblyFailureRatio (k : ℕ) (a L : ℝ) (n : ℕ) : ℝ :=
  ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n)
    (criticalLogarithmicSparseCutoff L n)).card : ℝ) /
      (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ)

theorem eventually_criticalWindowCoPartiteCount_pos
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) :=
  eventually_coMultipartiteGraphCountWithEdges_pos k hk (gammaK k)
    ⟨one_div_parts_lt_gammaK hk, gammaK_lt_one hk⟩
    (criticalWindowEdgeCount k a) (criticalWindowEdgeCount_hasAsymptoticEdgeDensity hk a)

theorem criticalWindowCoPartiteCount_le_fullCount
    {k n : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    coMultipartiteGraphCountWithEdges (k - 1) n (criticalWindowEdgeCount k a n) ≤
      inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) :=
  Finset.card_le_card (coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree (by omega))

/-- The full coarse sum is negligible after any positive linear penalty. -/
theorem criticalWindowCoarseSeries_mul_exp_neg_tendsto_zero
    {c C K d : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ)
    (hK : 0 < K) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ criticalWindowCoarseSeries c C r K n *
      Real.exp (-d * n)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_criticalWindowCoarseSeries_le hc hC r hK
  have hlog : Tendsto (fun n : ℕ ↦
      (Real.log ((n + 1 : ℕ) : ℝ))^2 / (n : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 2 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    change Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)^2 /
      (1 * ((n + 1 : ℕ) : ℝ) + -1)) atTop (𝓝 0) at h
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, add_neg_cancel_right] using h
  have hscale : Tendsto (fun n : ℕ ↦
      B * ((Real.log ((n + 1 : ℕ) : ℝ))^2 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlog.const_mul B
  have hsmall := hscale.eventually (Iio_mem_nhds (half_pos hd))
  have hdecay : Tendsto (fun n : ℕ ↦ Real.exp (-(d / 2) * n)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_neg_of_pos (half_pos hd)))
  apply squeeze_zero' ?_ ?_ hdecay
  · exact Eventually.of_forall fun n ↦ by
      dsimp [criticalWindowCoarseSeries, criticalWindowCoarseSeriesTerm]
      positivity
  · filter_upwards [hbound, hsmall, eventually_ge_atTop 1] with n hb hs hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hs' : B * (Real.log ((n + 1 : ℕ) : ℝ))^2 ≤ d / 2 * n := by
      have hs'' : B * ((Real.log ((n + 1 : ℕ) : ℝ))^2 / (n : ℝ)) < d / 2 := hs
      rw [← mul_div_assoc] at hs''
      exact ((div_lt_iff₀ hnR).mp hs'').le
    calc
      _ ≤ Real.exp (B * (Real.log ((n + 1 : ℕ) : ℝ))^2) *
          Real.exp (-d * n) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = Real.exp (B * (Real.log ((n + 1 : ℕ) : ℝ))^2 - d * n) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem criticalWindowFarGaussian_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * (n : ℝ)^2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ ↦ (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp (hsq.const_mul_atTop_of_neg (neg_neg_of_pos hc))

/-- Concrete bounds for the canonical defect total and clean tail imply
the logarithmic coarse decomposition for the uniform exact-edge family. -/
theorem exists_criticalWindowSmallAssemblyFailureRatio_tendsto_zero_of_bounds
    (k : ℕ) (hk : 3 ≤ k) (a tau : ℝ) (htau : 0 < tau)
    {c C K d : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ)
    (hK : 0 < K) (hd : 0 < d)
    (hdefect : ∀ᶠ n : ℕ in atTop,
      (criticalWindowDefectTotal k hk n (criticalWindowEdgeCount k a n) tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalWindowEdgeCount k a n) : ℝ) *
            criticalWindowCoarseSeries c C r K n * Real.exp (-d * n))
    (htail : ∀ L : ℝ, 0 < L → ∀ᶠ n : ℕ in atTop,
      (criticalWindowCleanTailTotal k hk n (criticalWindowEdgeCount k a n)
        (criticalLogarithmicSparseCutoff L n) tau : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalWindowEdgeCount k a n) : ℝ) *
              criticalWindowCoarseTail c C r K L n) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (criticalWindowSmallAssemblyFailureRatio k a L) atTop (𝓝 0) := by
  obtain ⟨L, hL, htailZero⟩ := exists_criticalWindowCoarseTail_tendsto_zero hc hC r hK
  obtain ⟨cFar, hcFar, hfar⟩ := eventually_criticalWindowFar_le k hk a tau htau
  have hdefectZero := criticalWindowCoarseSeries_mul_exp_neg_tendsto_zero hc hC r hK hd
  have hzero := ((criticalWindowFarGaussian_tendsto_zero hcFar).add htailZero).add hdefectZero
  simp only [add_zero] at hzero
  refine ⟨L, hL, squeeze_zero' ?_ ?_ hzero⟩
  · exact Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hfar, hdefect, htail L hL,
      eventually_criticalWindowCoPartiteCount_pos k hk a,
      eventually_ge_atTop (k - 1)] with n hfar hdef htail hcoPos hn
    let F := (inducedStarFreeGraphCountWithEdges k n (criticalWindowEdgeCount k a n) : ℝ)
    let Co := (coMultipartiteGraphCountWithEdges (k - 1) n
      (criticalWindowEdgeCount k a n) : ℝ)
    have hCoF : Co ≤ F := by
      dsimp [Co, F]
      exact_mod_cast criticalWindowCoPartiteCount_le_fullCount (n := n) hk a
    have hCo : 0 < Co := by dsimp [Co]; exact_mod_cast hcoPos
    have hF : 0 < F := lt_of_lt_of_le hCo hCoF
    have htpos : 0 ≤ criticalWindowCoarseTail c C r K L n := by
      dsimp [criticalWindowCoarseTail, criticalWindowCoarseSeriesTerm]
      positivity
    have hdpos : 0 ≤ criticalWindowCoarseSeries c C r K n * Real.exp (-d * n) := by
      dsimp [criticalWindowCoarseSeries, criticalWindowCoarseSeriesTerm]
      positivity
    have htail' :
        (criticalWindowCleanTailTotal k hk n (criticalWindowEdgeCount k a n)
          (criticalLogarithmicSparseCutoff L n) tau : ℝ) ≤
            F * criticalWindowCoarseTail c C r K L n :=
      htail.trans (mul_le_mul_of_nonneg_right hCoF htpos)
    have hdef' :
        (criticalWindowDefectTotal k hk n (criticalWindowEdgeCount k a n) tau : ℝ) ≤
          F * (criticalWindowCoarseSeries c C r K n * Real.exp (-d * n)) := by
      calc
        _ ≤ Co * (criticalWindowCoarseSeries c C r K n * Real.exp (-d * n)) := by
          simpa only [mul_assoc] using hdef
        _ ≤ _ := mul_le_mul_of_nonneg_right hCoF hdpos
    have hcover :
        ((criticalNoSmallAssemblyGraphFinset k n (criticalWindowEdgeCount k a n)
          (criticalLogarithmicSparseCutoff L n)).card : ℝ) ≤
        ((supercriticalFarGraphFinset k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          (criticalWindowEdgeCount k a n) n tau).card : ℝ) +
        (criticalWindowCleanTailTotal k hk n (criticalWindowEdgeCount k a n)
          (criticalLogarithmicSparseCutoff L n) tau : ℝ) +
        (criticalWindowDefectTotal k hk n (criticalWindowEdgeCount k a n) tau : ℝ) := by
      exact_mod_cast card_criticalNoSmallAssemblyGraphFinset_le
        k hk n (criticalWindowEdgeCount k a n) (criticalLogarithmicSparseCutoff L n) tau hn
    apply (div_le_iff₀ hF).mpr
    change _ ≤ (Real.exp (-cFar * (n : ℝ)^2) + criticalWindowCoarseTail c C r K L n +
      criticalWindowCoarseSeries c C r K n * Real.exp (-d * n)) * F
    change _ ≤ F * Real.exp (-cFar * (n : ℝ)^2) at hfar
    calc
      _ ≤ _ := hcover
      _ ≤ F * Real.exp (-cFar * (n : ℝ)^2) +
          F * criticalWindowCoarseTail c C r K L n +
          F * (criticalWindowCoarseSeries c C r K n * Real.exp (-d * n)) :=
        add_le_add (add_le_add hfar htail') hdef'
      _ = _ := by ring

/-- Every fixed signed window displacement has a logarithmic literal
assembly with probability tending to one. -/
theorem exists_criticalWindowSmallAssemblyFailureRatio_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) (a : ℝ) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (criticalWindowSmallAssemblyFailureRatio k a L) atTop (𝓝 0) := by
  obtain ⟨P⟩ := exists_criticalAggregationParameters k hk
  obtain ⟨C, hC, hbounds⟩ := eventually_criticalWindowTotals_le k hk a P
  apply exists_criticalWindowSmallAssemblyFailureRatio_tendsto_zero_of_bounds
    k hk a P.tau P.tau_pos
    (criticalSparsePenaltyConstant_pos hk) hC (k - 1)
    (K := ((2 * (k - 1).factorial : ℕ) : ℝ))
    (d := P.cMat / 4) (by positivity) (div_pos P.cMat_pos (by norm_num))
  · exact hbounds.mono fun _ h ↦ h.1
  · intro L _
    exact hbounds.mono fun _ h ↦ h.2 L

end InducedStars
