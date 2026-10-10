import InducedStars.Structure.Critical.Totals
import InducedStars.Structure.Critical.Families
import InducedStars.Structure.Critical.GaussianSums
import InducedStars.Structure.Supercritical.ReferenceFiber
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Probability assembly at the exact critical density

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
def criticalSmallAssemblyFailureRatio (k : ℕ) (L : ℝ) (n : ℕ) : ℝ :=
  ((criticalNoSmallAssemblyGraphFinset k n (criticalEdgeCount k n)
    (criticalLogarithmicSparseCutoff L n)).card : ℝ) /
      (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ)

theorem eventually_criticalCoPartiteCount_pos
    (k : ℕ) (hk : 3 ≤ k) :
    ∀ᶠ n : ℕ in atTop,
      0 < coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) :=
  eventually_coMultipartiteGraphCountWithEdges_pos k hk (gammaK k)
    ⟨one_div_parts_lt_gammaK hk, gammaK_lt_one hk⟩
    (criticalEdgeCount k) (criticalEdgeCount_hasAsymptoticEdgeDensity hk)

theorem criticalCoPartiteCount_le_fullCount
    {k n : ℕ} (hk : 3 ≤ k) :
    coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) ≤
      inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) :=
  Finset.card_le_card (coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree (by omega))

/-- The full coarse sum is negligible after any positive linear penalty. -/
theorem criticalRemainderSeries_mul_exp_neg_tendsto_zero
    {c C K d : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ)
    (hK : 0 < K) (hd : 0 < d) :
    Tendsto (fun n : ℕ ↦ criticalRemainderSeries c C r K n *
      Real.exp (-d * n)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := exists_eventually_criticalRemainderSeries_le hc hC r hK
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
      dsimp [criticalRemainderSeries, criticalRemainderSeriesTerm]
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

theorem criticalFarGaussian_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ Real.exp (-c * (n : ℝ)^2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ ↦ (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp (hsq.const_mul_atTop_of_neg (neg_neg_of_pos hc))

/-- Concrete bounds for the canonical defect total and clean tail imply
the logarithmic coarse decomposition for the uniform exact-edge family. -/
theorem exists_criticalSmallAssemblyFailureRatio_tendsto_zero_of_bounds
    (k : ℕ) (hk : 3 ≤ k) (tau : ℝ) (htau : 0 < tau)
    {c C K d : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ)
    (hK : 0 < K) (hd : 0 < d)
    (hdefect : ∀ᶠ n : ℕ in atTop,
      (criticalDefectTotal k hk n (criticalEdgeCount k n) tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
            criticalRemainderSeries c C r K n * Real.exp (-d * n))
    (htail : ∀ L : ℝ, 0 < L → ∀ᶠ n : ℕ in atTop,
      (criticalCleanTailTotal k hk n (criticalEdgeCount k n)
        (criticalLogarithmicSparseCutoff L n) tau : ℝ) ≤
          (coMultipartiteGraphCountWithEdges (k - 1) n
            (criticalEdgeCount k n) : ℝ) *
              criticalRemainderTail c C r K L n) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (criticalSmallAssemblyFailureRatio k L) atTop (𝓝 0) := by
  obtain ⟨L, hL, htailZero⟩ := exists_criticalRemainderTail_tendsto_zero hc hC r hK
  obtain ⟨cFar, hcFar, hfar⟩ := eventually_criticalFar_le k hk tau htau
  have hdefectZero := criticalRemainderSeries_mul_exp_neg_tendsto_zero hc hC r hK hd
  have hzero := ((criticalFarGaussian_tendsto_zero hcFar).add htailZero).add hdefectZero
  simp only [add_zero] at hzero
  refine ⟨L, hL, squeeze_zero' ?_ ?_ hzero⟩
  · exact Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [hfar, hdefect, htail L hL,
      eventually_criticalCoPartiteCount_pos k hk,
      eventually_ge_atTop (k - 1)] with n hfar hdef htail hcoPos hn
    let F := (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ)
    let Co := (coMultipartiteGraphCountWithEdges (k - 1) n
      (criticalEdgeCount k n) : ℝ)
    have hCoF : Co ≤ F := by
      dsimp [Co, F]
      exact_mod_cast criticalCoPartiteCount_le_fullCount (n := n) hk
    have hCo : 0 < Co := by dsimp [Co]; exact_mod_cast hcoPos
    have hF : 0 < F := lt_of_lt_of_le hCo hCoF
    have htpos : 0 ≤ criticalRemainderTail c C r K L n := by
      dsimp [criticalRemainderTail, criticalRemainderSeriesTerm]
      positivity
    have hdpos : 0 ≤ criticalRemainderSeries c C r K n * Real.exp (-d * n) := by
      dsimp [criticalRemainderSeries, criticalRemainderSeriesTerm]
      positivity
    have htail' :
        (criticalCleanTailTotal k hk n (criticalEdgeCount k n)
          (criticalLogarithmicSparseCutoff L n) tau : ℝ) ≤
            F * criticalRemainderTail c C r K L n :=
      htail.trans (mul_le_mul_of_nonneg_right hCoF htpos)
    have hdef' :
        (criticalDefectTotal k hk n (criticalEdgeCount k n) tau : ℝ) ≤
          F * (criticalRemainderSeries c C r K n * Real.exp (-d * n)) := by
      calc
        _ ≤ Co * (criticalRemainderSeries c C r K n * Real.exp (-d * n)) := by
          simpa only [mul_assoc] using hdef
        _ ≤ _ := mul_le_mul_of_nonneg_right hCoF hdpos
    have hcover :
        ((criticalNoSmallAssemblyGraphFinset k n (criticalEdgeCount k n)
          (criticalLogarithmicSparseCutoff L n)).card : ℝ) ≤
        ((supercriticalFarGraphFinset k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          (criticalEdgeCount k n) n tau).card : ℝ) +
        (criticalCleanTailTotal k hk n (criticalEdgeCount k n)
          (criticalLogarithmicSparseCutoff L n) tau : ℝ) +
        (criticalDefectTotal k hk n (criticalEdgeCount k n) tau : ℝ) := by
      exact_mod_cast card_criticalNoSmallAssemblyGraphFinset_le
        k hk n (criticalEdgeCount k n) (criticalLogarithmicSparseCutoff L n) tau hn
    apply (div_le_iff₀ hF).mpr
    change _ ≤ (Real.exp (-cFar * (n : ℝ)^2) + criticalRemainderTail c C r K L n +
      criticalRemainderSeries c C r K n * Real.exp (-d * n)) * F
    change _ ≤ F * Real.exp (-cFar * (n : ℝ)^2) at hfar
    calc
      _ ≤ _ := hcover
      _ ≤ F * Real.exp (-cFar * (n : ℝ)^2) +
          F * criticalRemainderTail c C r K L n +
          F * (criticalRemainderSeries c C r K n * Real.exp (-d * n)) :=
        add_le_add (add_le_add hfar htail') hdef'
      _ = _ := by ring

/-- The exact critical-density family has a logarithmic literal assembly with probability tending to one. -/
theorem exists_criticalSmallAssemblyFailureRatio_tendsto_zero
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (criticalSmallAssemblyFailureRatio k L) atTop (𝓝 0) := by
  obtain ⟨P, hdelta⟩ := exists_criticalAggregationParameters k hk
    (criticalCombinedSliceDelta k) (criticalCombinedSliceDelta_pos hk)
  obtain ⟨C, hC, hbounds⟩ := eventually_criticalTotals_le k hk P hdelta
  apply exists_criticalSmallAssemblyFailureRatio_tendsto_zero_of_bounds
    k hk P.tau P.tau_pos
    (criticalSparsePenaltyConstant_pos hk) hC (k - 1)
    (K := ((2 * (k - 1).factorial : ℕ) : ℝ))
    (d := P.cMat / 4) (by positivity) (div_pos P.cMat_pos (by norm_num))
  · exact hbounds.mono fun _ h ↦ h.1
  · intro L _
    exact hbounds.mono fun _ h ↦ h.2 L

/-- Uniform probability of a literal co-partite core and a remainder with
at most the prescribed number of vertices. -/
def criticalStructuredProbability (k n exceptionalBound : ℕ) : ℝ := by
  classical
  exact uniformSubfamilyProbability
    (inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n))
    ((inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n)).filter
      (HasCriticalStructure k exceptionalBound))

/-- The natural-logarithmic cutoff already gives probability tending to one. -/
theorem exists_criticalStructuredProbability_log_succ_tendsto_one
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (criticalLogarithmicSparseCutoff L n)) atTop (𝓝 1) := by
  classical
  obtain ⟨L, hL, hbad⟩ := exists_criticalSmallAssemblyFailureRatio_tendsto_zero k hk
  refine ⟨L, hL, ?_⟩
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_criticalCoPartiteCount_pos k hk] with n hn
  have hfull : 0 < inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) :=
    lt_of_lt_of_le hn (criticalCoPartiteCount_le_fullCount hk)
  have hcard :
      (((inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n)).filter
          (HasCriticalStructure k (criticalLogarithmicSparseCutoff L n))).card : ℝ) +
        ((criticalNoSmallAssemblyGraphFinset k n (criticalEdgeCount k n)
          (criticalLogarithmicSparseCutoff L n)).card : ℝ) =
            (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ) := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not
      (s := inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n))
      (HasCriticalStructure k (criticalLogarithmicSparseCutoff L n)))
  have htotal : (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ) ≠ 0 := by
    exact_mod_cast hfull.ne'
  unfold criticalStructuredProbability uniformSubfamilyProbability
    criticalSmallAssemblyFailureRatio
  apply (sub_eq_iff_eq_add).mpr
  change 1 = _ / (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ) +
    _ / (inducedStarFreeGraphCountWithEdges k n (criticalEdgeCount k n) : ℝ)
  rw [← add_div, hcard, div_self htotal]

/-- A natural-logarithmic cutoff is bounded by a constant multiple of the
paper's base-two logarithm once the order is at least two. -/
theorem criticalLogarithmicSparseCutoff_le_baseTwo
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 2 ≤ n) :
    criticalLogarithmicSparseCutoff L n ≤
      Nat.ceil ((2 * L * Real.log 2) * Real.logb 2 (n : ℝ)) := by
  exact Nat.ceil_mono (criticalLog_succ_mul_le_baseTwo hL hn)

/-- Paper: the critical clause of Theorem thm:main-almostall. At the exact
floor edge count, almost every graph is a literal disjoint union of a
co-(k-1)-partite graph and a graph on O(log n) vertices. -/
theorem inducedStarCriticalAlmostAll (k : ℕ) (hk : 3 ≤ k) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (fun n ↦ criticalStructuredProbability k n
        (Nat.ceil (L * Real.logb 2 (n : ℝ)))) atTop (𝓝 1) := by
  classical
  obtain ⟨L, hL, hlim⟩ := exists_criticalStructuredProbability_log_succ_tendsto_one k hk
  refine ⟨2 * L * Real.log 2, by positivity, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
  · filter_upwards [eventually_criticalCoPartiteCount_pos k hk, eventually_ge_atTop 2]
      with n hn hnTwo
    have hfull : (inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n)).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le hn (criticalCoPartiteCount_le_fullCount hk))
    apply uniformSubfamilyProbability_mono hfull (Finset.filter_subset _ _)
    intro G hG
    obtain ⟨hG, hstructure⟩ := Finset.mem_filter.mp hG
    exact Finset.mem_filter.mpr ⟨hG, hstructure.mono
      (criticalLogarithmicSparseCutoff_le_baseTwo hL.le hnTwo)⟩
  · filter_upwards [eventually_criticalCoPartiteCount_pos k hk] with n hn
    have hfull : (inducedStarFreeGraphFinsetWithEdges k n (criticalEdgeCount k n)).Nonempty :=
      Finset.card_pos.mp (lt_of_lt_of_le hn (criticalCoPartiteCount_le_fullCount hk))
    exact uniformSubfamilyProbability_le_one hfull (Finset.filter_subset _ _)

end InducedStars
