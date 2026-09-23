import InducedStars.C4.GlobalCounting
import InducedStars.C4.SplitEnumeration
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Consequences of the final exact C4 count comparison

Paper: the last counting display and entropy deduction in `paper/c4-free.tex`.
These are local adapters with an explicit eventual counting-bound premise;
the main theorem must prove that premise from the geometric decomposition
and penalty estimates. The objects throughout are the actual finite graph
families, not substitute benchmark counts.
-/

noncomputable section
open Filter
open scoped Topology
namespace InducedStars

/-- Elementary absorption of a small self-error in the actual graph count. -/
theorem c4CountRatio_abs_sub_one_le {n m : ℕ} {u v : ℝ}
    (hpos : 0 < splitGraphCountWithEdges n m)
    (hu : 0 ≤ u) (hsmall : u ≤ 1 / 4) (hv : v ≤ u)
    (hcount : (inducedC4FreeGraphCountWithEdges n m : ℝ) ≤
      (1 + u) * (splitGraphCountWithEdges n m : ℝ) +
        v * (inducedC4FreeGraphCountWithEdges n m : ℝ)) :
    |(inducedC4FreeGraphCountWithEdges n m : ℝ) /
      (splitGraphCountWithEdges n m : ℝ) - 1| ≤ 4 * u := by
  let S : ℝ := splitGraphCountWithEdges n m
  let N : ℝ := inducedC4FreeGraphCountWithEdges n m
  have hS : 0 < S := by dsimp [S]; exact_mod_cast hpos
  have hN : 0 ≤ N := by positivity
  have hSN : S ≤ N := by
    dsimp [S, N]
    exact_mod_cast splitGraphCountWithEdges_le_inducedC4Free n m
  change N ≤ (1 + u) * S + v * N at hcount
  change |N / S - 1| ≤ 4 * u
  have htwo : N ≤ 2 * S := by
    have h1 := mul_le_mul_of_nonneg_right hsmall hS.le
    have h2 := mul_le_mul_of_nonneg_right (hv.trans hsmall) hN
    nlinarith
  have hdiff : N - S ≤ 3 * u * S := by
    have h1 := mul_le_mul_of_nonneg_right hv hN
    have h2 := mul_le_mul_of_nonneg_left htwo hu
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr ((one_le_div hS).mpr hSN))]
  apply (sub_le_iff_le_add).mpr
  apply (div_le_iff₀ hS).mpr
  nlinarith [mul_nonneg hu hS.le]

/-- A linear exponential rate for the exact count ratio, conditional only
on the displayed final counting estimate. The rate is explicitly `a / 2`. -/
theorem eventually_c4CountRatio_abs_sub_one_le_exp_of_count_bound
    {gamma a b : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1)
    (ha : 0 < a) (hb : 0 < b) {m : ℕ → ℕ}
    (hm : HasAsymptoticEdgeDensity m gamma)
    (hcount : ∀ᶠ n in atTop,
      (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) ≤
        (1 + Real.exp (-a * n)) * (splitGraphCountWithEdges n (m n) : ℝ) +
          Real.exp (-b * (n : ℝ) ^ 2) * (inducedC4FreeGraphCountWithEdges n (m n) : ℝ)) :
    ∀ᶠ n in atTop,
      |(inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
        (splitGraphCountWithEdges n (m n) : ℝ) - 1| ≤ Real.exp (-(a / 2) * n) := by
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.exp (-a * n) ≤ 1 / 4 := by
    filter_upwards [(tendsto_exp_neg_mul_natCast_zero ha).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))] with n hn
    exact hn.le
  have hlinear : ∀ᶠ n : ℕ in atTop, a ≤ b * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hb).eventually_ge_atTop a
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log 4 ≤ (a / 2) * n :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (show 0 < a / 2 by positivity)).eventually_ge_atTop _
  filter_upwards [hcount, eventually_splitGraphCountWithEdges_pos hgamma hm,
    hsmall, hlinear, hlog] with n hcount hpos hsmall hlinear hlog
  have hquad : Real.exp (-b * (n : ℝ) ^ 2) ≤ Real.exp (-a * n) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hlinear (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  apply (c4CountRatio_abs_sub_one_le hpos (Real.exp_pos _).le hsmall hquad hcount).trans
  conv_lhs => lhs; rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

theorem c4CountRatio_tendsto_one_of_count_bound
    {gamma a b : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1)
    (ha : 0 < a) (hb : 0 < b) {m : ℕ → ℕ}
    (hm : HasAsymptoticEdgeDensity m gamma)
    (hcount : ∀ᶠ n in atTop,
      (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) ≤
        (1 + Real.exp (-a * n)) * (splitGraphCountWithEdges n (m n) : ℝ) +
          Real.exp (-b * (n : ℝ) ^ 2) * (inducedC4FreeGraphCountWithEdges n (m n) : ℝ)) :
    Tendsto (fun n ↦ (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1) := by
  have hbound := eventually_c4CountRatio_abs_sub_one_le_exp_of_count_bound hgamma ha hb hm hcount
  have hz := squeeze_zero' (Eventually.of_forall (fun n ↦
    abs_nonneg ((inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ) - 1))) hbound
      (tendsto_exp_neg_mul_natCast_zero (show 0 < a / 2 by positivity))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hz)

theorem splitCount_div_c4Count_tendsto_one_of_countRatio
    {m : ℕ → ℕ}
    (hratio : Tendsto (fun n ↦ (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n ↦ (splitGraphCountWithEdges n (m n) : ℝ) /
      (inducedC4FreeGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1) := by
  simpa only [inv_div, inv_one] using hratio.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem c4SplitProbability_tendsto_one_of_countRatio
    {m : ℕ → ℕ}
    (hratio : Tendsto (fun n ↦ (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n ↦ c4SplitProbability n (m n)) atTop (𝓝 1) := by
  simpa only [c4SplitProbability, uniformSubfamilyProbability,
    splitGraphCountWithEdges, inducedC4FreeGraphCountWithEdges] using
      splitCount_div_c4Count_tendsto_one_of_countRatio hratio

theorem c4NonsplitProbability_tendsto_zero_of_splitProbability
    {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) {m : ℕ → ℕ}
    (hm : HasAsymptoticEdgeDensity m gamma)
    (hprob : Tendsto (fun n ↦ c4SplitProbability n (m n)) atTop (𝓝 1)) :
    Tendsto (fun n ↦ c4NonsplitProbability n (m n)) atTop (𝓝 0) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hprob
  have h' : Tendsto (fun n ↦ 1 - c4SplitProbability n (m n)) atTop (𝓝 0) := by
    simpa using h
  apply h'.congr'
  filter_upwards [eventually_splitGraphCountWithEdges_pos hgamma hm] with n hpos
  have htotal : 0 < inducedC4FreeGraphCountWithEdges n (m n) :=
    hpos.trans_le (splitGraphCountWithEdges_le_inducedC4Free n (m n))
  linarith [c4SplitProbability_add_nonsplit htotal]

/-- Transfer of the proved split-graph entropy through an actual count-ratio
limit. No Stirling formula or unproved enumeration statement is used. -/
theorem c4Count_normalizedLog_tendsto_of_countRatio
    {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) {m : ℕ → ℕ}
    (hm : HasAsymptoticEdgeDensity m gamma)
    (hratio : Tendsto (fun n ↦ (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (splitGraphCountWithEdges n (m n) : ℝ)) atTop (𝓝 1)) :
    Tendsto (fun n ↦ log2 (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
      (completeEdgeCount n : ℝ)) atTop (𝓝 (c4SplitOptimalEntropy gamma)) := by
  have hlog : Tendsto (fun n ↦ Real.log
      ((inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
        (splitGraphCountWithEdges n (m n) : ℝ))) atTop (𝓝 0) := by
    simpa only [Real.log_one, Function.comp_def] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hinv : Tendsto (fun n ↦ (completeEdgeCount n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_completeEdgeCount_cast_atTop
  have herror : Tendsto (fun n ↦ log2
      ((inducedC4FreeGraphCountWithEdges n (m n) : ℝ) /
        (splitGraphCountWithEdges n (m n) : ℝ)) /
          (completeEdgeCount n : ℝ)) atTop (𝓝 0) := by
    simpa only [log2, div_eq_mul_inv, zero_mul] using
      (hlog.div_const (Real.log 2)).mul hinv
  have hsum := (splitGraphCount_normalizedLog_tendsto hgamma hm).add herror
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_splitGraphCountWithEdges_pos hgamma hm] with n hpos
  have hS : (splitGraphCountWithEdges n (m n) : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hN : (inducedC4FreeGraphCountWithEdges n (m n) : ℝ) ≠ 0 := by
    exact_mod_cast (hpos.trans_le (splitGraphCountWithEdges_le_inducedC4Free n (m n))).ne'
  unfold log2
  rw [Real.log_div hN hS]
  ring

end InducedStars
