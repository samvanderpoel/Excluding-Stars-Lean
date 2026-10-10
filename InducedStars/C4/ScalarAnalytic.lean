import InducedStars.C4.ScalarParametrization
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Analytic dependence of the optimal split model

The inverse function theorem applies to the strictly increasing analytic
stationary-density parametrization.  Its local inverse is identified with
the actual optimizer's cross density, using uniqueness of the parameter.
This proves the analyticity assertion following `eqn:c4-entropy-main` in
the introduction, rather than merely continuity of the variational value.
-/

namespace InducedStars

open Filter Set
open scoped Topology

/-- Cross density of the entropy-maximizing split model. -/
noncomputable def c4OptimalCrossDensity (γ : ℝ) : ℝ :=
  c4SplitCrossDensity γ (c4Lambda γ)

/-- The optimized base-two entropy in the paper's `binom(n,2)` normalization. -/
noncomputable def c4SplitOptimalEntropy (γ : ℝ) : ℝ :=
  2 * c4SplitEntropy γ (c4Lambda γ)

lemma c4OptimalCrossDensity_mem_Ioo {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4OptimalCrossDensity γ ∈ Ioo 0 1 :=
  c4SplitCrossDensity_c4Lambda_mem_Ioo hγ

lemma analyticAt_c4OptimalCrossDensity {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    AnalyticAt ℝ c4OptimalCrossDensity γ := by
  let q := c4OptimalCrossDensity γ
  have hq : q ∈ Ioo 0 1 := c4OptimalCrossDensity_mem_Ioo hγ
  have hΓ : c4StationaryTotalDensity q = γ := c4StationaryTotalDensity_at_optimizer hγ
  have ha := analyticAt_c4StationaryTotalDensity hq
  have hd : deriv c4StationaryTotalDensity q ≠ 0 := (deriv_c4StationaryTotalDensity_pos hq).ne'
  let r : ℝ → ℝ := ha.hasStrictDerivAt.localInverse _ _ _ hd
  have hr : AnalyticAt ℝ r (c4StationaryTotalDensity q) := ha.analyticAt_localInverse hd
  have hrγ : AnalyticAt ℝ r γ := by rwa [hΓ] at hr
  have hrbase : r γ = q := by
    have hbase : r (c4StationaryTotalDensity q) = q :=
      (ha.hasStrictDerivAt.eventually_left_inverse hd).self_of_nhds
    rwa [hΓ] at hbase
  have hrange : ∀ᶠ y in 𝓝 γ, r y ∈ Ioo 0 1 :=
    hrγ.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rwa [hrbase]))
  have hright : ∀ᶠ y in 𝓝 γ, c4StationaryTotalDensity (r y) = y := by
    simpa only [hΓ] using ha.hasStrictDerivAt.eventually_right_inverse hd
  apply hrγ.congr
  filter_upwards [isOpen_Ioo.mem_nhds hγ, hrange, hright] with y hy hry hrighty
  apply strictMonoOn_c4StationaryTotalDensity.injOn hry (c4OptimalCrossDensity_mem_Ioo hy)
  exact hrighty.trans (c4StationaryTotalDensity_at_optimizer hy).symm

/-- The maximizing clique proportion is real analytic at every density in `(0,1)`. -/
lemma analyticAt_c4Lambda {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    AnalyticAt ℝ c4Lambda γ := by
  have hp := analyticAt_c4StationaryCliqueProportion (c4OptimalCrossDensity_mem_Ioo hγ)
  have ha := hp.comp (analyticAt_c4OptimalCrossDensity hγ)
  apply ha.congr
  filter_upwards [isOpen_Ioo.mem_nhds hγ] with y hy
  exact c4StationaryCliqueProportion_at_optimizer hy

lemma analyticOnNhd_c4Lambda : AnalyticOnNhd ℝ c4Lambda (Ioo 0 1) :=
  fun _ hγ => analyticAt_c4Lambda hγ

lemma analyticOnNhd_c4OptimalCrossDensity :
    AnalyticOnNhd ℝ c4OptimalCrossDensity (Ioo 0 1) :=
  fun _ hγ => analyticAt_c4OptimalCrossDensity hγ

private lemma analyticAt_binEntropy_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo 0 1) :
    AnalyticAt ℝ Real.binEntropy q := by
  have heq : Real.binEntropy = fun y : ℝ =>
      -y * Real.log y - (1 - y) * Real.log (1 - y) := by
    funext y
    simp only [Real.binEntropy, Real.log_inv]
    ring
  rw [heq]
  exact (analyticAt_id.neg.mul (analyticAt_log hq.1)).sub
    ((analyticAt_const.sub analyticAt_id).mul
      ((analyticAt_const.sub analyticAt_id).log (sub_pos.mpr hq.2)))

lemma analyticAt_c4SplitEntropyNat_optimizer {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    AnalyticAt ℝ (fun y => c4SplitEntropyNat y (c4Lambda y)) γ := by
  have hl := analyticAt_c4Lambda hγ
  have hq := analyticAt_c4OptimalCrossDensity hγ
  exact (hl.mul (analyticAt_const.sub hl)).mul
    ((analyticAt_binEntropy_of_mem_Ioo (c4OptimalCrossDensity_mem_Ioo hγ)).comp hq)

lemma analyticAt_c4SplitEntropy_optimizer {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    AnalyticAt ℝ (fun y => c4SplitEntropy y (c4Lambda y)) γ := by
  have heq : (fun y => c4SplitEntropy y (c4Lambda y)) =
      (fun y => c4SplitEntropyNat y (c4Lambda y) / Real.log 2) := by
    funext y
    exact c4SplitEntropy_eq_nat_div_log_two y (c4Lambda y)
  rw [heq]
  exact (analyticAt_c4SplitEntropyNat_optimizer hγ).div_const

/-- Paper: the real-analyticity assertion following `eqn:c4-entropy-main`.
This is the actual maximizing value, with the factor two required by the
paper's complete-edge-count normalization. -/
lemma analyticAt_c4SplitOptimalEntropy {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    AnalyticAt ℝ c4SplitOptimalEntropy γ :=
  analyticAt_const.mul (analyticAt_c4SplitEntropy_optimizer hγ)

lemma analyticOnNhd_c4SplitOptimalEntropy :
    AnalyticOnNhd ℝ c4SplitOptimalEntropy (Ioo 0 1) :=
  fun _ hγ => analyticAt_c4SplitOptimalEntropy hγ

lemma continuousOn_c4Lambda : ContinuousOn c4Lambda (Ioo 0 1) :=
  fun _ hγ => (analyticAt_c4Lambda hγ).continuousAt.continuousWithinAt

lemma continuousOn_c4OptimalCrossDensity : ContinuousOn c4OptimalCrossDensity (Ioo 0 1) :=
  fun _ hγ => (analyticAt_c4OptimalCrossDensity hγ).continuousAt.continuousWithinAt

end InducedStars
