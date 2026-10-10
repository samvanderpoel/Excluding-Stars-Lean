import InducedStars.Structure.Subcritical.AdmissibleResidualMatching
import InducedStars.Structure.Subcritical.ResidualMatchingScalars
import InducedStars.Structure.Subcritical.ResidualParameterFeasibility

/-!
# Entropy reserve for an arbitrary residual edge weight

The weighted sum in lemma:residual-matching-estimate-K1k permits any fixed
edge-weight constant. Continuity at zero gives one positive degree interval
for that constant; the graph-order threshold is then uniform on the interval.
All entropy and exponential rates here are measured in natural units.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InducedStars

/-- Choose the degree cap before the graph order, uniformly for every degree
in the resulting closed interval. The scalar estimate holds for every real
edge weight; weighted enumeration subsequently uses a nonnegative weight. -/
theorem exists_subcriticalAdmissibleResidualDegreeReserve
    {k R₀ : ℕ} {eta : ℝ} (hk : 3 ≤ k) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (C : ℝ) :
    ∃ d0 : ℝ, 0 < d0 ∧ d0 ≤ subcriticalResidualDegreeCap k eta R₀ ∧
      d0 ≤ 1 / 2 ∧
      ∀ᶠ n : ℕ in atTop, ∀ d ∈ Icc (0 : ℝ) d0,
        subcriticalAdmissibleResidualEnumerationCoefficient d C n ≤
          subcriticalResidualMatchingConstant k eta R₀ /
            (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) := by
  let c := subcriticalResidualMatchingConstant k eta R₀ /
    (2 * (subcriticalResidualMatchingKappa eta R₀ : ℝ))
  have hkap : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
    have hh := subcriticalResidualMatchingKappa_pos heta hR
    exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ by omega)
  have hc : 0 < c := by
    exact div_pos (subcriticalResidualMatchingConstant_pos hk heta hR)
      (mul_pos (by norm_num) hkap)
  have hCap : 0 < subcriticalResidualDegreeCap k eta R₀ :=
    subcriticalResidualDegreeCap_pos k heta hR
  have hcont : ContinuousAt (fun d : ℝ ↦ 2 * (Real.binEntropy d + C * d)) 0 := by
    fun_prop
  have ht : Tendsto (fun d : ℝ ↦ 2 * (Real.binEntropy d + C * d))
      (𝓝 0) (𝓝 0) := by
    simpa only [Real.binEntropy_zero, mul_zero, add_zero] using hcont.tendsto
  have he := ht.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 2))
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp he
  let d0 := min (r / 2) (min (subcriticalResidualDegreeCap k eta R₀) (1 / 2))
  have hd0 : 0 < d0 := by
    dsimp [d0]
    positivity
  have hd0Cap : d0 ≤ subcriticalResidualDegreeCap k eta R₀ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hd0Half : d0 ≤ 1 / 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hbase : ∀ d ∈ Icc (0 : ℝ) d0, 2 * (Real.binEntropy d + C * d) < c / 2 := by
    intro d hd
    apply he
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd.1]
    have hdr : d0 ≤ r / 2 := min_le_left _ _
    linarith [hd.2]
  have hlog := subcriticalResidual_logOrder_tendsto_zero.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 4))
  refine ⟨d0, hd0, hd0Cap, hd0Half, ?_⟩
  filter_upwards [hlog] with n hnLog
  intro d hd
  have hdBase := hbase d hd
  change Real.log ((n : ℝ) + 1) / n < c / 4 at hnLog
  change 2 * (Real.binEntropy d + C * d + Real.log (n + 1) / n) ≤ c
  linarith only [hdBase, hnLog]

end InducedStars
