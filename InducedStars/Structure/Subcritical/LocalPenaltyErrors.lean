import InducedStars.Structure.Subcritical.RootEntropyAssembly
import InducedStars.Structure.Subcritical.LocalTail

/-!
# A common quantitative local-error reserve

All local entropy and tail errors are combined before selecting parameters.
Joint continuity at the origin provides one uniform positive radius, while
an explicit minimum enforces every elementary compact-density condition.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace InducedStars

/-- Sum of every finite error used in the retained-root compensation. -/
def subcriticalTotalErrorNat (k R₀ : ℕ) (eta alpha delta xi zeta : ℝ) : ℝ :=
  subcriticalSmallOwnErrorNat k alpha xi + Real.binEntropy (2 * alpha) +
    ((k - 1 : ℕ) : ℝ) * subcriticalRowErrorNat k alpha (zeta + xi) +
    subcriticalExternalComponentErrorNat k R₀ eta alpha (zeta + xi) +
    ((k - 2 : ℕ) : ℝ) * subcriticalTailErrorNat k alpha delta xi zeta

theorem subcriticalSmallOwnErrorNat_nonneg {k : ℕ} (hk : 3 ≤ k)
    {alpha xi : ℝ} (ha : 0 ≤ alpha) (hxi1 : xi < 1)
    (hband : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2) :
    0 ≤ subcriticalSmallOwnErrorNat k alpha xi := by
  have hC : 0 ≤ subcriticalSmallOwnConstant k := by
    unfold subcriticalSmallOwnConstant
    positivity
  have hden : 0 < 1 - xi := by linarith
  have hh := Real.binEntropy_nonneg (div_nonneg (mul_nonneg hC ha) hden.le)
    (show subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 by linarith)
  have hL := (subcriticalLogOddsNat_pos hk).le
  unfold subcriticalSmallOwnErrorNat
  positivity

theorem subcriticalExternalComponentErrorNat_nonneg {k R₀ : ℕ} (hk : 3 ≤ k)
    {eta alpha zeta : ℝ} (heta : 0 ≤ eta) (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4)
    (hz : 0 ≤ zeta) : 0 ≤ subcriticalExternalComponentErrorNat k R₀ eta alpha zeta := by
  have hE := subcriticalRowErrorNat_nonneg hk ha ha4 hz
  unfold subcriticalExternalComponentErrorNat
  positivity

/-- Every component of the common error budget is nonnegative. -/
theorem subcriticalTotalErrorNat_components_nonneg {k R₀ : ℕ} (hk : 3 ≤ k)
    {eta alpha delta xi zeta : ℝ} (heta : 0 ≤ eta)
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hz : 0 ≤ zeta)
    (hown : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2)
    (htail : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    0 ≤ subcriticalSmallOwnErrorNat k alpha xi ∧
    0 ≤ Real.binEntropy (2 * alpha) ∧
    0 ≤ ((k - 1 : ℕ) : ℝ) * subcriticalRowErrorNat k alpha (zeta + xi) ∧
    0 ≤ subcriticalExternalComponentErrorNat k R₀ eta alpha (zeta + xi) ∧
    0 ≤ ((k - 2 : ℕ) : ℝ) * subcriticalTailErrorNat k alpha delta xi zeta := by
  exact ⟨subcriticalSmallOwnErrorNat_nonneg hk ha hxi1 hown,
    Real.binEntropy_nonneg (by linarith) (by linarith),
    mul_nonneg (Nat.cast_nonneg _) (subcriticalRowErrorNat_nonneg hk ha ha4 (add_nonneg hz hxi)),
    subcriticalExternalComponentErrorNat_nonneg hk heta ha ha4 (add_nonneg hz hxi),
    mul_nonneg (Nat.cast_nonneg _) (subcriticalTailErrorNat_nonneg hk ha hd hxi hxi1 htail hz)⟩

theorem subcriticalTotalErrorNat_nonneg {k R₀ : ℕ} (hk : 3 ≤ k)
    {eta alpha delta xi zeta : ℝ} (heta : 0 ≤ eta)
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hz : 0 ≤ zeta)
    (hown : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2)
    (htail : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    0 ≤ subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    subcriticalTotalErrorNat_components_nonneg hk heta ha ha4 hd hxi hxi1 hz hown htail
  unfold subcriticalTotalErrorNat
  linarith

/-- Each summand is dominated by the common error. -/
theorem subcriticalTotalErrorNat_component_le {k R₀ : ℕ} (hk : 3 ≤ k)
    {eta alpha delta xi zeta : ℝ} (heta : 0 ≤ eta)
    (ha : 0 ≤ alpha) (ha4 : alpha ≤ 1 / 4) (hd : 0 ≤ delta)
    (hxi : 0 ≤ xi) (hxi1 : xi < 1) (hz : 0 ≤ zeta)
    (hown : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2)
    (htail : 2 * alpha / (1 - xi) ≤ 1 / 2) :
    subcriticalSmallOwnErrorNat k alpha xi ≤ subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta ∧
    Real.binEntropy (2 * alpha) ≤ subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta ∧
    ((k - 1 : ℕ) : ℝ) * subcriticalRowErrorNat k alpha (zeta + xi) ≤
      subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta ∧
    subcriticalExternalComponentErrorNat k R₀ eta alpha (zeta + xi) ≤
      subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta ∧
    ((k - 2 : ℕ) : ℝ) * subcriticalTailErrorNat k alpha delta xi zeta ≤
      subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta := by
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    subcriticalTotalErrorNat_components_nonneg hk heta ha ha4 hd hxi hxi1 hz hown htail
  unfold subcriticalTotalErrorNat
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The complete four-parameter error is continuous at zero. Its only
variable denominator is `1-xi`, which equals one there. -/
theorem subcriticalTotalErrorNat_continuousAt_zero (k R₀ : ℕ) (eta : ℝ) :
    ContinuousAt (fun x : ℝ × ℝ × ℝ × ℝ ↦
      subcriticalTotalErrorNat k R₀ eta x.1 x.2.1 x.2.2.1 x.2.2.2) (0, 0, 0, 0) := by
  unfold subcriticalTotalErrorNat subcriticalSmallOwnErrorNat
    subcriticalExternalComponentErrorNat subcriticalRowErrorNat subcriticalHighRowErrorNat
    subcriticalTailErrorNat subcriticalTailBaseErrorNat
  fun_prop (disch := norm_num)

@[simp] theorem subcriticalTotalErrorNat_zero (k R₀ : ℕ) (eta : ℝ) :
    subcriticalTotalErrorNat k R₀ eta 0 0 0 0 = 0 := by
  simp [subcriticalTotalErrorNat, subcriticalSmallOwnErrorNat,
    subcriticalExternalComponentErrorNat, subcriticalRowErrorNat, subcriticalHighRowErrorNat,
    subcriticalTailErrorNat, subcriticalTailBaseErrorNat]

/-- One positive closed-box radius controls all local errors and the
compact density and entropy bands. No parameter choice depends on a graph,
profile, division, or graph order. -/
theorem subcriticalTotalErrorNat_uniform_radius {k : ℕ} (hk : 3 ≤ k)
    (R₀ : ℕ) (eta : ℝ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 8 ∧ subcriticalSmallOwnConstant k * r ≤ 1 / 4 ∧
      2 * r ≤ pK k ∧ 2 * r ≤ 1 - pK k ∧
      ∀ alpha delta xi zeta : ℝ,
        alpha ∈ Icc 0 r → delta ∈ Icc 0 r → xi ∈ Icc 0 r → zeta ∈ Icc 0 r →
        subcriticalTotalErrorNat k R₀ eta alpha delta xi zeta ≤ subcriticalLocalA_Nat k / 4 := by
  have hA := subcriticalLocalA_Nat_pos hk
  have hp := pK_pos (show 2 ≤ k by omega)
  have hp1 := pK_lt_one (show 2 ≤ k by omega)
  have hC : 0 ≤ subcriticalSmallOwnConstant k := by
    unfold subcriticalSmallOwnConstant
    positivity
  have he : ∀ᶠ x : ℝ × ℝ × ℝ × ℝ in 𝓝 (0, 0, 0, 0),
      subcriticalTotalErrorNat k R₀ eta x.1 x.2.1 x.2.2.1 x.2.2.2 <
        subcriticalLocalA_Nat k / 4 := by
    have ht : Tendsto (fun x : ℝ × ℝ × ℝ × ℝ ↦
        subcriticalTotalErrorNat k R₀ eta x.1 x.2.1 x.2.2.1 x.2.2.2)
        (𝓝 (0, 0, 0, 0)) (𝓝 (0 : ℝ)) := by
      simpa only [subcriticalTotalErrorNat_zero] using
        (subcriticalTotalErrorNat_continuousAt_zero k R₀ eta).tendsto
    exact ht.eventually (p := fun y : ℝ ↦ y < subcriticalLocalA_Nat k / 4)
      (Iio_mem_nhds (by positivity))
  obtain ⟨d, hd, he⟩ := Metric.eventually_nhds_iff.mp he
  let r := min (d / 2) (min (1 / 8) (min (1 / (4 * subcriticalSmallOwnConstant k + 4))
    (min (pK k / 2) ((1 - pK k) / 2))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrD : r ≤ d / 2 := min_le_left _ _
  have hr8 : r ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1 / (4 * subcriticalSmallOwnConstant k + 4) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrP : r ≤ pK k / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hrQ : r ≤ (1 - pK k) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hc : subcriticalSmallOwnConstant k * r ≤ 1 / 4 := by
    have hden : 0 < 4 * subcriticalSmallOwnConstant k + 4 := by positivity
    have hm := (le_div_iff₀ hden).mp hrC
    nlinarith
  refine ⟨r, hr, hr8, hc, by linarith, by linarith, ?_⟩
  intro alpha delta xi zeta ha hδ hxi hz
  apply le_of_lt (he (y := (alpha, delta, xi, zeta)) ?_)
  simp only [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
  exact ⟨by rw [abs_of_nonneg ha.1]; linarith [ha.2],
    ⟨by rw [abs_of_nonneg hδ.1]; linarith [hδ.2],
      ⟨by rw [abs_of_nonneg hxi.1]; linarith [hxi.2],
        by rw [abs_of_nonneg hz.1]; linarith [hz.2]⟩⟩⟩

end InducedStars
