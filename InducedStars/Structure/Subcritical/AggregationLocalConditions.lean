import InducedStars.Structure.Subcritical.LocalPenaltyParameters

/-!
# Certifying local compensation inside a larger hierarchy

This theorem does not choose a second parameter tuple. Explicit closed-interval
bounds certify any tuple selected by the simultaneous aggregation hierarchy.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InducedStars

set_option maxHeartbeats 600000 in
theorem eventually_subcriticalLocalPenaltyParameters_of_bounds
    {k R₀ : ℕ} {eta theta alpha delta epsilon r : ℝ}
    (hk : 3 ≤ k) (hR : 1 ≤ R₀) (heta : 0 < eta) (htheta : 0 < theta)
    (ha : 0 < alpha) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hr : 0 < r) (hr8 : r ≤ 1 / 8)
    (hCr : subcriticalSmallOwnConstant k * r ≤ 1 / 4)
    (herror : ∀ a d xi zeta : ℝ,
      a ∈ Icc 0 r → d ∈ Icc 0 r → xi ∈ Icc 0 r → zeta ∈ Icc 0 r →
      subcriticalTotalErrorNat k R₀ eta a d xi zeta ≤ subcriticalLocalA_Nat k / 4)
    (hvisible : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hrelocation : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)))
    (haR : alpha ≤ r / 4) (ha20 : alpha ≤ 1 / 20)
    (haRelocation : alpha ≤ 1 / (8 * (k : ℝ) + 16))
    (hdR : delta ≤ r) (hdHalf : delta ≤ 1 / 2)
    (hdTolerance : delta ≤ subcriticalRowCountingTolerance k / 2)
    (hdp : delta ≤ pK k / 12) (hdq : delta ≤ (1 - pK k) / 12)
    (hfrac : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 4) :
    ∀ᶠ n : ℕ in atTop,
      SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n := by
  have haR' : alpha ≤ r := by linarith
  have haSmall : 5 * alpha ≤ 1 / 2 := by linarith
  have hdenK : 0 < 8 * (k : ℝ) + 16 := by positivity
  have haReloc : (4 * (k : ℝ) + 8) * alpha ≤ 1 := by
    have hh := (le_div_iff₀ hdenK).mp haRelocation
    nlinarith only [hh]
  let xi := subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta
  have hxi0 : 0 ≤ xi := by
    dsimp [xi, subcriticalTrimErrorNat, subcriticalProfileRootFraction]
    positivity
  have hxiAlpha : xi ≤ alpha / 2 := by
    dsimp [xi, subcriticalTrimErrorNat]
    apply (div_le_iff₀ htheta).mpr
    linarith only [hfrac]
  have hxiR : xi ≤ r := by linarith only [hxiAlpha, haR', hr]
  have hC : 0 ≤ subcriticalSmallOwnConstant k := by
    unfold subcriticalSmallOwnConstant
    positivity
  have hCAlpha : subcriticalSmallOwnConstant k * alpha ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left haR' hC).trans hCr
  have hband : subcriticalSmallOwnConstant k * alpha / (1 - xi) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - xi)).mpr
    linarith only [hCAlpha, hxiR, hr8]
  have hnLarge (B : ℝ) : ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop B)
  filter_upwards [hnLarge (8 / (alpha * theta)), hnLarge (32 * (k : ℝ) ^ 3 / theta),
    hnLarge (4 * (R₀ : ℝ) / eta),
    hnLarge (((k - 2 : ℕ) : ℝ) * subcriticalLocalU_Nat k),
    hnLarge (32 / (theta * r)), hnLarge 1] with n hnRow hnSparse hnSource hnZero hnRound hnOne
  have hnPos : (0 : ℝ) < n := by linarith
  have hzRound : 8 / (theta * n) ≤ r / 4 := by
    have hm := (div_le_iff₀ (mul_pos htheta hr)).mp hnRound
    apply (div_le_iff₀ (mul_pos htheta hnPos)).mpr
    nlinarith only [hm]
  have hz0 : 0 ≤ subcriticalInsideScaleErrorNat alpha delta theta n := by
    unfold subcriticalInsideScaleErrorNat
    positivity
  have hzR : subcriticalInsideScaleErrorNat alpha delta theta n ≤ r := by
    unfold subcriticalInsideScaleErrorNat
    have hm := mul_le_mul_of_nonneg_right hdHalf ha.le
    linarith only [hm, haR, hzRound, hr]
  refine
    { star_order := hk
      retained_order := hR
      eta_pos := heta
      theta_pos := htheta
      alpha_pos := ha
      alpha_small := haSmall
      relocation_alpha := haReloc
      delta_nonneg := hd
      epsilon_nonneg := he
      retained_visible := hvisible
      relocation_theta := hrelocation
      row_counting := by linarith
      density_lower := by linarith
      density_upper := by linarith
      root_fraction := hfrac
      entropy_band := hband
      row_scale := ?_
      sparse_scale := ?_
      source_scale := ?_
      zero_probability_reserve := by nlinarith only [hnZero, hnOne]
      total_error := herror alpha delta xi (subcriticalInsideScaleErrorNat alpha delta theta n)
        ⟨ha.le, haR'⟩ ⟨hd, hdR⟩ ⟨hxi0, hxiR⟩ ⟨hz0, hzR⟩ }
  · simpa only [mul_comm] using (div_le_iff₀ (mul_pos ha htheta)).mp hnRow
  · simpa only [mul_comm] using (div_le_iff₀ htheta).mp hnSparse
  · simpa only [mul_comm] using (div_le_iff₀ heta).mp hnSource

end InducedStars
