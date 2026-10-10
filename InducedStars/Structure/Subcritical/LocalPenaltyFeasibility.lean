import InducedStars.Structure.Subcritical.LocalPenaltyParameters

/-!
# Feasibility of the common finite local-penalty reserves

All choices precede the graph order, division, profile, and candidate.
The free upper bounds preserve earlier parameter restrictions. Alpha is
arbitrarily small; no illustrative sparse-row witness is frozen here.
-/

noncomputable section
open Filter Set
open scoped Topology

namespace InducedStars

/-- An arbitrarily small positive visible cutoff satisfying both the
retained-visibility and sparse-relocation reserves. -/
theorem exists_subcriticalLocalTheta
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (eta thetaMax : ℝ) (heta : 0 < eta) (hmax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      theta ≤ eta / (2 * (R₀ : ℝ)) ∧
      20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  let b := min thetaMax (min (eta / (2 * (R₀ : ℝ)))
    ((eta / (2 * (R₀ : ℝ))) / (20 * (k : ℝ))))
  have hb : 0 < b := by dsimp [b]; positivity
  let theta := b / 2
  have ht : 0 < theta := by dsimp [theta]; positivity
  have htb : theta ≤ b := by dsimp [theta]; linarith
  have hh : theta ≤ thetaMax ∧ theta ≤ eta / (2 * (R₀ : ℝ)) ∧
      theta ≤ (eta / (2 * (R₀ : ℝ))) / (20 * (k : ℝ)) := by
    simpa only [b, le_min_iff] using htb
  refine ⟨theta, ht, hh.1, hh.2.1, ?_⟩
  simpa only [mul_comm] using (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * k)).mp hh.2.2

set_option maxHeartbeats 800000 in
-- The synchronized choice proof builds all numerical reserves in one theorem.
/-- Genuine hierarchy feasibility for local compensation. The closed-box
continuity radius is followed by alpha, delta, epsilon, and only then by
the finite order thresholds. Arbitrary positive outer upper bounds and
the extra linear epsilon-versus-delta cap are all retained. -/
theorem exists_subcriticalLocalPenaltyParameters
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (eta theta : ℝ) (heta : 0 < eta) (htheta : 0 < theta)
    (hvisible : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hrelocation : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)))
    (alphaMax deltaMax epsilonMax epsilonSlope : ℝ)
    (haMax : 0 < alphaMax) (hdMax : 0 < deltaMax)
    (heMax : 0 < epsilonMax) (heSlope : 0 < epsilonSlope) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧
        ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧
          epsilon ≤ min eta (theta ^ 2) ∧ epsilon ≤ delta * epsilonSlope ∧
          ∀ᶠ n : ℕ in atTop,
            SubcriticalLocalPenaltyParameters k R₀ eta theta alpha delta epsilon n := by
  obtain ⟨r, hr, hr8, hCr, _hrp, _hrq, herror⟩ :=
    subcriticalTotalErrorNat_uniform_radius hk R₀ eta
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hdenK : 0 < 8 * (k : ℝ) + 16 := by positivity
  let alphaBound := min alphaMax (min (r / 4) (min (1 / 20) (1 / (8 * (k : ℝ) + 16))))
  have hab : 0 < alphaBound := by dsimp [alphaBound]; positivity
  let alpha := alphaBound / 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have habound : alpha ≤ alphaBound := by dsimp [alpha]; linarith
  have haBounds : alpha ≤ alphaMax ∧ alpha ≤ r / 4 ∧
      alpha ≤ 1 / 20 ∧ alpha ≤ 1 / (8 * (k : ℝ) + 16) := by
    simpa only [alphaBound, le_min_iff] using habound
  have haR : alpha ≤ r := by linarith [haBounds.2.1]
  have haSmall : 5 * alpha ≤ 1 / 2 := by linarith [haBounds.2.2.1]
  have haReloc : (4 * (k : ℝ) + 8) * alpha ≤ 1 := by
    have hh := (le_div_iff₀ hdenK).mp haBounds.2.2.2
    nlinarith only [hh]
  have htol := subcriticalRowCountingTolerance_pos hk
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  let deltaBound := min deltaMax (min r (min (1 / 2)
    (min (subcriticalRowCountingTolerance k / 2) (min (pK k / 12) ((1 - pK k) / 12)))))
  have hdb : 0 < deltaBound := by dsimp [deltaBound]; positivity
  let delta := deltaBound / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hdbound : delta ≤ deltaBound := by dsimp [delta]; linarith
  have hdBounds : delta ≤ deltaMax ∧ delta ≤ r ∧ delta ≤ 1 / 2 ∧
      delta ≤ subcriticalRowCountingTolerance k / 2 ∧
      delta ≤ pK k / 12 ∧ delta ≤ (1 - pK k) / 12 := by
    simpa only [deltaBound, le_min_iff] using hdbound
  let epsilonBound := min epsilonMax (min eta (min (theta ^ 2)
    (min (delta * epsilonSlope) (alpha ^ 2 * theta ^ 2 / 32))))
  have heb : 0 < epsilonBound := by dsimp [epsilonBound]; positivity
  let epsilon := epsilonBound / 2
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have hebound : epsilon ≤ epsilonBound := by dsimp [epsilon]; linarith
  have heBounds : epsilon ≤ epsilonMax ∧ epsilon ≤ eta ∧ epsilon ≤ theta ^ 2 ∧
      epsilon ≤ delta * epsilonSlope ∧ epsilon ≤ alpha ^ 2 * theta ^ 2 / 32 := by
    simpa only [epsilonBound, le_min_iff] using hebound
  refine ⟨alpha, ha, haBounds.1, delta, hd, hdBounds.1, epsilon, he, heBounds.1,
    le_min heBounds.2.1 heBounds.2.2.1, heBounds.2.2.2.1, ?_⟩
  have hfrac : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 4 := by
    unfold subcriticalProfileRootFraction
    apply (div_le_iff₀ (mul_pos ha htheta)).mpr
    have hh := heBounds.2.2.2.2
    nlinarith only [hh, mul_nonneg (sq_nonneg alpha) (sq_nonneg theta)]
  let xi := subcriticalTrimErrorNat (subcriticalProfileRootFraction alpha theta epsilon) theta
  have hxi0 : 0 ≤ xi := by
    dsimp [xi, subcriticalTrimErrorNat, subcriticalProfileRootFraction]
    positivity
  have hxiAlpha : xi ≤ alpha / 2 := by
    dsimp [xi, subcriticalTrimErrorNat]
    apply (div_le_iff₀ htheta).mpr
    linarith only [hfrac]
  have hxiR : xi ≤ r := by linarith only [hxiAlpha, haR, hr]
  have hxi1 : xi < 1 := by linarith only [hxiR, hr8]
  have hC : 0 ≤ subcriticalSmallOwnConstant k := by unfold subcriticalSmallOwnConstant; positivity
  have hCAlpha : subcriticalSmallOwnConstant k * alpha ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left haR hC).trans hCr
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
    have hm := mul_le_mul_of_nonneg_right hdBounds.2.2.1 ha.le
    linarith only [hm, haBounds.2.1, hzRound, hr]
  refine
    { star_order := hk
      retained_order := hR₀
      eta_pos := heta
      theta_pos := htheta
      alpha_pos := ha
      alpha_small := haSmall
      relocation_alpha := haReloc
      delta_nonneg := hd.le
      epsilon_nonneg := he.le
      retained_visible := hvisible
      relocation_theta := hrelocation
      row_counting := by linarith [hdBounds.2.2.2.1]
      density_lower := by linarith [hdBounds.2.2.2.2.1]
      density_upper := by linarith [hdBounds.2.2.2.2.2]
      root_fraction := hfrac
      entropy_band := hband
      row_scale := ?_
      sparse_scale := ?_
      source_scale := ?_
      zero_probability_reserve := by nlinarith only [hnZero, hnOne]
      total_error := herror alpha delta xi (subcriticalInsideScaleErrorNat alpha delta theta n)
        ⟨ha.le, haR⟩ ⟨hd.le, hdBounds.2.1⟩ ⟨hxi0, hxiR⟩ ⟨hz0, hzR⟩ }
  · simpa only [mul_comm] using (div_le_iff₀ (mul_pos ha htheta)).mp hnRow
  · simpa only [mul_comm] using (div_le_iff₀ htheta).mp hnSparse
  · simpa only [mul_comm] using (div_le_iff₀ heta).mp hnSource

end InducedStars
