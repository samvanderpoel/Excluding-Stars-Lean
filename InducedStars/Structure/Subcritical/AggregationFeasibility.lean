import InducedStars.Structure.Subcritical.AggregationProfileError
import InducedStars.Structure.Subcritical.AggregationLocalConditions

/-!
# A single nested feasible aggregation hierarchy

The residual hierarchy selects the actual tuple. Its successive caps enforce
all local-compensation, profile-counting and headroom reserves at the same
time. No separately selected tuple is intersected coordinatewise afterward.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InducedStars

/-- Outer parameters can satisfy arbitrary earlier eta caps and retained-order
lower bounds. This works throughout the whole positive-density regime. -/
theorem exists_subcriticalAggregationOuterParameters
    (k : ℕ) {gamma omega etaMax : ℝ} (hgamma : 0 < gamma)
    (homega : 0 < omega) (hetaMax : 0 < etaMax) (Rmin : ℕ) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ etaMax ∧ eta ≤ omega ∧ eta ≤ 1 ∧
      subcriticalSparseSideConstant k * eta ≤ gamma / 32 ∧
      ∃ R₀ : ℕ, 1 ≤ R₀ ∧ Rmin ≤ R₀ ∧ 1 / (R₀ : ℝ) ≤ eta := by
  have hC : 0 ≤ subcriticalSparseSideConstant k := by
    unfold subcriticalSparseSideConstant
    positivity
  let b := min etaMax (min omega (min 1 (gamma / (64 * (subcriticalSparseSideConstant k + 1)))))
  have hb : 0 < b := by dsimp [b]; positivity
  let eta := b / 2
  have he : 0 < eta := by dsimp [eta]; positivity
  have heb : eta ≤ b := by dsimp [eta]; linarith
  have hs : eta ≤ etaMax ∧ eta ≤ omega ∧ eta ≤ 1 ∧
      eta ≤ gamma / (64 * (subcriticalSparseSideConstant k + 1)) := by
    simpa only [b, le_min_iff] using heb
  have hbudget : subcriticalSparseSideConstant k * eta ≤ gamma / 32 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 64 * (subcriticalSparseSideConstant k + 1))).mp hs.2.2.2
    nlinarith only [hh, he, hgamma]
  let R₀ := max Rmin (Nat.ceil (1 / eta) + 1)
  have hR : 1 ≤ R₀ := le_trans (by omega) (Nat.le_max_right _ _)
  have hRreal : 1 / eta ≤ (R₀ : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (show Nat.ceil (1 / eta) ≤ R₀ from
      le_trans (Nat.le_succ _) (Nat.le_max_right _ _)))
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  refine ⟨eta, he, hs.1, hs.2.1, hs.2.2.1, hbudget, R₀, hR, Nat.le_max_left _ _, ?_⟩
  apply (div_le_iff₀ hRpos).mpr
  have hh := (div_le_iff₀ he).mp hRreal
  nlinarith only [hh]

set_option maxHeartbeats 1200000 in
/-- Simultaneous arbitrary-cap feasibility. The fixed root and matching rates
precede theta. The alpha cap is received only after theta, and similarly for
delta and epsilon. Only the graph-order thresholds are combined at the end. -/
theorem exists_subcriticalAggregationParameters
    {k R₀ : ℕ} {gamma eta : ℝ}
    (hk : 3 ≤ k) (hgamma : 0 < gamma) (heta : 0 < eta) (hR : 1 ≤ R₀)
    (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (hetaReserve : subcriticalSparseSideConstant k * eta ≤ gamma / 32)
    (thetaMax : ℝ) (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∀ alphaMax : ℝ, 0 < alphaMax →
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
        ∀ deltaMax : ℝ, 0 < deltaMax →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧
          ∀ epsilonMax : ℝ, 0 < epsilonMax →
          ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧
            ∀ᶠ n : ℕ in atTop,
              SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hRpos : (0 : ℝ) < R₀ := by exact_mod_cast (show 0 < R₀ by omega)
  have hkap : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
    have hh := subcriticalResidualMatchingKappa_pos heta hR
    exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ by omega)
  have hMat := subcriticalResidualMatchingConstant_pos hk heta hR
  let c := subcriticalResidualMatchingConstant k eta R₀ /
    (subcriticalResidualMatchingKappa eta R₀ : ℝ)
  have hc : 0 < c := div_pos hMat hkap
  let a := subcriticalAggregationRootRate k eta R₀
  have haRate : 0 < a := subcriticalAggregationRootRate_pos hk heta hR
  let C := subcriticalProfileErrorConstant k R₀
  have hC : 0 < C := subcriticalProfileErrorConstant_pos k R₀
  let e := a / (32 * C)
  have he : 0 < e := by dsimp [e]; positivity
  let w := subcriticalResidualMatchingConstant k eta R₀ /
    (32 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)^2)
  have hw : 0 < w := by dsimp [w]; positivity
  obtain ⟨r, hr, hr8, hCr, _hrp, _hrq, herror⟩ :=
    subcriticalTotalErrorNat_uniform_radius hk R₀ eta
  obtain ⟨rEntropy, hrEntropy, hEntropy⟩ :=
    exists_subcriticalProfileEntropyRadius (lt_min he hw)
  let thetaCap := min thetaMax (min e (min w
    (min (eta / (2 * (R₀ : ℝ))) ((eta / (2 * (R₀ : ℝ))) / (20 * (k : ℝ))))))
  have htCap : 0 < thetaCap := by dsimp [thetaCap]; positivity
  obtain ⟨theta, ht, htBound, hAlpha⟩ := exists_subcriticalResidualParameterHierarchy k c
    (subcriticalResidualDegreeCap k eta R₀) (subcriticalResidualMatchingLambda eta R₀)
    (subcriticalPaletteGap k) thetaCap hc (subcriticalResidualDegreeCap_pos k heta hR)
    (subcriticalResidualMatchingLambda_pos heta hR) (subcriticalPaletteGap_pos hk) htCap
  have htBounds : theta ≤ thetaMax ∧ theta ≤ e ∧ theta ≤ w ∧
      theta ≤ eta / (2 * (R₀ : ℝ)) ∧
      theta ≤ (eta / (2 * (R₀ : ℝ))) / (20 * (k : ℝ)) := by
    simpa only [thetaCap, le_min_iff] using htBound
  have hreloc : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)) := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * k)).mp htBounds.2.2.2.2
  refine ⟨theta, ht, htBounds.1, ?_⟩
  intro alphaMax haMax
  let alphaCap := min alphaMax (min (r / 4) (min (1 / 20)
    (min (1 / (8 * (k : ℝ) + 16)) (min rEntropy (theta / (100 * (k : ℝ)))))))
  have haCap : 0 < alphaCap := by dsimp [alphaCap]; positivity
  obtain ⟨alpha, ha, haBound, hDegree, _hCost, hDelta⟩ := hAlpha alphaCap haCap
  have haBounds : alpha ≤ alphaMax ∧ alpha ≤ r / 4 ∧ alpha ≤ 1 / 20 ∧
      alpha ≤ 1 / (8 * (k : ℝ) + 16) ∧ alpha ≤ rEntropy ∧
      alpha ≤ theta / (100 * (k : ℝ)) := by
    simpa only [alphaCap, le_min_iff] using haBound
  have hEnt : binaryEntropy (5 * alpha) ≤ min e w := hEntropy alpha ⟨ha.le, haBounds.2.2.2.2.1⟩
  refine ⟨alpha, ha, haBounds.1, ?_⟩
  intro deltaMax hdMax
  have hTol := subcriticalRowCountingTolerance_pos hk
  have hp := pK_pos (show 2 ≤ k by omega)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (show 2 ≤ k by omega))
  let deltaCap := min deltaMax (min e (min r (min (1 / 2)
    (min (subcriticalRowCountingTolerance k / 2) (min (pK k / 12) ((1 - pK k) / 12))))))
  have hdCap : 0 < deltaCap := by dsimp [deltaCap]; positivity
  obtain ⟨delta, hd, hdBound, hdPalette, hEpsilon⟩ := hDelta deltaCap hdCap
  have hdBounds : delta ≤ deltaMax ∧ delta ≤ e ∧ delta ≤ r ∧ delta ≤ 1 / 2 ∧
      delta ≤ subcriticalRowCountingTolerance k / 2 ∧
      delta ≤ pK k / 12 ∧ delta ≤ (1 - pK k) / 12 := by
    simpa only [deltaCap, le_min_iff] using hdBound
  refine ⟨delta, hd, hdBounds.1, ?_⟩
  intro epsilonMax heMax
  let epsilonCap := min epsilonMax (min eta (min (gamma / 32)
    (min (delta * gamma / 192) (min (alpha ^ 2 * theta ^ 2 / 32)
      (e * alpha * theta / 2)))))
  have heCap : 0 < epsilonCap := by dsimp [epsilonCap]; positivity
  obtain ⟨epsilon, hepsilon, heBound, heTheta, heRoots, hnResidual⟩ :=
    hEpsilon epsilonCap heCap
  have heBounds : epsilon ≤ epsilonMax ∧ epsilon ≤ eta ∧ epsilon ≤ gamma / 32 ∧
      epsilon ≤ delta * gamma / 192 ∧ epsilon ≤ alpha ^ 2 * theta ^ 2 / 32 ∧
      epsilon ≤ e * alpha * theta / 2 := by
    simpa only [epsilonCap, le_min_iff] using heBound
  have hfrac : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 4 := by
    unfold subcriticalProfileRootFraction
    apply (div_le_iff₀ (mul_pos ha ht)).mpr
    nlinarith only [heBounds.2.2.2.2.1, mul_nonneg (sq_nonneg alpha) (sq_nonneg theta)]
  have hfracE : subcriticalProfileRootFraction alpha theta epsilon ≤ e := by
    unfold subcriticalProfileRootFraction
    apply (div_le_iff₀ (mul_pos ha ht)).mpr
    nlinarith only [heBounds.2.2.2.2.2]
  have hbase : C * (binaryEntropy (5 * alpha) + theta + delta +
      subcriticalProfileRootFraction alpha theta epsilon) ≤ a / 8 := by
    have hsum : binaryEntropy (5 * alpha) + theta + delta +
        subcriticalProfileRootFraction alpha theta epsilon ≤ 4 * e := by
      linarith only [(le_min_iff.mp hEnt).1, htBounds.2.1, hdBounds.2.1, hfracE]
    have hh := mul_le_mul_of_nonneg_left hsum hC.le
    have heq : C * (4 * e) = a / 8 := by dsimp [e]; field_simp [ne_of_gt hC]; ring
    exact hh.trans_eq heq
  have hmatchingEntropy : binaryEntropy (5 * alpha) + theta ≤
      subcriticalResidualMatchingConstant k eta R₀ /
        (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)^2) := by
    have hh : binaryEntropy (5 * alpha) + theta ≤ 2 * w := by
      simpa only [two_mul] using add_le_add (le_min_iff.mp hEnt).2 htBounds.2.2.1
    calc
      _ ≤ 2 * w := hh
      _ ≤ 4 * w := by linarith only [hw]
      _ = _ := by dsimp [w]; ring
  have hnLocal := eventually_subcriticalLocalPenaltyParameters_of_bounds hk hR heta ht ha
    hd.le hepsilon.le hr hr8 hCr herror htBounds.2.2.2.1 hreloc
    haBounds.2.1 haBounds.2.2.1 haBounds.2.2.2.1
    hdBounds.2.2.1 hdBounds.2.2.2.1 hdBounds.2.2.2.2.1
    hdBounds.2.2.2.2.2.1 hdBounds.2.2.2.2.2.2 hfrac
  have hnLog := eventually_subcritical_log_overhead_le C (a / 8) (by positivity)
  refine ⟨epsilon, hepsilon, heBounds.1, ?_⟩
  filter_upwards [hnLocal, hnResidual, hnLog, eventually_ge_atTop (2 : ℕ),
    eventually_ge_atTop (subcriticalActiveRoundingThreshold delta theta)] with n hlocal hres hlog hn hround
  refine
    { localConditions := hlocal
      residual := {
        alpha_pos := ha
        theta_pos := ht
        delta_pos := hd
        epsilon_pos := hepsilon
        theta_cutoff := htBounds.2.2.2.1
        degree_half := (le_min_iff.mp hDegree).1
        degree_cap := (le_min_iff.mp hDegree).2
        delta_palette := hdPalette
        epsilon_theta := heTheta
        roots_room := heRoots
        enumeration_error := ?_
        matching_room := hres.2.1
        sparse_scale := hres.2.2.1
        fallback_order := hres.2.2.2.1
        order_pos := hres.2.2.2.2 }
      gamma_pos := hgamma
      retained_inverse := hinv
      alpha_theta := haBounds.2.2.2.2.2
      matching_entropy := hmatchingEntropy
      epsilon_cap := le_min heBounds.2.1 heTheta
      density_headroom := by linarith only [hetaReserve, heBounds.2.2.1]
      shift_headroom := heBounds.2.2.2.1
      profile_error_base := hbase
      profile_error_log := hlog
      profile_order := hn
      active_rounding := hround }
  convert hres.1 using 1 <;> dsimp [c] <;> ring

end InducedStars
