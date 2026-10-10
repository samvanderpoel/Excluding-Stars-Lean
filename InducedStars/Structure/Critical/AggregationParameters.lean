import InducedStars.Structure.Critical.BinomialExpansion
import InducedStars.Structure.Supercritical.MatchingPenalty
import InducedStars.Structure.Supercritical.MediumPenalty

/-!
# Parameters for fixed-remainder counting at the critical density

The matching and medium-degree estimates apply at the endpoint `gammaK k`.
This module chooses their support-pattern and compact-density shift budgets
with an arbitrarily small positive upper bound on the division error.
-/

noncomputable section

open Filter Finset Set Topology

namespace InducedStars

/-- Entropy budget for support-incident defect patterns at the critical
density. -/
def criticalSupportPatternBudgetRate
    (k : ℕ) (alpha delta : ℝ) : ℝ :=
  8 * (k : ℝ) * (binaryEntropy (3 * alpha) + delta)

/-- An edge-count shift bound inside the compact density band used by the
fixed-remainder binomial comparison. -/
def criticalSignedShiftEpsilonBound (k : ℕ) : ℝ :=
  criticalDensityMargin k /
    (100 * (((k - 1 : ℕ) : ℝ) ^ 2))

theorem criticalSignedShiftEpsilonBound_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalSignedShiftEpsilonBound k := by
  unfold criticalSignedShiftEpsilonBound
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  positivity [criticalDensityMargin_pos hk]

/-- The exact critical density satisfies every closed density hypothesis used
by the supercritical matching, medium, and close-structure interfaces. -/
theorem criticalDensity_mem_Ico
    {k : ℕ} (hk : 3 ≤ k) :
    gammaK k ∈ Set.Ico (gammaK k) 1 :=
  ⟨le_rfl, gammaK_lt_one hk⟩

/-- Scalar data for the endpoint fixed-remainder estimate.

The equality fields identify each rate with its proved finite estimate.
The inequalities pay for support-pattern enumeration, signed edge-count
shifts, and medium-degree profile comparison. -/
structure CriticalAggregationParameters (k : ℕ) where
  rank : 3 ≤ k

  alpha : ℝ
  delta : ℝ
  epsilon : ℝ
  tau : ℝ

  cMat : ℝ
  cMed : ℝ
  cShift : ℝ

  alpha_pos : 0 < alpha
  alpha_lt : alpha < 1 / (100 * (k : ℝ))
  delta_pos : 0 < delta
  delta_lt_alpha : delta < alpha / 100
  epsilon_pos : 0 < epsilon
  tau_pos : 0 < tau

  rho_three_lower : 3 * delta < supercriticalOffDiagonal k (gammaK k)
  rho_three_upper :
    supercriticalOffDiagonal k (gammaK k) + 3 * delta < 1
  density_margin_delta : delta < criticalDensityMargin k / 16
  matching_delta :
    delta < supercriticalMatchingDeltaBound k (gammaK k) alpha

  cMat_eq : cMat = supercriticalMatchingPenaltyConstant k (gammaK k)
  cMed_eq : cMed = supercriticalMediumPenalty k (gammaK k) alpha
  cShift_eq : cShift = criticalShiftErrorConstant k

  cMat_pos : 0 < cMat
  cMed_pos : 0 < cMed
  cShift_pos : 0 < cShift

  support_overhead_small :
    criticalSupportPatternBudgetRate k alpha delta < cMat / 4
  support_shift_small :
    cShift * (8 * (k : ℝ) * (alpha + delta)) < cMat / 4
  epsilon_pattern_small : 3 * epsilon < 1 / 2
  medium_shift_small : cShift * epsilon < cMed / 4

  medium_janson_range :
    2 * delta < min (supercriticalOffDiagonal k (gammaK k))
      (1 - supercriticalOffDiagonal k (gammaK k)) / 2
  medium_profile_lower :
    0 < supercriticalOffDiagonal k (gammaK k) - 2 * delta
  medium_profile_upper :
    supercriticalOffDiagonal k (gammaK k) + 2 * delta < 1
  medium_candidate_delta :
    delta < supercriticalMediumCandidateDeltaBound k
  medium_candidate_epsilon :
    epsilon < supercriticalMediumCandidateRate k alpha / 2
  signed_shift_epsilon :
    epsilon < criticalSignedShiftEpsilonBound k
  medium_defect_rate :
    supercriticalDefectPatternRate epsilon <
      supercriticalMediumBernoulliPenalty k (gammaK k)
        (supercriticalMediumCandidateRate k alpha) / 16
  medium_profile_rate :
    supercriticalMediumProfileComparisonRate k
        (supercriticalOffDiagonal k (gammaK k)) delta <
      supercriticalMediumBernoulliPenalty k (gammaK k)
        (supercriticalMediumCandidateRate k alpha) / 16

  tau_eq : tau = supercriticalCloseStructureCutRadius k rank (gammaK k)
    (criticalDensity_mem_Ico rank) alpha ⟨alpha_pos, alpha_lt⟩
      delta delta_pos delta_lt_alpha rho_three_lower rho_three_upper
        epsilon epsilon_pos

namespace CriticalAggregationParameters

variable {k : ℕ}

theorem alpha_mem_Ioo (P : CriticalAggregationParameters k) :
    P.alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * (k : ℝ))) :=
  ⟨P.alpha_pos, P.alpha_lt⟩

end CriticalAggregationParameters

/-! ## Existence at the exact critical density -/

set_option maxHeartbeats 800000 in
-- The explicit nested minimum hierarchy and its nonlinear rate arithmetic
-- require more elaboration work than the default heartbeat budget.
/-- Choose endpoint fixed-remainder parameters below any prescribed
positive division-error bound. -/
theorem exists_criticalAggregationParameters
    (k : ℕ) (hk : 3 ≤ k) (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ P : CriticalAggregationParameters k, P.delta < ξ := by
  let hgamma : gammaK k ∈ Set.Ico (gammaK k) 1 :=
    criticalDensity_mem_Ico hk
  let cMat := supercriticalMatchingPenaltyConstant k (gammaK k)
  let cShift := criticalShiftErrorConstant k
  have hkReal : (0 : ℝ) < k := by
    exact_mod_cast (show 0 < k by omega)
  have hcMat : 0 < cMat := by
    exact supercriticalMatchingPenaltyConstant_pos hk hgamma
  have hcShift : 0 < cShift := by
    exact criticalShiftErrorConstant_pos hk
  have hsignedShift : 0 < criticalSignedShiftEpsilonBound k :=
    criticalSignedShiftEpsilonBound_pos hk

  let alphaRateTarget := cMat * Real.log 2 / (64 * (k : ℝ))
  have halphaRateTarget : 0 < alphaRateTarget := by
    dsimp [alphaRateTarget]
    positivity
  obtain ⟨alphaEntropy, halphaEntropy, halphaEntropySpec⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt halphaRateTarget
  let alphaBound := min alphaEntropy
    (min (1 / (100 * (k : ℝ)))
      (cMat / (64 * (k : ℝ) * cShift)))
  have halphaBound : 0 < alphaBound := by
    dsimp [alphaBound]
    exact lt_min halphaEntropy
      (lt_min (by positivity) (by positivity))
  let alpha := alphaBound / 2
  have halpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  have halphaLtBound : alpha < alphaBound := by
    dsimp [alpha]
    linarith
  have halphaLtEntropy : alpha < alphaEntropy :=
    halphaLtBound.trans_le (by
      dsimp [alphaBound]
      exact min_le_left _ _)
  have halphaLtRange : alpha < 1 / (100 * (k : ℝ)) :=
    halphaLtBound.trans_le (by
      dsimp [alphaBound]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have halphaLtShift :
      alpha < cMat / (64 * (k : ℝ) * cShift) :=
    halphaLtBound.trans_le (by
      dsimp [alphaBound]
      exact (min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_halphaThree, halphaEntropyRate⟩ :=
    halphaEntropySpec halpha halphaLtEntropy
  have hHplus :
      binaryEntropy (3 * alpha) + alpha <
        cMat / (64 * (k : ℝ)) := by
    apply lt_of_mul_lt_mul_right (α := ℝ) ?_ realLogTwo_pos.le
    calc
      (binaryEntropy (3 * alpha) + alpha) * Real.log 2 =
          supercriticalDefectPatternRate alpha := by rfl
      _ < alphaRateTarget := halphaEntropyRate
      _ = (cMat / (64 * (k : ℝ))) * Real.log 2 := by
        dsimp [alphaRateTarget]
        ring
  have hSupportAlpha :
      8 * (k : ℝ) * binaryEntropy (3 * alpha) < cMat / 8 := by
    have hHnonneg : 0 ≤ binaryEntropy (3 * alpha) :=
      binaryEntropy_nonneg (by positivity) (by
        have := _halphaThree
        linarith)
    have hH : binaryEntropy (3 * alpha) <
        cMat / (64 * (k : ℝ)) :=
      lt_of_le_of_lt (by linarith) hHplus
    have hscale : 0 < (8 : ℝ) * (k : ℝ) := by positivity
    have hmul := mul_lt_mul_of_pos_left hH hscale
    calc
      8 * (k : ℝ) * binaryEntropy (3 * alpha) <
          8 * (k : ℝ) * (cMat / (64 * (k : ℝ))) := by
        simpa [mul_assoc] using hmul
      _ = cMat / 8 := by (field_simp; norm_num)
  have hShiftAlpha :
      cShift * (8 * (k : ℝ) * alpha) < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) * cShift := by positivity
    have hmul := mul_lt_mul_of_pos_left halphaLtShift hscale
    calc
      cShift * (8 * (k : ℝ) * alpha) <
          (8 * (k : ℝ) * cShift) *
            (cMat / (64 * (k : ℝ) * cShift)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = cMat / 8 := by (field_simp; norm_num)

  let candidateRate := supercriticalMediumCandidateRate k alpha
  let bernoulliPenalty :=
    supercriticalMediumBernoulliPenalty k (gammaK k) candidateRate
  let cMed := supercriticalMediumPenalty k (gammaK k) alpha
  have hcandidateRate : 0 < candidateRate := by
    exact supercriticalMediumCandidateRate_pos hk halpha
  have hbernoulliPenalty : 0 < bernoulliPenalty := by
    exact supercriticalMediumBernoulliPenalty_pos hk hgamma hcandidateRate
  have hcMed : 0 < cMed := by
    exact supercriticalMediumPenalty_pos hk hgamma halpha
  obtain ⟨deltaMedium, hdeltaMedium, hdeltaMediumSpec⟩ :=
    exists_supercriticalMediumDelta0 hk hgamma halpha hbernoulliPenalty

  let rho := supercriticalOffDiagonal k (gammaK k)
  have hrho : 0 < rho := by
    exact supercriticalOffDiagonal_pos hk hgamma.1
  have hrhoOne : rho < 1 := by
    exact supercriticalOffDiagonal_lt_one hk hgamma.2
  have hmatchingDelta :
      0 < supercriticalMatchingDeltaBound k (gammaK k) alpha :=
    supercriticalMatchingDeltaBound_pos hk hgamma halpha
  have hradius : 0 < min ξ (criticalDensityMargin k / 16) :=
    lt_min hξ (div_pos (criticalDensityMargin_pos hk) (by norm_num))
  let deltaBound := min deltaMedium
    (min (alpha / 100)
      (min (supercriticalMatchingDeltaBound k (gammaK k) alpha)
        (min (min ξ (criticalDensityMargin k / 16))
          (min (rho / 3)
            (min ((1 - rho) / 3)
              (min (cMat / (64 * (k : ℝ)))
                (cMat / (64 * (k : ℝ) * cShift))))))))
  have hdeltaBound : 0 < deltaBound := by
    dsimp [deltaBound]
    exact lt_min hdeltaMedium
      (lt_min (by positivity)
        (lt_min hmatchingDelta
          (lt_min hradius
            (lt_min (by positivity)
              (lt_min (by positivity)
                (lt_min (by positivity) (by positivity)))))))
  let delta := deltaBound / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaLtBound : delta < deltaBound := by
    dsimp [delta]
    linarith
  have hdeltaSpecs :
      delta < deltaMedium ∧
      delta < alpha / 100 ∧
      delta < supercriticalMatchingDeltaBound k (gammaK k) alpha ∧
      delta < min ξ (criticalDensityMargin k / 16) ∧
      delta < rho / 3 ∧
      delta < (1 - rho) / 3 ∧
      delta < cMat / (64 * (k : ℝ)) ∧
      delta < cMat / (64 * (k : ℝ) * cShift) := by
    have h := hdeltaLtBound
    dsimp [deltaBound] at h
    simpa only [lt_min_iff] using h
  obtain ⟨_hdeltaAlphaMedium, hJansonRange, _hrhoThreeMedium,
      _hrhoUpperThreeMedium, hprofileLower, hprofileUpper,
      hdeltaCandidate, hprofileRate⟩ :=
    hdeltaMediumSpec hdelta hdeltaSpecs.1
  have hrhoLower :
      3 * delta < supercriticalOffDiagonal k (gammaK k) := by
    change 3 * delta < rho
    linarith [hdeltaSpecs.2.2.2.2.1]
  have hrhoUpper :
      supercriticalOffDiagonal k (gammaK k) + 3 * delta < 1 := by
    change rho + 3 * delta < 1
    linarith [hdeltaSpecs.2.2.2.2.2.1]
  have hSupportDelta :
      8 * (k : ℝ) * delta < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) := by positivity
    have hmul := mul_lt_mul_of_pos_left
      hdeltaSpecs.2.2.2.2.2.2.1 hscale
    calc
      8 * (k : ℝ) * delta <
          8 * (k : ℝ) * (cMat / (64 * (k : ℝ))) := by
        simpa [mul_assoc] using hmul
      _ = cMat / 8 := by (field_simp; norm_num)
  have hShiftDelta :
      cShift * (8 * (k : ℝ) * delta) < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) * cShift := by positivity
    have hmul := mul_lt_mul_of_pos_left
      hdeltaSpecs.2.2.2.2.2.2.2 hscale
    calc
      cShift * (8 * (k : ℝ) * delta) <
          (8 * (k : ℝ) * cShift) *
            (cMat / (64 * (k : ℝ) * cShift)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = cMat / 8 := by (field_simp; norm_num)
  have hSupportBudget :
      criticalSupportPatternBudgetRate k alpha delta < cMat / 4 := by
    dsimp [criticalSupportPatternBudgetRate]
    nlinarith [hSupportAlpha, hSupportDelta]
  have hShiftBudget :
      cShift * (8 * (k : ℝ) * (alpha + delta)) < cMat / 4 := by
    nlinarith [hShiftAlpha, hShiftDelta]
  obtain ⟨epsilonDefect, hepsilonDefect, hepsilonDefectSpec⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt
      (show 0 < bernoulliPenalty / 16 by positivity)
  let epsilonBound := min epsilonDefect
    (min (candidateRate / 2)
      (min (cMed / (4 * cShift))
        (criticalSignedShiftEpsilonBound k)))
  have hepsilonBound : 0 < epsilonBound := by
    dsimp [epsilonBound]
    exact lt_min hepsilonDefect
      (lt_min (half_pos hcandidateRate)
        (lt_min (by positivity) hsignedShift))
  let epsilon := epsilonBound / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hepsilonLt : epsilon < epsilonBound := by
    dsimp [epsilon]
    linarith
  have hepsilonDefect' : epsilon < epsilonDefect :=
    hepsilonLt.trans_le (by
      dsimp [epsilonBound]
      exact min_le_left _ _)
  have hepsilonCandidate : epsilon < candidateRate / 2 :=
    hepsilonLt.trans_le (by
      dsimp [epsilonBound]
      exact (min_le_right _ _).trans (min_le_left _ _))
  have hepsilonShift : epsilon < cMed / (4 * cShift) :=
    hepsilonLt.trans_le (by
      dsimp [epsilonBound]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _))
  have hepsilonSigned :
      epsilon < criticalSignedShiftEpsilonBound k :=
    hepsilonLt.trans_le (by
      dsimp [epsilonBound]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hepsilonPattern, hdefectRate⟩ :=
    hepsilonDefectSpec hepsilon hepsilonDefect'
  have hMediumShift : cShift * epsilon < cMed / 4 := by
    have h := mul_lt_mul_of_pos_left hepsilonShift hcShift
    calc
      cShift * epsilon < cShift * (cMed / (4 * cShift)) := h
      _ = cMed / 4 := by field_simp

  let halphaIoo : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))) := ⟨halpha, halphaLtRange⟩
  let tau := supercriticalCloseStructureCutRadius k hk (gammaK k) hgamma
    alpha halphaIoo delta hdelta hdeltaSpecs.2.1 hrhoLower hrhoUpper
      epsilon hepsilon
  have htau : 0 < tau := by
    exact supercriticalCloseStructureCutRadius_pos k hk (gammaK k) hgamma
      alpha halphaIoo delta hdelta hdeltaSpecs.2.1 hrhoLower hrhoUpper
        epsilon hepsilon

  exact ⟨{
    rank := hk
    alpha := alpha
    delta := delta
    epsilon := epsilon
    tau := tau
    cMat := cMat
    cMed := cMed
    cShift := cShift
    alpha_pos := halpha
    alpha_lt := halphaLtRange
    delta_pos := hdelta
    delta_lt_alpha := hdeltaSpecs.2.1
    epsilon_pos := hepsilon
    tau_pos := htau
    rho_three_lower := hrhoLower
    rho_three_upper := hrhoUpper
    matching_delta := hdeltaSpecs.2.2.1
    density_margin_delta := hdeltaSpecs.2.2.2.1.trans_le (min_le_right _ _)
    cMat_eq := rfl
    cMed_eq := rfl
    cShift_eq := rfl
    cMat_pos := hcMat
    cMed_pos := hcMed
    cShift_pos := hcShift
    support_overhead_small := hSupportBudget
    support_shift_small := hShiftBudget
    epsilon_pattern_small := hepsilonPattern
    medium_shift_small := hMediumShift
    medium_janson_range := hJansonRange
    medium_profile_lower := hprofileLower
    medium_profile_upper := hprofileUpper
    medium_candidate_delta := hdeltaCandidate
    medium_candidate_epsilon := by
      simpa [candidateRate] using hepsilonCandidate
    signed_shift_epsilon := hepsilonSigned
    medium_defect_rate := by
      simpa [bernoulliPenalty, candidateRate] using hdefectRate
    medium_profile_rate := by
      simpa [bernoulliPenalty, candidateRate] using hprofileRate
    tau_eq := rfl
  }, hdeltaSpecs.2.2.2.1.trans_le (min_le_left _ _)⟩

end InducedStars
