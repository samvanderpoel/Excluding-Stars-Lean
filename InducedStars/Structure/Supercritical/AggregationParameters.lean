import InducedStars.Structure.Supercritical.MatchingPenalty
import InducedStars.Structure.Supercritical.MediumPenalty
import InducedStars.Structure.Supercritical.JointAbsorption

/-!
# Parameters for the strictly supercritical aggregation

This module records, in one transparent object, the scalar hierarchy used by
the final finite aggregation.  The fields are deliberately inequalities, not
an opaque "sufficiently small" predicate.  In particular, the linear
support-shift and quadratic medium-shift costs are paid explicitly before any
eventual threshold is chosen.
-/

noncomputable section

set_option maxHeartbeats 800000

open Set

namespace InducedStars

/-- A coarse explicit rate which budgets the entropy of support-incident
defect patterns.  The later counting theorem may use a smaller rate; this
one is useful because its dependence on `alpha` and `delta` is visible. -/
def supercriticalSupportPatternBudgetRate
    (k : ℕ) (alpha delta : ℝ) : ℝ :=
  8 * (k : ℝ) * (binaryEntropy (3 * alpha) + delta)

/-- A uniform signed-shift budget leaving room both below the off-diagonal
density and below density one.  This is the finite margin needed when a
canonical defect shift of size at most `epsilon * n^2` is inserted into the
repaired joint-absorption comparison. -/
def supercriticalSignedShiftEpsilonBound
    (k : ℕ) (gamma : ℝ) : ℝ :=
  min
    ((supercriticalOffDiagonal k gamma -
        supercriticalAbsorptionLowerDensity k gamma) /
      (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))
    ((1 - supercriticalOffDiagonal k gamma) /
      (100 * (((k - 1 : ℕ) : ℝ) ^ 2)))

/-- Common scalar data for the final strictly supercritical aggregation.

The constants are tied definitionally, through the four equality fields, to
the locally proved matching, medium, and repaired joint-absorption rates.
The remaining fields are precisely the open conditions needed to synchronize
close structure and to absorb the two shift/entropy overheads. -/
structure SupercriticalAggregationParameters
    (k : ℕ) (gamma : ℝ) where
  rank : 3 ≤ k
  density_mem : gamma ∈ Set.Ico (gammaK k) 1

  alpha : ℝ
  delta : ℝ
  epsilon : ℝ
  tau : ℝ

  cMat : ℝ
  cMed : ℝ
  cAbs : ℝ
  cShift : ℝ

  alpha_pos : 0 < alpha
  alpha_lt : alpha < 1 / (100 * (k : ℝ))
  delta_pos : 0 < delta
  delta_lt_alpha : delta < alpha / 100
  epsilon_pos : 0 < epsilon
  tau_pos : 0 < tau

  rho_three_lower : 3 * delta < supercriticalOffDiagonal k gamma
  rho_three_upper : supercriticalOffDiagonal k gamma + 3 * delta < 1
  matching_delta : delta < supercriticalMatchingDeltaBound k gamma alpha
  joint_absorption_delta :
    delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma

  cMat_eq : cMat = supercriticalMatchingPenaltyConstant k gamma
  cMed_eq : cMed = supercriticalMediumPenalty k gamma alpha
  cAbs_eq : cAbs = supercriticalJointAbsorptionPenalty k gamma
  cShift_eq : cShift = supercriticalJointShiftConstant k gamma

  cMat_pos : 0 < cMat
  cMed_pos : 0 < cMed
  cAbs_pos : 0 < cAbs
  cShift_pos : 0 < cShift

  support_overhead_small :
    supercriticalSupportPatternBudgetRate k alpha delta < cMat / 4
  support_shift_small :
    cShift * (8 * (k : ℝ) * (alpha + delta)) < cMat / 4
  epsilon_pattern_small : 3 * epsilon < 1 / 2
  medium_shift_small : cShift * epsilon < cMed / 4

  medium_janson_range :
    2 * delta < min (supercriticalOffDiagonal k gamma)
      (1 - supercriticalOffDiagonal k gamma) / 2
  medium_profile_lower :
    0 < supercriticalOffDiagonal k gamma - 2 * delta
  medium_profile_upper :
    supercriticalOffDiagonal k gamma + 2 * delta < 1
  medium_candidate_delta :
    delta < supercriticalMediumCandidateDeltaBound k
  medium_candidate_epsilon :
    epsilon < supercriticalMediumCandidateRate k alpha / 2
  signed_shift_epsilon :
    epsilon < supercriticalSignedShiftEpsilonBound k gamma
  support_signed_shift :
    2 * (alpha + delta) < supercriticalSignedShiftEpsilonBound k gamma
  medium_defect_rate :
    supercriticalDefectPatternRate epsilon <
      supercriticalMediumBernoulliPenalty k gamma
        (supercriticalMediumCandidateRate k alpha) / 16
  medium_profile_rate :
    supercriticalMediumProfileComparisonRate k
        (supercriticalOffDiagonal k gamma) delta <
      supercriticalMediumBernoulliPenalty k gamma
        (supercriticalMediumCandidateRate k alpha) / 16

  tau_eq : tau = supercriticalCloseStructureCutRadius k rank gamma density_mem
    alpha ⟨alpha_pos, alpha_lt⟩ delta delta_pos delta_lt_alpha
      rho_three_lower rho_three_upper epsilon epsilon_pos

namespace SupercriticalAggregationParameters

variable {k : ℕ} {gamma : ℝ}

/-- The admissible interval required by both `superFPiT` and
`superFPiPrime`. -/
theorem alpha_mem_Ioo (P : SupercriticalAggregationParameters k gamma) :
    P.alpha ∈ Set.Ioo (0 : ℝ) (1 / (100 * (k : ℝ))) :=
  ⟨P.alpha_pos, P.alpha_lt⟩

/-- The strict repaired joint-absorption tolerance also supplies the weak
tolerance used by the shifted comparison. -/
theorem delta_le_jointAbsorptionBound
    (P : SupercriticalAggregationParameters k gamma) :
    P.delta ≤ supercriticalJointAbsorptionDeltaBound k gamma :=
  P.joint_absorption_delta.le.trans
    (supercriticalJointAbsorptionGeometryDeltaBound_le_scalar k gamma)

/-- Positive linear rate left after reserving half of both the matching and
joint-absorption penalties. -/
def linearRate (P : SupercriticalAggregationParameters k gamma) : ℝ :=
  min (P.cMat / 2) (P.cAbs / 2)

theorem linearRate_pos (P : SupercriticalAggregationParameters k gamma) :
    0 < P.linearRate := by
  exact lt_min (half_pos P.cMat_pos) (half_pos P.cAbs_pos)

/-- Positive quadratic rate left after paying the medium shifted-profile
budget. -/
def mediumRate (P : SupercriticalAggregationParameters k gamma) : ℝ :=
  P.cMed / 2

theorem mediumRate_pos (P : SupercriticalAggregationParameters k gamma) :
    0 < P.mediumRate := half_pos P.cMed_pos

/-- The stored medium-shift inequality leaves at least three quarters of the
raw medium penalty. -/
theorem medium_shift_sub_pos
    (P : SupercriticalAggregationParameters k gamma) :
    0 < 3 * P.cMed / 4 - P.cShift * P.epsilon := by
  linarith [P.medium_shift_small, P.cMed_pos]

end SupercriticalAggregationParameters

/-! ## Existence in the strict supercritical regime -/

/-- The transparent aggregation package is inhabited at every strictly
supercritical density.  The proof follows the required order: first the
matching rate and `alpha`, then all `delta` tolerances, then the medium rate
and `epsilon`, and finally the synchronized close-structure radius. -/
theorem exists_supercriticalAggregationParameters
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    Nonempty (SupercriticalAggregationParameters k gamma) := by
  let hgammaIco : gamma ∈ Set.Ico (gammaK k) 1 :=
    ⟨hgamma.1.le, hgamma.2⟩
  let cMat := supercriticalMatchingPenaltyConstant k gamma
  let cAbs := supercriticalJointAbsorptionPenalty k gamma
  let cShift := supercriticalJointShiftConstant k gamma
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcMat : 0 < cMat := by
    exact supercriticalMatchingPenaltyConstant_pos hk hgammaIco
  have hcAbs : 0 < cAbs := by
    exact supercriticalJointAbsorptionPenalty_pos hk hgamma
  have hcShift : 0 < cShift := by
    exact supercriticalJointShiftConstant_pos hk hgamma
  have hsignedShift :
      0 < supercriticalSignedShiftEpsilonBound k gamma := by
    have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < k - 1)
    have hlambda :
        supercriticalAbsorptionLowerDensity k gamma <
          supercriticalOffDiagonal k gamma :=
      supercriticalAbsorptionLowerDensity_lt_rho hk hgamma
    have hrhoOne : supercriticalOffDiagonal k gamma < 1 :=
      supercriticalOffDiagonal_lt_one hk hgamma.2
    dsimp [supercriticalSignedShiftEpsilonBound]
    exact lt_min (by positivity) (by positivity)

  let alphaRateTarget := cMat * Real.log 2 / (64 * (k : ℝ))
  have halphaRateTarget : 0 < alphaRateTarget := by
    dsimp [alphaRateTarget]
    positivity
  obtain ⟨alphaEntropy, halphaEntropy,
      halphaEntropySpec⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt
      halphaRateTarget
  let alphaBound := min alphaEntropy
    (min (1 / (100 * (k : ℝ)))
      (min (cMat / (64 * (k : ℝ) * cShift))
        (supercriticalSignedShiftEpsilonBound k gamma / 4)))
  have halphaBound : 0 < alphaBound := by
    dsimp [alphaBound]
    exact lt_min halphaEntropy
      (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
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
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _))
  have halphaLtSigned :
      alpha < supercriticalSignedShiftEpsilonBound k gamma / 4 :=
    halphaLtBound.trans_le (by
      dsimp [alphaBound]
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨halphaThree, halphaEntropyRate⟩ :=
    halphaEntropySpec halpha halphaLtEntropy
  have hHnonneg : 0 ≤ binaryEntropy (3 * alpha) :=
    binaryEntropy_nonneg (by positivity) (by linarith)
  have hHplus :
      binaryEntropy (3 * alpha) + alpha <
        cMat / (64 * (k : ℝ)) := by
    apply lt_of_mul_lt_mul_right (α := ℝ) ?_ realLogTwo_pos.le
    calc
      (binaryEntropy (3 * alpha) + alpha) * Real.log 2 =
          supercriticalDefectPatternRate alpha := by
        rfl
      _ < alphaRateTarget := halphaEntropyRate
      _ = (cMat / (64 * (k : ℝ))) * Real.log 2 := by
        dsimp [alphaRateTarget]
        ring
  have hSupportAlpha :
      8 * (k : ℝ) * binaryEntropy (3 * alpha) < cMat / 8 := by
    have hH : binaryEntropy (3 * alpha) <
        cMat / (64 * (k : ℝ)) :=
      (lt_of_le_of_lt (by linarith) hHplus)
    have hscale : 0 < (8 : ℝ) * (k : ℝ) :=
      mul_pos (by norm_num) hkReal
    have hmul := mul_lt_mul_of_pos_left hH hscale
    calc
      8 * (k : ℝ) * binaryEntropy (3 * alpha) <
          8 * (k : ℝ) * (cMat / (64 * (k : ℝ))) := by
        simpa [mul_assoc] using hmul
      _ = cMat / 8 := by field_simp <;> norm_num
  have hShiftAlpha :
      cShift * (8 * (k : ℝ) * alpha) < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) * cShift :=
      mul_pos (mul_pos (by norm_num) hkReal) hcShift
    have hmul := mul_lt_mul_of_pos_left halphaLtShift hscale
    calc
      cShift * (8 * (k : ℝ) * alpha) <
          (8 * (k : ℝ) * cShift) *
            (cMat / (64 * (k : ℝ) * cShift)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = cMat / 8 := by field_simp <;> norm_num

  let candidateRate := supercriticalMediumCandidateRate k alpha
  let bernoulliPenalty :=
    supercriticalMediumBernoulliPenalty k gamma candidateRate
  let cMed := supercriticalMediumPenalty k gamma alpha
  have hcandidateRate : 0 < candidateRate := by
    exact supercriticalMediumCandidateRate_pos hk halpha
  have hbernoulliPenalty : 0 < bernoulliPenalty := by
    exact supercriticalMediumBernoulliPenalty_pos hk hgammaIco hcandidateRate
  have hcMed : 0 < cMed := by
    exact supercriticalMediumPenalty_pos hk hgammaIco halpha
  obtain ⟨deltaMedium, hdeltaMedium, hdeltaMediumSpec⟩ :=
    exists_supercriticalMediumDelta0 hk hgammaIco halpha hbernoulliPenalty

  let rho := supercriticalOffDiagonal k gamma
  have hrho : 0 < rho := by
    exact supercriticalOffDiagonal_pos hk hgammaIco.1
  have hrhoOne : rho < 1 := by
    exact supercriticalOffDiagonal_lt_one hk hgamma.2
  have hmatchingDelta :
      0 < supercriticalMatchingDeltaBound k gamma alpha :=
    supercriticalMatchingDeltaBound_pos hk hgammaIco halpha
  have hjointDelta :
      0 < supercriticalJointAbsorptionGeometryDeltaBound k gamma :=
    supercriticalJointAbsorptionGeometryDeltaBound_pos hk hgamma
  let deltaBound := min deltaMedium
    (min (alpha / 100)
      (min (supercriticalMatchingDeltaBound k gamma alpha)
        (min (supercriticalJointAbsorptionGeometryDeltaBound k gamma)
          (min (rho / 3)
            (min ((1 - rho) / 3)
              (min (cMat / (64 * (k : ℝ)))
                (cMat / (64 * (k : ℝ) * cShift))))))))
  have hdeltaBound : 0 < deltaBound := by
    dsimp [deltaBound]
    exact lt_min hdeltaMedium
      (lt_min (by positivity)
        (lt_min hmatchingDelta
          (lt_min hjointDelta
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
      delta < supercriticalMatchingDeltaBound k gamma alpha ∧
      delta < supercriticalJointAbsorptionGeometryDeltaBound k gamma ∧
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
  have hrhoLower : 3 * delta < supercriticalOffDiagonal k gamma := by
    change 3 * delta < rho
    linarith [hdeltaSpecs.2.2.2.2.1]
  have hrhoUpper : supercriticalOffDiagonal k gamma + 3 * delta < 1 := by
    change rho + 3 * delta < 1
    linarith [hdeltaSpecs.2.2.2.2.2.1]
  have hSupportDelta : 8 * (k : ℝ) * delta < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) :=
      mul_pos (by norm_num) hkReal
    have hmul := mul_lt_mul_of_pos_left
      hdeltaSpecs.2.2.2.2.2.2.1 hscale
    calc
      8 * (k : ℝ) * delta <
          8 * (k : ℝ) * (cMat / (64 * (k : ℝ))) := by
        simpa [mul_assoc] using hmul
      _ = cMat / 8 := by field_simp <;> norm_num
  have hShiftDelta :
      cShift * (8 * (k : ℝ) * delta) < cMat / 8 := by
    have hscale : 0 < (8 : ℝ) * (k : ℝ) * cShift :=
      mul_pos (mul_pos (by norm_num) hkReal) hcShift
    have hmul := mul_lt_mul_of_pos_left
      hdeltaSpecs.2.2.2.2.2.2.2 hscale
    calc
      cShift * (8 * (k : ℝ) * delta) <
          (8 * (k : ℝ) * cShift) *
            (cMat / (64 * (k : ℝ) * cShift)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = cMat / 8 := by field_simp <;> norm_num
  have hSupportBudget :
      supercriticalSupportPatternBudgetRate k alpha delta < cMat / 4 := by
    dsimp [supercriticalSupportPatternBudgetRate]
    nlinarith [hSupportAlpha, hSupportDelta]
  have hShiftBudget :
      cShift * (8 * (k : ℝ) * (alpha + delta)) < cMat / 4 := by
    nlinarith [hShiftAlpha, hShiftDelta]
  have hSupportSigned :
      2 * (alpha + delta) <
        supercriticalSignedShiftEpsilonBound k gamma := by
    have hdeltaAlpha : delta < alpha := by
      have halpha100 : alpha / 100 < alpha := by
        nlinarith [halpha]
      exact hdeltaSpecs.2.1.trans halpha100
    nlinarith [halphaLtSigned]

  obtain ⟨epsilonDefect, hepsilonDefect, hepsilonDefectSpec⟩ :=
    exists_epsilon0_supercriticalDefectPatternRate_lt
      (show 0 < bernoulliPenalty / 16 by positivity)
  let epsilonBound := min epsilonDefect
    (min (candidateRate / 2)
      (min (cMed / (4 * cShift))
        (supercriticalSignedShiftEpsilonBound k gamma)))
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
      epsilon < supercriticalSignedShiftEpsilonBound k gamma :=
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
  let tau := supercriticalCloseStructureCutRadius k hk gamma hgammaIco
    alpha halphaIoo delta hdelta hdeltaSpecs.2.1 hrhoLower hrhoUpper
      epsilon hepsilon
  have htau : 0 < tau := by
    exact supercriticalCloseStructureCutRadius_pos k hk gamma hgammaIco
      alpha halphaIoo delta hdelta hdeltaSpecs.2.1 hrhoLower hrhoUpper
        epsilon hepsilon
  exact ⟨{
    rank := hk
    density_mem := hgammaIco
    alpha := alpha
    delta := delta
    epsilon := epsilon
    tau := tau
    cMat := cMat
    cMed := cMed
    cAbs := cAbs
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
    joint_absorption_delta := hdeltaSpecs.2.2.2.1
    cMat_eq := rfl
    cMed_eq := rfl
    cAbs_eq := rfl
    cShift_eq := rfl
    cMat_pos := hcMat
    cMed_pos := hcMed
    cAbs_pos := hcAbs
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
    support_signed_shift := hSupportSigned
    medium_defect_rate := by
      simpa [bernoulliPenalty, candidateRate] using hdefectRate
    medium_profile_rate := by
      simpa [bernoulliPenalty, candidateRate] using hprofileRate
    tau_eq := rfl
  }⟩

end InducedStars
