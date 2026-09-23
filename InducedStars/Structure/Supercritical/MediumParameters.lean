import InducedStars.Structure.Supercritical.MediumAggregation
import InducedStars.Structure.Supercritical.MediumCandidateAbundance
import InducedStars.Structure.Supercritical.MediumJanson
import Mathlib.Tactic

/-!
# Scalar parameters for the supercritical medium-degree penalty

This module makes the small-parameter choices used by the medium-degree
argument explicit.  The choices depend only on the fixed parameters, and all
claims below are elementary consequences of continuity and positivity.
-/

noncomputable section

open Set

namespace InducedStars

/-- The final quadratic rate reserved for the supercritical medium-degree
family.  The factor eight leaves separate slack for exact-cardinality
conditioning, profile comparison, and the remaining combinatorial overhead. -/
def supercriticalMediumPenalty (k : ℕ) (gamma alpha : ℝ) : ℝ :=
  supercriticalMediumBernoulliPenalty k gamma
      (supercriticalMediumCandidateRate k alpha) / 8

theorem supercriticalMediumPenalty_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma alpha : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) (halpha : 0 < alpha) :
    0 < supercriticalMediumPenalty k gamma alpha := by
  unfold supercriticalMediumPenalty
  exact div_pos
    (supercriticalMediumBernoulliPenalty_pos hk hgamma
      (supercriticalMediumCandidateRate_pos hk halpha))
    (by norm_num)

/-- The combined-defect entropy rate tends to zero with the defect parameter.
This epsilon-delta form also packages the range condition needed by the
Hamming-ball estimate. -/
theorem exists_epsilon0_supercriticalDefectPatternRate_lt
    {q : ℝ} (hq : 0 < q) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {epsilon : ℝ}, 0 < epsilon → epsilon < epsilon0 →
        3 * epsilon < 1 / 2 ∧
          supercriticalDefectPatternRate epsilon < q := by
  have hcontinuous : ContinuousAt supercriticalDefectPatternRate 0 := by
    unfold supercriticalDefectPatternRate
    exact (((binaryEntropy_continuous.comp
      (continuous_const.mul continuous_id)).add continuous_id).mul
        continuous_const).continuousAt
  have hzero : supercriticalDefectPatternRate 0 = 0 := by
    simp [supercriticalDefectPatternRate]
  obtain ⟨d, hd, hcontrol⟩ :=
    (Metric.continuousAt_iff.mp hcontinuous) q hq
  refine ⟨min d (1 / 6), lt_min hd (by norm_num), ?_⟩
  intro epsilon hepsilon hepsilon0
  have hed : epsilon < d := hepsilon0.trans_le (min_le_left _ _)
  have heone : epsilon < 1 / 6 :=
    hepsilon0.trans_le (min_le_right _ _)
  constructor
  · linarith
  · have hdist : dist epsilon 0 < d := by
      simpa [Real.dist_eq, abs_of_pos hepsilon] using hed
    have hclose := hcontrol hdist
    rw [hzero, Real.dist_eq, sub_zero] at hclose
    exact lt_of_le_of_lt (le_abs_self _) hclose

/-- A conservative balance threshold used by the candidate-abundance
argument. -/
def supercriticalMediumCandidateDeltaBound (k : ℕ) : ℝ :=
  1 / (6 * ((k - 1 : ℕ) : ℝ))

/-- All small-`delta` requirements used by the medium-degree proof can be
met simultaneously.  The comparison-rate conclusion is stated for an
arbitrary positive Bernoulli penalty so that the bookkeeping lemma remains
reusable independently of the particular candidate rate. -/
theorem exists_supercriticalMediumDelta0
    {k : ℕ} (hk : 3 ≤ k) {gamma alpha penalty : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (halpha : 0 < alpha) (hpenalty : 0 < penalty) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ {delta : ℝ}, 0 < delta → delta < delta0 →
        delta < alpha / 100 ∧
        2 * delta <
          min (supercriticalOffDiagonal k gamma)
              (1 - supercriticalOffDiagonal k gamma) / 2 ∧
        3 * delta < supercriticalOffDiagonal k gamma ∧
        supercriticalOffDiagonal k gamma + 3 * delta < 1 ∧
        0 < supercriticalOffDiagonal k gamma - 2 * delta ∧
        supercriticalOffDiagonal k gamma + 2 * delta < 1 ∧
        delta < supercriticalMediumCandidateDeltaBound k ∧
        supercriticalMediumProfileComparisonRate k
            (supercriticalOffDiagonal k gamma) delta < penalty / 16 := by
  let rho := supercriticalOffDiagonal k gamma
  let C := DenseGraph.binomialDensityBandConstant rho *
    Fintype.card (SupercriticalPartPair k)
  have hrho : 0 < rho := by
    exact supercriticalOffDiagonal_pos hk hgamma.1
  have hrhoOne : rho < 1 := by
    exact supercriticalOffDiagonal_lt_one hk hgamma.2
  have hmin : 0 < min rho (1 - rho) := lt_min hrho (sub_pos.mpr hrhoOne)
  have hkOneNat : 0 < k - 1 := by omega
  have hkOne : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast hkOneNat
  have hcandidateBound : 0 < supercriticalMediumCandidateDeltaBound k := by
    unfold supercriticalMediumCandidateDeltaBound
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    have hconstant : 0 ≤ DenseGraph.binomialDensityBandConstant rho := by
      exact DenseGraph.binomialDensityBandConstant_nonneg
        (rho := rho) (delta := 0) (by norm_num) (by simpa using hrho)
          (by simpa using hrhoOne)
    positivity
  have hCOne : 0 < C + 1 := by linarith
  let comparisonBound := penalty / (32 * (C + 1))
  have hcomparisonBound : 0 < comparisonBound := by
    dsimp [comparisonBound]
    positivity
  let delta0 := min (alpha / 100)
    (min (min rho (1 - rho) / 4)
      (min (rho / 4)
        (min ((1 - rho) / 4)
          (min (supercriticalMediumCandidateDeltaBound k)
            comparisonBound))))
  have hdelta0 : 0 < delta0 := by
    dsimp [delta0]
    repeat' apply lt_min
    all_goals positivity
  refine ⟨delta0, hdelta0, ?_⟩
  intro delta hdelta hsmall
  have halphaSmall : delta < alpha / 100 :=
    hsmall.trans_le (min_le_left _ _)
  have hrest : delta < min (min rho (1 - rho) / 4)
      (min (rho / 4)
        (min ((1 - rho) / 4)
          (min (supercriticalMediumCandidateDeltaBound k)
            comparisonBound))) :=
    hsmall.trans_le (min_le_right _ _)
  have hminSmall : delta < min rho (1 - rho) / 4 :=
    hrest.trans_le (min_le_left _ _)
  have hrest2 : delta < min (rho / 4)
      (min ((1 - rho) / 4)
        (min (supercriticalMediumCandidateDeltaBound k)
          comparisonBound)) :=
    hrest.trans_le (min_le_right _ _)
  have hrhoSmall : delta < rho / 4 :=
    hrest2.trans_le (min_le_left _ _)
  have hrest3 : delta < min ((1 - rho) / 4)
      (min (supercriticalMediumCandidateDeltaBound k) comparisonBound) :=
    hrest2.trans_le (min_le_right _ _)
  have honeSmall : delta < (1 - rho) / 4 :=
    hrest3.trans_le (min_le_left _ _)
  have hrest4 : delta <
      min (supercriticalMediumCandidateDeltaBound k) comparisonBound :=
    hrest3.trans_le (min_le_right _ _)
  have hcandidateSmall :
      delta < supercriticalMediumCandidateDeltaBound k :=
    hrest4.trans_le (min_le_left _ _)
  have hcomparisonSmall : delta < comparisonBound :=
    hrest4.trans_le (min_le_right _ _)
  have hjansonSmall : 2 * delta < min rho (1 - rho) / 2 := by
    linarith
  have hrhoThree : 3 * delta < rho := by linarith
  have honeThree : rho + 3 * delta < 1 := by linarith
  have hrhoTwo : 0 < rho - 2 * delta := by linarith
  have honeTwo : rho + 2 * delta < 1 := by linarith
  have hcomparison :
      supercriticalMediumProfileComparisonRate k rho delta < penalty / 16 := by
    have hCdelta : C * delta < penalty / 16 := by
      have hmul : (C + 1) * delta < (C + 1) * comparisonBound :=
        mul_lt_mul_of_pos_left hcomparisonSmall hCOne
      have hbound : (C + 1) * comparisonBound = penalty / 32 := by
        dsimp [comparisonBound]
        field_simp
      have hCle : C * delta ≤ (C + 1) * delta := by
        nlinarith
      rw [hbound] at hmul
      linarith
    simpa [supercriticalMediumProfileComparisonRate, C, rho] using hCdelta
  simpa [rho] using ⟨halphaSmall, hjansonSmall, hrhoThree, honeThree,
    sub_pos.mp hrhoTwo, honeTwo, hcandidateSmall, hcomparison⟩

end InducedStars
