import InducedStars.Structure.Supercritical.MediumCandidates
import InducedStars.Structure.Supercritical.MediumOverhead
import InducedStars.Structure.Supercritical.ProfileModels
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Scalar parameters for the supercritical matching penalty

The matching argument uses the same compact density interval as the
medium-degree argument but loses only a linear exponential.  This module
records the uniform coordinate/event floors and the separate linear
polynomial-absorption estimate.
-/

noncomputable section

open Filter Finset Set

namespace InducedStars

/-- A fixed lower bound for both possible statuses of a random cross edge.
This is deliberately the same normalization as the Goal-7b medium floor. -/
abbrev supercriticalMatchingSuccessFloor (k : ℕ) (gamma : ℝ) : ℝ :=
  mediumSuccessProbabilityFloor k gamma

theorem supercriticalMatchingSuccessFloor_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    0 < supercriticalMatchingSuccessFloor k gamma :=
  mediumSuccessProbabilityFloor_pos hk hgamma

theorem supercriticalMatchingSuccessFloor_le_one
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    supercriticalMatchingSuccessFloor k gamma ≤ 1 :=
  mediumSuccessProbabilityFloor_le_one hk hgamma

/-- A quarter-width density band remains above the common success floor and
below its complementary ceiling.  This is the exact scalar input needed by
the full-profile matching model. -/
theorem supercriticalMatchingSuccessFloor_densityBand
    {k : ℕ} (hk : 3 ≤ k) {gamma delta : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (hsmall : 4 * delta ≤
      min (supercriticalOffDiagonal k gamma)
        (1 - supercriticalOffDiagonal k gamma)) :
    supercriticalMatchingSuccessFloor k gamma ≤
        supercriticalOffDiagonal k gamma - delta ∧
      supercriticalOffDiagonal k gamma + delta ≤
        1 - supercriticalMatchingSuccessFloor k gamma := by
  let rho := supercriticalOffDiagonal k gamma
  have hrho : 0 < rho := supercriticalOffDiagonal_pos hk hgamma.1
  have hrhoOne : rho < 1 := supercriticalOffDiagonal_lt_one hk hgamma.2
  have hminLeft : min rho (1 - rho) ≤ rho := min_le_left _ _
  have hminRight : min rho (1 - rho) ≤ 1 - rho := min_le_right _ _
  change min rho (1 - rho) / 2 ≤ rho - delta ∧
    rho + delta ≤ 1 - min rho (1 - rho) / 2
  constructor <;> nlinarith

/-- A coarse common bound for the random center/leaf and leaf/leaf roles in
both matching geometries. -/
def supercriticalMatchingRandomRoleBound (k : ℕ) : ℕ :=
  3 * (k - 2) + (k - 2) ^ 2

/-- Uniform probability floor for one complete matching-star event. -/
def supercriticalMatchingEventProbabilityFloor (k : ℕ) (gamma : ℝ) : ℝ :=
  supercriticalMatchingSuccessFloor k gamma ^
    supercriticalMatchingRandomRoleBound k

theorem supercriticalMatchingEventProbabilityFloor_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1) :
    0 < supercriticalMatchingEventProbabilityFloor k gamma := by
  unfold supercriticalMatchingEventProbabilityFloor
  exact pow_pos (supercriticalMatchingSuccessFloor_pos hk hgamma) _

/-! ## Density-band consequences for the full-profile Bernoulli model -/

theorem supercriticalProfileBernoulli_probability_mem_band
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {D : SupercriticalDivision k V} {m : ℕ} {rho delta : ℝ} {t : ℤ}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalProfileBernoulliModel D profile).probability c ∈
      Set.Icc (rho - delta) (rho + delta) := by
  rw [supercriticalProfileBernoulliModel_probability_eq_profileDensity]
  exact hprofile.2 c.1

/-- Every globally complemented full-profile coordinate retains the common
success floor when the profile band is narrower than that floor. -/
theorem supercriticalProfile_or_complement_probability_lower
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {D : SupercriticalDivision k V} {m : ℕ} {rho delta : ℝ} {t : ℤ}
    {profile : SupercriticalEdgeProfile D}
    (hprofile : SupercriticalProfileAtShift D m rho delta t profile)
    {qFloor : ℝ}
    (hlower : qFloor ≤ rho - delta)
    (hupper : rho + delta ≤ 1 - qFloor)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    qFloor ≤ (supercriticalProfileBernoulliModel D profile).probability c ∧
      qFloor ≤ 1 -
        (supercriticalProfileBernoulliModel D profile).probability c := by
  have hband := supercriticalProfileBernoulli_probability_mem_band hprofile c
  constructor
  · exact hlower.trans hband.1
  · linarith [hband.2, hupper]

/-! ## Linear exponential absorption -/

/-- A fixed power of `n²+1` is eventually smaller than every positive
linear exponential.  This is separate from the quadratic estimate used by
the medium-degree penalty. -/
theorem eventually_nsq_add_one_pow_le_exp_linear
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ((((n ^ 2 + 1) ^ r : ℕ) : ℝ)) ≤ Real.exp (c * (n : ℝ)) := by
  have hlittle :
      (fun x : ℝ ↦ (2 : ℝ) ^ r * x ^ (2 * r)) =o[atTop]
        (fun x : ℝ ↦ Real.exp (c * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop (2 * r) hc).const_mul_left
      ((2 : ℝ) ^ r)
  have hgrowth := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
  filter_upwards [hgrowth, eventually_ge_atTop 1] with n hnGrowth hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (n : ℝ) ^ 2 + 1 ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  calc
    ((((n ^ 2 + 1) ^ r : ℕ) : ℝ)) = ((n : ℝ) ^ 2 + 1) ^ r := by simp
    _ ≤ (2 * (n : ℝ) ^ 2) ^ r := by gcongr
    _ = (2 : ℝ) ^ r * (n : ℝ) ^ (2 * r) := by
      rw [mul_pow, ← pow_mul]
    _ ≤ Real.exp (c * (n : ℝ)) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg] using hnGrowth

/-- Uniform linear absorption with an arbitrary positive integer multiplier
`h`.  This is the form needed to preserve the matching-number exponent. -/
theorem eventually_polynomial_le_exp_mul_hn
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ h : ℕ, 1 ≤ h →
      ((((n ^ 2 + 1) ^ r : ℕ) : ℝ)) ≤
        Real.exp (c * (h : ℝ) * (n : ℝ)) := by
  filter_upwards [eventually_nsq_add_one_pow_le_exp_linear r hc]
      with n hn h hh
  refine hn.trans (Real.exp_le_exp.mpr ?_)
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hch : c ≤ c * (h : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hhR hc.le
  exact mul_le_mul_of_nonneg_right hch hn0

end InducedStars
