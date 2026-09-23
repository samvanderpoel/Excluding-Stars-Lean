import InducedStars.Structure.Supercritical.Reference
import DenseGraph.Combinatorics.BinomialJointShift
import Mathlib.Tactic

/-!
# Scalar constants for the strict-supercritical absorption repair

The logarithmic gap in this file is the one exposed by the joint
cross/sparse binomial comparison.  It vanishes at `pK k` and is strictly
positive throughout the open supercritical regime.  No asymptotic or
Stirling input is used here.
-/

noncomputable section

open Set

namespace InducedStars

/-- The exact natural-log gap governing joint sparse absorption. -/
noncomputable def supercriticalAbsorptionLogGap
    (k : ℕ) (gamma : ℝ) : ℝ :=
  Real.log (supercriticalOffDiagonal k gamma) -
    ((k - 1 : ℕ) : ℝ) *
      Real.log (1 - supercriticalOffDiagonal k gamma)

/-- The absorption gap is positive precisely on the strict-supercritical
side used in `lemma:super-Fstar`. -/
theorem supercriticalAbsorptionLogGap_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalAbsorptionLogGap k gamma := by
  have hrho : supercriticalOffDiagonal k gamma ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨supercriticalOffDiagonal_pos hk hgamma.1.le,
      supercriticalOffDiagonal_lt_one hk hgamma.2⟩
  have hpk : pK k < supercriticalOffDiagonal k gamma :=
    (pK_lt_phaseLower_iff hk gamma).2 hgamma.1
  have hneg := criticalLogBalance_neg (k := k) (by omega : 2 ≤ k) hrho hpk
  have hpos : 0 < -criticalLogBalance k
      (supercriticalOffDiagonal k gamma) := neg_pos.mpr hneg
  simpa [supercriticalAbsorptionLogGap, criticalLogBalance] using hpos

/-- A deliberately conservative fraction of the sharp logarithmic gap. -/
noncomputable def supercriticalJointAbsorptionPenalty
    (k : ℕ) (gamma : ℝ) : ℝ :=
  supercriticalAbsorptionLogGap k gamma /
    (100 * ((k - 1 : ℕ) : ℝ))

theorem supercriticalJointAbsorptionPenalty_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalJointAbsorptionPenalty k gamma := by
  unfold supercriticalJointAbsorptionPenalty
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  exact div_pos (supercriticalAbsorptionLogGap_pos hk hgamma) (by positivity)

private theorem exists_supercriticalAbsorptionLowerDensity
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∃ lambda : ℝ,
      0 < lambda ∧
      lambda < supercriticalOffDiagonal k gamma ∧
      supercriticalAbsorptionLogGap k gamma / 2 ≤
        Real.log lambda - ((k - 1 : ℕ) : ℝ) * Real.log (1 - lambda) := by
  let rho := supercriticalOffDiagonal k gamma
  let gap := supercriticalAbsorptionLogGap k gamma
  let f : ℝ → ℝ := fun x ↦
    Real.log x - ((k - 1 : ℕ) : ℝ) * Real.log (1 - x)
  have hrho0 : 0 < rho := supercriticalOffDiagonal_pos hk hgamma.1.le
  have hrho1 : rho < 1 := supercriticalOffDiagonal_lt_one hk hgamma.2
  have hgap : 0 < gap := supercriticalAbsorptionLogGap_pos hk hgamma
  have hfrho : f rho = gap := by
    rfl
  have hf : ContinuousAt f rho := by
    dsimp [f]
    have hlogrho : ContinuousAt (fun x : ℝ ↦ Real.log x) rho :=
      Real.continuousAt_log hrho0.ne'
    have hlogone : ContinuousAt (fun x : ℝ ↦ Real.log (1 - x)) rho :=
      (Real.continuousAt_log (by linarith : 1 - rho ≠ 0)).comp
        (continuousAt_const.sub continuousAt_id)
    exact hlogrho.sub (continuousAt_const.mul hlogone)
  have hhalf : gap / 2 < f rho := by
    rw [hfrho]
    linarith
  have hevent : ∀ᶠ x in nhds rho, gap / 2 < f x :=
    hf.eventually (Ioi_mem_nhds hhalf)
  obtain ⟨lower, upper, hrhoInterval, hinterval⟩ :=
    hevent.exists_Ioo_subset
  have hlower : max lower 0 < rho := max_lt hrhoInterval.1 hrho0
  obtain ⟨lambda, hlambdaLower, hlambdaRho⟩ := exists_between hlower
  have hlambdaInterval : lambda ∈ Set.Ioo lower upper :=
    ⟨lt_of_le_of_lt (le_max_left _ _) hlambdaLower,
      hlambdaRho.trans hrhoInterval.2⟩
  refine ⟨lambda, ?_, hlambdaRho, (hinterval hlambdaInterval).le⟩
  exact lt_of_le_of_lt (le_max_right _ _) hlambdaLower

/-- A fixed lower-density parameter below `rho` which retains at least half
of the sharp absorption gap.  Outside the intended parameter regime the
definition uses a harmless fallback; all exported specifications assume the
strict-supercritical hypotheses. -/
noncomputable def supercriticalAbsorptionLowerDensity
    (k : ℕ) (gamma : ℝ) : ℝ :=
  if h : 3 ≤ k ∧ gamma ∈ Set.Ioo (gammaK k) 1 then
    Classical.choose
      (exists_supercriticalAbsorptionLowerDensity h.1 h.2)
  else 1 / 2

theorem supercriticalAbsorptionLowerDensity_spec
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalAbsorptionLowerDensity k gamma ∧
      supercriticalAbsorptionLowerDensity k gamma <
        supercriticalOffDiagonal k gamma ∧
      supercriticalAbsorptionLogGap k gamma / 2 ≤
        Real.log (supercriticalAbsorptionLowerDensity k gamma) -
          ((k - 1 : ℕ) : ℝ) *
            Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) := by
  rw [supercriticalAbsorptionLowerDensity, dite_eq_left ⟨hk, hgamma⟩]
  exact Classical.choose_spec
    (exists_supercriticalAbsorptionLowerDensity hk hgamma)

theorem supercriticalAbsorptionLowerDensity_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalAbsorptionLowerDensity k gamma :=
  (supercriticalAbsorptionLowerDensity_spec hk hgamma).1

theorem supercriticalAbsorptionLowerDensity_lt_rho
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    supercriticalAbsorptionLowerDensity k gamma <
      supercriticalOffDiagonal k gamma :=
  (supercriticalAbsorptionLowerDensity_spec hk hgamma).2.1

theorem supercriticalAbsorptionLowerDensity_lt_one
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    supercriticalAbsorptionLowerDensity k gamma < 1 :=
  (supercriticalAbsorptionLowerDensity_lt_rho hk hgamma).trans
    (supercriticalOffDiagonal_lt_one hk hgamma.2)

theorem supercriticalAbsorptionLowerDensity_gap
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    supercriticalAbsorptionLogGap k gamma / 2 ≤
      Real.log (supercriticalAbsorptionLowerDensity k gamma) -
        ((k - 1 : ℕ) : ℝ) *
          Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) :=
  (supercriticalAbsorptionLowerDensity_spec hk hgamma).2.2

/-! ## Uniform constants for the joint comparison -/

/-- A compact-band parameter which is simultaneously below half the selected
density and below one quarter of the available unselected density. -/
noncomputable def supercriticalShiftBandDensity
    (k : ℕ) (gamma : ℝ) : ℝ :=
  min (supercriticalAbsorptionLowerDensity k gamma / 2)
    ((1 - supercriticalOffDiagonal k gamma) / 4)

theorem supercriticalShiftBandDensity_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalShiftBandDensity k gamma := by
  unfold supercriticalShiftBandDensity
  apply lt_min
  · have := supercriticalAbsorptionLowerDensity_pos hk hgamma
    positivity
  · have := supercriticalOffDiagonal_lt_one hk hgamma.2
    positivity

theorem supercriticalShiftBandDensity_lt_half
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    supercriticalShiftBandDensity k gamma < 1 / 2 := by
  have hlambda : supercriticalAbsorptionLowerDensity k gamma < 1 :=
    supercriticalAbsorptionLowerDensity_lt_one hk hgamma
  calc
    supercriticalShiftBandDensity k gamma ≤
        supercriticalAbsorptionLowerDensity k gamma / 2 := min_le_left _ _
    _ < 1 / 2 := by linarith

/-- The uniform exponential cost used to move the selected count by a signed
support-incident shift. -/
noncomputable def supercriticalJointShiftConstant
    (k : ℕ) (gamma : ℝ) : ℝ :=
  DenseGraph.binomialCompactBandShiftConstant
    (supercriticalShiftBandDensity k gamma)

theorem supercriticalJointShiftConstant_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalJointShiftConstant k gamma := by
  exact DenseGraph.binomialCompactBandShiftConstant_pos
    (supercriticalShiftBandDensity_pos hk hgamma)
    (supercriticalShiftBandDensity_lt_half hk hgamma)

/-- The logarithmic magnitude controlling all error terms in the absorption
exponent.  The added `1` keeps this denominator uniformly positive. -/
noncomputable def supercriticalJointAbsorptionLogMagnitude
    (k : ℕ) (gamma : ℝ) : ℝ :=
  |Real.log (supercriticalAbsorptionLowerDensity k gamma)| +
    |Real.log (1 - supercriticalAbsorptionLowerDensity k gamma)| + 1

theorem supercriticalJointAbsorptionLogMagnitude_pos
    (k : ℕ) (gamma : ℝ) :
    0 < supercriticalJointAbsorptionLogMagnitude k gamma := by
  unfold supercriticalJointAbsorptionLogMagnitude
  positivity

/-- An explicit smallness threshold for the joint absorption proof.  Its
three entries preserve the lower-density margin, make the logarithmic error
smaller than the strict gap, and provide elementary rank-scale slack. -/
noncomputable def supercriticalJointAbsorptionDeltaBound
    (k : ℕ) (gamma : ℝ) : ℝ :=
  min
    ((supercriticalOffDiagonal k gamma -
        supercriticalAbsorptionLowerDensity k gamma) / 4)
    (min
      (supercriticalAbsorptionLogGap k gamma /
        (24 * ((k - 1 : ℕ) : ℝ) *
          supercriticalJointAbsorptionLogMagnitude k gamma))
      (1 / (20 * ((k - 1 : ℕ) : ℝ))))

theorem supercriticalJointAbsorptionDeltaBound_pos
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalJointAbsorptionDeltaBound k gamma := by
  unfold supercriticalJointAbsorptionDeltaBound
  have hr : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hmargin : 0 < supercriticalOffDiagonal k gamma -
      supercriticalAbsorptionLowerDensity k gamma := by
    linarith [supercriticalAbsorptionLowerDensity_lt_rho hk hgamma]
  have hgap := supercriticalAbsorptionLogGap_pos hk hgamma
  have hmag := supercriticalJointAbsorptionLogMagnitude_pos k gamma
  positivity

theorem supercriticalJointAbsorptionDeltaBound_le_densityMargin
    (k : ℕ) (gamma : ℝ) :
    supercriticalJointAbsorptionDeltaBound k gamma ≤
      (supercriticalOffDiagonal k gamma -
        supercriticalAbsorptionLowerDensity k gamma) / 4 :=
  min_le_left _ _

theorem supercriticalJointAbsorptionDeltaBound_le_gapError
    (k : ℕ) (gamma : ℝ) :
    supercriticalJointAbsorptionDeltaBound k gamma ≤
      supercriticalAbsorptionLogGap k gamma /
        (24 * ((k - 1 : ℕ) : ℝ) *
          supercriticalJointAbsorptionLogMagnitude k gamma) :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem supercriticalJointAbsorptionDeltaBound_le_rankSlack
    (k : ℕ) (gamma : ℝ) :
    supercriticalJointAbsorptionDeltaBound k gamma ≤
      1 / (20 * ((k - 1 : ℕ) : ℝ)) :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem supercriticalJointAbsorption_delta_mul_logMagnitude_le_gap
    {k : ℕ} (hk : 3 ≤ k) {gamma delta : ℝ}
    (hdelta : delta ≤ supercriticalJointAbsorptionDeltaBound k gamma) :
    delta * supercriticalJointAbsorptionLogMagnitude k gamma ≤
      supercriticalAbsorptionLogGap k gamma /
        (24 * ((k - 1 : ℕ) : ℝ)) := by
  have hR : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hM := supercriticalJointAbsorptionLogMagnitude_pos k gamma
  have hraw := hdelta.trans
    (supercriticalJointAbsorptionDeltaBound_le_gapError k gamma)
  have hdenom : 0 < 24 * ((k - 1 : ℕ) : ℝ) *
      supercriticalJointAbsorptionLogMagnitude k gamma := by positivity
  have hcross := (le_div_iff₀ hdenom).mp hraw
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 24 * ((k - 1 : ℕ) : ℝ))).2
  nlinarith

/-! ## Exact absorption exponent -/

/-- Exact algebra behind the two sharp binomial-ratio bounds.  Here `q` is
the sparse-pair capacity, and `a + b = n - s` says that the other main parts
and the absorbed part partition the nonsparse vertices. -/
theorem supercriticalJointAbsorptionExponent_eq
    {lambda a b n s q : ℝ} (hparts : a + b = n - s) :
    (s * b - q) * Real.log (1 - lambda) +
        (a * s + q) *
          (Real.log (1 - lambda) - Real.log lambda) =
      s * (n - s) * Real.log (1 - lambda) -
        a * s * Real.log lambda - q * Real.log lambda := by
  rw [← hparts]
  ring

private theorem jointAbsorptionExponent_le_aux
    {R G delta n a s q ell ellOne M : ℝ}
    (hR : 0 < R) (hG : 0 < G)
    (hdelta0 : 0 ≤ delta) (hn : 0 ≤ n) (hs : 0 ≤ s)
    (hell : ell ≤ 0) (hellOne : ellOne ≤ 0)
    (hellMag : -ell ≤ M) (hellOneMag : -ellOne ≤ M)
    (hgap : G / 2 ≤ ell - R * ellOne)
    (hsmall : 24 * R * M * delta ≤ G)
    (hbalance : |a - n / R| ≤ delta * n)
    (hsparse : s ≤ delta * n / 2)
    (hq : q ≤ s ^ 2 / 2) :
    s * (n - s) * ellOne - a * s * ell - q * ell ≤
      -(G / (100 * R)) * s * n := by
  have hM : 0 ≤ M := le_trans (neg_nonneg.mpr hell) hellMag
  have hsn : 0 ≤ s * n := mul_nonneg hs hn
  have hdeltaN : 0 ≤ delta * n := mul_nonneg hdelta0 hn
  have hbalanceUpper : a - n / R ≤ delta * n :=
    (le_abs_self (a - n / R)).trans hbalance
  have hsquare : s ^ 2 ≤ delta * n * s := by
    have hmul := mul_le_mul_of_nonneg_right hsparse hs
    nlinarith [hmul]
  have hqCoarse : q ≤ delta * n * s := by
    nlinarith [hq, hsquare, sq_nonneg s]
  have hbalanceError :
      -(a - n / R) * s * ell ≤ delta * n * s * M := by
    calc
      -(a - n / R) * s * ell =
          (a - n / R) * (s * (-ell)) := by ring
      _ ≤ (delta * n) * (s * (-ell)) :=
        mul_le_mul_of_nonneg_right hbalanceUpper
          (mul_nonneg hs (neg_nonneg.mpr hell))
      _ ≤ delta * n * s * M := by
        have hm := mul_le_mul_of_nonneg_left hellMag
          (mul_nonneg hdeltaN hs)
        nlinarith
  have hsquareError : -s ^ 2 * ellOne ≤ delta * n * s * M := by
    calc
      -s ^ 2 * ellOne = s ^ 2 * (-ellOne) := by ring
      _ ≤ (delta * n * s) * (-ellOne) :=
        mul_le_mul_of_nonneg_right hsquare (neg_nonneg.mpr hellOne)
      _ ≤ delta * n * s * M := by
        exact mul_le_mul_of_nonneg_left hellOneMag
          (mul_nonneg hdeltaN hs)
  have hqError : -q * ell ≤ delta * n * s * M := by
    calc
      -q * ell = q * (-ell) := by ring
      _ ≤ (delta * n * s) * (-ell) :=
        mul_le_mul_of_nonneg_right hqCoarse (neg_nonneg.mpr hell)
      _ ≤ delta * n * s * M :=
        mul_le_mul_of_nonneg_left hellMag
          (mul_nonneg hdeltaN hs)
  have herrorSum :
      -s ^ 2 * ellOne - (a - n / R) * s * ell - q * ell ≤
        3 * (delta * n * s * M) := by
    linarith
  have herrorScaled :
      R * (-s ^ 2 * ellOne - (a - n / R) * s * ell - q * ell) ≤
        R * (3 * (delta * n * s * M)) :=
    mul_le_mul_of_nonneg_left herrorSum hR.le
  have hgapScaled := mul_le_mul_of_nonneg_right hgap hsn
  have hsmallScaled := mul_le_mul_of_nonneg_right hsmall hsn
  have hidentity :
      R * (s * (n - s) * ellOne - a * s * ell - q * ell) =
        -(ell - R * ellOne) * (s * n) +
          R * (-s ^ 2 * ellOne - (a - n / R) * s * ell - q * ell) := by
    field_simp [hR.ne']
    ring
  refine le_of_mul_le_mul_left ?_ hR
  rw [hidentity]
  have htargetIdentity :
      R * (-(G / (100 * R)) * s * n) = -(G / 100) * (s * n) := by
    field_simp [hR.ne']
  rw [htargetIdentity]
  nlinarith

/-- The strict joint-absorption exponent.  Under the explicit delta bound,
balanced absorbed-part size, and sparse-size hypotheses, the exact exponent
from the two sharp binomial comparisons loses at least
`supercriticalJointAbsorptionPenalty * s * n`.

The hypothesis on `q` is applied later with `q = Nat.choose s 2`; unlike the
old argument, that quadratic term remains visible throughout this proof. -/
theorem supercriticalJointAbsorptionExponent_le
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta n a s q : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ supercriticalJointAbsorptionDeltaBound k gamma)
    (hn : 0 ≤ n) (hs : 0 ≤ s)
    (hbalance :
      |a - n / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : s ≤ delta * n / 2)
    (hq : q ≤ s ^ 2 / 2) :
    s * (n - s) *
          Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) -
        a * s * Real.log (supercriticalAbsorptionLowerDensity k gamma) -
        q * Real.log (supercriticalAbsorptionLowerDensity k gamma) ≤
      -supercriticalJointAbsorptionPenalty k gamma * s * n := by
  let R : ℝ := ((k - 1 : ℕ) : ℝ)
  let G : ℝ := supercriticalAbsorptionLogGap k gamma
  let lambda : ℝ := supercriticalAbsorptionLowerDensity k gamma
  let M : ℝ := supercriticalJointAbsorptionLogMagnitude k gamma
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast (by omega : 0 < k - 1)
  have hG : 0 < G := by
    exact supercriticalAbsorptionLogGap_pos hk hgamma
  have hlambda0 : 0 < lambda := by
    exact supercriticalAbsorptionLowerDensity_pos hk hgamma
  have hlambda1 : lambda < 1 := by
    exact supercriticalAbsorptionLowerDensity_lt_one hk hgamma
  have hell : Real.log lambda ≤ 0 :=
    (Real.log_neg hlambda0 hlambda1).le
  have hellOne : Real.log (1 - lambda) ≤ 0 := by
    exact (Real.log_neg (by linarith) (by linarith)).le
  have hM : 0 < M := by
    exact supercriticalJointAbsorptionLogMagnitude_pos k gamma
  have hellMag : -Real.log lambda ≤ M := by
    rw [← abs_of_nonpos hell]
    dsimp [M, supercriticalJointAbsorptionLogMagnitude, lambda]
    linarith [abs_nonneg
      (Real.log (1 - supercriticalAbsorptionLowerDensity k gamma))]
  have hellOneMag : -Real.log (1 - lambda) ≤ M := by
    rw [← abs_of_nonpos hellOne]
    dsimp [M, supercriticalJointAbsorptionLogMagnitude, lambda]
    linarith [abs_nonneg
      (Real.log (supercriticalAbsorptionLowerDensity k gamma))]
  have hgap : G / 2 ≤ Real.log lambda - R * Real.log (1 - lambda) := by
    exact supercriticalAbsorptionLowerDensity_gap hk hgamma
  have hdeltaRaw : delta ≤ G / (24 * R * M) := by
    exact hdelta.trans
      (supercriticalJointAbsorptionDeltaBound_le_gapError k gamma)
  have hdenom : 0 < 24 * R * M := by positivity
  have hsmall : 24 * R * M * delta ≤ G := by
    have := (le_div_iff₀ hdenom).mp hdeltaRaw
    nlinarith
  have hmain := jointAbsorptionExponent_le_aux
    hR hG hdelta0 hn hs hell hellOne hellMag hellOneMag hgap hsmall
      hbalance hsparse hq
  simpa [R, G, lambda, M, supercriticalJointAbsorptionPenalty] using hmain

/-- The strict bound in the literal `Q = s*b-q`, `E = a*s+q` form delivered
by the two sharp binomial-ratio comparisons. -/
theorem supercriticalJointAbsorptionRatioExponent_le
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    {delta n a b s q : ℝ}
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ supercriticalJointAbsorptionDeltaBound k gamma)
    (hn : 0 ≤ n) (hs : 0 ≤ s)
    (hparts : a + b = n - s)
    (hbalance :
      |a - n / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : s ≤ delta * n / 2)
    (hq : q ≤ s ^ 2 / 2) :
    (s * b - q) *
          Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) +
        (a * s + q) *
          (Real.log (1 - supercriticalAbsorptionLowerDensity k gamma) -
            Real.log (supercriticalAbsorptionLowerDensity k gamma)) ≤
      -supercriticalJointAbsorptionPenalty k gamma * s * n := by
  rw [supercriticalJointAbsorptionExponent_eq hparts]
  exact supercriticalJointAbsorptionExponent_le hk hgamma hdelta0 hdelta
    hn hs hbalance hsparse hq

/-- Symbolic `k = 3`, `s = 1` specialization of the joint absorption exponent.
The gain is exactly `-(n/2)` times the strict logarithmic gap. -/
theorem supercriticalJointAbsorption_k3_s1_audit
    {lambda n : ℝ} :
    (n - 1) * Real.log (1 - lambda) -
        (n / 2 - 1) * Real.log lambda =
      -(n / 2) *
          (Real.log lambda - 2 * Real.log (1 - lambda)) +
        (Real.log lambda - Real.log (1 - lambda)) := by
  ring

/-- Exact leading-order identity in the `k = 3`, `s = 1` audit.  It exhibits
the missing capacity-enlargement contribution as one half of the strict
logarithmic gap. -/
theorem supercriticalJointAbsorption_k3_s1_leading_audit
    {lambda n : ℝ} :
    n * Real.log (1 - lambda) - n / 2 * Real.log lambda =
      -(n / 2) *
        (Real.log lambda - 2 * Real.log (1 - lambda)) := by
  ring

/-- In the actual strict-supercritical regime, the coefficient isolated by
the `k = 3`, `s = 1` audit is symbolically positive. -/
theorem supercriticalJointAbsorption_k3_s1_gain_pos
    {gamma n : ℝ} (hgamma : gamma ∈ Set.Ioo (gammaK 3) 1)
    (hn : 0 < n) :
    0 < n / 2 * supercriticalAbsorptionLogGap 3 gamma := by
  exact mul_pos (by positivity) (supercriticalAbsorptionLogGap_pos (by omega) hgamma)

end InducedStars
