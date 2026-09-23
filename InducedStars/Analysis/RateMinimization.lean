import InducedStars.Analysis.ScalarOptimization
import InducedStars.Analysis.RelativeEntropy

/-!
# Scalar minimization of the fixed-density rate

This file proves the one-dimensional minimization in the conditioned graphon
variational problem.  The objective is the entropy profile from
`ScalarOptimization` tilted by the Bernoulli edge weight.
-/

namespace InducedStars

open Set

/-- The density-dependent part of the fixed-density rate objective. -/
noncomputable def rateCoreObjective (k : ℕ) (p γ : ℝ) : ℝ :=
  -entropyDensity k γ + γ * log2 ((1 - p) / p)

/-- The full fixed-density relative-entropy value. -/
noncomputable def rateAtDensity (k : ℕ) (p γ : ℝ) : ℝ :=
  rateCoreObjective k p γ - log2 (1 - p)

/-! ## Endpoints and the critical entropy identity -/

@[simp] theorem entropyDensity_zero (k : ℕ) (hk : 3 ≤ k) :
    entropyDensity k 0 = 0 := by
  rw [entropyDensity_of_le (gammaK_pos hk).le]
  simp [entropyDensityLower]

@[simp] theorem entropyDensity_one (k : ℕ) (hk : 3 ≤ k) :
    entropyDensity k 1 = 0 := by
  rw [entropyDensity_of_ge hk (gammaK_lt_one hk).le, entropyDensityUpper]
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have harg :
      ((((k - 1 : ℕ) : ℝ) * 1 - 1) / (k - 2 : ℕ)) = 1 := by
    field_simp [hd]
    norm_num [Nat.cast_sub (show 2 ≤ k by omega),
      Nat.cast_sub (show 1 ≤ k by omega)]
    ring
  rw [harg, binaryEntropy_one, mul_zero]

@[simp] theorem rateCoreObjective_zero (k : ℕ) (p : ℝ) (hk : 3 ≤ k) :
    rateCoreObjective k p 0 = 0 := by
  simp [rateCoreObjective, entropyDensity_zero k hk]

@[simp] theorem rateAtDensity_zero (k : ℕ) (p : ℝ) (hk : 3 ≤ k) :
    rateAtDensity k p 0 = -log2 (1 - p) := by
  simp [rateAtDensity, rateCoreObjective_zero k p hk]

@[simp] theorem rateAtDensity_one (k : ℕ) (p : ℝ) (hk : 3 ≤ k)
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    rateAtDensity k p 1 = -log2 p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  rw [rateAtDensity, rateCoreObjective, entropyDensity_one k hk]
  rw [log2_div hq0 hp0]
  ring

/-- The entropy of the critical probability in the form used on the lower branch. -/
theorem binaryEntropy_pK_identity (k : ℕ) (hk : 3 ≤ k) :
    binaryEntropy (pK k) =
      -(1 + (k - 2 : ℕ) * pK k) * log2 (1 - pK k) := by
  rw [binaryEntropy_eq_formula, log2_pK_eq]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-- The critical logarithmic slope identity from `p_k = (1-p_k)^(k-1)`. -/
theorem criticalEntropySlope_identity (k : ℕ) (hk : 3 ≤ k) :
    ((k - 2 : ℕ) : ℝ) / (1 + (k - 2 : ℕ) * pK k) *
        binaryEntropy (pK k) =
      log2 ((1 - pK k) / pK k) := by
  have hp0 : pK k ≠ 0 := (pK_pos (show 2 ≤ k by omega)).ne'
  have hq0 : 1 - pK k ≠ 0 := (sub_pos.mpr
    (pK_lt_one (show 2 ≤ k by omega))).ne'
  have hden : 1 + ((k - 2 : ℕ) : ℝ) * pK k ≠ 0 := by
    have hd := deltaK_pos hk
    rw [deltaK] at hd
    apply ne_of_gt
    nlinarith [mul_pos hd (pK_pos (show 2 ≤ k by omega))]
  rw [binaryEntropy_pK_identity k hk, log2_div hq0 hp0, log2_pK_eq]
  field_simp [hden]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-! ## The affine lower branch -/

/-- The slope of the rate objective on the lower-density branch. -/
noncomputable def rateLowerCoefficient (k : ℕ) (p : ℝ) : ℝ :=
  log2 (((1 - p) * pK k) / (p * (1 - pK k)))

/-- Exact affine formula for the lower branch of the core objective. -/
theorem rateCoreObjective_lower_eq {k : ℕ} (hk : 3 ≤ k) {p γ : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hγ : γ ≤ gammaK k) :
    rateCoreObjective k p γ = γ * rateLowerCoefficient k p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hpk0 : pK k ≠ 0 := (pK_pos (show 2 ≤ k by omega)).ne'
  have hqk0 : 1 - pK k ≠ 0 := (sub_pos.mpr
    (pK_lt_one (show 2 ≤ k by omega))).ne'
  have hden : 1 + ((k - 2 : ℕ) : ℝ) * pK k ≠ 0 := by
    have hd := deltaK_pos hk
    rw [deltaK] at hd
    apply ne_of_gt
    nlinarith [mul_pos hd (pK_pos (show 2 ≤ k by omega))]
  rw [rateCoreObjective, entropyDensity_of_le hγ, entropyDensityLower]
  have hslope := criticalEntropySlope_identity k hk
  rw [rateLowerCoefficient, log2_div (mul_ne_zero hq0 hpk0)
    (mul_ne_zero hp0 hqk0), log2_mul hq0 hpk0, log2_mul hp0 hqk0,
    log2_div hq0 hp0]
  calc
    -(((k - 2 : ℕ) : ℝ) * γ /
          (1 + (k - 2 : ℕ) * pK k) * binaryEntropy (pK k)) +
        γ * (log2 (1 - p) - log2 p) =
        γ * (-( (((k - 2 : ℕ) : ℝ) /
          (1 + (k - 2 : ℕ) * pK k)) * binaryEntropy (pK k)) +
          (log2 (1 - p) - log2 p)) := by ring
    _ = γ * (-(log2 (1 - pK k) - log2 (pK k)) +
          (log2 (1 - p) - log2 p)) := by rw [hslope, log2_div hqk0 hpk0]
    _ = γ * (log2 (1 - p) + log2 (pK k) -
          (log2 p + log2 (1 - pK k))) := by ring

theorem rateLowerCoefficient_pos_iff {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    0 < rateLowerCoefficient k p ↔ p < pK k := by
  have hpk := pK_mem_Ioo (show 2 ≤ k by omega)
  have hnum : 0 < (1 - p) * pK k := mul_pos (sub_pos.mpr hp.2) hpk.1
  have hden : 0 < p * (1 - pK k) := mul_pos hp.1 (sub_pos.mpr hpk.2)
  rw [rateLowerCoefficient, log2_pos_iff_of_pos (div_pos hnum hden),
    one_lt_div hden]
  constructor <;> intro h <;> nlinarith

theorem rateLowerCoefficient_neg_iff {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    rateLowerCoefficient k p < 0 ↔ pK k < p := by
  have hpk := pK_mem_Ioo (show 2 ≤ k by omega)
  have hnum : 0 < (1 - p) * pK k := mul_pos (sub_pos.mpr hp.2) hpk.1
  have hden : 0 < p * (1 - pK k) := mul_pos hp.1 (sub_pos.mpr hpk.2)
  rw [rateLowerCoefficient, log2_neg_iff_of_pos (div_pos hnum hden),
    div_lt_one hden]
  constructor <;> intro h <;> nlinarith

theorem rateLowerCoefficient_eq_zero_iff {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    rateLowerCoefficient k p = 0 ↔ p = pK k := by
  constructor
  · intro hzero
    rcases lt_trichotomy p (pK k) with hlt | heq | hgt
    · exact (ne_of_gt ((rateLowerCoefficient_pos_iff hk hp).2 hlt) hzero).elim
    · exact heq
    · exact (ne_of_lt ((rateLowerCoefficient_neg_iff hk hp).2 hgt) hzero).elim
  · rintro rfl
    have hpk := pK_mem_Ioo (show 2 ≤ k by omega)
    rw [rateLowerCoefficient]
    have hp0 : pK k ≠ 0 := hpk.1.ne'
    have hq0 : 1 - pK k ≠ 0 := (sub_pos.mpr hpk.2).ne'
    rw [mul_comm (1 - pK k) (pK k), div_self (mul_ne_zero hp0 hq0), log2_one]

theorem rateCoreObjective_lower_strictMonoOn {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hsub : p < pK k) :
    StrictMonoOn (rateCoreObjective k p) (Icc 0 (gammaK k)) := by
  intro a ha b hb hab
  rw [rateCoreObjective_lower_eq hk hp ha.2,
    rateCoreObjective_lower_eq hk hp hb.2]
  exact mul_lt_mul_of_pos_right hab ((rateLowerCoefficient_pos_iff hk hp).2 hsub)

theorem rateCoreObjective_lower_strictAntiOn {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p) :
    StrictAntiOn (rateCoreObjective k p) (Icc 0 (gammaK k)) := by
  intro a ha b hb hab
  rw [rateCoreObjective_lower_eq hk hp ha.2,
    rateCoreObjective_lower_eq hk hp hb.2]
  exact mul_lt_mul_of_neg_right hab ((rateLowerCoefficient_neg_iff hk hp).2 hsuper)

theorem rateCoreObjective_lower_eq_zero_of_critical {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ≤ gammaK k) :
    rateCoreObjective k (pK k) γ = 0 := by
  rw [rateCoreObjective_lower_eq hk (pK_mem_Ioo (show 2 ≤ k by omega)) hγ,
    (rateLowerCoefficient_eq_zero_iff hk
      (pK_mem_Ioo (show 2 ≤ k by omega))).2 rfl, mul_zero]

/-! ## The affine upper coordinate -/

/-- The inverse affine change of variables to `phaseLower`. -/
noncomputable def gammaFromProbability (k : ℕ) (x : ℝ) : ℝ :=
  (1 + ((k - 2 : ℕ) : ℝ) * x) / ((k - 1 : ℕ) : ℝ)

@[simp] theorem phaseLower_gammaFromProbability (k : ℕ) (hk : 3 ≤ k) (x : ℝ) :
    phaseLower k (gammaFromProbability k x) = x := by
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  rw [phaseLower, gammaFromProbability]
  field_simp [hd, hn]
  ring

@[simp] theorem gammaFromProbability_phaseLower (k : ℕ) (hk : 3 ≤ k) (γ : ℝ) :
    gammaFromProbability k (phaseLower k γ) = γ := by
  have hd : ((k - 2 : ℕ) : ℝ) ≠ 0 := (deltaK_pos hk).ne'
  have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  rw [phaseLower, gammaFromProbability]
  field_simp [hd, hn]
  ring

@[simp] theorem gammaFromProbability_pK (k : ℕ) :
    gammaFromProbability k (pK k) = gammaK k := by
  rfl

@[simp] theorem gammaFromProbability_one (k : ℕ) (hk : 3 ≤ k) :
    gammaFromProbability k 1 = 1 := by
  have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  rw [gammaFromProbability]
  field_simp [hn]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

theorem gammaFromProbability_strictMono (k : ℕ) (hk : 3 ≤ k) :
    StrictMono (gammaFromProbability k) := by
  intro x y hxy
  rw [gammaFromProbability, gammaFromProbability]
  have hd : 0 < ((k - 2 : ℕ) : ℝ) := by simpa [deltaK] using deltaK_pos hk
  apply div_lt_div_of_pos_right _ (kSubOne_pos hk)
  nlinarith [mul_lt_mul_of_pos_left hxy hd]

theorem gammaFromProbability_mem_Icc_iff {k : ℕ} (hk : 3 ≤ k) {x : ℝ} :
    x ∈ Icc (pK k) 1 ↔
      gammaFromProbability k x ∈ Icc (gammaK k) 1 := by
  let hmono := gammaFromProbability_strictMono k hk
  constructor
  · intro hx
    constructor
    · simpa only [gammaFromProbability_pK] using hmono.monotone hx.1
    · simpa only [gammaFromProbability_one k hk] using hmono.monotone hx.2
  · intro hx
    constructor
    · apply hmono.le_iff_le.mp
      simpa only [gammaFromProbability_pK] using hx.1
    · apply hmono.le_iff_le.mp
      simpa only [gammaFromProbability_one k hk] using hx.2

theorem gammaK_lt_gammaFromProbability_iff {k : ℕ} (hk : 3 ≤ k) {x : ℝ} :
    gammaK k < gammaFromProbability k x ↔ pK k < x := by
  simpa only [gammaFromProbability_pK] using
    (gammaFromProbability_strictMono k hk).lt_iff_lt (a := pK k) (b := x)

theorem gammaFromProbability_lt_one_iff {k : ℕ} (hk : 3 ≤ k) {x : ℝ} :
    gammaFromProbability k x < 1 ↔ x < 1 := by
  simpa only [gammaFromProbability_one k hk] using
    (gammaFromProbability_strictMono k hk).lt_iff_lt (a := x) (b := 1)

theorem phaseLower_le_one {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} (hγ : γ ≤ 1) :
    phaseLower k γ ≤ 1 := by
  apply (gammaFromProbability_strictMono k hk).le_iff_le.mp
  rw [gammaFromProbability_phaseLower k hk γ, gammaFromProbability_one k hk]
  exact hγ

/-! ## Calculus of the transformed upper branch -/

/-- The upper branch of the core objective in the `phaseLower` coordinate. -/
noncomputable def rateUpperObjective (k : ℕ) (p x : ℝ) : ℝ :=
  -(((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * binaryEntropy x +
    gammaFromProbability k x * log2 ((1 - p) / p)

theorem rateCoreObjective_upper_eq {k : ℕ} (hk : 3 ≤ k) {p γ : ℝ}
    (hγ : gammaK k ≤ γ) :
    rateCoreObjective k p γ = rateUpperObjective k p (phaseLower k γ) := by
  have harg :
      ((((k - 1 : ℕ) : ℝ) * γ - 1) / (k - 2 : ℕ)) = phaseLower k γ := by
    rw [phaseLower]
    ring
  rw [rateCoreObjective, entropyDensity_of_ge hk hγ, entropyDensityUpper,
    harg, ← upperScale_eq k hk, rateUpperObjective,
    gammaFromProbability_phaseLower k hk γ]
  ring

theorem rateUpperSlope_log_identity {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    log2 ((1 - p) / p) - log2 ((1 - x) / x) =
      log2 ((x * (1 - p)) / ((1 - x) * p)) := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hx0 : x ≠ 0 := hx.1.ne'
  have hy0 : 1 - x ≠ 0 := (sub_pos.mpr hx.2).ne'
  rw [log2_div hq0 hp0, log2_div hy0 hx0,
    log2_div (mul_ne_zero hx0 hq0) (mul_ne_zero hy0 hp0),
    log2_mul hx0 hq0, log2_mul hy0 hp0]
  ring

theorem hasDerivAt_rateUpperObjective {k : ℕ} (_hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (rateUpperObjective k p)
      ((((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
        log2 ((x * (1 - p)) / ((1 - x) * p))) x := by
  let a : ℝ := ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)
  let L : ℝ := log2 ((1 - p) / p)
  have hH : HasDerivAt (fun y : ℝ ↦ -a * binaryEntropy y)
      (-a * log2 ((1 - x) / x)) x :=
    (hasDerivAt_binaryEntropy hx.1 hx.2).const_mul (-a)
  have hlin : HasDerivAt
      (fun y : ℝ ↦ 1 + ((k - 2 : ℕ) : ℝ) * y)
      (((k - 2 : ℕ) : ℝ)) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul ((k - 2 : ℕ) : ℝ)).const_add 1
  have hgamma0 : HasDerivAt
      (fun y : ℝ ↦ (1 + ((k - 2 : ℕ) : ℝ) * y) / ((k - 1 : ℕ) : ℝ))
      (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) x :=
    hlin.div_const (((k - 1 : ℕ) : ℝ))
  have hgamma : HasDerivAt (gammaFromProbability k)
      (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) x := by
    change HasDerivAt
      (fun y : ℝ ↦ (1 + ((k - 2 : ℕ) : ℝ) * y) / ((k - 1 : ℕ) : ℝ))
      (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) x
    exact hgamma0
  have hsum := hH.add (hgamma.mul_const L)
  have hslope :
      -a * log2 ((1 - x) / x) +
          (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) * L =
        a * log2 ((x * (1 - p)) / ((1 - x) * p)) := by
    rw [← rateUpperSlope_log_identity hp hx]
    dsimp only [a, L]
    ring
  have hsum' := hsum.congr_deriv hslope
  change HasDerivAt
    (fun y : ℝ ↦ -a * binaryEntropy y + gammaFromProbability k y * L)
    (a * log2 ((x * (1 - p)) / ((1 - x) * p))) x at hsum'
  change HasDerivAt
    (fun y : ℝ ↦ -a * binaryEntropy y + gammaFromProbability k y * L)
    (a * log2 ((x * (1 - p)) / ((1 - x) * p))) x
  exact hsum'

theorem deriv_rateUpperObjective {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (rateUpperObjective k p) x =
      (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
        log2 ((x * (1 - p)) / ((1 - x) * p)) :=
  (hasDerivAt_rateUpperObjective hk hp hx).deriv

theorem rateUpperDerivative_neg_iff {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (rateUpperObjective k p) x < 0 ↔ x < p := by
  rw [deriv_rateUpperObjective hk hp hx]
  have ha : 0 < ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) :=
    div_pos (deltaK_pos hk) (kSubOne_pos hk)
  have hnum : 0 < x * (1 - p) := mul_pos hx.1 (sub_pos.mpr hp.2)
  have hden : 0 < (1 - x) * p := mul_pos (sub_pos.mpr hx.2) hp.1
  constructor
  · intro h
    have hlog : log2 ((x * (1 - p)) / ((1 - x) * p)) < 0 := by
      by_contra hnot
      have hnonneg : 0 ≤ log2 ((x * (1 - p)) / ((1 - x) * p)) := le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonneg ha.le hnonneg)) h
    rw [log2_neg_iff_of_pos (div_pos hnum hden), div_lt_one hden] at hlog
    nlinarith
  · intro hxp
    apply mul_neg_of_pos_of_neg ha
    rw [log2_neg_iff_of_pos (div_pos hnum hden), div_lt_one hden]
    nlinarith

theorem rateUpperDerivative_pos_iff {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < deriv (rateUpperObjective k p) x ↔ p < x := by
  rw [deriv_rateUpperObjective hk hp hx]
  have ha : 0 < ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) :=
    div_pos (deltaK_pos hk) (kSubOne_pos hk)
  have hnum : 0 < x * (1 - p) := mul_pos hx.1 (sub_pos.mpr hp.2)
  have hden : 0 < (1 - x) * p := mul_pos (sub_pos.mpr hx.2) hp.1
  constructor
  · intro h
    have hlog : 0 < log2 ((x * (1 - p)) / ((1 - x) * p)) := by
      by_contra hnot
      have hnonpos : log2 ((x * (1 - p)) / ((1 - x) * p)) ≤ 0 := le_of_not_gt hnot
      exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos ha.le hnonpos)) h
    rw [log2_pos_iff_of_pos (div_pos hnum hden), one_lt_div hden] at hlog
    nlinarith
  · intro hpx
    apply mul_pos ha
    rw [log2_pos_iff_of_pos (div_pos hnum hden), one_lt_div hden]
    nlinarith

theorem rateUpperDerivative_eq_zero_iff {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    deriv (rateUpperObjective k p) x = 0 ↔ x = p := by
  constructor
  · intro hzero
    rcases lt_trichotomy x p with hlt | heq | hgt
    · exact (ne_of_lt ((rateUpperDerivative_neg_iff hk hp hx).2 hlt) hzero).elim
    · exact heq
    · exact (ne_of_gt ((rateUpperDerivative_pos_iff hk hp hx).2 hgt) hzero).elim
  · intro hxp
    subst x
    rw [deriv_rateUpperObjective hk hp hp]
    have hp0 : p ≠ 0 := hp.1.ne'
    have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
    rw [show p * (1 - p) = (1 - p) * p by ring,
      div_self (mul_ne_zero hq0 hp0), log2_one, mul_zero]

theorem rateUpperObjective_continuousOn (k : ℕ) (p : ℝ) :
    ContinuousOn (rateUpperObjective k p) (Icc 0 1) := by
  have hgamma : Continuous (gammaFromProbability k) := by
    unfold gammaFromProbability
    fun_prop
  apply ContinuousOn.add
  · exact continuousOn_const.mul binaryEntropy_continuous.continuousOn
  · exact hgamma.continuousOn.mul continuousOn_const

theorem rateUpperObjective_strictAntiOn {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    StrictAntiOn (rateUpperObjective k p) (Icc 0 p) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 p)
  · exact (rateUpperObjective_continuousOn k p).mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans hp.2.le⟩)
  · intro x hx
    rw [interior_Icc] at hx
    exact (rateUpperDerivative_neg_iff hk hp ⟨hx.1, hx.2.trans hp.2⟩).2 hx.2

theorem rateUpperObjective_strictMonoOn {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    StrictMonoOn (rateUpperObjective k p) (Icc p 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc p 1)
  · exact (rateUpperObjective_continuousOn k p).mono (by
      intro x hx
      exact ⟨hp.1.le.trans hx.1, hx.2⟩)
  · intro x hx
    rw [interior_Icc] at hx
    exact (rateUpperDerivative_pos_iff hk hp ⟨hp.1.trans hx.1, hx.2⟩).2 hx.1

/-! ## Relative-entropy form of the upper branch -/

/-- The upper objective differs from its value at `x = p` by a positive
multiple of binary relative entropy. -/
theorem rateUpperObjective_eq_at_probability_add_relativeEntropy
    {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    rateUpperObjective k p x = rateUpperObjective k p p +
      (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
        binaryRelativeEntropy p x := by
  rw [binaryRelativeEntropy_eq_entropy_tangent hp hx]
  unfold rateUpperObjective gammaFromProbability
  have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  field_simp [hn]
  ring

/-- The reference probability is the unique minimizer of the transformed
upper objective on the probability interval. -/
theorem rateUpperObjective_minimum {k : ℕ} (hk : 3 ≤ k) {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    rateUpperObjective k p p ≤ rateUpperObjective k p x := by
  rw [rateUpperObjective_eq_at_probability_add_relativeEntropy hk hp hx]
  exact le_add_of_nonneg_right (mul_nonneg
    (div_nonneg (deltaK_pos hk).le (kSubOne_pos hk).le)
    (binaryRelativeEntropy_nonneg hp hx))

theorem rateUpperObjective_eq_minimum_iff {k : ℕ} (hk : 3 ≤ k)
    {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    rateUpperObjective k p x = rateUpperObjective k p p ↔ x = p := by
  rw [rateUpperObjective_eq_at_probability_add_relativeEntropy hk hp hx]
  have ha : ((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) ≠ 0 :=
    (div_pos (deltaK_pos hk) (kSubOne_pos hk)).ne'
  constructor
  · intro h
    have hprod :
        (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
          binaryRelativeEntropy p x = 0 := by linarith
    exact (binaryRelativeEntropy_eq_zero_iff hp hx).mp
      ((mul_eq_zero.mp hprod).resolve_left ha)
  · rintro rfl
    rw [(binaryRelativeEntropy_eq_zero_iff hp ⟨hp.1.le, hp.2.le⟩).2 rfl,
      mul_zero, add_zero]

/-- Closed form of the upper objective at its stationary probability. -/
theorem rateUpperObjective_at_probability {k : ℕ} (hk : 3 ≤ k)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    rateUpperObjective k p p =
      log2 (1 - p) - (1 / ((k - 1 : ℕ) : ℝ)) * log2 p := by
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  have hentropy :
      -binaryEntropy p + p * log2 ((1 - p) / p) = log2 (1 - p) := by
    have h := binaryEntropy_sub_mul_log2_div hp0 hp.2.ne
    linarith
  have hdn : ((k - 2 : ℕ) : ℝ) + 1 = ((k - 1 : ℕ) : ℝ) := by
    simpa [deltaK] using deltaK_add_one hk
  calc
    rateUpperObjective k p p =
        (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
            (-binaryEntropy p + p * log2 ((1 - p) / p)) +
          (1 / ((k - 1 : ℕ) : ℝ)) * log2 ((1 - p) / p) := by
      unfold rateUpperObjective gammaFromProbability
      ring
    _ = (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
            log2 (1 - p) +
          (1 / ((k - 1 : ℕ) : ℝ)) * log2 ((1 - p) / p) := by
      rw [hentropy]
    _ = log2 (1 - p) -
          (1 / ((k - 1 : ℕ) : ℝ)) * log2 p := by
      rw [log2_div hq0 hp0]
      have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
      field_simp [hn]
      rw [← hdn]
      ring

theorem phaseLower_mem_Icc_iff {k : ℕ} (hk : 3 ≤ k) {γ : ℝ} :
    phaseLower k γ ∈ Icc (pK k) 1 ↔ γ ∈ Icc (gammaK k) 1 := by
  rw [gammaFromProbability_mem_Icc_iff hk]
  simp only [gammaFromProbability_phaseLower k hk γ]

/-- The supercritical stationary density lies strictly between the phase
boundary and one. -/
theorem gammaFromProbability_mem_Ioo {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hsuper : pK k < p) (hp1 : p < 1) :
    gammaFromProbability k p ∈ Ioo (gammaK k) 1 :=
  ⟨(gammaK_lt_gammaFromProbability_iff hk).2 hsuper,
    (gammaFromProbability_lt_one_iff hk).2 hp1⟩

/-- Relative-entropy formula for the full rate on the upper branch. -/
theorem rateAtDensity_gammaFromProbability_eq {k : ℕ} (hk : 3 ≤ k)
    {p x : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (pK k) 1) :
    rateAtDensity k p (gammaFromProbability k x) =
      (1 / ((k - 1 : ℕ) : ℝ)) * log2 (1 / p) +
        (((k - 2 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) *
          binaryRelativeEntropy p x := by
  have hγ := (gammaFromProbability_mem_Icc_iff hk).1 hx
  rw [rateAtDensity, rateCoreObjective_upper_eq hk hγ.1,
    phaseLower_gammaFromProbability k hk x,
    binaryRelativeEntropy_eq_negEntropy_add hp
      ⟨(pK_mem_Icc k).1.trans hx.1, hx.2⟩]
  unfold rateUpperObjective gammaFromProbability
  have hloginv : log2 (1 / p) = -log2 p := by
    rw [one_div, log2_inv]
  rw [hloginv]
  have hp0 : p ≠ 0 := hp.1.ne'
  have hq0 : 1 - p ≠ 0 := (sub_pos.mpr hp.2).ne'
  rw [log2_div hq0 hp0]
  have hn : ((k - 1 : ℕ) : ℝ) ≠ 0 := (kSubOne_pos hk).ne'
  have hdn : ((k - 2 : ℕ) : ℝ) + 1 = ((k - 1 : ℕ) : ℝ) := by
    simpa [deltaK] using deltaK_add_one hk
  field_simp [hn]
  rw [← hdn]
  ring

/-! ## Exact minimization in the three probability regimes -/

/-- Below the critical probability, the core objective is nonnegative and
vanishes only at density zero. -/
theorem rateCoreObjective_subcritical_minimization {k : ℕ} (hk : 3 ≤ k)
    {p γ : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hsub : p < pK k)
    (hγ : γ ∈ Icc (0 : ℝ) 1) :
    0 ≤ rateCoreObjective k p γ ∧
      (rateCoreObjective k p γ = 0 ↔ γ = 0) := by
  by_cases hlow : γ ≤ gammaK k
  · rw [rateCoreObjective_lower_eq hk hp hlow]
    have hc : 0 < rateLowerCoefficient k p :=
      (rateLowerCoefficient_pos_iff hk hp).2 hsub
    constructor
    · exact mul_nonneg hγ.1 hc.le
    · constructor
      · intro hzero
        exact (mul_eq_zero.mp hzero).resolve_right hc.ne'
      · rintro rfl
        simp
  · have hupper : gammaK k < γ := lt_of_not_ge hlow
    have hx : phaseLower k γ ∈ Icc (pK k) 1 :=
      (phaseLower_mem_Icc_iff hk).2 ⟨hupper.le, hγ.2⟩
    have hpkMem : pK k ∈ Icc p 1 :=
      ⟨hsub.le, (pK_mem_Icc k).2⟩
    have hxMem : phaseLower k γ ∈ Icc p 1 :=
      ⟨hsub.le.trans hx.1, hx.2⟩
    have hstrict : rateUpperObjective k p (pK k) <
        rateUpperObjective k p (phaseLower k γ) :=
      rateUpperObjective_strictMonoOn hk hp hpkMem hxMem
        ((pK_lt_phaseLower_iff hk γ).2 hupper)
    have hjunction : 0 < rateUpperObjective k p (pK k) := by
      have hcore : 0 < rateCoreObjective k p (gammaK k) := by
        rw [rateCoreObjective_lower_eq hk hp le_rfl]
        exact mul_pos (gammaK_pos hk)
          ((rateLowerCoefficient_pos_iff hk hp).2 hsub)
      have hjoin : rateCoreObjective k p (gammaK k) =
          rateUpperObjective k p (pK k) := by
        simpa only [phaseLower_at_gammaK k hk] using
          (rateCoreObjective_upper_eq (p := p) hk (le_refl (gammaK k)))
      rwa [hjoin] at hcore
    have hpos : 0 < rateCoreObjective k p γ := by
      rw [rateCoreObjective_upper_eq hk hupper.le]
      exact hjunction.trans hstrict
    constructor
    · exact hpos.le
    · constructor
      · exact fun hzero ↦ (hpos.ne' hzero).elim
      · intro hzero
        subst γ
        exact (not_lt_of_ge (gammaK_pos hk).le hupper).elim

/-- At the critical probability, exactly the whole lower-density interval
minimizes the core objective. -/
theorem rateCoreObjective_critical_minimization {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) :
    0 ≤ rateCoreObjective k (pK k) γ ∧
      (rateCoreObjective k (pK k) γ = 0 ↔
        γ ∈ Icc (0 : ℝ) (gammaK k)) := by
  by_cases hlow : γ ≤ gammaK k
  · have hzero := rateCoreObjective_lower_eq_zero_of_critical hk hlow
    constructor
    · rw [hzero]
    · constructor
      · exact fun _ ↦ ⟨hγ.1, hlow⟩
      · exact fun _ ↦ hzero
  · have hupper : gammaK k < γ := lt_of_not_ge hlow
    have hp := pK_mem_Ioo (show 2 ≤ k by omega)
    have hx : phaseLower k γ ∈ Icc (pK k) 1 :=
      (phaseLower_mem_Icc_iff hk).2 ⟨hupper.le, hγ.2⟩
    have hstrict : rateUpperObjective k (pK k) (pK k) <
        rateUpperObjective k (pK k) (phaseLower k γ) :=
      rateUpperObjective_strictMonoOn hk hp
        ⟨le_rfl, (pK_mem_Icc k).2⟩ hx
        ((pK_lt_phaseLower_iff hk γ).2 hupper)
    have hjunction : rateUpperObjective k (pK k) (pK k) = 0 := by
      have hjoin : rateCoreObjective k (pK k) (gammaK k) =
          rateUpperObjective k (pK k) (pK k) := by
        simpa only [phaseLower_at_gammaK k hk] using
          (rateCoreObjective_upper_eq (p := pK k) hk (le_refl (gammaK k)))
      rw [← hjoin, rateCoreObjective_lower_eq_zero_of_critical hk le_rfl]
    have hpos : 0 < rateCoreObjective k (pK k) γ := by
      rw [rateCoreObjective_upper_eq hk hupper.le, ← hjunction]
      exact hstrict
    constructor
    · exact hpos.le
    · constructor
      · exact fun hzero ↦ (hpos.ne' hzero).elim
      · intro hmem
        exact (not_lt_of_ge hmem.2 hupper).elim

/-- Above the critical probability, the core objective has the unique
minimizer `gammaFromProbability k p`. -/
theorem rateCoreObjective_supercritical_minimization {k : ℕ} (hk : 3 ≤ k)
    {p γ : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p)
    (hγ : γ ∈ Icc (0 : ℝ) 1) :
    rateCoreObjective k p (gammaFromProbability k p) ≤
        rateCoreObjective k p γ ∧
      (rateCoreObjective k p γ =
          rateCoreObjective k p (gammaFromProbability k p) ↔
        γ = gammaFromProbability k p) := by
  have hγp := gammaFromProbability_mem_Ioo hk hsuper hp.2
  have hcoreP : rateCoreObjective k p (gammaFromProbability k p) =
      rateUpperObjective k p p := by
    rw [rateCoreObjective_upper_eq hk hγp.1.le,
      phaseLower_gammaFromProbability k hk p]
  by_cases hlow : γ ≤ gammaK k
  · have hc : rateLowerCoefficient k p < 0 :=
      (rateLowerCoefficient_neg_iff hk hp).2 hsuper
    have htoJunction : rateCoreObjective k p (gammaK k) ≤
        rateCoreObjective k p γ := by
      rw [rateCoreObjective_lower_eq hk hp le_rfl,
        rateCoreObjective_lower_eq hk hp hlow]
      exact mul_le_mul_of_nonpos_right hlow hc.le
    have hjoin : rateCoreObjective k p (gammaK k) =
        rateUpperObjective k p (pK k) := by
      simpa only [phaseLower_at_gammaK k hk] using
        (rateCoreObjective_upper_eq (p := p) hk (le_refl (gammaK k)))
    have hstrictUpper : rateUpperObjective k p p <
        rateUpperObjective k p (pK k) :=
      rateUpperObjective_strictAntiOn hk hp
        ⟨(pK_mem_Icc k).1, hsuper.le⟩ ⟨hp.1.le, le_rfl⟩ hsuper
    have hstrict : rateCoreObjective k p (gammaFromProbability k p) <
        rateCoreObjective k p γ := by
      calc
        rateCoreObjective k p (gammaFromProbability k p) =
            rateUpperObjective k p p := hcoreP
        _ < rateUpperObjective k p (pK k) := hstrictUpper
        _ = rateCoreObjective k p (gammaK k) := hjoin.symm
        _ ≤ rateCoreObjective k p γ := htoJunction
    constructor
    · exact hstrict.le
    · constructor
      · exact fun heq ↦ (hstrict.ne' heq).elim
      · rintro rfl
        rfl
  · have hupper : gammaK k ≤ γ := le_of_not_ge hlow
    have hx : phaseLower k γ ∈ Icc (pK k) 1 :=
      (phaseLower_mem_Icc_iff hk).2 ⟨hupper, hγ.2⟩
    have hx01 : phaseLower k γ ∈ Icc (0 : ℝ) 1 :=
      ⟨(pK_mem_Icc k).1.trans hx.1, hx.2⟩
    have hcoreγ : rateCoreObjective k p γ =
        rateUpperObjective k p (phaseLower k γ) :=
      rateCoreObjective_upper_eq hk hupper
    constructor
    · rw [hcoreP, hcoreγ]
      exact rateUpperObjective_minimum hk hp hx01
    · rw [hcoreP, hcoreγ]
      constructor
      · intro heq
        have hxEq := (rateUpperObjective_eq_minimum_iff hk hp hx01).mp heq
        have := congrArg (gammaFromProbability k) hxEq
        simpa only [gammaFromProbability_phaseLower k hk γ] using this
      · rintro rfl
        rw [phaseLower_gammaFromProbability k hk p]

/-! ## The full rate and the published piecewise rate function -/

theorem rateFunction_eq_neg_log2_one_sub_of_le_pK {k : ℕ} {p : ℝ}
    (hp : p ≤ pK k) :
    rateFunction k p = -log2 (1 - p) := by
  rw [rateFunction_of_le hp, one_div, log2_inv]

/-- The lower closed form of `rateFunction`, with the branch condition named
as in the fixed-density variational statement. -/
theorem rateFunction_of_le_pK {k : ℕ} {p : ℝ} (hp : p ≤ pK k) :
    rateFunction k p = log2 (1 / (1 - p)) :=
  rateFunction_of_le hp

theorem rateFunction_of_lt_pK {k : ℕ} {p : ℝ} (hp : p < pK k) :
    rateFunction k p = log2 (1 / (1 - p)) :=
  rateFunction_of_le hp.le

@[simp] theorem rateFunction_at_pK (k : ℕ) :
    rateFunction k (pK k) = log2 (1 / (1 - pK k)) :=
  rateFunction_of_le le_rfl

/-- The upper closed form of `rateFunction` above the phase transition. -/
theorem rateFunction_of_pK_lt {k : ℕ} (hk : 3 ≤ k) {p : ℝ}
    (hp : pK k < p) :
    rateFunction k p =
      (1 / ((k - 1 : ℕ) : ℝ)) * log2 (1 / p) :=
  rateFunction_of_ge (show 2 ≤ k by omega) hp.le

@[simp] theorem rateFunction_at_pK_eq_neg_log2_one_sub (k : ℕ) :
    rateFunction k (pK k) = -log2 (1 - pK k) :=
  rateFunction_eq_neg_log2_one_sub_of_le_pK le_rfl

theorem rateAtDensity_gammaFromProbability_eq_rateFunction {k : ℕ}
    (hk : 3 ≤ k) {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hsuper : pK k < p) :
    rateAtDensity k p (gammaFromProbability k p) = rateFunction k p := by
  rw [rateAtDensity_gammaFromProbability_eq hk hp
      ⟨hsuper.le, hp.2.le⟩,
    (binaryRelativeEntropy_eq_zero_iff hp ⟨hp.1.le, hp.2.le⟩).2 rfl,
    mul_zero, add_zero, rateFunction_of_pK_lt hk hsuper]

/-- Exact scalar minimization below the critical probability. -/
theorem rateAtDensity_subcritical_minimization {k : ℕ} (hk : 3 ≤ k)
    {p γ : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hsub : p < pK k)
    (hγ : γ ∈ Icc (0 : ℝ) 1) :
    rateFunction k p ≤ rateAtDensity k p γ ∧
      (rateAtDensity k p γ = rateFunction k p ↔ γ = 0) := by
  have hcore := rateCoreObjective_subcritical_minimization hk hp hsub hγ
  rw [rateFunction_eq_neg_log2_one_sub_of_le_pK hsub.le, rateAtDensity]
  constructor
  · linarith [hcore.1]
  · constructor
    · intro heq
      apply hcore.2.mp
      linarith
    · intro hzero
      have := hcore.2.mpr hzero
      linarith

/-- Exact scalar minimization at the critical probability. -/
theorem rateAtDensity_critical_minimization {k : ℕ} (hk : 3 ≤ k)
    {γ : ℝ} (hγ : γ ∈ Icc (0 : ℝ) 1) :
    rateFunction k (pK k) ≤ rateAtDensity k (pK k) γ ∧
      (rateAtDensity k (pK k) γ = rateFunction k (pK k) ↔
        γ ∈ Icc (0 : ℝ) (gammaK k)) := by
  have hcore := rateCoreObjective_critical_minimization hk hγ
  rw [rateFunction_at_pK_eq_neg_log2_one_sub, rateAtDensity]
  constructor
  · linarith [hcore.1]
  · constructor
    · intro heq
      apply hcore.2.mp
      linarith
    · intro hmem
      have := hcore.2.mpr hmem
      linarith

/-- Exact scalar minimization above the critical probability. -/
theorem rateAtDensity_supercritical_minimization {k : ℕ} (hk : 3 ≤ k)
    {p γ : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (hsuper : pK k < p)
    (hγ : γ ∈ Icc (0 : ℝ) 1) :
    rateFunction k p ≤ rateAtDensity k p γ ∧
      (rateAtDensity k p γ = rateFunction k p ↔
        γ = gammaFromProbability k p) := by
  have hcore := rateCoreObjective_supercritical_minimization hk hp hsuper hγ
  have hvalue := rateAtDensity_gammaFromProbability_eq_rateFunction hk hp hsuper
  constructor
  · rw [← hvalue]
    unfold rateAtDensity
    linarith [hcore.1]
  · constructor
    · intro heq
      apply hcore.2.mp
      unfold rateAtDensity at heq hvalue
      linarith
    · intro hγeq
      rw [hγeq, hvalue]

/-- Paper Lemma `lemma:rate-scalar-minimization`: the explicit rate is the
minimum over edge densities, with the complete equality classification. -/
theorem rateScalarMinimization
    (k : ℕ) (hk : 3 ≤ k) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    (∀ γ ∈ Icc (0 : ℝ) 1,
      rateFunction k p ≤ rateAtDensity k p γ) ∧
    (∀ γ ∈ Icc (0 : ℝ) 1,
      rateAtDensity k p γ = rateFunction k p ↔
        if p < pK k then
          γ = 0
        else if p = pK k then
          γ ∈ Icc (0 : ℝ) (gammaK k)
        else
          γ = gammaFromProbability k p) := by
  constructor
  · intro γ hγ
    rcases lt_trichotomy p (pK k) with hsub | hcrit | hsuper
    · exact (rateAtDensity_subcritical_minimization hk hp hsub hγ).1
    · subst p
      exact (rateAtDensity_critical_minimization hk hγ).1
    · exact (rateAtDensity_supercritical_minimization hk hp hsuper hγ).1
  · intro γ hγ
    by_cases hsub : p < pK k
    · simpa [hsub] using
        (rateAtDensity_subcritical_minimization hk hp hsub hγ).2
    · by_cases hcrit : p = pK k
      · subst p
        simpa [hsub] using (rateAtDensity_critical_minimization hk hγ).2
      · have hsuper : pK k < p :=
          lt_of_le_of_ne (le_of_not_gt hsub) (Ne.symm hcrit)
        simpa [hsub, hcrit] using
          (rateAtDensity_supercritical_minimization hk hp hsuper hγ).2

end InducedStars
