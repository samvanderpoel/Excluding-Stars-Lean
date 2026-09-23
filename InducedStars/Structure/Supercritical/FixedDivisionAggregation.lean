import InducedStars.Structure.Supercritical.FixedSupportAggregation

/-!
# Divisionwise aggregation of the supercritical fixed-defect family

This module pays the entropy and signed-shift overhead of the
support-incident defect patterns, then sums their positive matching numbers.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedDivisionAggregationGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Uniform support-pattern overhead -/

/-- The explicit support-pattern encoding costs at most one eighth of the
matching exponent selected by the common parameter package. -/
theorem eventually_card_supercriticalLowSupportPatternFinset_le_exp
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (P : SupercriticalAggregationParameters k gamma) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (h : ℕ),
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      0 < h →
      ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) ≤
        Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto ht).bound
    (show 0 < P.cMat / 64 by exact div_pos P.cMat_pos (by norm_num))
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ 3 * P.alpha * (n : ℝ) := by
    have hgrow : Tendsto (fun n : ℕ ↦ 3 * P.alpha * (n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (mul_pos (by norm_num) P.alpha_pos)
    exact hgrow.eventually (eventually_ge_atTop 1)
  filter_upwards [hlog, hlarge, eventually_ge_atTop 1]
      with n hlogN hlargeN hn
  intro D h hsparse hh
  let b : ℕ := ⌊3 * P.alpha * (n : ℝ)⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < b := by
    exact Nat.floor_pos.mpr hlargeN
  have hbReal : (b : ℝ) ≤ 3 * P.alpha * (n : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hSix : 6 * P.alpha < 1 := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hkPos : (0 : ℝ) < k := by positivity
    have halpha : P.alpha * (100 * (k : ℝ)) < 1 := by
      have h := P.alpha_lt
      rwa [lt_div_iff₀ (by positivity)] at h
    have hscale : (300 : ℝ) ≤ 100 * (k : ℝ) := by nlinarith
    have hmul : P.alpha * 300 ≤ P.alpha * (100 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale P.alpha_pos.le
    linarith
  have hhalf : 2 * b ≤ n := by
    have hreal : (2 : ℝ) * b ≤ n := by
      have hn0 : (0 : ℝ) ≤ n := hnR.le
      have hSixMul := mul_le_mul_of_nonneg_right hSix.le hn0
      nlinarith [hbReal, hSixMul]
    exact_mod_cast hreal
  have hdegree : ∀ T ∈ supercriticalLowSupportPatternFinset
      D P.alpha h, ∀ v : Fin n,
      degreeInFinset T v Finset.univ ≤ b := by
    intro T hT v
    have hmem := mem_supercriticalLowSupportPatternFinset.mp hT
    have hdeg := supercriticalSupportPattern_degree_real_le D T
      P.alpha_pos.le P.delta_pos.le hmem.2.2.2 hsparse v
    have hreal : (degreeInFinset T v Finset.univ : ℝ) ≤
        3 * P.alpha * (n : ℝ) := by
      have had : P.alpha + P.delta ≤ 3 * P.alpha := by
        linarith [P.delta_lt_alpha, P.alpha_pos]
      exact hdeg.trans (mul_le_mul_of_nonneg_right had (by positivity))
    by_cases hz : degreeInFinset T v Finset.univ = 0
    · simp [hz]
    · exact (Nat.le_floor_iff' hz).2 hreal
  have hq0 : (0 : ℝ) ≤ (b : ℝ) / (n : ℝ) := by positivity
  have hqle : (b : ℝ) / (n : ℝ) ≤ 3 * P.alpha := by
    rw [div_le_iff₀ hnR]
    simpa [mul_assoc] using hbReal
  have hthreeHalf : 3 * P.alpha ≤ (2 : ℝ)⁻¹ := by
    have := hSix.le
    norm_num at ⊢
    linarith
  have hqhalf : (b : ℝ) / (n : ℝ) ≤ (2 : ℝ)⁻¹ :=
    hqle.trans hthreeHalf
  have hbin := Real.binEntropy_strictMonoOn.monotoneOn
    ⟨hq0, hqhalf⟩ ⟨by nlinarith [P.alpha_pos], hthreeHalf⟩ hqle
  have hentropy : binaryEntropy ((b : ℝ) / (n : ℝ)) ≤
      binaryEntropy (3 * P.alpha) + P.delta := by
    unfold binaryEntropy
    have hdiv : Real.binEntropy ((b : ℝ) / (n : ℝ)) /
        Real.log 2 ≤ Real.binEntropy (3 * P.alpha) / Real.log 2 :=
      (div_le_div_iff_of_pos_right realLogTwo_pos).2 hbin
    linarith [P.delta_pos]
  have hcount := card_supercriticalLowSupportPatternFinset_real_le_exp
    D P.alpha P.delta h b (by omega) hh hb hhalf hdegree hentropy
  have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 1) := by
    exact Real.log_nonneg (by linarith)
  have hlogBound : Real.log (((n + 1 : ℕ) : ℝ)) ≤
      (P.cMat / 32) * (n : ℝ) := by
    dsimp [Function.comp_def, id] at hlogN
    rw [abs_of_nonneg hlogNonneg,
      abs_of_nonneg (by positivity)] at hlogN
    norm_num at hlogN ⊢
    have hnTwo : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    calc
      Real.log ((n : ℝ) + 1) ≤
          (P.cMat / 64) * ((n : ℝ) + 1) := hlogN
      _ ≤ (P.cMat / 64) * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnTwo
          (div_nonneg P.cMat_pos.le (by norm_num))
      _ = (P.cMat / 32) * (n : ℝ) := by ring
  let x := binaryEntropy (3 * P.alpha) + P.delta
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact add_nonneg
      (binaryEntropy_nonneg (by nlinarith [P.alpha_pos])
        (hthreeHalf.trans (by norm_num)))
      P.delta_pos.le
  have hlogTwo0 : 0 ≤ Real.log 2 := realLogTwo_pos.le
  have hlogTwo1 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hentropyCoeff : 2 * x * Real.log 2 < P.cMat / 16 := by
    have hsmall : 2 * (k : ℝ) * x < P.cMat / 16 := by
      have h := P.support_overhead_small
      unfold supercriticalSupportPatternBudgetRate at h
      nlinarith
    have hxk : 2 * x ≤ 2 * (k : ℝ) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkOne) hx0]
    calc
      2 * x * Real.log 2 ≤ 2 * x * 1 := by
        exact mul_le_mul_of_nonneg_left hlogTwo1 (by positivity)
      _ ≤ 2 * (k : ℝ) * x := by simpa using hxk
      _ < P.cMat / 16 := hsmall
  apply hcount.trans
  apply Real.exp_le_exp.mpr
  have hlogCost :
      2 * (h : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) ≤
        (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by
    calc
      2 * (h : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) ≤
          2 * (h : ℝ) * ((P.cMat / 32) * (n : ℝ)) := by
        gcongr
      _ = (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by ring
  have hentropyCost :
      (2 * (h : ℝ) * (n : ℝ)) * x * Real.log 2 ≤
        (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by
    have hnonneg : 0 ≤ (h : ℝ) * (n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hentropyCoeff.le hnonneg
    dsimp [x] at hmul ⊢
    nlinarith
  dsimp [x] at hentropyCost
  nlinarith

end InducedStars
