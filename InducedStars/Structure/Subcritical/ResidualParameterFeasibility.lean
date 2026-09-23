import InducedStars.Structure.Subcritical.ResidualMatchingWeight

/-!
# Ordered feasibility of the residual matching reserves

The positive probability rate and geometric degree cap are fixed first.
The cutoff theta precedes alpha, delta, epsilon and the graph order. Each
stage accepts arbitrary earlier positive upper bounds. This does not yet
intersect the residual hierarchy with the local-compensation hierarchy.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace InducedStars

/-- The order-independent part of the enumeration coefficient. -/
def subcriticalResidualEnumerationBase (k : ℕ) (d : ℝ) : ℝ :=
  2 * (Real.binEntropy d + subcriticalResidualWeightConstant k * d)

theorem subcriticalResidualEnumerationCoefficient_eq_base_add
    (k n : ℕ) (alpha theta : ℝ) :
    subcriticalResidualEnumerationCoefficient k alpha theta n =
      subcriticalResidualEnumerationBase k (subcriticalResidualDegreeCoefficient k alpha theta) +
        2 * Real.log (n + 1) / n := by
  unfold subcriticalResidualEnumerationCoefficient subcriticalResidualEnumerationBase
  ring

/-- A closed positive degree interval on which the entropy cost is small.
Only continuity of natural binary entropy at zero is used. -/
theorem exists_subcriticalResidualDegreeRadius
    (k : ℕ) (c dCap : ℝ) (hc : 0 < c) (hCap : 0 < dCap) :
    ∃ b : ℝ, 0 < b ∧ b ≤ min (1 / 2) dCap ∧
      ∀ d ∈ Icc (0 : ℝ) b, subcriticalResidualEnumerationBase k d ≤ c / 4 := by
  have hcont : ContinuousAt (subcriticalResidualEnumerationBase k) 0 := by
    unfold subcriticalResidualEnumerationBase
    fun_prop
  have ht : Tendsto (subcriticalResidualEnumerationBase k) (𝓝 0) (𝓝 0) := by
    simpa only [subcriticalResidualEnumerationBase, Real.binEntropy_zero,
      mul_zero, add_zero] using hcont.tendsto
  have he := ht.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 4))
  obtain ⟨r, hr, he⟩ := Metric.eventually_nhds_iff.mp he
  let b := min (r / 2) (min (1 / 2) dCap)
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨b, hb, min_le_right _ _, ?_⟩
  intro d hd
  apply le_of_lt (he ?_)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hd.1]
  have hbr : b ≤ r / 2 := min_le_left _ _
  linarith [hd.2]

theorem subcriticalResidual_logOrder_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) / n) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  convert (Real.tendsto_pow_log_div_mul_add_atTop (1 : ℝ) (-1) 1 one_ne_zero).comp harg using 1
  funext n
  simp only [Function.comp_apply, pow_one, one_mul, add_neg_cancel_right]

/-- The finite order thresholds are synchronized only after all small
parameters have been chosen. No order restriction is hidden in an `o(1)`. -/
theorem eventually_subcriticalResidualNumericalReserves
    (k : ℕ) (c lambda theta alpha : ℝ)
    (hc : 0 < c) (hlambda : 0 < lambda) (htheta : 0 < theta)
    (hbase : subcriticalResidualEnumerationBase k
      (subcriticalResidualDegreeCoefficient k alpha theta) ≤ c / 4) :
    ∀ᶠ n : ℕ in atTop,
      subcriticalResidualEnumerationCoefficient k alpha theta n ≤ c / 2 ∧
      16 ≤ lambda * n ∧ 1 ≤ theta * n ∧ c ≤ n + 1 ∧ 0 < n := by
  have hlog := subcriticalResidual_logOrder_tendsto_zero.eventually
    (Iio_mem_nhds (by positivity : (0 : ℝ) < c / 8))
  have hlarge (B : ℝ) : ∀ᶠ n : ℕ in atTop, B ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop B)
  filter_upwards [hlog, hlarge (16 / lambda), hlarge (1 / theta), hlarge c, hlarge 1]
    with n hnLog hnLambda hnTheta hnC hnOne
  refine ⟨?_, ?_, ?_, by linarith, ?_⟩
  · rw [subcriticalResidualEnumerationCoefficient_eq_base_add]
    rw [mul_div_assoc]
    change Real.log ((n : ℝ) + 1) / n < c / 8 at hnLog
    linarith only [hnLog, hbase]
  · simpa only [mul_comm] using (div_le_iff₀ hlambda).mp hnLambda
  · simpa only [mul_comm] using (div_le_iff₀ htheta).mp hnTheta
  · have hh : (0 : ℝ) < n := by linarith
    exact_mod_cast hh

set_option maxHeartbeats 600000 in
-- The nested hierarchy keeps all arbitrary prior caps in one explicit theorem.
/-- Residual matching hierarchy, with the rate `c`, geometric cap `dCap`,
room parameter `lambda` and atom band `rho` fixed before theta and alpha.
The arbitrary alpha, delta and epsilon caps are quantified at their own
stages. Root trimming uses exactly `2 * epsilon / (alpha * theta)`.
The weighted residual entropy bound introduces no change to this parameter order. -/
theorem exists_subcriticalResidualParameterHierarchy
    (k : ℕ) (c dCap lambda rho thetaMax : ℝ)
    (hc : 0 < c) (hCap : 0 < dCap) (hlambda : 0 < lambda) (hrho : 0 < rho)
    (hthetaMax : 0 < thetaMax) :
    ∃ theta : ℝ, 0 < theta ∧ theta ≤ thetaMax ∧
      ∀ alphaMax : ℝ, 0 < alphaMax →
      ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ alphaMax ∧
        subcriticalResidualDegreeCoefficient k alpha theta ≤ min (1 / 2) dCap ∧
        subcriticalResidualEnumerationBase k (subcriticalResidualDegreeCoefficient k alpha theta)
          ≤ c / 4 ∧
        ∀ deltaMax : ℝ, 0 < deltaMax →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaMax ∧ delta ≤ rho / 2 ∧
          ∀ epsilonMax : ℝ, 0 < epsilonMax →
          ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ epsilonMax ∧ epsilon ≤ theta ^ 2 ∧
            subcriticalProfileRootFraction alpha theta epsilon ≤ lambda / 2 ∧
            ∀ᶠ n : ℕ in atTop,
              subcriticalResidualEnumerationCoefficient k alpha theta n ≤ c / 2 ∧
              16 ≤ lambda * n ∧ 1 ≤ theta * n ∧ c ≤ n + 1 ∧ 0 < n := by
  obtain ⟨b, hb, hbCap, hbCost⟩ := exists_subcriticalResidualDegreeRadius k c dCap hc hCap
  have hC : 0 ≤ subcriticalSparseSideConstant k := by
    unfold subcriticalSparseSideConstant
    positivity
  have hden : 0 < 4 * (subcriticalSparseSideConstant k + 1) := by positivity
  let thetaBound := min thetaMax (b / (4 * (subcriticalSparseSideConstant k + 1)))
  have htb : 0 < thetaBound := by dsimp [thetaBound]; positivity
  let theta := thetaBound / 2
  have ht : 0 < theta := by dsimp [theta]; positivity
  have httb : theta ≤ thetaBound := by dsimp [theta]; linarith only [htb]
  have htBounds : theta ≤ thetaMax ∧ theta ≤ b / (4 * (subcriticalSparseSideConstant k + 1)) := by
    simpa only [thetaBound, le_min_iff] using httb
  have hCtheta : subcriticalSparseSideConstant k * theta ≤ b / 4 := by
    have hh := (le_div_iff₀ hden).mp htBounds.2
    nlinarith only [hh, ht]
  refine ⟨theta, ht, htBounds.1, ?_⟩
  intro alphaMax haMax
  let alphaBound := min alphaMax (b / 16)
  have hab : 0 < alphaBound := by dsimp [alphaBound]; positivity
  let alpha := alphaBound / 2
  have ha : 0 < alpha := by dsimp [alpha]; positivity
  have haab : alpha ≤ alphaBound := by dsimp [alpha]; linarith only [hab]
  have haBounds : alpha ≤ alphaMax ∧ alpha ≤ b / 16 := by
    simpa only [alphaBound, le_min_iff] using haab
  have hD : subcriticalResidualDegreeCoefficient k alpha theta ∈ Icc (0 : ℝ) b := by
    refine ⟨subcriticalResidualDegreeCoefficient_nonneg k ha.le ht.le, ?_⟩
    unfold subcriticalResidualDegreeCoefficient
    linarith only [hCtheta, haBounds.2, hb]
  have hcost := hbCost _ hD
  refine ⟨alpha, ha, haBounds.1, hD.2.trans hbCap, hcost, ?_⟩
  intro deltaMax hdMax
  let deltaBound := min deltaMax (rho / 2)
  have hdb : 0 < deltaBound := by dsimp [deltaBound]; positivity
  let delta := deltaBound / 2
  have hd : 0 < delta := by dsimp [delta]; positivity
  have hddb : delta ≤ deltaBound := by dsimp [delta]; linarith only [hdb]
  have hdBounds : delta ≤ deltaMax ∧ delta ≤ rho / 2 := by
    simpa only [deltaBound, le_min_iff] using hddb
  refine ⟨delta, hd, hdBounds.1, hdBounds.2, ?_⟩
  intro epsilonMax heMax
  let epsilonBound := min epsilonMax (min (theta ^ 2) (lambda * alpha * theta / 4))
  have heb : 0 < epsilonBound := by dsimp [epsilonBound]; positivity
  let epsilon := epsilonBound / 2
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have heeb : epsilon ≤ epsilonBound := by dsimp [epsilon]; linarith only [heb]
  have heBounds : epsilon ≤ epsilonMax ∧ epsilon ≤ theta ^ 2 ∧
      epsilon ≤ lambda * alpha * theta / 4 := by
    simpa only [epsilonBound, le_min_iff] using heeb
  refine ⟨epsilon, he, heBounds.1, heBounds.2.1, ?_,
    eventually_subcriticalResidualNumericalReserves k c lambda theta alpha hc hlambda ht hcost⟩
  unfold subcriticalProfileRootFraction
  apply (div_le_iff₀ (mul_pos ha ht)).mpr
  nlinarith only [heBounds.2.2]

end InducedStars
