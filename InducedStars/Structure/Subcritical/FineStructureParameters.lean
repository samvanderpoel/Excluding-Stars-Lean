import InducedStars.Structure.Subcritical.GroupedUpperBound
import InducedStars.Structure.Subcritical.DistinguishedDenominatorShift
import InducedStars.Structure.Subcritical.DistinguishedReference

/-!
# One hierarchy for exact subcritical structure

The lower-edge coefficient is deliberately absent from this accuracy-dependent
package. It was fixed from k and gamma in RemainderMatchingParameters.
All fields below are scalar reserves or the already proved finite hierarchy.
-/

noncomputable section
open Filter Set
namespace InducedStars

structure SubcriticalFineStructureParameters (k : ℕ) (gamma xi : ℝ) where
  eta : ℝ
  theta : ℝ
  alpha : ℝ
  delta : ℝ
  epsilon : ℝ
  R₀ : ℕ
  eta_pos : 0 < eta
  eta_one : eta ≤ 1
  theta_pos : 0 < theta
  alpha_pos : 0 < alpha
  delta_pos : 0 < delta
  epsilon_pos : 0 < epsilon
  order_one : 1 ≤ R₀
  order_star : k - 1 ≤ R₀
  size_reserve : eta + delta ≤ subcriticalOneBlockLength k gamma
  delta_mu : delta ≤ subcriticalOneBlockLength k gamma / 2
  delta_remainder : delta ≤ (1 - subcriticalOneBlockLength k gamma) / 2
  variance_reserve : delta ≤ (1 - pK k) *
    (subcriticalOneBlockLength k gamma / (4 * (k - 1 : ℕ))) ^ 2 / 10
  shift_reserve : delta ≤ subcriticalReferenceShiftBand k / 2
  support_reserve : subcriticalSparseSideConstant k * eta <
    (subcriticalOneBlockLength k gamma / (4 * (k - 1 : ℕ))) ^ 2 / 4
  size_accuracy : delta ≤ xi
  edge_accuracy : subcriticalSparseSideConstant k * eta ≤ xi
  aggregation : ∀ᶠ n : ℕ in atTop,
    SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n

/-- Every positive accuracy admits the full previously proved hierarchy,
simultaneously with the support-identification and matching reserves. -/
theorem exists_subcriticalFineStructureParameters {k : ℕ} (hk : 3 ≤ k)
    {gamma xi : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hxi : 0 < xi) :
    Nonempty (SubcriticalFineStructureParameters k gamma xi) := by
  let mu := subcriticalOneBlockLength k gamma
  let a := mu / (4 * (k - 1 : ℕ))
  let C := subcriticalSparseSideConstant k
  have hmu : 0 < mu := subcriticalOneBlockLength_pos hk hgamma.1
  have hmu1 : mu < 1 := subcriticalOneBlockLength_lt_one hk hgamma.2
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have ha : 0 < a := by dsimp [a]; positivity
  have hC : 0 < C := by dsimp [C, subcriticalSparseSideConstant]; positivity
  let etaMax := min (mu / 4) (min (a ^ 2 / (8 * C)) (xi / (2 * C)))
  have hetaMax : 0 < etaMax := by dsimp [etaMax]; positivity
  obtain ⟨eta, heta, hecap, _, heone, heres, R₀, hR, hRstar, hinv⟩ :=
    exists_subcriticalAggregationOuterParameters k hgamma.1 (by norm_num : (0 : ℝ) < 1)
      hetaMax (k - 1)
  have heMu : eta ≤ mu / 4 := hecap.trans (min_le_left _ _)
  have heA : C * eta ≤ a ^ 2 / 8 := by
    have h := hecap.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * C)).mp h
    nlinarith
  have heXi : C * eta ≤ xi := by
    have h := hecap.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp h
    nlinarith
  let deltaMax := min (mu / 4) (min ((1 - mu) / 2)
    (min ((1 - pK k) * a ^ 2 / 10) (min (subcriticalReferenceShiftBand k / 2) xi)))
  have hp := pK_mem_Ioo (by omega : 2 ≤ k)
  have hband := (subcriticalReferenceShiftBand_bounds hk).1
  have hdeltaMax : 0 < deltaMax := by
    have : 0 < 1 - mu := sub_pos.mpr hmu1
    have : 0 < 1 - pK k := sub_pos.mpr hp.2
    dsimp [deltaMax]; positivity
  obtain ⟨theta, ht, _, hnext⟩ := exists_subcriticalAggregationParameters hk hgamma.1
    heta hR hinv heres 1 (by norm_num)
  obtain ⟨alpha, halpha, _, hnext⟩ := hnext 1 (by norm_num)
  obtain ⟨delta, hd, hdcap, hnext⟩ := hnext deltaMax hdeltaMax
  obtain ⟨epsilon, hepsilon, _, hparameters⟩ := hnext 1 (by norm_num)
  have hdMu : delta ≤ mu / 4 := hdcap.trans (min_le_left _ _)
  have hdRest := hdcap.trans (min_le_right _ _)
  have hdRem : delta ≤ (1 - mu) / 2 := hdRest.trans (min_le_left _ _)
  have hdRest' := hdRest.trans (min_le_right _ _)
  have hdVar : delta ≤ (1 - pK k) * a ^ 2 / 10 := hdRest'.trans (min_le_left _ _)
  have hdBand : delta ≤ subcriticalReferenceShiftBand k / 2 :=
    hdRest'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdXi : delta ≤ xi := hdRest'.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨{
    eta := eta, theta := theta, alpha := alpha, delta := delta, epsilon := epsilon, R₀ := R₀
    eta_pos := heta, eta_one := heone, theta_pos := ht, alpha_pos := halpha
    delta_pos := hd, epsilon_pos := hepsilon, order_one := hR, order_star := hRstar
    size_reserve := by change eta + delta ≤ mu; linarith
    delta_mu := by change delta ≤ mu / 2; linarith
    delta_remainder := hdRem, variance_reserve := hdVar, shift_reserve := hdBand
    support_reserve := by change C * eta < a ^ 2 / 4; nlinarith [sq_pos_of_pos ha]
    size_accuracy := hdXi, edge_accuracy := heXi, aggregation := hparameters }⟩

end InducedStars
