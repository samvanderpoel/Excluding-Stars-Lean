import InducedStars.Structure.Gnp.CriticalParameters
import InducedStars.Structure.Gnp.WeightedGroupedUpper
import InducedStars.Structure.Gnp.WeightedMatchingGain
import InducedStars.Structure.Subcritical.RetainedKeyCounting

/-!
# Critical optimizer-ball comparison

The exponential number of actual retained keys is absorbed by the
labeled matching gain, after summing the exact binomial-model weights.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators Classical
namespace InducedStars

/-- Finite combination of the weighted grouped upper bound and the matching
lower bound. The matching estimate is applied to each actual retained key. -/
theorem gnpCriticalCutBallMass_le_exp_neg_of_sparse_gain
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (L : AdmissibleBlockSequence k) (R₀ : ℕ)
    {eta delta tau c gamma omega E : ℝ} (heta : 0 < eta) (hc : 0 ≤ c)
    (hgamma : 0 ≤ gamma)
    (hseparated : gamma ≤ cutDist (WLambda hk L) zeroGraphon)
    (htau : tau ≤ gamma / 2)
    (hcount : ∀ m : ℕ, m ≤ completeEdgeCount n →
      gamma / 8 * (n : ℝ)^2 ≤ m →
      SubcriticalGroupedCandidateUpperBounds hk hn L R₀ m eta delta tau c)
    (hgain : ∀ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      Real.exp ((criticalRetainedWeightConstant k +
        retainedKeyCountingConstant k eta R₀ + 2) * n + E) *
        retainedKeyWeightedSparseSum K eta (pK k) ≤
          gnpInducedStarCutBallMass k n (pK k) zeroGraphon omega) :
    gnpInducedStarCutBallMass k n (pK k) (WLambda hk L) tau ≤
      Real.exp (-(n : ℝ) - E) * gnpInducedStarCutBallMass k n (pK k) zeroGraphon omega := by
  let C := criticalRetainedWeightConstant k
  let D := retainedKeyCountingConstant k eta R₀
  let Z := gnpInducedStarCutBallMass k n (pK k) zeroGraphon omega
  let B := C + D + 2
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  have hZ : 0 ≤ Z := gnpInducedStarCutBallMass_nonneg k n ⟨hp.1.le, hp.2.le⟩ _ _
  have hS K (hK : K ∈ compatibleRetainedKeys k n L eta delta R₀) :
      retainedKeyWeightedSparseSum K eta (pK k) ≤ Real.exp (-(B * n + E)) * Z := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (B * n + E))).mp
    calc
      _ ≤ Z := hgain K hK
      _ = Real.exp (B * n + E) * (Real.exp (-(B * n + E)) * Z) := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
  have hsum : (∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      retainedKeyWeightedSparseSum K eta (pK k)) ≤
      Real.exp (D * n) * (Real.exp (-(B * n + E)) * Z) := by
    calc
      _ ≤ ∑ _K ∈ compatibleRetainedKeys k n L eta delta R₀,
          Real.exp (-(B * n + E)) * Z := Finset.sum_le_sum hS
      _ = ((compatibleRetainedKeys k n L eta delta R₀).card : ℝ) *
          (Real.exp (-(B * n + E)) * Z) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (card_compatibleRetainedKeys_le_exp k n L heta delta R₀) (by positivity)
  have hfac : 1 + Real.exp (-c * n) ≤ 2 := by
    have hh : -c * (n : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Nat.cast_nonneg n)
    have := Real.exp_le_exp.mpr hh
    rw [Real.exp_zero] at this
    linarith
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have htwo : (2 : ℝ) ≤ Real.exp (n : ℝ) := by
    linarith [Real.add_one_le_exp (n : ℝ)]
  have hexp : Real.exp (C * n) * Real.exp (D * n) * Real.exp (-(B * n + E)) =
      Real.exp (-2 * (n : ℝ) - E) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [B]
    ring
  calc
    _ ≤ (1 + Real.exp (-c * n)) * Real.exp (C * n) *
        ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          retainedKeyWeightedSparseSum K eta (pK k) :=
      gnpCriticalCutBallMass_le_weightedSparseSum hk hn L R₀ eta delta tau c
        hgamma hseparated htau hcount
    _ ≤ (1 + Real.exp (-c * n)) * Real.exp (C * n) *
        (Real.exp (D * n) * (Real.exp (-(B * n + E)) * Z)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 2 * Real.exp (C * n) * (Real.exp (D * n) * (Real.exp (-(B * n + E)) * Z)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfac (by positivity)) (by positivity)
    _ = 2 * Real.exp (-2 * (n : ℝ) - E) * Z := by
      calc
        _ = 2 * (Real.exp (C * n) * Real.exp (D * n) * Real.exp (-(B * n + E))) * Z := by ring
        _ = _ := by rw [hexp]
    _ ≤ Real.exp (n : ℝ) * Real.exp (-2 * (n : ℝ) - E) * Z :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htwo (by positivity)) hZ
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- Paper: Lemma `lemma:critical-gnp-comparison-K1k`.
The weighted comparison uses actual retained keys and the fixed-key,
fixed-remainder estimates. It includes the full complete-core endpoint.
The radius and positive rate precede the candidate representation. -/
theorem criticalGnpComparison (k : ℕ) (hk : 3 ≤ k)
    {separation omega : ℝ} (hseparation : 0 < separation)
    (homega : 0 < omega) (homegaOne : omega ≤ 1) :
    ∃ nu tau : ℝ, 0 < nu ∧ 0 < tau ∧ tau ≤ separation / 2 ∧ tau ≤ omega / 4 ∧
      ∀ L : AdmissibleBlockSequence k,
        separation ≤ cutDist (WLambda hk L) zeroGraphon →
        ∀ᶠ n : ℕ in atTop,
          gnpInducedStarCutBallMass k n (pK k) (WLambda hk L) tau ≤
            Real.exp (-nu * n * Real.log n) *
              gnpInducedStarCutBallMass k n (pK k) zeroGraphon omega := by
  obtain ⟨P⟩ := exists_gnpCriticalComparisonParameters hk hseparation homega
  let A := 1 + ((k - 2 : ℕ) : ℝ) * pK k
  let a := min 1 (separation / (4 * A))
  have hA : 0 < A := by
    have hp := (pK_mem_Ioo (show 2 ≤ k by omega)).1
    dsimp [A]
    positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have haOne : a ≤ 1 := min_le_left _ _
  let nu := a / 128
  let B := criticalRetainedWeightConstant k + retainedKeyCountingConstant k P.eta P.R₀ + 2
  have hgain := eventually_retainedKeyWeightedSparseSum_matching_gain k hk
    P.eta a omega P.eta_pos ha haOne homega homegaOne P.sparse_reserve B
  refine ⟨nu, P.tau, by dsimp [nu]; positivity, P.tau_pos,
    P.tau_separation, P.tau_omega, ?_⟩
  intro L hL
  obtain ⟨n0, hn0, hcount⟩ := P.grouped L
  filter_upwards [hgain, eventually_ge_atTop n0] with n hgain hn
  have hsupport K (hK : K ∈ compatibleRetainedKeys k n L P.eta P.delta P.R₀) :
      a * n ≤ K.support.card := by
    exact (mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) _)
      (Nat.cast_nonneg n)).trans
        (gnpCompatibleRetainedKey_support_lower hk L P.eta_pos P.delta_pos.le P.delta_eta
          hL P.tail_reserve P.mass_reserve hK)
  have hb := gnpCriticalCutBallMass_le_exp_neg_of_sparse_gain hk (hn0.trans hn) L P.R₀
    P.eta_pos (subcriticalAggregationConstant_pos hk P.eta_pos P.order_one).le
    hseparation.le hL P.tau_separation (fun m _ hm ↦ hcount hn m hm)
    (fun K hK ↦ hgain K (hsupport K hK))
  apply hb.trans
  apply mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (show -(n : ℝ) - (nu * n * Real.log n) ≤
      -nu * n * Real.log n by nlinarith [Nat.cast_nonneg (α := ℝ) n]))
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  exact gnpInducedStarCutBallMass_nonneg k n ⟨hp.1.le, hp.2.le⟩ _ _

end InducedStars
