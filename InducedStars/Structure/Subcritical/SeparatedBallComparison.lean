import InducedStars.Structure.Subcritical.SeparatedKeyComparison
import InducedStars.Structure.Subcritical.GroupedUpperBound
import InducedStars.Structure.Subcritical.RetainedMassGap

/-!
# Uniform comparison of separated candidate balls with the total family

Choose the geometric gap, the nested scalar hierarchy, and
one radius before choosing a candidate. The shifted balanced full-slice
denominator lies in the total exact-edge family. This intermediate theorem
does not claim a denominator in a smaller cut ball before concentration.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators
namespace InducedStars

private theorem eventually_two_mul_exp_comparison {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 2 * Real.exp (-c*n*Real.log n) ≤
      Real.exp (-(c/2)*n*Real.log n) := by
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (Nat.ceil (4/c))] with n hl hn
  have hN : 4/c ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hN' := (div_le_iff₀ hc).mp hN
  have hmul := mul_nonneg (show 0 ≤ c*n by positivity) (sub_nonneg.mpr hl)
  have htwo : 2 ≤ Real.exp ((c/2)*n*Real.log n) := by
    nlinarith [Real.add_one_le_exp ((c/2)*n*Real.log n)]
  calc
    _ ≤ Real.exp ((c/2)*n*Real.log n) * Real.exp (-c*n*Real.log n) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- Source-scale suppression with a total-family denominator. All counting
inputs are proved dependencies; only the original density and separation
are supplied. The common radius and rate precede the candidate and sequence. -/
theorem subcriticalSeparatedCandidateBallComparison
    (k : ℕ) (hk : 3 ≤ k) {gamma separation tauMax : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hsep : 0 < separation)
    (htauMax : 0 < tauMax) :
    ∃ nu : ℝ, 0 < nu ∧ ∃ tau : ℝ, 0 < tau ∧ tau ≤ tauMax ∧
      ∀ L : AdmissibleBlockSequence k, IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) →
        ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
          ∀ᶠ n : ℕ in atTop,
            ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) ≤
              (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
                Real.exp (-nu*n*Real.log n) := by
  obtain ⟨gap, hgap, hgapOne, hmass⟩ :=
    subcriticalCompatibleRetainedKeyMassGap k hk hgamma hsep
  obtain ⟨eta, heta, hetagap, hetaomega, hetaOne, hreserve, R₀, hR, hRgap, hinv⟩ :=
    exists_subcriticalAggregationOuterParameters k hgamma.1
      (by norm_num : (0 : ℝ) < 1) (show 0 < gap/4 by positivity) (Nat.ceil (2/gap))
  obtain ⟨theta, htheta, hthetaOne, halphaExists⟩ :=
    exists_subcriticalAggregationParameters hk hgamma.1 heta hR hinv hreserve
      1 (by norm_num)
  obtain ⟨alpha, halpha, halphaOne, hdeltaExists⟩ := halphaExists 1 (by norm_num)
  let deltaCap := min eta (min (eta*gap) (min (pK k/2) ((1-pK k)/2)))
  have hp := pK_pos (by omega : 2 ≤ k)
  have hq : 0 < 1-pK k := sub_pos.mpr (pK_lt_one (by omega : 2 ≤ k))
  have hdeltaCap : 0 < deltaCap := by dsimp [deltaCap]; positivity
  obtain ⟨delta, hdelta, hdCap, hepsilonExists⟩ := hdeltaExists deltaCap hdeltaCap
  have hdBounds : delta ≤ eta ∧ delta ≤ eta*gap ∧ delta ≤ pK k/2 ∧ delta ≤ (1-pK k)/2 := by
    simpa only [deltaCap, le_min_iff] using hdCap
  obtain ⟨epsilon, hepsilon, hepsilonOne, hparameters⟩ := hepsilonExists 1 (by norm_num)
  obtain ⟨tau, htau, htauCap, hupper⟩ := subcriticalGroupedUpperBound_fixedDensity
    k hk hgamma R₀ 1 eta theta alpha delta epsilon tauMax
      (by norm_num) (by norm_num) hetaOne htauMax hparameters
  let c := subcriticalAggregationConstant k eta R₀
  have hc : 0 < c := subcriticalAggregationConstant_pos hk heta hR
  let rate := subcriticalSeparatedComparisonRate gap
  have hrate : 0 < rate := subcriticalSeparatedComparisonRate_pos hgap
  refine ⟨rate/2, half_pos hrate, tau, htau, htauCap, ?_⟩
  intro L hL hdist m hm
  have hLmem : WLambda hk L ∈ candidateOptimizerFamily k gamma := by
    rw [candidateOptimizerFamily_of_lt hk
      ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩ hgamma.2]
    exact ⟨L, hL, rfl⟩
  obtain ⟨n0, hn0, hball⟩ := hupper L hLmem m hm
  have hmassL := hmass eta delta R₀ heta hetagap hRgap hdelta.le hdBounds.1 hdBounds.2.1
    L hL hdist
  have hbudget : 16 * (subcriticalSparseSideConstant k * eta) ≤ gamma := by
    linarith [hgamma.1]
  have hclean := eventually_subcriticalSeparatedCleanKeySum hk hgamma hgap heta hdelta
    hdBounds.2.2.1 hdBounds.2.2.2 hbudget L hmassL m hm
  filter_upwards [hclean, eventually_ge_atTop n0, eventually_two_mul_exp_comparison hrate]
    with n hn hn0' htwo
  have hb := (hball hn0').cutBall
  have he : Real.exp (-c*n) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hn : (0 : ℝ) ≤ n := by positivity
    nlinarith)
  have hsum0 : 0 ≤ ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
      (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ) := by positivity
  have hN : (0 : ℝ) ≤ inducedStarFreeGraphCountWithEdges k n (m n) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hn
    (show 0 ≤ 1 + Real.exp (-c*n) by positivity)
  have hpre : ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) ≤
      (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
        (2 * Real.exp (-rate*n*Real.log n)) := by
    calc
      _ ≤ (1 + Real.exp (-c*n)) * ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ) := hb
      _ ≤ 2 * ∑ K ∈ compatibleRetainedKeys k n L eta delta R₀,
          (retainedKeyCleanPartitionFunction K eta (m n) delta : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hsum0
      _ ≤ 2 * ((inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
          Real.exp (-rate*n*Real.log n)) := mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  exact hpre.trans (mul_le_mul_of_nonneg_left htwo hN)

end InducedStars
