import InducedStars.Structure.Subcritical.FineStructureRadius
import InducedStars.Structure.Subcritical.CleanRetainedComparison
import InducedStars.Structure.Subcritical.RemainderLowerTail
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Vanishing nonclean probability in the selected input ball

The proved grouped bound is multiplied by the constant 2(k-1)!,
not by an exponential count of arbitrary full divisions. Probabilities
are compared only after eventual nonemptiness of the exact-edge family.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

def subcriticalNoncleanGraphFinset {k : ℕ} (hk : 3 ≤ k) {gamma xi : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (P : SubcriticalFineStructureParameters k gamma xi) (n m : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  if hn : k - 1 ≤ n then subcriticalCanonicalNoncleanGraphFinset
    (subcriticalCandidateCutBallGraphFinset k n m
      (subcriticalDistinguishedGraphon k hk gamma hgamma) (P.inputRadius hk hgamma))
    P.eta P.R₀ hk hn else ∅

def subcriticalNoncleanProbability {k : ℕ} (hk : 3 ≤ k) {gamma xi : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (P : SubcriticalFineStructureParameters k gamma xi) (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
    (subcriticalNoncleanGraphFinset hk hgamma P n m)

theorem subcriticalNoncleanProbability_tendsto_zero {k : ℕ} (hk : 3 ≤ k)
    {gamma xi : ℝ} (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (P : SubcriticalFineStructureParameters k gamma xi)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    Tendsto (fun n ↦ subcriticalNoncleanProbability hk hgamma P n (m n)) atTop (𝓝 0) := by
  let mu := subcriticalOneBlockLength k gamma
  let c := subcriticalAggregationConstant k P.eta P.R₀
  let A : ℝ := 2 * (k - 1).factorial
  have hc : 0 < c := subcriticalAggregationConstant_pos hk P.eta_pos P.order_one
  have hmu := subcriticalOneBlockLength_pos hk hgamma.1
  have hmu1 := (subcriticalOneBlockLength_lt_one hk hgamma.2).le
  have hm' : HasAsymptoticEdgeDensity m (gammaK k * mu ^ 2) := by
    simpa only [mu, subcriticalOneBlockLength_density_identity hk hgamma.1.le] using hm
  have hclean := eventually_retainedKeyCleanSum_le_total hk hmu hmu1 P.eta_pos.le
    P.delta_pos P.size_reserve P.order_star P.delta_mu P.variance_reserve P.shift_reserve
    P.support_reserve m hm'
  obtain ⟨n0, hn0, hbound⟩ := P.inputRadius_spec hk hgamma m hm
  apply squeeze_zero' (g := fun n : ℕ ↦ A * Real.exp (-c * n))
  · exact Eventually.of_forall fun n ↦ by
      unfold subcriticalNoncleanProbability uniformSubfamilyProbability; positivity
  · filter_upwards [hclean, eventually_ge_atTop n0,
      eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma
        ⟨hgamma.1,hgamma.2.trans (gammaK_lt_one hk)⟩ m hm] with n hclean hn hpos
    have hN : (0 : ℝ) < (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := by
      exact_mod_cast hpos.card_pos
    have hsum : (∑ K ∈ compatibleRetainedKeys k n
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma) P.eta P.delta P.R₀,
        (retainedKeyCleanPartitionFunction K P.eta (m n) P.delta : ℝ)) ≤
        A * (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := by
      dsimp only [A, subcriticalDistinguishedBlockSequence]
      have hh : (∑ K ∈ compatibleRetainedKeys k n
          (oneBlockSequence k hk (subcriticalOneBlockLength k gamma) hmu hmu1)
          P.eta P.delta P.R₀, retainedKeyCleanPartitionFunction K P.eta (m n) P.delta) ≤
          (2 * (k - 1).factorial) *
            (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := hclean
      exact_mod_cast hh
    have hcount := (hbound hn).1.cutBall_nonclean
    have hb := hcount.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)
    unfold subcriticalNoncleanProbability uniformSubfamilyProbability
    rw [subcriticalNoncleanGraphFinset, dif_pos (hn0.trans hn)]
    apply (div_le_iff₀ hN).mpr
    calc
      _ ≤ Real.exp (-c * n) * (A * (inducedStarFreeGraphFinsetWithEdges k n (m n)).card) := hb
      _ = _ := by ring
  · simpa only [mul_zero] using (tendsto_exp_neg_mul_natCast_zero hc).const_mul A

end InducedStars
