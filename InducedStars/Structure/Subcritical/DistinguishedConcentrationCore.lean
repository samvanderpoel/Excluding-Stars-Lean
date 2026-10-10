import InducedStars.Structure.Subcritical.DistinguishedCutCover
import InducedStars.Structure.Subcritical.Closeness
import InducedStars.Asymptotics.RoughStructure
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# From separated candidate-ball estimates to distinguished concentration

This is the finite-cover assembly, with the local counting input displayed
explicitly. It is not a substitute for proving that input. All centres use
the same previously selected radius; no later shrinking argument is hidden.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

def subcriticalDistinguishedFarGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ) (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (radius : ℝ) (n m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (inducedStarFreeGraphFinsetWithEdges k n m).filter fun G ↦
    radius ≤ cutDist (graphGraphon G) (subcriticalDistinguishedGraphon k hk gamma hgamma)

def subcriticalDistinguishedFarProbability
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ) (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (radius : ℝ) (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedStarFreeGraphFinsetWithEdges k n m)
    (subcriticalDistinguishedFarGraphFinset k hk gamma hgamma radius n m)

/-- Exact finite inclusion behind the cover assembly. -/
theorem subcriticalDistinguishedFar_subset_cover
    {k n : ℕ} (hk : 3 ≤ k) {gamma radius tau : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (m : ℕ → ℕ)
    (F : Finset (AdmissibleBlockSequence k))
    (hcover : ∀ X : Graphon,
      radius ≤ cutDist X (subcriticalDistinguishedGraphon k hk gamma hgamma) →
      cutDistToSet X (fixedDensityOptimizers k gamma) < tau / 4 →
      ∃ L ∈ F, cutDist X (WLambda hk L) < tau) :
    subcriticalDistinguishedFarGraphFinset k hk gamma hgamma radius n (m n) ⊆
      fixedDensityOptimizerFarGraphFinset k gamma (tau / 4) m n ∪
        F.biUnion (fun L ↦ subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau) := by
  intro G hG
  obtain ⟨hfree, hfar⟩ := Finset.mem_filter.mp hG
  by_cases hnear : cutDistToSet (graphGraphon G) (fixedDensityOptimizers k gamma) < tau / 4
  · obtain ⟨L, hL, hGL⟩ := hcover (graphGraphon G) hfar hnear
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨L, hL, mem_subcriticalCandidateCutBallGraphFinset.mpr ⟨hfree, hGL⟩⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hfree, le_of_not_gt hnear⟩)

/-- At any single, uniformly chosen positive radius, vanishing proportions
in every separated candidate ball imply concentration at Wdist. The local
ball estimates remain an explicit hypothesis and are proved by the later
matching/entropy comparison, not by compactness. -/
theorem subcriticalDistinguishedCutConcentration_of_candidate_bounds
    (k : ℕ) (hk : 3 ≤ k) {gamma radius tau : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (hradius : 0 < radius) (htau : 0 < tau) (hcap : tau ≤ radius)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma)
    (hlocal : ∀ L : AdmissibleBlockSequence k,
      IsSubcriticalCandidate k gamma L →
      radius / 2 ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) →
      Tendsto (fun n ↦
        ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) /
          (inducedStarFreeGraphFinsetWithEdges k n (m n)).card) atTop (𝓝 0)) :
    Tendsto (fun n ↦ subcriticalDistinguishedFarProbability k hk gamma hgamma radius n (m n))
      atTop (𝓝 0) := by
  have hg : gamma ∈ Ioo (0 : ℝ) 1 := ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩
  obtain ⟨F, hF, hcover⟩ := subcriticalSeparatedCandidateFiniteCover k hk hgamma hradius htau hcap
  obtain ⟨c, hc, hrough⟩ := inducedStarFixedDensityRoughStructure k hk gamma hg
    (tau / 4) (by positivity)
  have hroughLimit : Tendsto (fun n ↦ fixedDensityOptimizerFarProbability k gamma (tau / 4) m n)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n ↦ by
      unfold fixedDensityOptimizerFarProbability uniformSubfamilyProbability
      positivity) (hrough m hm)
    exact tendsto_exp_neg_mul_natCast_sq_zero hc
  have hsumLimit : Tendsto (fun n ↦ ∑ L ∈ F,
      ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) /
        (inducedStarFreeGraphFinsetWithEdges k n (m n)).card) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum F
      (fun L hL ↦ hlocal L (hF L hL).1 (hF L hL).2)
  have hpos := eventually_inducedStarFreeGraphFinsetWithEdges_nonempty k hk gamma hg m hm
  apply squeeze_zero' (Eventually.of_forall fun n ↦ by
    unfold subcriticalDistinguishedFarProbability uniformSubfamilyProbability
    positivity) (g := fun n ↦ fixedDensityOptimizerFarProbability k gamma (tau / 4) m n +
      ∑ L ∈ F, ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) /
        (inducedStarFreeGraphFinsetWithEdges k n (m n)).card)
  · filter_upwards [hpos] with n hn
    have hden : (0 : ℝ) < (inducedStarFreeGraphFinsetWithEdges k n (m n)).card := by
      exact_mod_cast hn.card_pos
    have hcard := (Finset.card_le_card
      (subcriticalDistinguishedFar_subset_cover hk hgamma m F hcover (n := n))).trans
      (Finset.card_union_le _ _)
    have hbi := Finset.card_biUnion_le (s := F)
      (t := fun L ↦ subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau)
    have hcardR : ((subcriticalDistinguishedFarGraphFinset k hk gamma hgamma radius n (m n)).card : ℝ) ≤
        (fixedDensityOptimizerFarGraphFinset k gamma (tau / 4) m n).card +
          ∑ L ∈ F, ((subcriticalCandidateCutBallGraphFinset k n (m n) (WLambda hk L) tau).card : ℝ) := by
      exact_mod_cast hcard.trans (Nat.add_le_add_left hbi _)
    change (_ : ℝ) / _ ≤ _
    rw [← Finset.sum_div, fixedDensityOptimizerFarProbability_eq_card_ratio, ← add_div]
    exact div_le_div_of_nonneg_right hcardR hden.le
  · simpa using hroughLimit.add hsumLimit

end InducedStars
