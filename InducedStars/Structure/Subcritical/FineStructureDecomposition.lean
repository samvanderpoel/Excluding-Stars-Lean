import InducedStars.Structure.Subcritical.NoncleanCleanup
import InducedStars.Structure.Subcritical.StructuredCompatibility
import InducedStars.Structure.Subcritical.DistinguishedConcentration

/-!
# The exact subcritical exceptional-family decomposition

Every graph outside the three exceptional families has a single clean
canonical retained core. Its complement simultaneously satisfies the
sparse upper bound and the accuracy-independent linear lower bound.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical
namespace InducedStars

theorem subcriticalUnstructured_subset_three_families
    {k n m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) {gamma xi : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (P : SubcriticalFineStructureParameters k gamma xi)
    (hP : SubcriticalAggregationParameters k gamma P.eta P.R₀
      P.theta P.alpha P.delta P.epsilon n)
    (hbridge : SubcriticalMinimizerBridge hk
      (subcriticalDistinguishedBlockSequence k hk gamma hgamma) P.R₀
      1 P.eta P.theta P.alpha P.delta P.epsilon (P.inputRadius hk hgamma) n) :
    subcriticalUnstructuredGraphFinset k n m gamma
      (subcriticalRemainderLowerCoefficient k gamma) xi ⊆
      (subcriticalDistinguishedFarGraphFinset k hk gamma hgamma (P.inputRadius hk hgamma) n m ∪
        subcriticalNoncleanGraphFinset hk hgamma P n m) ∪
      subcriticalLowRemainderGraphFinset k n m
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma) P.eta P.delta P.R₀
        (Nat.floor (subcriticalRemainderLowerCoefficient k gamma * n)) := by
  intro G hG
  obtain ⟨hfree, hbad⟩ := mem_subcriticalUnstructuredGraphFinset.mp hG
  by_cases hfar : P.inputRadius hk hgamma ≤
      cutDist (graphGraphon G) (subcriticalDistinguishedGraphon k hk gamma hgamma)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hfree,hfar⟩))
  have hnear := lt_of_not_ge hfar
  have hball := mem_subcriticalCandidateCutBallGraphFinset.mpr ⟨hfree,hnear⟩
  let D := canonicalSubcriticalDivision G P.R₀ hk (by simpa using hn)
  by_cases hclean : subcriticalRetainedIncidentDefectGraph G D P.eta P.R₀ = ⊥
  · obtain ⟨R⟩ := hbridge G D (canonicalSubcriticalDivision_minimal G P.R₀ hk _) hnear
    have hnpos : 0 < n := by omega
    have hscale : 1 ≤ P.theta * n := by
      have ht : 0 ≤ P.theta * (n : ℝ) := mul_nonneg P.theta_pos.le (Nat.cast_nonneg n)
      nlinarith [hP.localConditions.row_scale, hP.localConditions.alpha_quarter]
    have hmodel := R.mem_cleanModelGraphFinset P.order_one P.eta_pos.le P.theta_pos.le
      hP.localConditions.retained_visible (hP.localConditions.alpha_quarter.trans (by norm_num))
      P.delta_pos.le hP.retained_inverse (by norm_num) hP.epsilon_cap hscale
      (mem_inducedStarFreeGraphFinsetWithEdges.mp hfree).1
      (by simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using
        (mem_inducedStarFreeGraphFinsetWithEdges.mp hfree).2) hclean
    have hD : D ∈ subcriticalCompatibleDivisions k n
        (subcriticalDistinguishedBlockSequence k hk gamma hgamma) P.eta P.delta P.R₀ :=
      (mem_subcriticalCompatibleDivisions D).mpr
        ⟨canonicalSubcriticalDivision_isOrdered G P.R₀ hk _, ⟨R.compatibility⟩⟩
    have hK := retainedKey_mem_compatibleRetainedKeys hD
    obtain ⟨E,hkey,_,_,_⟩ := compatibleRetainedKeys_oneBlock_geometry hk
      (subcriticalOneBlockLength_pos hk hgamma.1)
      (subcriticalOneBlockLength_lt_one hk hgamma.2).le P.eta_pos.le P.delta_pos.le
      P.size_reserve P.order_star hK
    by_cases hlower : subcriticalRemainderLowerCoefficient k gamma * n ≤
        (finiteGraphEdges (subcriticalRemainderGraph G D P.eta P.R₀)).card
    · exfalso
      apply hbad
      apply hasSubcriticalStructure_of_oneBlock_compatibility hk hgamma R.compatibility
        P.eta_pos.le P.delta_pos.le P.size_reserve P.order_star hnpos P.size_accuracy hclean hlower
      obtain ⟨_,_,hb,_⟩ := (mem_subcriticalCleanModelGraphFinset_iff G D P.eta P.R₀ m P.delta).mp hmodel
      have hC : 0 ≤ subcriticalSparseSideConstant k := by
        unfold subcriticalSparseSideConstant; positivity
      have hfloor := Nat.floor_le (mul_nonneg (mul_nonneg hC P.eta_pos.le)
        (sq_nonneg (n : ℝ)))
      have hbR : ((finiteGraphEdges (subcriticalRemainderGraph G D P.eta P.R₀)).card : ℝ) ≤
          Nat.floor (subcriticalSparseSideConstant k * P.eta * (n : ℝ) ^ 2) := by
        simpa only [Fintype.card_fin] using (show
          ((finiteGraphEdges (subcriticalRemainderGraph G D P.eta P.R₀)).card : ℝ) ≤
            Nat.floor (subcriticalSparseSideConstant k * P.eta * (Fintype.card (Fin n) : ℝ) ^ 2) by
          exact_mod_cast hb)
      exact (hbR.trans hfloor).trans
        (mul_le_mul_of_nonneg_right P.edge_accuracy (sq_nonneg (n : ℝ)))
    · apply Finset.mem_union_right
      exact mem_subcriticalLowRemainderGraphFinset_of_model hD hkey hmodel
        (Nat.le_floor (le_of_lt (lt_of_not_ge hlower)))
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [subcriticalNoncleanGraphFinset, dif_pos hn]
    exact mem_subcriticalCanonicalNoncleanGraphFinset _ P.eta P.R₀ hk hn G |>.mpr ⟨hball,hclean⟩

end InducedStars
