import InducedStars.C4.CountingFamilies
import InducedStars.C4.LowDegreeAggregation

/-!
# Canonical low-degree graph families

The canonical family maps into the actual fixed-defect fibers without
changing its graph or edge count. This transfers the finite pattern sum to
the families appearing in `eqn:c4-union-bound`.
-/

noncomputable section
open Finset Filter
open scoped Classical Topology
namespace InducedStars

theorem card_c4LowDegreeMatchingGraphFinset_le_fiberSum
    (n m : ℕ) (gamma epsilon zeta alpha : ℝ) (D : C4Division (Fin n)) (q : ℕ) :
    (c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card ≤
      ∑ T ∈ (c4LowDegreeDefectPatternFinset D alpha q).filter
        (fun T ↦ ((finiteGraphEdges T).card : ℝ) ≤ epsilon * (n : ℝ) ^ 2),
          (c4FixedDefectFreeFiber D T m).card := by
  let patterns := (c4LowDegreeDefectPatternFinset D alpha q).filter
    (fun T ↦ ((finiteGraphEdges T).card : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
  have hsub : c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q ⊆
      patterns.biUnion (fun T ↦ c4FixedDefectFreeFiber D T m) := by
    intro G hG
    obtain ⟨hclose, hdegree, hindex⟩ := mem_c4LowDegreeMatchingGraphFinset.mp hG
    refine mem_biUnion.mpr ⟨c4DefectGraph G D, ?_, c4CloseDivision_mem_fixedDefectFiber hclose⟩
    exact mem_filter.mpr ⟨mem_c4LowDegreeDefectPatternFinset.mpr
      ⟨c4DefectGraph_supported G D, hindex, hdegree⟩,
      (mem_c4CloseDivisionGraphFinset.mp hclose).2.2.1⟩
  exact (card_le_card hsub).trans card_biUnion_le

theorem sum_card_c4LowDegreeMatchingGraphFinset_le_freeTotal
    (n m : ℕ) (gamma epsilon zeta alpha : ℝ) (D : C4Division (Fin n)) :
    (∑ q ∈ Icc 1 n,
      ((c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card : ℝ)) ≤
        c4LowDegreeFreeTotal D m alpha epsilon := by
  unfold c4LowDegreeFreeTotal
  apply sum_le_sum
  intro q hq
  exact_mod_cast card_c4LowDegreeMatchingGraphFinset_le_fiberSum
    n m gamma epsilon zeta alpha D q

/-- The canonical low-degree contribution is exponentially small for every
division. An out-of-range division has an empty canonical family. The
thresholds are uniform in every smaller defect and nondegeneracy tolerance. -/
theorem inducedC4CanonicalLowDegreeRate {gamma : ℝ} (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zeta0 > 0, ∃ epsilon0 > 0, ∃ alpha0 > 0, alpha0 ≤ 1 / 2 ∧ ∃ c > 0,
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
          ∀ zeta ≤ zeta0, ∀ epsilon ≤ epsilon0,
            ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0,
              (∑ q ∈ Icc 1 n,
                ((c4LowDegreeMatchingGraphFinset n (m n)
                  gamma epsilon zeta alpha D q).card : ℝ)) ≤
                (Nat.choose (D.independentPart.card * D.cliquePart.card)
                  (m n - D.cliquePart.card.choose 2) : ℝ) * Real.exp (-c * n) := by
  obtain ⟨zeta0, hzeta0, epsilon0, hepsilon0, alpha0, halpha0, hahalf, c, hc, htotal⟩ :=
    inducedC4LowDegreeMatchingTotal hgamma
  refine ⟨zeta0, hzeta0, epsilon0, hepsilon0, alpha0, halpha0, hahalf, c, hc, ?_⟩
  intro m hm
  filter_upwards [htotal m hm, eventually_ge_atTop 1] with n htotal hn
  intro D zeta hzeta epsilon hepsilon alpha halpha
  by_cases hclose : |(D.cliquePart.card : ℝ) / n - c4Lambda gamma| ≤ zeta0
  · exact (sum_card_c4LowDegreeMatchingGraphFinset_le_freeTotal
      n (m n) gamma epsilon zeta alpha D).trans
        (htotal D hclose alpha halpha epsilon hepsilon)
  · have hempty (q : ℕ) :
        c4LowDegreeMatchingGraphFinset n (m n) gamma epsilon zeta alpha D q = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro G hG
      have hD := (mem_c4CloseDivisionGraphFinset.mp
        (mem_c4LowDegreeMatchingGraphFinset.mp hG).1).2.2.2
      have hratio := (c4_nondegenerate_ratio_iff (by omega) D gamma zeta).mpr hD
      exact hclose (hratio.trans hzeta)
    simp only [hempty, card_empty, Nat.cast_zero, sum_const_zero]
    positivity

/-- Guarded split-fiber form for the final sum over all divisions.
Feasibility follows from the zero-defect sampling band on every relevant
division; an irrelevant division contributes an empty canonical family. -/
theorem inducedC4CanonicalLowDegreeSplitRate {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo 0 1) :
    ∃ zeta0 > 0, ∃ epsilon0 > 0, ∃ alpha0 > 0, alpha0 ≤ 1 / 2 ∧ ∃ c > 0,
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop, ∀ D : C4Division (Fin n),
          ∀ zeta ≤ zeta0, ∀ epsilon ≤ epsilon0,
            ∀ alpha ∈ Set.Icc (0 : ℝ) alpha0,
              (∑ q ∈ Icc 1 n,
                ((c4LowDegreeMatchingGraphFinset n (m n)
                  gamma epsilon zeta alpha D q).card : ℝ)) ≤
                ((c4SplitFiber D (m n)).card : ℝ) * Real.exp (-c * n) := by
  obtain ⟨zl, hzl, epsilon0, hepsilon0, alpha0, halpha0, hahalf, c, hc, hlow⟩ :=
    inducedC4CanonicalLowDegreeRate hgamma
  obtain ⟨zb, hzb, eb, heb, beta, hbeta, hhalf, hband⟩ :=
    exists_c4NondegenerateSamplingBand hgamma
  refine ⟨min zl zb, lt_min hzl hzb, epsilon0, hepsilon0,
    alpha0, halpha0, hahalf, c, hc, ?_⟩
  intro m hm
  filter_upwards [hlow m hm, hband m hm] with n hlow hband
  intro D zeta hzeta epsilon hepsilon alpha halpha
  by_cases hclose : |(D.cliquePart.card : ℝ) / n - c4Lambda gamma| ≤ zb
  · have hparts := D.card_add
    simp only [Fintype.card_fin] at hparts
    have hsamp := hband.2 D.cliquePart.card (by omega) hclose
      0 (by simp only [Int.cast_zero, abs_zero]; positivity) 0 (Nat.zero_le n)
    have hbase := (c4ReferenceBand_of_samplingBounds D hsamp).1
    rw [card_c4SplitFiber, if_pos hbase]
    exact hlow D zeta (hzeta.trans (min_le_left _ _)) epsilon hepsilon alpha halpha
  · have hempty (q : ℕ) :
        c4LowDegreeMatchingGraphFinset n (m n) gamma epsilon zeta alpha D q = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro G hG
      have hD := (mem_c4CloseDivisionGraphFinset.mp
        (mem_c4LowDegreeMatchingGraphFinset.mp hG).1).2.2.2
      have hratio := (c4_nondegenerate_ratio_iff hband.1 D gamma zeta).mpr hD
      exact hclose (hratio.trans (hzeta.trans (min_le_right _ _)))
    simp only [hempty, card_empty, Nat.cast_zero, sum_const_zero]
    positivity

end InducedStars
