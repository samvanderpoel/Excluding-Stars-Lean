import InducedStars.Structure.Subcritical.ResidualGraphCount
import InducedStars.Structure.Subcritical.ResidualMatchingEstimate

/-!
# The zero-matching endpoint of the profile bound

The actual residual family is a subset of the singleton empty graph. The
outer operation over rooted patterns remains a maximum, never a sum.
The safe logarithm is retained when the admissible family is empty.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

theorem subcriticalResidualSafeMaximum_le_one
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (TB R : SimpleGraph V) :
    subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R ≤ 1 := by
  apply subcriticalFiniteMax_le zero_le_one
  intro z _
  exact (subcriticalResidualSafeProbability_mem_Icc p z.1 TB R z.2.1 z.2.2).2

theorem subcriticalResidualDefectPatternFinset_subset_singleton_of_ell_zero
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (TB : SimpleGraph V) (hell : p.ell = 0) :
    subcriticalResidualDefectPatternFinset F alpha p TB ⊆ {⊥} := by
  intro R hR
  exact Finset.mem_singleton.mpr ((DenseGraph.matchingNumber_eq_zero_iff R).mp
    ((subcriticalResidualPattern_matching hR).trans hell))

theorem subcriticalProfileMatchingWeight_le_one_of_ell_zero
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (hell : p.ell = 0) :
    subcriticalProfileMatchingWeight F p m C alpha delta epsilon ≤ 1 := by
  apply subcriticalFiniteMax_le zero_le_one
  intro TB _
  calc
    _ ≤ ∑ R ∈ ({⊥} : Finset (SimpleGraph V)),
        Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
          subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (subcriticalResidualDefectPatternFinset_subset_singleton_of_ell_zero
          F p alpha TB hell)
      intro R _ _
      exact mul_nonneg (Real.exp_pos _).le
        (subcriticalResidualSafeMaximum_nonneg F p m C alpha delta epsilon TB R)
    _ ≤ 1 := by
      have he : finiteGraphEdges (⊥ : SimpleGraph V) = ∅ := by
        ext e
        simp [mem_finiteGraphEdges]
      simpa [he] using
        subcriticalResidualSafeMaximum_le_one F p m C alpha delta epsilon TB ⊥

theorem subcriticalProfileMatchingExponent_nonpos_of_ell_zero
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ) (hell : p.ell = 0) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤ 0 := by
  unfold subcriticalProfileMatchingExponent subcriticalLogWeight
  split_ifs
  · exact neg_nonpos.mpr (by positivity)
  · exact Real.log_nonpos (subcriticalFiniteMax_nonneg _ _)
      (subcriticalProfileMatchingWeight_le_one_of_ell_zero F p m C alpha delta epsilon hell)

/-- The completed residual estimate includes zero matching without assuming
that any of its probability maxima are nonzero. -/
theorem subcriticalResidualMatchingEstimateCore_all_ell
    {n : ℕ} {D : SubcriticalDivision k (Fin n)} {alpha delta epsilon : ℝ}
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C : ℝ) (heta : 0 < eta) (hetaOne : eta ≤ 1) (hR₀ : 1 ≤ R₀)
    (hnum : SubcriticalResidualMatchingConditions k eta R₀ theta alpha delta epsilon n)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ))
    (hfree : ∀ G ∈ F, ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : ∀ G ∈ F, (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2) :
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon ≤
      -(subcriticalResidualMatchingConstant k eta R₀ /
        (2 * subcriticalResidualMatchingKappa eta R₀)) * p.ell * n := by
  by_cases hell : p.ell = 0
  · simpa [hell] using subcriticalProfileMatchingExponent_nonpos_of_ell_zero
      F p m C alpha delta epsilon hell
  · exact subcriticalResidualMatchingEstimateCore hk J F p m C heta hetaOne hR₀
      hnum hpart hvisible hfree hdefect (Nat.one_le_iff_ne_zero.mpr hell)

end InducedStars
