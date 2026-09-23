import DenseGraph.Graphon.FiniteCutCover
import InducedStars.Structure.Subcritical.DistinguishedReference
import InducedStars.Graphon.SetDistance
import InducedStars.Graphon.OptimizerClassification
import InducedStars.PriorInstances

/-!
# Finite candidate covers away from the distinguished optimizer

The cover uses the cut pseudometric and actual candidate representations.
It does not assert uniqueness of subcritical entropy optimizers or L1
compactness of their selected representatives.
-/

noncomputable section
open Set
namespace InducedStars

/-- Finite nets within the separated candidate family. Every centre carries
an actual candidate representation and retains the requested separation. -/
theorem subcriticalSeparatedCandidateNet
    (C : DenseGraph.SequentialCompactnessInput)
    (k : ℕ) (hk : 3 ≤ k) {gamma separation epsilon : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (hepsilon : 0 < epsilon) :
    ∃ F : Finset (AdmissibleBlockSequence k),
      (∀ L ∈ F, IsSubcriticalCandidate k gamma L ∧
        separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma)) ∧
      ∀ L : AdmissibleBlockSequence k, IsSubcriticalCandidate k gamma L →
        separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) →
        ∃ L' ∈ F, cutDist (WLambda hk L) (WLambda hk L') < epsilon := by
  classical
  let S : Set Graphon := {W | ∃ L : AdmissibleBlockSequence k,
    IsSubcriticalCandidate k gamma L ∧
      separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) ∧
      WLambda hk L = W}
  obtain ⟨A, hA, hcover⟩ := C.exists_finite_cut_cover S hepsilon
  have hex : ∀ U : ↥A, ∃ L : AdmissibleBlockSequence k,
      IsSubcriticalCandidate k gamma L ∧
        separation ≤ cutDist (WLambda hk L) (subcriticalDistinguishedGraphon k hk gamma hgamma) ∧
        WLambda hk L = U.val := fun U ↦ hA U.val U.property
  choose f hf hfar heq using hex
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hL
    exact ⟨hf U, hfar U⟩
  · intro L hL hsep
    obtain ⟨U, hU, hdist⟩ := hcover (WLambda hk L) ⟨L, hL, hsep, rfl⟩
    refine ⟨f ⟨U, hU⟩, Finset.mem_image.mpr ⟨⟨U, hU⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [heq] using hdist

/-- A single finite list of separated candidate centres covers every
optimizer-near graphon separated from Wdist. The radius is fixed before
the centres and their representation-dependent finite thresholds.
This is the noncircular finite-cover step in the subcritical comparison. -/
theorem subcriticalSeparatedCandidateFiniteCover
    (k : ℕ) (hk : 3 ≤ k) {gamma separation tau : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (hsep : 0 < separation) (htau : 0 < tau) (hcap : tau ≤ separation) :
    ∃ F : Finset (AdmissibleBlockSequence k),
      (∀ L ∈ F, IsSubcriticalCandidate k gamma L ∧
        separation / 2 ≤ cutDist (WLambda hk L)
          (subcriticalDistinguishedGraphon k hk gamma hgamma)) ∧
      ∀ X : Graphon, separation ≤ cutDist X (subcriticalDistinguishedGraphon k hk gamma hgamma) →
        cutDistToSet X (fixedDensityOptimizers k gamma) < tau / 4 →
        ∃ L ∈ F, cutDist X (WLambda hk L) < tau := by
  have hg : gamma ∈ Ioo (0 : ℝ) 1 := ⟨hgamma.1, hgamma.2.trans (gammaK_lt_one hk)⟩
  obtain ⟨F, hF, hcover⟩ := subcriticalSeparatedCandidateNet PriorInstances.sequentialCompactnessInput
    k hk (separation := separation / 2) hgamma (show 0 < tau / 4 by positivity)
  refine ⟨F, hF, ?_⟩
  intro X hfar hnear
  have hex : ∃ W ∈ fixedDensityOptimizers k gamma, cutDist X W < tau / 4 := by
    by_contra h
    push_neg at h
    have hle := (le_cutDistToSet_iff (fixedDensityOptimizers_nonempty k hk gamma hg) (tau / 4)).mpr h
    linarith
  obtain ⟨W, hW, hXW⟩ := hex
  obtain ⟨V, hV, hWV⟩ := exists_candidate_cutEquivalent_of_optimizer k hk gamma hg W hW
  rw [candidateOptimizerFamily_of_lt hk hg hgamma.2] at hV
  obtain ⟨L, hL, rfl⟩ := hV
  have hXL : cutDist X (WLambda hk L) < tau / 4 := by
    have htri := cutDist_triangle X W (WLambda hk L)
    rw [hWV, add_zero] at htri
    exact htri.trans_lt hXW
  have hLfar : separation / 2 ≤ cutDist (WLambda hk L)
      (subcriticalDistinguishedGraphon k hk gamma hgamma) := by
    have htri := cutDist_triangle X (WLambda hk L)
      (subcriticalDistinguishedGraphon k hk gamma hgamma)
    linarith
  obtain ⟨L', hL', hLL'⟩ := hcover L hL hLfar
  refine ⟨L', hL', ?_⟩
  have htri := cutDist_triangle X (WLambda hk L) (WLambda hk L')
  linarith

end InducedStars
