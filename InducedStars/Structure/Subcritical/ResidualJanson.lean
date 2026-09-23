import InducedStars.Structure.Subcritical.ResidualStarPolarity
import InducedStars.Structure.Subcritical.ResidualCandidateGeometryOverlap
import InducedStars.Structure.Subcritical.ResidualMatchingScalars
import InducedStars.Structure.Subcritical.ResidualPatternGeometry

/-!
# Residual matching probability in the retained active model

Paper: the uniform probability step in `lemma:residual-matching-estimate-K1k`.
Actual homogeneous matching selections supply the stars, their abundance,
their global polarity, and their unordered overlap bound. Local
endpoint cleaning is part of the finite counting argument. The arbitrary remainder graph
does not need to be fixed across residual patterns.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped Classical
namespace InducedStars
variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta theta alpha : ℝ} {p : SubcriticalProfile D eta R₀ theta}
  {F : Finset (SimpleGraph (Fin n))} {TB R L : SimpleGraph (Fin n)}

set_option maxHeartbeats 800000 in
-- The finite candidate type and Bernoulli coordinates are dependent on the matching.
/-- The actual thinned homogeneous matching gives a uniform residual-safe
probability estimate, for every compatible remainder and narrow vector. -/
theorem subcriticalResidualMatchingSafeProbability_le
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (heta : 0 < eta) (hR₀ : 1 ≤ R₀)
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    {m : ℕ} {C delta epsilon d : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (hdelta : delta ≤ subcriticalPaletteGap k / 2)
    (hd0 : 0 ≤ d) (hd : d ≤ subcriticalResidualDegreeCap k eta R₀)
    (hdegree : ∀ v, (R.degree v : ℝ) ≤ d * n)
    (hpart : ∀ a ∈ D.retainedPartIndices eta R₀,
      eta * n / (2 * (R₀ : ℝ)) ≤ ((D.part a).card : ℝ))
    (hroots : (p.roots.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 2)
    (hsmall : (M.edges.card : ℝ) ≤ subcriticalResidualMatchingLambda eta R₀ * n / 8)
    (hlarge : subcriticalResidualMatchingLambda eta R₀ * p.ell /
      (8 * (subcriticalResidualMatchingKappa eta R₀ : ℝ)) ≤ (M.edges.card : ℝ)) :
    subcriticalResidualSafeProbability p H TB R L mvec ≤
      Real.exp (-(subcriticalResidualMatchingConstant k eta R₀ /
        subcriticalResidualMatchingKappa eta R₀) * p.ell * n) := by
  letI : LinearOrder M.Candidate :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  let K : M.Candidate → SubcriticalResidualStarWitness p R M.Role M.candidateCenter :=
    fun c ↦ M.selectionWitness c.1 c.2
  have hlambda := subcriticalResidualMatchingLambda_pos heta hR₀
  have hcard := M.candidate_card_lower hk heta hR₀ hpart hroots hsmall hd0 hdegree
    (subcriticalResidualDegreeCap_endpoint k heta hR₀ hd)
    (subcriticalResidualDegreeCap_free k hd0 hd)
  have hpairs := M.candidate_unorderedOverlap_card_le hk
  have hprob := subcriticalResidualWitnessFamily_probability_le K
    (card_subcriticalResidualStarRole hk M.placement.leftPart) hk J h H mvec hm hdelta
    M.globalFlip (fun c ↦ M.present_disjoint_globalFlip c.1 c.2)
    (fun c ↦ M.absent_subset_globalFlip c.1 c.2)
    (subcriticalResidualCandidateRate_pos k hlambda)
    (subcriticalResidualDependencyCoefficient_pos k) hcard hpairs
  have hcJ := subcriticalResidualJansonLinearConstant_pos
    (subcriticalResidualMuCoefficient_pos hk heta hR₀)
    (subcriticalResidualDependencyCoefficient_pos k)
  have hkappa : (0 : ℝ) < subcriticalResidualMatchingKappa eta R₀ := by
    have hh := subcriticalResidualMatchingKappa_pos heta hR₀
    exact_mod_cast (show 0 < subcriticalResidualMatchingKappa eta R₀ by omega)
  exact hprob.trans (by
    simpa only [subcriticalResidualMatchingConstant, subcriticalResidualMuCoefficient,
      neg_mul, mul_assoc] using subcriticalResidualCandidateRate_le_matchingRate
        hcJ.le hlambda.le hkappa hlarge)

end InducedStars
