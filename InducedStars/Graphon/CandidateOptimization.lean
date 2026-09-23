import InducedStars.Graphon.Candidates

/-!
# The explicit candidate family attains the entropy profile

This file is the paper-facing conclusion for the candidate graphons.  Its
proofs only assemble the exact density, induced-freeness, and entropy formulas
proved by the two candidate branches.
-/

noncomputable section

open Set

namespace InducedStars

/-- The distinguished supercritical graphon has all three properties needed
in the candidate-family theorem. -/
theorem Wstar_candidate_properties (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    graphonInducedDensity (inducedStar k) (Wstar k hk γ hγ) = 0 ∧
      graphonEdgeDensity (Wstar k hk γ hγ) = γ ∧
      graphonEntropy (Wstar k hk γ hγ) = entropyDensity k γ := by
  exact ⟨Wstar_inducedStar_free k hk γ hγ,
    graphonEdgeDensity_Wstar k hk γ hγ,
    graphonEntropy_Wstar k hk γ hγ⟩

/-- The distinguished supercritical graphon is feasible at its prescribed
edge density. -/
theorem Wstar_mem_fixedDensityFeasible (k : ℕ) (hk : 3 ≤ k) (γ : ℝ)
    (hγ : γ ∈ Ico (gammaK k) 1) :
    Wstar k hk γ hγ ∈ fixedDensityFeasible k γ := by
  exact ⟨Wstar_inducedStar_free k hk γ hγ,
    graphonEdgeDensity_Wstar k hk γ hγ⟩

/-- A subcritical candidate graphon has the three properties needed in the
candidate-family theorem.  Its induced-freeness proof uses the
closed-neighborhood pigeonhole obstruction in `lemma:Vgamma-opt`. -/
theorem WLambda_candidate_properties {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ < gammaK k) (L : AdmissibleBlockSequence k)
    (hL : IsSubcriticalCandidate k γ L) :
    graphonInducedDensity (inducedStar k) (WLambda hk L) = 0 ∧
      graphonEdgeDensity (WLambda hk L) = γ ∧
      graphonEntropy (WLambda hk L) = entropyDensity k γ := by
  exact ⟨WLambda_inducedStar_free hk L,
    graphonEdgeDensity_WLambda_of_isSubcriticalCandidate hk hL,
    graphonEntropy_WLambda_of_isSubcriticalCandidate hk hγ hL⟩

/-- Paper: Lemma `lemma:Vgamma-opt`.

Every graphon in the explicit candidate family is induced-`K_{1,k}`-free,
has edge density `γ`, and has entropy `entropyDensity k γ`. -/
theorem VgammaOpt
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    {W : Graphon}
    (hW : W ∈ candidateOptimizerFamily k γ) :
    graphonInducedDensity (inducedStar k) W = 0 ∧
      graphonEdgeDensity W = γ ∧
      graphonEntropy W = entropyDensity k γ := by
  by_cases hsub : γ < gammaK k
  · rw [candidateOptimizerFamily_of_lt hk hγ hsub] at hW
    obtain ⟨L, hL, hEq⟩ := (mem_subcriticalCandidateFamily.mp hW)
    subst W
    exact WLambda_candidate_properties hk hsub L hL
  · have hcrit : gammaK k ≤ γ := le_of_not_gt hsub
    rw [candidateOptimizerFamily_of_ge hk hγ hcrit] at hW
    simp only [Set.mem_singleton_iff] at hW
    subst W
    exact Wstar_candidate_properties k hk γ ⟨hcrit, hγ.2⟩

/-- Every member of the explicit candidate family belongs to the
fixed-density feasible set. -/
theorem candidate_mem_fixedDensityFeasible
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    {W : Graphon} (hW : W ∈ candidateOptimizerFamily k γ) :
    W ∈ fixedDensityFeasible k γ := by
  have h := VgammaOpt k hk γ hγ hW
  exact ⟨h.1, h.2.1⟩

/-- The fixed-density feasible set is nonempty throughout the paper's
parameter range.  This is a direct candidate construction, not an
optimizer-existence assumption. -/
theorem exists_fixedDensityFeasible
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ W : Graphon, W ∈ fixedDensityFeasible k γ := by
  obtain ⟨W, hW⟩ := candidateOptimizerFamily_nonempty k hk γ hγ
  exact ⟨W, candidate_mem_fixedDensityFeasible k hk γ hγ hW⟩

end InducedStars
