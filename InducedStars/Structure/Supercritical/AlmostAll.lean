import InducedStars.Structure.Supercritical.CoPartiteFamilies
import InducedStars.Asymptotics.RoughStructure
import InducedStars.Main.VariationalConsequences

/-!
# Final supercritical asymptotic interfaces

This file contains the graphon-distance identification and, downstream, the
finite exceptional-family aggregation and paper-facing limit theorem.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-! ## The supercritical optimizer set is one cut-equivalence class -/

/-- At and above the transition, distance to the complete fixed-density
optimizer set is exactly distance to the distinguished representative
`Wstar`.  This is equality of cut distances, not literal equality of graphon
representatives. -/
theorem cutDistToSet_fixedDensityOptimizers_eq_Wstar
    (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ) (hgamma : gamma ∈ Ico (gammaK k) 1)
    (W : Graphon) :
    cutDistToSet W (fixedDensityOptimizers k gamma) =
      cutDist W (Wstar k hk gamma hgamma) := by
  have hgammaIoo : gamma ∈ Ioo (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).trans_le hgamma.1, hgamma.2⟩
  have hWstarCandidate :
      Wstar k hk gamma hgamma ∈ candidateOptimizerFamily k gamma := by
    rw [candidateOptimizerFamily_of_ge hk hgammaIoo hgamma.1]
    simp
  have hWstarOptimizer :
      Wstar k hk gamma hgamma ∈ fixedDensityOptimizers k gamma :=
    candidate_mem_fixedDensityOptimizers k hk gamma hgammaIoo
      hWstarCandidate
  apply le_antisymm
  · exact cutDistToSet_le W hWstarOptimizer
  · rw [le_cutDistToSet_iff
      (fixedDensityOptimizers_nonempty k hk gamma hgammaIoo)]
    intro U hU
    obtain ⟨V, hV, hUV⟩ :=
      exists_candidate_cutEquivalent_of_optimizer
        k hk gamma hgammaIoo U hU
    have hVeq : V = Wstar k hk gamma hgamma := by
      rw [candidateOptimizerFamily_of_ge hk hgammaIoo hgamma.1] at hV
      simpa only [mem_singleton_iff] using hV
    subst V
    calc
      cutDist W (Wstar k hk gamma hgamma) ≤
          cutDist W U + cutDist U (Wstar k hk gamma hgamma) :=
        cutDist_triangle W U (Wstar k hk gamma hgamma)
      _ = cutDist W U := by rw [hUV, add_zero]

/-- The paper's Wstar-far finite family is literally the optimizer-set-far
family used by the fixed-density rough-structure theorem. -/
theorem supercriticalFarGraphFinset_eq_fixedDensityOptimizerFarGraphFinset
    (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ) (hgamma : gamma ∈ Ico (gammaK k) 1)
    (m : ℕ → ℕ) (n : ℕ) (tau : ℝ) :
    supercriticalFarGraphFinset k hk gamma hgamma (m n) n tau =
      fixedDensityOptimizerFarGraphFinset k gamma tau m n := by
  classical
  ext G
  rw [mem_supercriticalFarGraphFinset,
    mem_fixedDensityOptimizerFarGraphFinset,
    cutDistToSet_fixedDensityOptimizers_eq_Wstar k hk gamma hgamma]

/-- Rough structure in the exact cardinality form used by the final union
bound.  The exponential constant is fixed before the edge-count sequence. -/
theorem eventually_supercriticalFarTotal_le
    (k : ℕ) (hk : 3 ≤ k)
    (gamma : ℝ) (hgamma : gamma ∈ Ico (gammaK k) 1)
    (tau : ℝ) (htau : 0 < tau) :
    ∃ cFar : ℝ, 0 < cFar ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m gamma →
        ∀ᶠ n in atTop,
          ((supercriticalFarGraphFinset
              k hk gamma hgamma (m n) n tau).card : ℝ) ≤
            (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) *
              Real.exp (-cFar * (n : ℝ) ^ 2) := by
  have hgammaIoo : gamma ∈ Ioo (0 : ℝ) 1 :=
    ⟨(gammaK_pos hk).trans_le hgamma.1, hgamma.2⟩
  obtain ⟨cFar, hcFar, hrough⟩ :=
    inducedStarFixedDensityRoughStructure
      k hk gamma hgammaIoo tau htau
  refine ⟨cFar, hcFar, ?_⟩
  intro m hm
  have hnonempty :=
    eventually_inducedStarFreeGraphFinsetWithEdges_nonempty
      k hk gamma hgammaIoo m hm
  filter_upwards [hrough m hm, hnonempty] with n hn hne
  rw [supercriticalFarGraphFinset_eq_fixedDensityOptimizerFarGraphFinset
    k hk gamma hgamma m n tau]
  rw [fixedDensityOptimizerFarProbability_eq_card_ratio] at hn
  have hden : (0 : ℝ) <
      (inducedStarFreeGraphCountWithEdges k n (m n) : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hne
  simpa [mul_comm] using (div_le_iff₀ hden).mp hn

end InducedStars
