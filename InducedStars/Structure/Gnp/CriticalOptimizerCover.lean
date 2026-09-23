import DenseGraph.Graphon.FiniteCutCover
import DenseGraph.Graphon.ZeroDistance
import InducedStars.Graphon.SupercriticalClassification
import InducedStars.Main.VariationalConsequences
import InducedStars.PriorInstances

/-!
# Critical optimizer representatives and separated finite cut covers

The endpoint density `gammaK k` is included explicitly: its distinguished
graphon is cut-equivalent to the admissible complete block of length one.
All finite-cover arguments use cut sequential compactness, not compactness
in the stronger L1 distance on selected representatives.
-/

noncomputable section

open Set

namespace InducedStars

/-- The full-length complete admissible block represents the critical
endpoint candidate. The quantitative profile-block estimate has zero error
at length one, including the different canonical endpoint conventions. -/
theorem cutDist_oneBlockSequence_one_Wstar_at_gammaK
    (k : ℕ) (hk : 3 ≤ k) :
    cutDist (WLambda hk (oneBlockSequence k hk 1 zero_lt_one le_rfl))
      (Wstar k hk (gammaK k) ⟨le_rfl, gammaK_lt_one hk⟩) = 0 := by
  have hL1 := graphonL1Dist_oneCompleteProfileBlock_Wstar_le hk
    (γ := gammaK k) (α := 1) le_rfl (gammaK_lt_one hk) zero_lt_one le_rfl
  have hzero : graphonL1Dist
      (WLambda hk (oneBlockSequence k hk 1 zero_lt_one le_rfl))
      (Wstar k hk (gammaK k) ⟨le_rfl, gammaK_lt_one hk⟩) ≤ 0 := by
    simpa only [oneCompleteProfileBlockGraphon, supercriticalOffDiagonal_at_gammaK k hk,
      profileWLambda_eq_WLambda hk, sub_self, mul_zero] using hL1
  exact le_antisymm ((cutDist_le_graphonL1Dist _ _).trans hzero) (cutDist_nonneg _ _)

/-- Every nonzero critical conditioned optimizer admits an actual
`WLambda` representative, including the density-`gammaK` endpoint.
The conclusion is cut equivalence, not equality of chosen coordinates. -/
theorem exists_WLambda_cutEquivalent_of_nonzero_criticalGnpOptimizer
    (k : ℕ) (hk : 3 ≤ k) (W : Graphon)
    (hW : W ∈ gnpGraphonOptimizers k (pK k)) (hzero : W ≠ zeroGraphon) :
    ∃ L : AdmissibleBlockSequence k, cutDist W (WLambda hk L) = 0 := by
  obtain ⟨V, hV, hWV⟩ :=
    (mem_gnpGraphonOptimizers_iff_exists_candidate_cutDist_zero k hk (pK k)
      (pK_mem_Ioo (by omega)) W).mp hW
  rw [gnpCandidateFamily_at_pK] at hV
  rcases hV with hVzero | ⟨γ, hγ, hV⟩
  · have heq : V = zeroGraphon := Set.mem_singleton_iff.mp hVzero
    rw [heq, DenseGraph.cutDist_zeroGraphon] at hWV
    exact False.elim (hzero ((graphonEdgeDensity_eq_zero_iff W).mp hWV))
  · by_cases hsub : γ < gammaK k
    · rw [candidateOptimizerFamily_of_lt hk
        ⟨hγ.1, hγ.2.trans_lt (gammaK_lt_one hk)⟩ hsub] at hV
      obtain ⟨L, _hL, rfl⟩ := hV
      exact ⟨L, hWV⟩
    · have heq : γ = gammaK k := le_antisymm hγ.2 (le_of_not_gt hsub)
      subst γ
      rw [candidateOptimizerFamily_at_gammaK k hk] at hV
      have hVeq := Set.mem_singleton_iff.mp hV
      subst V
      refine ⟨oneBlockSequence k hk 1 zero_lt_one le_rfl, ?_⟩
      apply le_antisymm _ (cutDist_nonneg _ _)
      calc
        _ ≤ cutDist W (Wstar k hk (gammaK k) ⟨le_rfl, gammaK_lt_one hk⟩) +
            cutDist (Wstar k hk (gammaK k) ⟨le_rfl, gammaK_lt_one hk⟩)
              (WLambda hk (oneBlockSequence k hk 1 zero_lt_one le_rfl)) :=
          cutDist_triangle _ _ _
        _ = 0 := by
          rw [hWV, zero_add]
          exact (cutDist_comm _ _).trans (cutDist_oneBlockSequence_one_Wstar_at_gammaK k hk)

/-- Finite cut nets of separated admissible representatives. The centers
remain admissible and retain the exact requested separation. -/
theorem criticalGnpSeparatedWLambdaNet
    (C : DenseGraph.SequentialCompactnessInput)
    (k : ℕ) (hk : 3 ≤ k) (separation : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset (AdmissibleBlockSequence k),
      (∀ L ∈ F, separation ≤ cutDist (WLambda hk L) zeroGraphon) ∧
      ∀ L : AdmissibleBlockSequence k,
        separation ≤ cutDist (WLambda hk L) zeroGraphon →
        ∃ L' ∈ F, cutDist (WLambda hk L) (WLambda hk L') < ε := by
  classical
  let S : Set Graphon := {W | ∃ L : AdmissibleBlockSequence k,
    separation ≤ cutDist (WLambda hk L) zeroGraphon ∧ WLambda hk L = W}
  obtain ⟨A, hA, hcover⟩ := C.exists_finite_cut_cover S hε
  have hex : ∀ U : ↥A, ∃ L : AdmissibleBlockSequence k,
      separation ≤ cutDist (WLambda hk L) zeroGraphon ∧ WLambda hk L = U.val :=
    fun U ↦ hA U.val U.property
  choose f hfar heq using hex
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · intro L hL
    obtain ⟨U, _, rfl⟩ := Finset.mem_image.mp hL
    exact hfar U
  · intro L hL
    obtain ⟨U, hU, hdist⟩ := hcover (WLambda hk L) ⟨L, hL, rfl⟩
    refine ⟨f ⟨U, hU⟩, Finset.mem_image.mpr ⟨⟨U, hU⟩, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [heq] using hdist

/-- Paper: the critical finite-net step in the proof of
Theorem `thm:gnp-typ-struc` in `paper/gnp.tex`.

A single finite family of admissible representatives covers all graphons
near the complete critical optimizer set and separated from zero. The
radius is chosen before the finite family and any center-dependent counting
thresholds. Every center retains half the initial separation. -/
theorem criticalGnpSeparatedOptimizerFiniteCover
    (k : ℕ) (hk : 3 ≤ k) {separation τ : ℝ}
    (hsep : 0 < separation) (hτ : 0 < τ) (hcap : τ ≤ separation) :
    ∃ F : Finset (AdmissibleBlockSequence k),
      (∀ L ∈ F, separation / 2 ≤ cutDist (WLambda hk L) zeroGraphon) ∧
      ∀ X : Graphon, separation ≤ cutDist X zeroGraphon →
        cutDistToSet X (gnpGraphonOptimizers k (pK k)) < τ / 4 →
        ∃ L ∈ F, cutDist X (WLambda hk L) < τ := by
  obtain ⟨F, hF, hcover⟩ := criticalGnpSeparatedWLambdaNet
    PriorInstances.sequentialCompactnessInput k hk (separation / 2)
    (show 0 < τ / 4 by positivity)
  refine ⟨F, hF, ?_⟩
  intro X hfar hnear
  have hex : ∃ W ∈ gnpGraphonOptimizers k (pK k), cutDist X W < τ / 4 := by
    by_contra h
    push_neg at h
    have hle := (le_cutDistToSet_iff
      (gnpGraphonOptimizers_nonempty k hk (pK k) (pK_mem_Ioo (by omega))) (τ / 4)).mpr h
    linarith
  obtain ⟨W, hW, hXW⟩ := hex
  have hWzero : W ≠ zeroGraphon := by
    intro hzero
    rw [hzero] at hXW
    linarith
  obtain ⟨L, hWL⟩ :=
    exists_WLambda_cutEquivalent_of_nonzero_criticalGnpOptimizer k hk W hW hWzero
  have hXL : cutDist X (WLambda hk L) < τ / 4 := by
    have htri := cutDist_triangle X W (WLambda hk L)
    rw [hWL, add_zero] at htri
    exact htri.trans_lt hXW
  have hLfar : separation / 2 ≤ cutDist (WLambda hk L) zeroGraphon := by
    have htri := cutDist_triangle X (WLambda hk L) zeroGraphon
    linarith
  obtain ⟨L', hL', hLL'⟩ := hcover L hLfar
  refine ⟨L', hL', ?_⟩
  have htri := cutDist_triangle X (WLambda hk L) (WLambda hk L')
  linarith

end InducedStars
