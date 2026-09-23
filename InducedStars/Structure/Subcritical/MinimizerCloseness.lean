import InducedStars.Structure.Subcritical.Closeness

/-!
# Close structure for every global minimum

The retained-key comparison uses a remainder-dependent minimizing completion as an auxiliary
counting witness. Its selector need not equal `canonicalSubcriticalDivision`.
The existing bridge uses canonicality only for the numerical edit bound:
the finite repair, component alignment, and five structural conclusions
already apply to an arbitrary division. These additive adapters retain the
original selector and every earlier public statement unchanged.
-/

noncomputable section
namespace InducedStars

open DenseGraph FiniteWeightedGraph

/-- Global minimizers have the same cost, without an assertion about their
identity, component ordering, retained key, or tie-breaking rule. -/
theorem subcriticalDefectCost_eq_canonical_of_global_minimal
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (R₀ : ℕ) (hk : 3 ≤ k) (hcard : k - 1 ≤ Fintype.card V)
    (hmin : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E) :
    subcriticalDefectCost G D = canonicalSubcriticalDefectCost G R₀ hk hcard := by
  exact Nat.le_antisymm (hmin _) (canonicalSubcriticalDivision_minimal G R₀ hk hcard D)

/-- Pure finite alignment for an arbitrary repaired division with a small
edit cost. This is the existing alignment calculation, with no selector or
minimality hypothesis. The rectangle signs are consistent, and unordered edit counts carry the matrix factor two. -/
theorem subcriticalComponentAlignment_of_small_defect
    {k n R₀ : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k)
    {omega eta theta alpha delta epsilon : ℝ}
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon)
    (pi : Equiv.Perm (Fin n))
    (hedit : (subcriticalDefectCost G D : ℝ) ≤ P.epsilonWork * (n : ℝ)^2)
    (hcut : finiteLabeledCutDist (ofSimpleGraph G)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ P.beta)
    (hround : 4 ≤ P.t * n / 4)
    (hdiag : 2 ≤ subcriticalPaletteGap k * (P.zeta * n)) :
    Nonempty (SubcriticalComponentAlignment D L pi P.t (P.zeta * n) P.B) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let H := subcriticalDivisionModelGraph G D
  have hcompare := subcritical_repaired_reference_cut_le hn G D
    ((subcriticalReferenceWeightedGraph hk L n).permute pi) hedit hcut
  have hfinite : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ)^2 <
        subcriticalPaletteGap k * (P.zeta * n)^2 := by
    have hh := mul_lt_mul_of_pos_right (hcompare.trans_lt P.contradiction_reserve)
      (sq_pos_of_pos hnR)
    nlinarith only [hh]
  apply subcritical_exists_component_alignment hk hn D H
    (subcriticalDivisionModelGraph_isRegularBlowupFor G D) L pi P.t_pos
    (mul_pos P.zeta_pos hnR) P.B P.four_div_t_le_B
  · have h := mul_le_mul_of_nonneg_right P.degree_reserve hnR.le
    nlinarith only [h]
  · exact hround
  · exact hdiag
  · have h := mul_le_mul_of_nonneg_right P.cell_error_reserve hnR.le
    push_cast at h
    have hz := mul_pos P.zeta_pos hnR
    nlinarith
  · exact hfinite

/-- The same uniform radius and reference alignment work for every global
minimizer. Only the equality of minimum costs is transferred; the finite
component alignment is constructed afresh for the specified division.
No canonical-selector independence is asserted or needed. -/
theorem subcriticalMinimizerAlignmentCore
    (alignment : FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ)
    {omega eta theta alpha delta epsilon : ℝ}
    (P : SubcriticalClosenessParameters k R₀ omega eta theta alpha delta epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
          (∀ E : SubcriticalDivision k (Fin n),
            subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            ∃ pi : Equiv.Perm (Fin n),
              (subcriticalDefectCost G D : ℝ) ≤ P.epsilonWork * (n : ℝ)^2 ∧
              finiteLabeledCutDist (ofSimpleGraph G)
                ((subcriticalReferenceWeightedGraph hk L n).permute pi) ≤ P.beta ∧
              4 ≤ P.t * n / 4 ∧
              2 ≤ subcriticalPaletteGap k * (P.zeta * n) ∧
              Nonempty (SubcriticalComponentAlignment D L pi P.t (P.zeta * n) P.B) := by
  obtain ⟨tau, htau, hmain⟩ := subcriticalCanonicalAlignmentCore alignment k hk R₀ P
  refine ⟨tau, htau, ?_⟩
  intro L
  obtain ⟨n0, hn0, hmain⟩ := hmain L
  refine ⟨n0, hn0, ?_⟩
  intro n hn G D hmin hG
  obtain ⟨pi, hedit, hcut, hround, hdiag, _hCanonicalAlignment⟩ := hmain hn G hG
  have hcost := subcriticalDefectCost_eq_canonical_of_global_minimal G D R₀ hk
    (by simpa using hn0.trans hn) hmin
  have heditD : (subcriticalDefectCost G D : ℝ) ≤ P.epsilonWork * (n : ℝ)^2 := by
    rw [hcost]
    exact hedit
  have hnpos : 0 < n := by have := hn0.trans hn; omega
  exact ⟨pi, heditD, hcut, hround, hdiag,
    subcriticalComponentAlignment_of_small_defect hk hnpos G D L P pi
      heditD hcut hround hdiag⟩

/-- Capability-parametric minimizer version of all five conclusions of
paper Lemma `lemma:WtoWtildeMetricsK1k`. The cutoff and candidate quantifier
order is unchanged. The statement is valid for all global minimizers, hence
in particular for the ordered fixed-remainder completion used in retained-key counting. -/
theorem subcriticalCloseStructure_of_global_minimalCore
    (alignment : FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
          (∀ E : SubcriticalDivision k (Fin n),
            subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            Nonempty (SubcriticalCloseStructureResult hk G D
              L R₀ omega eta theta alpha delta epsilon) := by
  obtain ⟨P⟩ := exists_subcriticalClosenessParameters k R₀ hk hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  obtain ⟨tau, htau, hmain⟩ := subcriticalMinimizerAlignmentCore alignment k hk R₀ P
  refine ⟨tau, htau, ?_⟩
  intro L
  obtain ⟨n0, hn0, hmain⟩ := hmain L
  refine ⟨n0, hn0, ?_⟩
  intro n hn G D hmin hG
  have hnpos : 0 < n := by have := hn0.trans hn; omega
  obtain ⟨pi, hedit, hcut, hround, hdiag, ⟨A⟩⟩ := hmain hn G D hmin hG
  exact ⟨subcriticalCloseStructureResult_of_alignment hk hnpos G D L R₀
    omega eta theta alpha delta epsilon hR₀ homega heta htheta halpha
    P pi A hedit hcut hround hdiag⟩

/-- Project-facing global-minimizer bridge. Its only external input is the
existing finite weighted alignment theorem. The retained-key comparison preserves the existing
canonical selector and does not identify different global minimizers. -/
theorem subcriticalCloseStructure_of_global_minimal
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
          (∀ E : SubcriticalDivision k (Fin n),
            subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            Nonempty (SubcriticalCloseStructureResult hk G D
              L R₀ omega eta theta alpha delta epsilon) :=
  subcriticalCloseStructure_of_global_minimalCore PriorInstances.finiteWeightedAlignmentInput
    k hk R₀ hR₀ omega eta theta alpha delta epsilon
    homega heta htheta halpha hdelta hepsilon

/-- Exact-edge candidate-ball specialization for an arbitrary global
minimizer. This is the minimizing-completion adapter used after selecting one
completion for a fixed retained key and fixed remainder graph. -/
theorem subcriticalCloseStructure_of_global_minimal_of_mem_candidateCutBall
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n)),
            (∀ E : SubcriticalDivision k (Fin n),
              subcriticalDefectCost G D ≤ subcriticalDefectCost G E) →
            G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau →
              Nonempty (SubcriticalCloseStructureResult hk G D
                L R₀ omega eta theta alpha delta epsilon) := by
  obtain ⟨tau, htau, hmain⟩ := subcriticalCloseStructure_of_global_minimal
    k hk R₀ hR₀ omega eta theta alpha delta epsilon
    homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨n0, hn0, hmain⟩ := hmain L
  refine ⟨n0, hn0, ?_⟩
  intro n hn m G D hmin hG
  exact hmain hn G D hmin (mem_subcriticalCandidateCutBallGraphFinset.mp hG).2

end InducedStars
