import InducedStars.Structure.Subcritical.ClosenessSetup
import InducedStars.Structure.Subcritical.ClosenessResult
import InducedStars.FiniteModels.GraphFamilies

/-!
# The complete subcritical cut-to-division bridge

Paper: Lemma `lemma:WtoWtildeMetricsK1k` and Corollary `cor:cut-closeness`.
The structural parameters are fixed before the cut radius, and that radius
is fixed before the candidate representation. The full result uses one
reference permutation and the canonical division of the original graph.
Matrix discrepancies count ordered pairs, and the alignment proof uses consistently signed rectangles. Unordered edit counts retain the factor two.
-/

noncomputable section

namespace InducedStars

open DenseGraph

/-- Capability-parametric full bridge. The result holds for every positive
choice of the structural tolerances, hence in particular in the paper's
successive small-parameter hierarchy. Only the finite order threshold may
depend on the explicit candidate representation. -/
theorem subcriticalCloseStructureCore
    (alignment : FiniteWeightedAlignmentInput)
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ G : SimpleGraph (Fin n),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            Nonempty (SubcriticalCloseStructureResult hk G
              (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
              L R₀ omega eta theta alpha delta epsilon) := by
  obtain ⟨P⟩ := exists_subcriticalClosenessParameters k R₀ hk hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  obtain ⟨tau, htau, hmain⟩ := subcriticalCanonicalAlignmentCore alignment k hk R₀ P
  refine ⟨tau, htau, ?_⟩
  intro L
  obtain ⟨n0, hn0, hmain⟩ := hmain L
  refine ⟨n0, hn0, ?_⟩
  intro n hn G hG
  have hnpos : 0 < n := by have := hn0.trans hn; omega
  obtain ⟨pi, hedit, hcut, hround, hdiag, ⟨A⟩⟩ := hmain hn G hG
  exact ⟨subcriticalCloseStructureResult_of_alignment hk hnpos G _ L R₀
    omega eta theta alpha delta epsilon hR₀ homega heta htheta halpha
    P pi A hedit hcut hround hdiag⟩

/-- Project-facing full bridge using only the approved finite weighted
alignment input. Paper: Lemma `lemma:WtoWtildeMetricsK1k`, all five items.
Compatibility remains relative to the explicitly supplied block sequence.
The canonical selector is not asserted to commute with relabeling. -/
theorem subcriticalCloseStructure
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
        ∀ G : SimpleGraph (Fin n),
          cutDist (graphGraphon G) (WLambda hk L) < tau →
            Nonempty (SubcriticalCloseStructureResult hk G
              (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
              L R₀ omega eta theta alpha delta epsilon) :=
  subcriticalCloseStructureCore PriorInstances.finiteWeightedAlignmentInput
    k hk R₀ hR₀ omega eta theta alpha delta epsilon
    homega heta htheta halpha hdelta hepsilon

/-- The paper's labeled induced-star-free exact-edge cut ball. This finite
filter imposes no choice of division or reference permutation. -/
def subcriticalCandidateCutBallGraphFinset
    (k n m : ℕ) (W : Graphon) (tau : ℝ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact (inducedStarFreeGraphFinsetWithEdges k n m).filter
    fun G ↦ cutDist (graphGraphon G) W < tau

@[simp] theorem mem_subcriticalCandidateCutBallGraphFinset
    {k n m : ℕ} {W : Graphon} {tau : ℝ} {G : SimpleGraph (Fin n)} :
    G ∈ subcriticalCandidateCutBallGraphFinset k n m W tau ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧
        cutDist (graphGraphon G) W < tau := by
  classical
  simp [subcriticalCandidateCutBallGraphFinset]

/-- Paper: Lemma `lemma:WtoWtildeMetricsK1k` for the exact-edge cut ball
around a subcritical candidate. All five conclusions, and the quantitative
visible-set cut corollary retained in the result, refer to the canonical
division of `G`. The representation is explicit, not chosen anew for each
component. The stronger core needs neither the edge count nor freeness. -/
theorem subcriticalCloseStructure_of_mem_candidateCutBall
    (k : ℕ) (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (0 : ℝ) (gammaK k))
    (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (omega eta theta alpha delta epsilon : ℝ)
    (homega : 0 < omega) (heta : 0 < eta) (htheta : 0 < theta)
    (halpha : 0 < alpha) (hdelta : 0 < delta) (hepsilon : 0 < epsilon) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ L : AdmissibleBlockSequence k,
      WLambda hk L ∈ candidateOptimizerFamily k gamma →
        ∃ n0 : ℕ, ∃ hn0 : k - 1 ≤ n0, ∀ {n : ℕ}, (hn : n0 ≤ n) →
          ∀ (m : ℕ) (G : SimpleGraph (Fin n)),
            G ∈ subcriticalCandidateCutBallGraphFinset k n m (WLambda hk L) tau →
              Nonempty (SubcriticalCloseStructureResult hk G
                (canonicalSubcriticalDivision G R₀ hk (by simpa using hn0.trans hn))
                L R₀ omega eta theta alpha delta epsilon) := by
  obtain ⟨tau, htau, hmain⟩ := subcriticalCloseStructure k hk R₀ hR₀
    omega eta theta alpha delta epsilon homega heta htheta halpha hdelta hepsilon
  refine ⟨tau, htau, ?_⟩
  intro L _hL
  obtain ⟨n0, hn0, hmain⟩ := hmain L
  refine ⟨n0, hn0, ?_⟩
  intro n hn m G hG
  exact hmain hn G (mem_subcriticalCandidateCutBallGraphFinset.mp hG).2

end InducedStars
