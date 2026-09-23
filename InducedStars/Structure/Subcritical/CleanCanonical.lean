import InducedStars.Structure.Subcritical.CleanFamilies
import InducedStars.Structure.Subcritical.CleanModelGeometry
import InducedStars.Structure.Subcritical.RetainedMembership

/-!
# Canonical clean fibers embed into the exact clean model family

Paper: the clean term of `lemma:NtaunmWUpperBdK1k`. The geometric witness
is the already selected common close-structure witness. This module does
not select another cut radius, assert canonicality of model graphs, or
prove the later canonical-clean lower bound.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

theorem subcriticalRemainderGraph_edgeCount
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card =
      inducedEdgeCount G (D.nonretainedVertices eta R₀) := by
  congr 1
  ext z
  simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rfl

/-- For a clean actual graph the exact signed shift is the actual
nonretained edge count, with no absolute-value or rounding error. -/
theorem retainedEdgeShift_eq_remainder_of_clean
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (G : SimpleGraph V)
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥) :
    retainedEdgeShift G D eta R₀ =
      ((finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card : ℤ) := by
  have hz := subcriticalSignedDefectSize_actual G D eta R₀
  have hb : finiteGraphEdges (⊥ : SimpleGraph V) = ∅ := by ext z; simp
  rw [hclean] at hz
  simp only [subcriticalSignedDefectSize, hb, Finset.card_empty,
    Finset.empty_inter, Nat.cast_zero, mul_zero, sub_self] at hz
  rw [retainedEdgeShift_eq_nonretained_add_present_sub_missing,
    subcriticalRemainderGraph_edgeCount]
  omega

namespace SubcriticalCloseStructureResult

variable {k n R₀ m : ℕ} {hk : 3 ≤ k}
  {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {L : AdmissibleBlockSequence k} {omega eta theta alpha delta epsilon : ℝ}

/-- Actual clean graphs supplied by the common bridge are represented by
the exact wide-level model family. -/
theorem mem_cleanModelGraphFinset
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    (hdelta : 0 ≤ delta) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (homega : omega ≤ 1) (hepsilon : epsilon ≤ min eta (theta ^ 2))
    (hscale : 1 ≤ theta * n)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    (hedges : (finiteGraphEdges G).card = m)
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥) :
    G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta := by
  have hRreal : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
  have hthetaEta : theta ≤ eta :=
    hcutoff.trans (div_le_self heta (by linarith))
  have hb := (R.sparseSideControls heta hR hinv homega hthetaEta
    (hepsilon.trans (min_le_left _ _)) (hepsilon.trans (min_le_right _ _))
    hscale hfree).1
  apply mem_subcriticalCleanModelGraphFinset_of_clean G hclean hfree
  · simpa only [Fintype.card_fin, subcriticalRemainderGraph_edgeCount] using hb
  · have hv := R.actualRetainedEdgeCountVector_mem_narrowLevel
      hR heta htheta hcutoff halpha hedges
    rw [retainedEdgeShift_eq_remainder_of_clean G hclean] at hv
    exact retainedNarrowEdgeCountLevel_subset D eta R₀ m hdelta _ hv

end SubcriticalCloseStructureResult

/-- Finite geometry-level comparison; only clean members need a geometric
witness. The map to actual model graphs is the identity on labeled graphs. -/
theorem subcriticalCleanDivision_card_le_of_geometry
    {k n R₀ m : ℕ} (hk : 3 ≤ k)
    (F : Finset (SimpleGraph (Fin n))) (D : SubcriticalDivision k (Fin n))
    (L : AdmissibleBlockSequence k) (omega eta theta alpha delta epsilon : ℝ)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    (hdelta : 0 ≤ delta) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (homega : omega ≤ 1) (hepsilon : epsilon ≤ min eta (theta ^ 2))
    (hscale : 1 ≤ theta * n)
    (hfree : ∀ G ∈ F, ¬Regularity.InducedEmbeds (inducedStar k) G)
    (hedges : ∀ G ∈ F, (finiteGraphEdges G).card = m)
    (hbridge : ∀ G ∈ subcriticalCleanDivisionGraphFinset F D eta R₀,
      Nonempty (SubcriticalCloseStructureResult hk G D L R₀
        omega eta theta alpha delta epsilon)) :
    (subcriticalCleanDivisionGraphFinset F D eta R₀).card ≤
      cleanRetainedPartitionFunction D eta R₀ m delta := by
  rw [← card_subcriticalCleanModelGraphFinset]
  apply Finset.card_le_card
  intro G hG
  obtain ⟨hF, hclean⟩ := (mem_subcriticalCleanDivisionGraphFinset F G).mp hG
  obtain ⟨R⟩ := hbridge G hG
  exact R.mem_cleanModelGraphFinset hR heta htheta hcutoff halpha hdelta hinv
    homega hepsilon hscale (hfree G hF) (hedges G hF) hclean

/-- Canonical clean-fiber bound at the radius already supplied by the common
bridge. No model graph is required to have canonical division `D`. -/
theorem subcriticalCleanCandidateDivision_card_le
    {k n R₀ m : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    (D : SubcriticalDivision k (Fin n)) (L : AdmissibleBlockSequence k)
    (omega eta theta alpha delta epsilon tau : ℝ)
    (hR : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 ≤ theta)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ))) (halpha : alpha ≤ 4)
    (hdelta : 0 ≤ delta) (hinv : 1 / (R₀ : ℝ) ≤ eta)
    (homega : omega ≤ 1) (hepsilon : epsilon ≤ min eta (theta ^ 2))
    (hscale : 1 ≤ theta * n)
    (hbridge : ∀ G : SimpleGraph (Fin n),
      cutDist (graphGraphon G) (WLambda hk L) < tau →
      Nonempty (SubcriticalCloseStructureResult hk G
        (canonicalSubcriticalDivision G R₀ hk (by simpa using hn))
        L R₀ omega eta theta alpha delta epsilon)) :
    (subcriticalCleanDivisionGraphFinset
      (subcriticalCandidateDivisionGraphFinset k n m (WLambda hk L) tau R₀ hk hn D)
      D eta R₀).card ≤ cleanRetainedPartitionFunction D eta R₀ m delta := by
  apply subcriticalCleanDivision_card_le_of_geometry hk _ D L
    omega eta theta alpha delta epsilon hR heta htheta hcutoff halpha
    hdelta hinv homega hepsilon hscale
  · intro G hG
    exact (mem_inducedStarFreeGraphFinsetWithEdges.mp
      (mem_subcriticalCandidateCutBallGraphFinset.mp
        (mem_subcriticalCandidateDivisionGraphFinset.mp hG).1).1).1
  · intro G hG
    have hh := (mem_inducedStarFreeGraphFinsetWithEdges.mp
      (mem_subcriticalCandidateCutBallGraphFinset.mp
        (mem_subcriticalCandidateDivisionGraphFinset.mp hG).1).1).2
    simpa only [finiteGraphEdges_card_eq_edgeFinset_card] using hh
  · intro G hG
    obtain ⟨hF, _⟩ := (mem_subcriticalCleanDivisionGraphFinset _ G).mp hG
    obtain ⟨hball, hcanonical⟩ := mem_subcriticalCandidateDivisionGraphFinset.mp hF
    have hh := hbridge G (mem_subcriticalCandidateCutBallGraphFinset.mp hball).2
    simpa only [hcanonical] using hh

end InducedStars
