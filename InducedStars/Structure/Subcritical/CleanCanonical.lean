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

end InducedStars
