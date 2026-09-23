import InducedStars.Structure.Subcritical.RetainedKeyCounts
import InducedStars.Structure.Subcritical.CleanModelGeometry

/-!
# Actual clean graph families are retained-key invariants

This is equality of finite families of labeled graphs, not just
equality of their counts. Recovery uses the actual induced remainder and
the exact capacity-preserving retained coordinate equivalence.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def actualRetainedKeyEdgeCountVector (G : SimpleGraph V)
    (K : SubcriticalRetainedKey k V) : RetainedKeyEdgeCountVector K :=
  fun e ↦ ⟨(K.activeEdges e ∩ finiteGraphEdges G).card,
    Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_left)⟩

@[simp] theorem retainedKeyVectorEquiv_actual (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    retainedKeyVectorEquiv D eta R₀ (actualRetainedEdgeCountVector G D eta R₀) =
      actualRetainedKeyEdgeCountVector G (retainedKey D eta R₀) := by
  funext e
  apply Fin.ext
  rw [retainedKeyVectorEquiv_count]
  change _ = ((retainedKey D eta R₀).activeEdges e ∩ finiteGraphEdges G).card
  rw [retainedKeyActiveEquiv_edges]
  exact (actualRetainedActiveEdges_card G D eta R₀ _).symm

theorem actualRetainedEdgeCountVector_mem_level_iff_of_retainedKey_eq
    (G : SimpleGraph V) {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (hkey : retainedKey D eta R₀ = retainedKey E eta R₀)
    (m : ℕ) (delta : ℝ) (u : ℤ) :
    actualRetainedEdgeCountVector G D eta R₀ ∈ retainedEdgeCountLevel D eta R₀ m delta u ↔
      actualRetainedEdgeCountVector G E eta R₀ ∈ retainedEdgeCountLevel E eta R₀ m delta u := by
  rw [← retainedKeyVectorEquiv_mem_level, retainedKeyVectorEquiv_actual,
    hkey, ← retainedKeyVectorEquiv_actual, retainedKeyVectorEquiv_mem_level]

theorem actualRetainedEdgeCountVector_mem_narrowLevel_iff_of_retainedKey_eq
    (G : SimpleGraph V) {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (hkey : retainedKey D eta R₀ = retainedKey E eta R₀)
    (m : ℕ) (delta : ℝ) (u : ℤ) :
    actualRetainedEdgeCountVector G D eta R₀ ∈
      retainedNarrowEdgeCountLevel D eta R₀ m delta u ↔
      actualRetainedEdgeCountVector G E eta R₀ ∈
        retainedNarrowEdgeCountLevel E eta R₀ m delta u := by
  rw [← retainedKeyVectorEquiv_mem_narrowLevel, retainedKeyVectorEquiv_actual,
    hkey, ← retainedKeyVectorEquiv_actual, retainedKeyVectorEquiv_mem_narrowLevel]

/-- Exact membership criterion, including the natural floor cutoff even if
its real argument is negative. No global induced-freeness is assumed. -/
theorem mem_subcriticalCleanModelGraphFinset_iff
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ m : ℕ) (delta : ℝ) :
    G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta ↔
      subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥ ∧
      ¬Regularity.InducedEmbeds (inducedStar k) (subcriticalRemainderGraph G D eta R₀) ∧
      (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card ≤
        Nat.floor (subcriticalSparseSideConstant k * eta * (Fintype.card V : ℝ)^2) ∧
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedEdgeCountLevel D eta R₀ m delta
          (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card := by
  constructor
  · intro hG
    obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hG
    have hH := (mem_subcriticalCleanRemainderGraphFinset d.2.1.val d.1.val).mp
      d.2.1.property
    change subcriticalRetainedIncidentDefectGraph (subcriticalCleanGraph d.2.1.val d.2.2.2)
      D eta R₀ = ⊥ ∧ _
    refine ⟨subcriticalCleanGraph_retainedIncident_empty _ _, ?_⟩
    change (¬Regularity.InducedEmbeds (inducedStar k)
        (subcriticalRemainderGraph (subcriticalCleanGraph d.2.1.val d.2.2.2) D eta R₀)) ∧ _
    simp only [SubcriticalCleanModelData.graph, subcriticalCleanGraph_remainder,
      subcriticalCleanGraph_active_vector, hH.2]
    exact ⟨hH.1, Nat.lt_succ_iff.mp (Finset.mem_range.mp d.1.property), d.2.2.1.property⟩
  · rintro ⟨hclean, hfree, hb, hv⟩
    have hH := (mem_subcriticalCleanRemainderGraphFinset
      (subcriticalRemainderGraph G D eta R₀)
      (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card).mpr ⟨hfree, rfl⟩
    let d : SubcriticalCleanModelData D eta R₀ m delta :=
      ⟨⟨_, Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩,
        ⟨subcriticalRemainderGraph G D eta R₀, hH⟩,
        ⟨actualRetainedEdgeCountVector G D eta R₀, hv⟩,
        subcriticalActualActiveSample G D eta R₀⟩
    apply Finset.mem_image.mpr
    refine ⟨d, Finset.mem_univ _, ?_⟩
    change subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀) ⊥
      (subcriticalActualActiveSample G D eta R₀) = G
    rw [← hclean]
    exact subcriticalActiveGraphFromOutcome_actual G D eta R₀

/-- Equality of actual labeled clean model families; no retained-key
uniqueness or canonicality of model graphs is needed. -/
theorem subcriticalCleanModelGraphFinset_eq_of_retainedKey_eq
    {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (hkey : retainedKey D eta R₀ = retainedKey E eta R₀)
    (m : ℕ) (delta : ℝ) :
    subcriticalCleanModelGraphFinset D eta R₀ m delta =
      subcriticalCleanModelGraphFinset E eta R₀ m delta := by
  ext G
  rw [mem_subcriticalCleanModelGraphFinset_iff, mem_subcriticalCleanModelGraphFinset_iff,
    subcriticalRetainedIncidentDefectGraph_eq_of_retainedKey_eq G hkey]
  have hS := nonretainedVertices_eq_of_retainedKey_eq hkey
  have hfree : (¬Regularity.InducedEmbeds (inducedStar k)
      (subcriticalRemainderGraph G D eta R₀)) ↔
      ¬Regularity.InducedEmbeds (inducedStar k)
        (subcriticalRemainderGraph G E eta R₀) := by
    exact Iff.of_eq (congrArg (fun S : Finset V ↦
      ¬Regularity.InducedEmbeds (inducedStar k) (G.induce (S : Set V))) hS)
  have hedge : (finiteGraphEdges (subcriticalRemainderGraph G D eta R₀)).card =
      (finiteGraphEdges (subcriticalRemainderGraph G E eta R₀)).card := by
    exact congrArg (fun S : Finset V ↦ (finiteGraphEdges (G.induce (S : Set V))).card) hS
  rw [hfree, hedge,
    actualRetainedEdgeCountVector_mem_level_iff_of_retainedKey_eq G hkey]

end InducedStars
