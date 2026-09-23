import InducedStars.Structure.Subcritical.ActiveModelsRecovery

/-!
# Exact clean retained models

Paper: `eqn:clean-partition-function-K1k` and the clean part of
`lemma:NtaunmWUpperBdK1k`. The remainder is the actual nonretained subtype,
not the original sparse part of the division. This file concerns a single
fixed division and asserts neither canonicality nor cut-ball membership.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

theorem isSubcriticalRetainedDefectPattern_bot (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) : IsSubcriticalRetainedDefectPattern D eta R₀ ⊥ := by
  intro x y h
  exact h.elim

/-- The existing active realization, with no retained-incident defect. -/
def subcriticalCleanGraph (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v) : SimpleGraph V :=
  subcriticalActiveGraphFromOutcome H ⊥ S

theorem subcriticalCleanGraph_active_edges
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v) :
    finiteGraphEdges (subcriticalCleanGraph H S) ∩ retainedActiveEdgeUniverse D eta R₀ =
      subcriticalActiveSelectedEdges ((retainedEdgeChoiceModel v).sampleOutcome S) :=
  subcriticalGraphFromActiveEdges_active_edges H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) (subcriticalActiveSelectedEdges_subset _)

theorem subcriticalCleanGraph_selectedInBlock
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v)
    (e : RetainedActivePair D eta R₀) :
    actualRetainedActiveEdges (subcriticalCleanGraph H S) D eta R₀ e =
      (retainedEdgeChoiceModel v).selectedInBlock S e := by
  let A := subcriticalActiveSelectedEdges ((retainedEdgeChoiceModel v).sampleOutcome S)
  have hA := subcriticalCleanGraph_active_edges H S
  change finiteGraphEdges (subcriticalCleanGraph H S) ∩
    retainedActiveEdgeUniverse D eta R₀ = A at hA
  have hpot : retainedActivePotentialEdges D eta R₀ e ⊆
      retainedActiveEdgeUniverse D eta R₀ :=
    fun z hz ↦ (mem_retainedActiveEdgeUniverse D eta R₀ z).mpr ⟨e, hz⟩
  have hfirst : actualRetainedActiveEdges (subcriticalCleanGraph H S) D eta R₀ e =
      retainedActivePotentialEdges D eta R₀ e ∩ A := by
    unfold actualRetainedActiveEdges
    rw [← hA]
    ext z
    simp only [Finset.mem_inter]
    exact ⟨fun h ↦ ⟨h.1, h.2, hpot h.1⟩, fun h ↦ ⟨h.1, h.2.1⟩⟩
  rw [hfirst]
  dsimp only [A]
  rw [subcriticalActiveSelectedEdges_sample_eq]
  ext z
  constructor
  · rintro hz
    obtain ⟨hz, hf⟩ := Finset.mem_inter.mp hz
    obtain ⟨f, _, hf⟩ := Finset.mem_biUnion.mp hf
    have hef : e = f := by
      by_contra hne
      exact Finset.disjoint_left.mp (retainedActivePotentialEdges_disjoint D eta R₀ hne)
        hz ((retainedEdgeChoiceModel v).selectedInBlock_subset S f hf)
    simpa only [hef] using hf
  · intro hz
    exact Finset.mem_inter.mpr ⟨(retainedEdgeChoiceModel v).selectedInBlock_subset S e hz,
      Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hz⟩⟩

theorem subcriticalCleanGraph_active_vector
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v) :
    actualRetainedEdgeCountVector (subcriticalCleanGraph H S) D eta R₀ = v := by
  apply RetainedEdgeCountVector.ext
  funext e
  rw [← actualRetainedActiveEdges_card, subcriticalCleanGraph_selectedInBlock,
    DenseGraph.FixedCardinalityBlockModel.card_selectedInBlock]
  rfl

theorem subcriticalCleanGraph_remainder
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v) :
    subcriticalRemainderGraph (subcriticalCleanGraph H S) D eta R₀ = H := by
  have he := subcriticalGraphFromActiveEdges_nonretained_edges H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀)
    (subcriticalActiveSelectedEdges_subset ((retainedEdgeChoiceModel v).sampleOutcome S))
  have hspan : subcriticalRemainderGraphSpanningCoe
      (subcriticalRemainderGraph (subcriticalCleanGraph H S) D eta R₀) =
      subcriticalRemainderGraphSpanningCoe H := by
    ext x y
    have hh := congrArg (fun E ↦ s(x, y) ∈ E)
      ((subcriticalRemainderGraph_edges (subcriticalCleanGraph H S) D eta R₀).trans he)
    exact Iff.of_eq (by simpa only [mk_mem_finiteGraphEdges] using hh)
  have hh := congrArg (fun G : SimpleGraph V ↦ G.induce (D.nonretainedVertices eta R₀ : Set V)) hspan
  simpa only [subcriticalRemainderGraphSpanningCoe, SimpleGraph.induce_spanningCoe] using hh

theorem subcriticalCleanGraph_card
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v) :
    (finiteGraphEdges (subcriticalCleanGraph H S)).card =
      retainedCliqueCapacity D eta R₀ + retainedEdgeCountTotal v + (finiteGraphEdges H).card := by
  have hh := subcriticalActiveGraphFromOutcome_card H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) S
  have hzero : subcriticalSignedDefectSize D eta R₀ ⊥ = 0 := by
    have hb : finiteGraphEdges (⊥ : SimpleGraph V) = ∅ := by ext z; simp
    simp [subcriticalSignedDefectSize, hb]
  rw [hzero, add_zero] at hh
  exact_mod_cast hh

theorem subcriticalCleanGraph_card_of_mem_level
    (H : SubcriticalRemainderGraph D eta R₀)
    {v : RetainedEdgeCountVector D eta R₀} (S : RetainedEdgeChoices v)
    {m : ℕ} {delta : ℝ}
    (hv : v ∈ retainedEdgeCountLevel D eta R₀ m delta (finiteGraphEdges H).card) :
    (finiteGraphEdges (subcriticalCleanGraph H S)).card = m := by
  rw [subcriticalCleanGraph_card]
  have hh := (mem_retainedEdgeCountLevel.mp hv).1
  omega

end InducedStars
