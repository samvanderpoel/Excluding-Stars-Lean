import InducedStars.Structure.Subcritical.CleanModelGeometry
import InducedStars.Structure.Subcritical.ActiveLevelComparison

/-!
# Full fixed-total retained slices

Paper: the denominator construction in the subcritical matching transfer.
This comparison family is deliberately separate from every narrow
or wide partition function. It imposes only the total number of selected
active edges, so an adjacent-level shift cannot fail at a window boundary.
Every counted object is an actual induced-free labeled graph.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

/-- An arbitrary active-edge subset is represented by its actual integral
coordinate vector and sample. -/
theorem subcriticalGraphFromActiveEdges_eq_cleanGraph
    (H : SubcriticalRemainderGraph D eta R₀) {A : Finset (Sym2 V)}
    (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    subcriticalGraphFromActiveEdges H ⊥ A =
      subcriticalCleanGraph H (subcriticalActualActiveSample
        (subcriticalGraphFromActiveEdges H ⊥ A) D eta R₀) := by
  symm
  change subcriticalGraphFromActiveEdges H ⊥
    (subcriticalActiveSelectedEdges
      ((subcriticalActiveFixedBlockModel (actualRetainedEdgeCountVector
        (subcriticalGraphFromActiveEdges H ⊥ A) D eta R₀)).sampleOutcome
        (subcriticalActualActiveSample (subcriticalGraphFromActiveEdges H ⊥ A) D eta R₀))) = _
  rw [subcriticalActualActiveSample_selected_all]
  have he := subcriticalGraphFromActiveEdges_active_edges H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) hA
  have he' : actualRetainedActiveEdgeUniverse (subcriticalGraphFromActiveEdges H ⊥ A)
      D eta R₀ = A := by
    simpa only [actualRetainedActiveEdgeUniverse, Finset.inter_comm] using he
  rw [he']

theorem subcriticalGraphFromActiveEdges_bot_remainder
    (H : SubcriticalRemainderGraph D eta R₀) {A : Finset (Sym2 V)}
    (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    subcriticalRemainderGraph (subcriticalGraphFromActiveEdges H ⊥ A) D eta R₀ = H := by
  rw [subcriticalGraphFromActiveEdges_eq_cleanGraph H hA, subcriticalCleanGraph_remainder]

theorem subcriticalGraphFromActiveEdges_bot_inducedFree (hk : 3 ≤ k)
    (H : SubcriticalRemainderGraph D eta R₀)
    (hH : ¬ Regularity.InducedEmbeds (inducedStar k) H) {A : Finset (Sym2 V)}
    (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    ¬ Regularity.InducedEmbeds (inducedStar k) (subcriticalGraphFromActiveEdges H ⊥ A) := by
  rw [subcriticalGraphFromActiveEdges_eq_cleanGraph H hA]
  exact subcriticalCleanModelGraph_inducedFree hk H hH _

/-- Actual exact-edge remainder and one full fixed-total active slice. -/
abbrev SubcriticalFullRetainedSliceData (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ M b : ℕ) :=
  ↥(subcriticalCleanRemainderGraphFinset D eta R₀ b) ×
    ↥((retainedActiveEdgeUniverse D eta R₀).powersetCard M)

def SubcriticalFullRetainedSliceData.graph {M b : ℕ}
    (d : SubcriticalFullRetainedSliceData D eta R₀ M b) : SimpleGraph V :=
  subcriticalGraphFromActiveEdges d.1.val ⊥ d.2.val

theorem SubcriticalFullRetainedSliceData.graph_injective {M b : ℕ} :
    Function.Injective (SubcriticalFullRetainedSliceData.graph
      (D := D) (eta := eta) (R₀ := R₀) (M := M) (b := b)) := by
  intro d e h
  have hd := (Finset.mem_powersetCard.mp d.2.property).1
  have he := (Finset.mem_powersetCard.mp e.2.property).1
  have hH := congrArg (fun G ↦ subcriticalRemainderGraph G D eta R₀) h
  simp only [SubcriticalFullRetainedSliceData.graph,
    subcriticalGraphFromActiveEdges_bot_remainder _ hd,
    subcriticalGraphFromActiveEdges_bot_remainder _ he] at hH
  have hA := congrArg (fun G ↦ finiteGraphEdges G ∩ retainedActiveEdgeUniverse D eta R₀) h
  simp only [SubcriticalFullRetainedSliceData.graph,
    subcriticalGraphFromActiveEdges_active_edges _ ⊥
      (isSubcriticalRetainedDefectPattern_bot D eta R₀) hd,
    subcriticalGraphFromActiveEdges_active_edges _ ⊥
      (isSubcriticalRetainedDefectPattern_bot D eta R₀) he] at hA
  exact Prod.ext (Subtype.ext hH) (Subtype.ext hA)

def subcriticalFullRetainedSliceGraphFinset (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ M b : ℕ) : Finset (SimpleGraph V) :=
  Finset.univ.image (SubcriticalFullRetainedSliceData.graph
    (D := D) (eta := eta) (R₀ := R₀) (M := M) (b := b))

/-- Exact full-slice count. Empty or infeasible active slices are included. -/
theorem card_subcriticalFullRetainedSliceGraphFinset
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ M b : ℕ) :
    (subcriticalFullRetainedSliceGraphFinset D eta R₀ M b).card =
      (retainedActiveTotalCapacity D eta R₀).choose M *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b := by
  rw [subcriticalFullRetainedSliceGraphFinset, Finset.card_image_of_injective _
    SubcriticalFullRetainedSliceData.graph_injective, Finset.card_univ]
  simp only [SubcriticalFullRetainedSliceData, Fintype.card_prod, Fintype.card_coe,
    card_subcriticalCleanRemainderGraphFinset, Finset.card_powersetCard,
    ← retainedActiveTotalCapacity_eq_card]
  exact Nat.mul_comm _ _

theorem SubcriticalFullRetainedSliceData.graph_inducedFree (hk : 3 ≤ k) {M b : ℕ}
    (d : SubcriticalFullRetainedSliceData D eta R₀ M b) :
    ¬ Regularity.InducedEmbeds (inducedStar k) d.graph :=
  subcriticalGraphFromActiveEdges_bot_inducedFree hk d.1.val
    ((mem_subcriticalCleanRemainderGraphFinset _ _).mp d.1.property).1
    (Finset.mem_powersetCard.mp d.2.property).1

theorem SubcriticalFullRetainedSliceData.graph_card {M b : ℕ}
    (d : SubcriticalFullRetainedSliceData D eta R₀ M b) :
    (finiteGraphEdges d.graph).card = retainedCliqueCapacity D eta R₀ + M + b := by
  have h := subcriticalGraphFromActiveEdges_card d.1.val ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀)
    (Finset.mem_powersetCard.mp d.2.property).1
  have hz : subcriticalSignedDefectSize D eta R₀ ⊥ = 0 := by
    have hb : finiteGraphEdges (⊥ : SimpleGraph V) = ∅ := by ext z; simp
    simp [subcriticalSignedDefectSize, hb]
  rw [hz, add_zero, (Finset.mem_powersetCard.mp d.2.property).2,
    ((mem_subcriticalCleanRemainderGraphFinset _ _).mp d.1.property).2] at h
  exact_mod_cast h

/-- A full fixed-total retained slice is a concrete denominator inside the
total exact-edge induced-free family. No cut-ball or window hypothesis is
needed. -/
theorem subcriticalFullRetainedSlice_le_total {n M b m : ℕ} (hk : 3 ≤ k)
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ : ℕ)
    (hm : retainedCliqueCapacity D eta R₀ + M + b = m) :
    (retainedActiveTotalCapacity D eta R₀).choose M *
        inducedStarFreeGraphCountWithEdges k (D.nonretainedVertices eta R₀).card b ≤
      inducedStarFreeGraphCountWithEdges k n m := by
  rw [← card_subcriticalFullRetainedSliceGraphFinset]
  apply Finset.card_le_card
  intro G hG
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hG
  rw [mem_inducedFreeGraphFinsetWithEdges_iff_finiteGraphEdges]
  exact ⟨d.graph_inducedFree hk, d.graph_card.trans hm⟩

end InducedStars
