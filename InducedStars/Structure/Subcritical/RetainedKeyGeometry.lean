import InducedStars.Structure.Subcritical.RetainedKey
import InducedStars.Structure.Subcritical.ActiveModels

/-!
# Retained geometry is independent of the discarded completion

These are exact finite equalities, not a cancellation of repeated
summands in a previously proved upper bound. They supply the retained term
in the separately proved fixed-remainder minimizing-completion argument.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D E : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}

theorem retainedCliquePotentialEdges_eq_of_retainedKey_eq
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    retainedCliquePotentialEdges D eta R₀ = retainedCliquePotentialEdges E eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    rw [mk_mem_retainedCliquePotentialEdges_iff, mk_mem_retainedCliquePotentialEdges_iff,
      ← retainedKey_samePart D, ← retainedKey_samePart E, h]

theorem retainedActiveEdgeUniverse_eq_of_retainedKey_eq
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    retainedActiveEdgeUniverse D eta R₀ = retainedActiveEdgeUniverse E eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    rw [mk_mem_retainedActiveEdgeUniverse_iff, mk_mem_retainedActiveEdgeUniverse_iff,
      ← retainedKey_activePair D, ← retainedKey_activePair E, h]

theorem retainedCliqueCapacity_eq_of_retainedKey_eq
    (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    retainedCliqueCapacity D eta R₀ = retainedCliqueCapacity E eta R₀ := by
  simpa only [retainedCliquePotentialEdges_card] using
    congrArg Finset.card (retainedCliquePotentialEdges_eq_of_retainedKey_eq h)

theorem subcriticalDivisionModelGraph_adj_iff_of_retainedKey_eq
    (G : SimpleGraph V) (h : retainedKey D eta R₀ = retainedKey E eta R₀)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) :
    (subcriticalDivisionModelGraph G D).Adj x y ↔
      (subcriticalDivisionModelGraph G E).Adj x y := by
  rw [subcriticalDivisionModelGraph_adj, subcriticalDivisionModelGraph_adj,
    samePart_iff_of_retainedKey_eq h hx, activePair_iff_of_retainedKey_eq h hx]

/-- Every ordinary defect touching retained vertices is determined by the
key and the graph, independently of the completion on its complement. -/
theorem subcriticalRetainedIncidentDefectGraph_eq_of_retainedKey_eq
    (G : SimpleGraph V) (h : retainedKey D eta R₀ = retainedKey E eta R₀) :
    subcriticalRetainedIncidentDefectGraph G D eta R₀ =
      subcriticalRetainedIncidentDefectGraph G E eta R₀ := by
  ext x y
  have hs := retainedVertices_eq_of_retainedKey_eq h
  by_cases hr : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀
  · have he : x ∈ E.retainedVertices eta R₀ ∨ y ∈ E.retainedVertices eta R₀ := hs ▸ hr
    have hD : ¬(x ∈ D.sparse ∧ y ∈ D.sparse) := by
      rintro ⟨hx, hy⟩
      exact hr.elim
        (fun hret ↦ (D.mem_sparse.mp hx) (D.retainedVertices_subset_support eta R₀ hret))
        (fun hret ↦ (D.mem_sparse.mp hy) (D.retainedVertices_subset_support eta R₀ hret))
    have hE : ¬(x ∈ E.sparse ∧ y ∈ E.sparse) := by
      rintro ⟨hx, hy⟩
      exact he.elim
        (fun hret ↦ (E.mem_sparse.mp hx) (E.retainedVertices_subset_support eta R₀ hret))
        (fun hret ↦ (E.mem_sparse.mp hy) (E.retainedVertices_subset_support eta R₀ hret))
    simp only [subcriticalRetainedIncidentDefectGraph_adj, hr, he, and_true,
      subcriticalDefectGraph_adj_iff, hD, hE,
      samePart_iff_of_retainedKey_eq h hr, activePair_iff_of_retainedKey_eq h hr]
  · have he : ¬(x ∈ E.retainedVertices eta R₀ ∨ y ∈ E.retainedVertices eta R₀) := by
      simpa only [← hs] using hr
    simp only [subcriticalRetainedIncidentDefectGraph_adj, hr, he, and_false]

end InducedStars
