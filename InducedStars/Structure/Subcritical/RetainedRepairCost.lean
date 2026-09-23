import InducedStars.Structure.Subcritical.ActiveModels

/-!
# Splitting the repair cost at the retained support

After fixing the retained data and the entire remainder graph, only
the remainder summand depends on the nonretained completion. These are exact
finite identities, with no probabilistic, canonicality, or balance assumption.
-/

noncomputable section

open Finset Set
open scoped Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The repair cost incident with the retained support, counting each
unordered edge once. -/
def subcriticalRetainedIncidentCost (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : ℕ :=
  (finiteGraphEdges (subcriticalRetainedIncidentDefectGraph G D eta R₀)).card

/-- The cost of the completion inside a fixed remainder S. The input H is
an actual graph on S, not merely its edge count. -/
def subcriticalRemainderRepairCost (S : Finset V)
    (H : SimpleGraph {v : V // v ∈ S}) (D : SubcriticalDivision k V) : ℕ :=
  (finiteGraphEdges (subcriticalCombinedDefectGraph H.spanningCoe D) ∩ S.sym2).card

theorem subcriticalRetainedIncidentDefectGraph_edges_sdiff
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    finiteGraphEdges (subcriticalRetainedIncidentDefectGraph G D eta R₀) =
      finiteGraphEdges (subcriticalCombinedDefectGraph G D) \
        (D.nonretainedVertices eta R₀).sym2 := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, subcriticalRetainedIncidentDefectGraph_adj,
      subcriticalDefectGraph_adj, Finset.mem_sdiff, Finset.mk_mem_sym2_iff,
      D.mem_nonretainedVertices]
    have hx : x ∈ D.sparse → x ∉ D.retainedVertices eta R₀ := fun h ↦
      (D.mem_nonretainedVertices eta R₀ x).mp (D.sparse_subset_nonretainedVertices eta R₀ h)
    have hy : y ∈ D.sparse → y ∉ D.retainedVertices eta R₀ := fun h ↦
      (D.mem_nonretainedVertices eta R₀ y).mp (D.sparse_subset_nonretainedVertices eta R₀ h)
    tauto

/-- Restricting the ambient graph before computing a repair does not change
any disagreement whose two endpoints lie in the restricted set. -/
theorem subcriticalCombinedDefectGraph_edges_inter_induce
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (S : Finset V) :
    finiteGraphEdges (subcriticalCombinedDefectGraph
      (G.induce (S : Set V)).spanningCoe D) ∩ S.sym2 =
        finiteGraphEdges (subcriticalCombinedDefectGraph G D) ∩ S.sym2 := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [Finset.mem_inter, mk_mem_finiteGraphEdges, Finset.mk_mem_sym2_iff]
    by_cases hx : x ∈ S
    · by_cases hy : y ∈ S
      · have hadj : (G.induce (S : Set V)).spanningCoe.Adj x y ↔ G.Adj x y := by
          simp only [SimpleGraph.spanningCoe, SimpleGraph.map_adj, SimpleGraph.induce_adj]
          constructor
          · rintro ⟨a, b, hab, rfl, rfl⟩
            exact hab
          · intro h
            exact ⟨⟨x, hx⟩, ⟨y, hy⟩, h, rfl, rfl⟩
        simp only [subcriticalCombinedDefectGraph_adj_iff, hadj, hx, hy]
      · simp [hy]
    · simp [hx]

/-- Exact additive split used to choose a completion after fixing H.
 -/
theorem subcriticalDefectCost_eq_retained_add_remainder
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    subcriticalDefectCost G D =
      subcriticalRetainedIncidentCost G D eta R₀ +
        subcriticalRemainderRepairCost (D.nonretainedVertices eta R₀)
          (subcriticalRemainderGraph G D eta R₀) D := by
  unfold subcriticalDefectCost subcriticalRetainedIncidentCost
    subcriticalRemainderRepairCost subcriticalRemainderGraph
  rw [subcriticalRetainedIncidentDefectGraph_edges_sdiff,
    subcriticalCombinedDefectGraph_edges_inter_induce]
  exact (Finset.card_sdiff_add_card_inter _ _).symm

/-- Form of the split with a fixed external remainder graph and explicit
identification of the complementary vertex set. -/
theorem subcriticalDefectCost_eq_retained_add_fixedRemainder
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (S : Finset V) (hS : S = D.nonretainedVertices eta R₀)
    (H : SimpleGraph {v : V // v ∈ S}) (hH : G.induce (S : Set V) = H) :
    subcriticalDefectCost G D = subcriticalRetainedIncidentCost G D eta R₀ +
      subcriticalRemainderRepairCost S H D := by
  subst S
  subst H
  exact subcriticalDefectCost_eq_retained_add_remainder G D eta R₀

end InducedStars
