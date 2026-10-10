import InducedStars.Structure.Subcritical.SingletonSource

/-!
# Dissolving a bounded all-singleton source component

An all-singleton source core cannot lose a vertex while its core is
kept unchanged. For the bounded-order branch, the entire source component
is replaced by the empty regular graph. Every source vertex becomes sparse,
and the actual core-edge loss is bounded by a constant depending only on `k`.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The transported all-singleton core has the exact regular edge count. -/
theorem subcriticalSingletonCore_twice_edgeCount
    (D : SubcriticalDivision k V) (i : Fin D.componentCount)
    (hsingle : ∀ j, (D.parts i j).card = 1) :
    2 * (D.singletonComponentCoreGraph i hsingle).edgeFinset.card =
      (D.core i).order * (k - 2) := by
  rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]
  have hr := D.singletonComponentCoreGraph_regular i hsingle
  simp only [hr.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe, D.singletonComponent_card i hsingle]

/-- Dissolving a small singleton component sacrifices at most `4*k^3`
active core edges. The estimate is deliberately generous and uniform. -/
theorem subcriticalSmallSingletonCore_edgeCount_le
    (D : SubcriticalDivision k V) (hk : 3 ≤ k) (i : Fin D.componentCount)
    (hsingle : ∀ j, (D.parts i j).card = 1)
    (hsmall : (D.core i).order ≤ 4 * (k - 2) + 8) :
    (D.singletonComponentCoreGraph i hsingle).edgeFinset.card ≤ 4 * k^3 := by
  have hsum := subcriticalSingletonCore_twice_edgeCount D i hsingle
  have hq : (D.core i).order ≤ 4 * k := by omega
  have hprod := Nat.mul_le_mul hq (Nat.sub_le k 2)
  have hkpow : k^2 ≤ k^3 := by
    calc
      k^2 = k^2 * 1 := by omega
      _ ≤ k^2 * k := Nat.mul_le_mul_left _ (by omega)
      _ = k^3 := by ring
  nlinarith

private theorem simpleGraphEditDistance_bot_eq_edgeCount
    {W : Type*} [Fintype W] [DecidableEq W] (Q : SimpleGraph W) :
    DenseGraph.simpleGraphEditDistance Q ⊥ = Q.edgeFinset.card := by
  unfold DenseGraph.simpleGraphEditDistance
  congr 1
  ext e
  simp only [DenseGraph.mem_simpleGraphEditFinset, SimpleGraph.mem_edgeFinset,
    SimpleGraph.edgeSet_bot, Set.mem_empty_iff_false, not_false_eq_true,
    and_true, false_and, or_false]

/-- The small-core branch of the singleton-safe source comparison.
The replacement is a valid division because another original component
survives. All parts in those other components are preserved exactly. -/
theorem subcriticalSmallSingletonSourceComparison
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (hk : 3 ≤ k)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (hsmall : (D.core i).order ≤ 4 * (k - 2) + 8)
    (hother : ∃ j : Fin D.componentCount, j ≠ i)
    (v : V) (hv : v ∈ D.componentSupport i) :
    ∃ E : SubcriticalDivision k V, v ∈ E.sparse ∧
      (∀ a : D.PartIndex, a.1 ≠ i → ∃ b : E.PartIndex, E.part b = D.part a) ∧
      subcriticalDefectCost G E ≤ subcriticalDefectCost G D + 4 * k^3 := by
  let S : Finset V := ∅
  have hS : S ⊆ D.componentSupport i := Finset.empty_subset _
  let H : SimpleGraph S := ⊥
  letI : DecidableRel H.Adj := Classical.decRel _
  have hr : H.IsRegularOfDegree (k - 2) := by
    intro x
    exact False.elim (Finset.notMem_empty x.val x.property)
  let E := D.replaceComponent i S hS H hr hother
  refine ⟨E, ?_, ?_, ?_⟩
  · change v ∈ (D.replaceComponent i S hS H hr hother).sparse
    rw [D.replaceComponent_sparse]
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, by simp [S]⟩)
  · intro a hai
    exact D.replaceComponent_exists_untouched_part i S hS H hr hother a hai
  · have hcost := subcriticalReplaceSingletonComponent_cost_le G D i hsingle S hS H hr hother
    have hmap : H.map (subcriticalSubsetEmbedding S (D.componentSupport i) hS) = ⊥ := by
      ext x y
      simp [SimpleGraph.map_adj, H]
    rw [hmap, simpleGraphEditDistance_bot_eq_edgeCount] at hcost
    exact hcost.trans (Nat.add_le_add_left
      (subcriticalSmallSingletonCore_edgeCount_le D hk i hsingle hsmall) _)

end InducedStars
