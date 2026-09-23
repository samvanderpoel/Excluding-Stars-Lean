import InducedStars.Structure.Subcritical.OneCoreSampleTransport
import InducedStars.Structure.Subcritical.CleanCoverRelabel

/-! # Exact support graph of a clean one-core sample -/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem subcriticalCleanGraph_active_adj_iff_selected
    {D : SubcriticalDivision k V} {eta : ℝ} {R₀ : ℕ}
    (H : SubcriticalRemainderGraph D eta R₀) {v : RetainedEdgeCountVector D eta R₀}
    (S : RetainedEdgeChoices v) (e : RetainedActivePair D eta R₀)
    {x y : V} (hx : x ∈ D.part e.leftPart) (hy : y ∈ D.part e.rightPart) :
    (subcriticalCleanGraph H S).Adj x y ↔
      s(x, y) ∈ (retainedEdgeChoiceModel v).selectedInBlock S e := by
  rw [← subcriticalCleanGraph_selectedInBlock H S e]
  have hpot : s(x, y) ∈ retainedActivePotentialEdges D eta R₀ e :=
    (mem_retainedActivePotentialEdges D eta R₀ e _).mpr ⟨x, hx, y, hy, rfl⟩
  simp only [actualRetainedActiveEdges, Finset.mem_inter, hpot, true_and,
    mk_mem_finiteGraphEdges]

theorem oneCoreCleanGraph_support_eq (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ}
    (hret : (SubcriticalDivision.ofSupercritical hk D).retainedComponentIndices eta R₀ = Finset.univ)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (H : SubcriticalRemainderGraph (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (S : (supercriticalFixedProfileBlockModel D.onSupportFin (oneCoreProfile hk D hret v)).Sample) :
    (subcriticalCleanGraph H (oneCoreProfileSampleEquiv hk D hret v S)).comap D.supportVertex =
      fixedProfileCleanGraph D.onSupportFin (oneCoreProfile hk D hret v) S := by
  let E := SubcriticalDivision.ofSupercritical hk D
  let p := oneCoreProfile hk D hret v
  let T := oneCoreProfileSampleEquiv hk D hret v S
  have hcross (e : SupercriticalPartPair k) (x y : Fin D.support.card)
      (hx : x ∈ D.onSupportFin.parts e.left) (hy : y ∈ D.onSupportFin.parts e.right) :
      (subcriticalCleanGraph H T).Adj (D.supportVertex x) (D.supportVertex y) ↔
        (fixedProfileCleanGraph D.onSupportFin p S).Adj x y := by
    rw [subcriticalCleanGraph_active_adj_iff_selected H T
      (oneCoreRetainedPairEquiv hk D eta R₀ hret e)
      ((D.mem_onSupportFin_part _ _).mp hx) ((D.mem_onSupportFin_part _ _).mp hy),
      fixedProfileCleanGraph_adj_iff_selected D.onSupportFin p S e (x, y)
        (Finset.mem_product.mpr ⟨hx, hy⟩)]
    exact oneCoreProfileSampleEquiv_selected hk D hret v S e
      ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  ext x y
  change (subcriticalCleanGraph H T).Adj (D.supportVertex x) (D.supportVertex y) ↔ _
  by_cases hxy : x = y
  · subst y
    simp only [SimpleGraph.irrefl, iff_self]
  have hxS : x ∈ D.onSupportFin.support := by
    rw [D.onSupportFin.support_eq_univ D.onSupportFin_isFull]
    exact Finset.mem_univ _
  have hyS : y ∈ D.onSupportFin.support := by
    rw [D.onSupportFin.support_eq_univ D.onSupportFin_isFull]
    exact Finset.mem_univ _
  obtain ⟨a, ha⟩ := D.onSupportFin.mem_support.mp hxS
  obtain ⟨b, hb⟩ := D.onSupportFin.mem_support.mp hyS
  by_cases hab : a = b
  · subst b
    have hpart : (⟨⟨0, by change 0 < 1; omega⟩, a⟩ : E.PartIndex) ∈
        E.retainedPartIndices eta R₀ := by
      rw [SubcriticalDivision.mem_retainedPartIndices]
      rw [hret]
      exact Finset.mem_univ _
    have h1 := subcriticalCleanGraph_part_clique H T hpart
      ((D.mem_onSupportFin_part _ _).mp ha) ((D.mem_onSupportFin_part _ _).mp hb)
      (fun h ↦ hxy (D.supportVertex_injective h))
    have h2 := fixedProfileCleanGraph_isClique D.onSupportFin p S a ha hb hxy
    exact iff_of_true h1 h2
  · rcases lt_or_gt_of_ne hab with h | h
    · exact hcross ⟨a, b, h⟩ x y ha hb
    · rw [SimpleGraph.adj_comm, SimpleGraph.adj_comm (G := fixedProfileCleanGraph _ _ _)]
      exact hcross ⟨b, a, h⟩ y x hb ha

def oneCoreCleanSupportIso (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    {eta : ℝ} {R₀ : ℕ} (hret)
    (v : RetainedEdgeCountVector (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (H : SubcriticalRemainderGraph (SubcriticalDivision.ofSupercritical hk D) eta R₀)
    (S : (supercriticalFixedProfileBlockModel D.onSupportFin (oneCoreProfile hk D hret v)).Sample) :
    fixedProfileCleanGraph D.onSupportFin (oneCoreProfile hk D hret v) S ≃g
      (subcriticalCleanGraph H (oneCoreProfileSampleEquiv hk D hret v S)).induce
        (D.support : Set V) where
  toEquiv := D.supportLabelEquiv.symm
  map_rel_iff' := by
    intro x y
    have h := congrArg (fun G : SimpleGraph (Fin D.support.card) ↦ G.Adj x y)
      (oneCoreCleanGraph_support_eq hk D hret v H S)
    exact Iff.of_eq h

end InducedStars
