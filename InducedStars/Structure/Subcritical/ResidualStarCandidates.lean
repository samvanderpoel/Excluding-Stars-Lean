import InducedStars.Structure.Subcritical.ResidualMatchingSelection
import InducedStars.Structure.Subcritical.CompanionRoles
import DenseGraph.FiniteModels.DefectFreeSelections

/-!
# Actual residual-star role selections

Paper: the four candidate families in `lemma:residual-matching-estimate-K1k`.
The two designated matching endpoints are fixed. All other vertices come
from distinct retained parts, avoid every root and matching endpoint, and
have no further residual defect. Endpoint cleaning uses local residual
degrees, not merely a global edge bound, in the endpoint-cleaning count.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta : ℝ}

abbrev SubcriticalResidualFreeRole (D : SubcriticalDivision k (Fin n)) (a : D.PartIndex) :=
  Option (SubcriticalCoreNeighbor D a.1 a.2)

abbrev SubcriticalResidualStarRole (D : SubcriticalDivision k (Fin n)) (a : D.PartIndex) :=
  Fin 2 ⊕ SubcriticalResidualFreeRole D a

theorem card_subcriticalResidualFreeRole (hk : 3 ≤ k) (a : D.PartIndex) :
    Fintype.card (SubcriticalResidualFreeRole D a) = k - 1 := by
  simp only [SubcriticalResidualFreeRole, Fintype.card_option, card_subcriticalCoreNeighbor]
  omega

theorem card_subcriticalResidualStarRole (hk : 3 ≤ k) (a : D.PartIndex) :
    Fintype.card (SubcriticalResidualStarRole D a) = k + 1 := by
  simp only [SubcriticalResidualStarRole, Fintype.card_sum, Fintype.card_fin,
    card_subcriticalResidualFreeRole hk]
  omega

def subcriticalResidualFreeParent (a : D.PartIndex) : SubcriticalResidualFreeRole D a → D.PartIndex
  | none => a
  | some t => ⟨a.1, t.val⟩

theorem subcriticalResidualFreeParent_component (a : D.PartIndex)
    (t : SubcriticalResidualFreeRole D a) : (subcriticalResidualFreeParent a t).1 = a.1 := by
  cases t <;> rfl

theorem subcriticalResidualFreeParent_injective (a : D.PartIndex) :
    Function.Injective (subcriticalResidualFreeParent a) := by
  rcases a with ⟨i, j⟩
  intro s t hst
  cases s with
  | none =>
      cases t with
      | none => rfl
      | some t =>
          have ht : j = t.val := by simpa [subcriticalResidualFreeParent] using hst
          exact ((D.core i).graph.ne_of_adj t.property ht).elim
  | some s =>
      cases t with
      | none =>
          have hs : s.val = j := by simpa [subcriticalResidualFreeParent] using hst
          exact ((D.core i).graph.ne_of_adj s.property hs.symm).elim
      | some t =>
          exact congrArg some (Subtype.ext (by simpa [subcriticalResidualFreeParent] using hst))

theorem subcriticalResidualFreeParent_retained
    (a : D.PartIndex) (ha : a ∈ D.retainedPartIndices eta R₀)
    (t : SubcriticalResidualFreeRole D a) :
    subcriticalResidualFreeParent a t ∈ D.retainedPartIndices eta R₀ := by
  rw [D.mem_retainedPartIndices, subcriticalResidualFreeParent_component]
  exact (D.mem_retainedPartIndices eta R₀ a).mp ha

namespace SubcriticalResidualMatchingPlacement

def IsInternal (c : SubcriticalResidualMatchingPlacement D eta R₀) : Prop :=
  match c with
  | .internal _ => True
  | _ => False

theorem right_mem_own_of_internal (c : SubcriticalResidualMatchingPlacement D eta R₀)
    (hc : c.IsInternal) {y : Fin n} (hy : y ∈ c.rightVertices) : y ∈ D.part c.leftPart := by
  cases c <;> simp_all [IsInternal, rightVertices, rightPart, leftPart, encoding]

/-- In cases 2--4 the other designated endpoint cannot lie in the own
part or any active-neighbor free target. -/
theorem right_not_mem_freeParent_of_not_internal
    (c : SubcriticalResidualMatchingPlacement D eta R₀) (hc : ¬ c.IsInternal)
    {y : Fin n} (hy : y ∈ c.rightVertices)
    (t : SubcriticalResidualFreeRole D c.leftPart) :
    y ∉ D.part (subcriticalResidualFreeParent c.leftPart t) := by
  intro hyt
  cases c with
  | internal a => exact hc trivial
  | inactive a b horder hcomp hno =>
      change y ∈ D.part b.val at hy
      have he := D.mem_part_unique hyt hy
      cases t with
      | none =>
          have hab : a = b := Subtype.ext he
          have := hab ▸ horder
          exact (lt_irrefl _ this)
      | some t =>
          apply hno
          exact ⟨a.val.1, a.val.2, t.val, rfl, he.symm, t.property⟩
  | different a b horder hcomp =>
      change y ∈ D.part b.val at hy
      have he := congrArg Sigma.fst (D.mem_part_unique hyt hy)
      exact hcomp ((subcriticalResidualFreeParent_component a.val t).symm.trans he)
  | sparse a =>
      change y ∈ D.nonretainedVertices eta R₀ at hy
      exact (D.mem_nonretainedVertices eta R₀ y).mp hy
        (D.part_subset_retainedVertices (subcriticalResidualFreeParent_retained a.val a.property t) hyt)

end SubcriticalResidualMatchingPlacement

namespace SubcriticalHomogeneousResidualMatching
variable {R : SimpleGraph (Fin n)} {B : Finset (Fin n)}

abbrev Edge (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) := {e // e ∈ M.edges}
abbrev FreeRole (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :=
  SubcriticalResidualFreeRole D M.placement.leftPart
abbrev Role (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :=
  SubcriticalResidualStarRole D M.placement.leftPart

def freeTarget (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (t : M.FreeRole) :
    Finset (Fin n) :=
  D.part (subcriticalResidualFreeParent M.placement.leftPart t) \
    (B ∪ DenseGraph.matchingEndpoints M.edges)

def cleanTarget (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (t : M.FreeRole) : Finset (Fin n) :=
  DenseGraph.endpointCleanTarget R (M.firstEndpoint e) (M.secondEndpoint e) (M.freeTarget t)

def candidateSelections (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (e : M.Edge) :
    Finset (M.FreeRole → Fin n) := DenseGraph.defectFreeSelections (M.cleanTarget e) R

abbrev Selection (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (e : M.Edge) :=
  {f // f ∈ M.candidateSelections e}

def selectionVertex (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : M.Role → Fin n :=
  Sum.elim (fun i ↦ if i = 0 then M.firstEndpoint e else M.secondEndpoint e) f.val

def candidateCenter (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) : M.Role :=
  if M.placement.IsInternal then Sum.inr none else Sum.inl 0

theorem cleanTarget_subset_freeTarget
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (e : M.Edge) (t : M.FreeRole) :
    M.cleanTarget e t ⊆ M.freeTarget t := Finset.filter_subset _ _

theorem freeTarget_subset_part
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (t : M.FreeRole) :
    M.freeTarget t ⊆ D.part (subcriticalResidualFreeParent M.placement.leftPart t) :=
  Finset.sdiff_subset

theorem freeTarget_pairwise_disjoint (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :
    Pairwise fun s t ↦ Disjoint (M.freeTarget s) (M.freeTarget t) := by
  intro s t hst
  exact (D.part_disjoint (fun h ↦ hst (subcriticalResidualFreeParent_injective _ h))).mono
    (M.freeTarget_subset_part s) (M.freeTarget_subset_part t)

theorem cleanTarget_pairwise_disjoint (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : Pairwise fun s t ↦ Disjoint (M.cleanTarget e s) (M.cleanTarget e t) := by
  intro s t hst
  exact (M.freeTarget_pairwise_disjoint hst).mono
    (M.cleanTarget_subset_freeTarget e s) (M.cleanTarget_subset_freeTarget e t)

theorem selection_mem_cleanTarget (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : f.val t ∈ M.cleanTarget e t :=
  (DenseGraph.mem_defectFreeSelections _ R f.val).mp f.property |>.1 t

theorem selection_mem_freeTarget (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : f.val t ∈ M.freeTarget t :=
  M.cleanTarget_subset_freeTarget e t (M.selection_mem_cleanTarget e f t)

theorem selection_mem_part (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) :
    f.val t ∈ D.part (subcriticalResidualFreeParent M.placement.leftPart t) :=
  M.freeTarget_subset_part t (M.selection_mem_freeTarget e f t)

theorem selection_not_mem_roots (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : f.val t ∉ B := by
  have h := (Finset.mem_sdiff.mp (M.selection_mem_freeTarget e f t)).2
  exact fun ht ↦ h (Finset.mem_union_left _ ht)

theorem selection_not_mem_endpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) :
    f.val t ∉ DenseGraph.matchingEndpoints M.edges := by
  have h := (Finset.mem_sdiff.mp (M.selection_mem_freeTarget e f t)).2
  exact fun ht ↦ h (Finset.mem_union_right _ ht)

theorem selection_free_injective (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : Function.Injective f.val :=
  DenseGraph.defectFreeSelections_injective (M.cleanTarget_pairwise_disjoint e) f.property

theorem first_ne_second (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (e : M.Edge) :
    M.firstEndpoint e ≠ M.secondEndpoint e := by
  have h := M.isMatching.1 e.val e.property
  rw [M.edge_eq_endpoints e, SimpleGraph.mem_edgeSet] at h
  exact h.ne

theorem first_ne_selection (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : M.firstEndpoint e ≠ f.val t := by
  intro he
  apply M.selection_not_mem_endpoints e f t
  rw [← he]
  exact (DenseGraph.mem_matchingEndpoints M.edges _).mpr ⟨e.val, e.property, M.firstEndpoint_mem_edge e⟩

theorem second_ne_selection (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : M.secondEndpoint e ≠ f.val t := by
  intro he
  apply M.selection_not_mem_endpoints e f t
  rw [← he]
  exact (DenseGraph.mem_matchingEndpoints M.edges _).mpr ⟨e.val, e.property, M.secondEndpoint_mem_edge e⟩

theorem selectionVertex_injective (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : Function.Injective (M.selectionVertex e f) := by
  intro s t hst
  cases s with
  | inl s =>
      cases t with
      | inl t =>
          fin_cases s <;> fin_cases t <;>
            simp_all [selectionVertex, M.first_ne_second e, (M.first_ne_second e).symm]
      | inr t =>
          fin_cases s <;>
            simp_all [selectionVertex, M.first_ne_selection e f t, M.second_ne_selection e f t]
  | inr s =>
      cases t with
      | inl t =>
          fin_cases t <;> simp_all [selectionVertex,
            (M.first_ne_selection e f s).symm, (M.second_ne_selection e f s).symm]
      | inr t => exact congrArg Sum.inr (M.selection_free_injective e f hst)

def selectionEmbedding (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : M.Role ↪ Fin n :=
  ⟨M.selectionVertex e f, M.selectionVertex_injective e f⟩

theorem selectionVertex_away (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.Role) : M.selectionVertex e f t ∉ B := by
  cases t with
  | inl t =>
      fin_cases t
      · simpa [selectionVertex] using M.firstEndpoint_not_mem_roots e
      · simpa [selectionVertex] using M.secondEndpoint_not_mem_roots e
  | inr t => exact M.selection_not_mem_roots e f t

theorem selectionVertex_retained_of_ne_second
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.Role) (ht : t ≠ Sum.inl 1) :
    M.selectionVertex e f t ∈ D.retainedVertices eta R₀ := by
  cases t with
  | inl t =>
      have ht0 : t = 0 := by fin_cases t <;> simp_all
      subst t
      exact D.part_subset_retainedVertices M.placement.leftPart_mem_retained (M.firstEndpoint_mem e)
  | inr t =>
      exact D.part_subset_retainedVertices
        (subcriticalResidualFreeParent_retained _ M.placement.leftPart_mem_retained t)
        (M.selection_mem_part e f t)

theorem selectionVertex_retained_pair
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (s t : M.Role) (hst : s ≠ t) :
    M.selectionVertex e f s ∈ D.retainedVertices eta R₀ ∨
      M.selectionVertex e f t ∈ D.retainedVertices eta R₀ := by
  by_cases hs : s = Sum.inl 1
  · exact Or.inr (M.selectionVertex_retained_of_ne_second e f t (fun ht ↦ hst (hs.trans ht.symm)))
  · exact Or.inl (M.selectionVertex_retained_of_ne_second e f s hs)

end SubcriticalHomogeneousResidualMatching
end InducedStars
