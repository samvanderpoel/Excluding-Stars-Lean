import InducedStars.Structure.Subcritical.Defect
import DenseGraph.FiniteModels.RegularCompletion

/-!
# Singleton components as actual finite regular graphs

This module transports the component core to its real vertices. It is used
in the singleton-safe canonical comparison, rather than deleting a required
nonempty part while pretending the original division remains valid.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars
namespace SubcriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

def singletonComponentVertex (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (j : Fin (D.core i).order) : V :=
  (D.parts_nonempty i j).choose

theorem singletonComponentVertex_mem (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (j : Fin (D.core i).order) :
    D.singletonComponentVertex i j ∈ D.parts i j :=
  (D.parts_nonempty i j).choose_spec

theorem mem_singletonComponentPart_iff (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (j : Fin (D.core i).order) (v : V) :
    v ∈ D.parts i j ↔ v = D.singletonComponentVertex i j := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hsingle j)
  have hpoint := D.singletonComponentVertex_mem i j
  rw [hw, Finset.mem_singleton] at hpoint
  simp [hw, hpoint]

/-- The core vertices are in bijection with actual component vertices when
all parts are singleton. -/
def singletonComponentEquiv (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1) :
    Fin (D.core i).order ≃ {v : V // v ∈ D.componentSupport i} :=
  Equiv.ofBijective
    (fun j ↦ ⟨D.singletonComponentVertex i j,
      mem_componentSupport.mpr ⟨j, D.singletonComponentVertex_mem i j⟩⟩)
    (by
      constructor
      · intro a b hab
        have he := congrArg Subtype.val hab
        change D.singletonComponentVertex i a = D.singletonComponentVertex i b at he
        have ha := D.singletonComponentVertex_mem i a
        have hb := D.singletonComponentVertex_mem i b
        rw [← he] at hb
        have h := D.mem_part_unique (a := ⟨i, a⟩) (b := ⟨i, b⟩) ha hb
        simpa using h
      · intro v
        obtain ⟨j, hj⟩ := mem_componentSupport.mp v.property
        refine ⟨j, Subtype.ext ?_⟩
        exact ((D.mem_singletonComponentPart_iff i hsingle j v.val).mp hj).symm)

@[simp] theorem singletonComponentEquiv_val (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (j : Fin (D.core i).order) :
    (D.singletonComponentEquiv i hsingle j).val = D.singletonComponentVertex i j := rfl

theorem singletonComponentEquiv_symm_mem (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (v : {v : V // v ∈ D.componentSupport i}) :
    v.val ∈ D.parts i ((D.singletonComponentEquiv i hsingle).symm v) := by
  have h := D.singletonComponentVertex_mem i ((D.singletonComponentEquiv i hsingle).symm v)
  have he := congrArg Subtype.val ((D.singletonComponentEquiv i hsingle).apply_symm_apply v)
  simpa using he ▸ h

/-- The full regular core on the actual vertices of a singleton component;
this contains every allowed active coordinate, not only the edges of `G`. -/
def singletonComponentCoreGraph (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1) :
    SimpleGraph {v : V // v ∈ D.componentSupport i} :=
  (D.core i).graph.comap (D.singletonComponentEquiv i hsingle).symm

theorem singletonComponentCoreGraph_adj (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1)
    (x y : {v : V // v ∈ D.componentSupport i}) :
    (D.singletonComponentCoreGraph i hsingle).Adj x y ↔ D.ActivePair x.val y.val := by
  have hx := D.singletonComponentEquiv_symm_mem i hsingle x
  have hy := D.singletonComponentEquiv_symm_mem i hsingle y
  rw [D.activePair_iff_of_mem_parts (a := ⟨i, _⟩) (b := ⟨i, _⟩) hx hy,
    D.activePart_mk_mk]
  rfl

theorem singletonComponentCoreGraph_regular (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1) :
    (D.singletonComponentCoreGraph i hsingle).IsRegularOfDegree (k - 2) := by
  let e := D.singletonComponentEquiv i hsingle
  intro v
  let f : (D.core i).graph.neighborSet (e.symm v) ≃
      (D.singletonComponentCoreGraph i hsingle).neighborSet v :=
    { toFun := fun x ↦ ⟨e x.val, by
        change (D.core i).graph.Adj (e.symm v) (e.symm (e x.val))
        rw [e.symm_apply_apply]
        exact x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, x.property⟩
      left_inv := by intro x; apply Subtype.ext; exact e.symm_apply_apply x.val
      right_inv := by intro x; apply Subtype.ext; exact e.apply_symm_apply x.val }
  have h := Fintype.card_congr f
  rw [SimpleGraph.card_neighborSet_eq_degree, SimpleGraph.card_neighborSet_eq_degree] at h
  exact h.symm.trans ((D.core i).degree_eq (e.symm v))

theorem singletonComponent_card (D : SubcriticalDivision k V)
    (i : Fin D.componentCount) (hsingle : ∀ j, (D.parts i j).card = 1) :
    (D.componentSupport i).card = (D.core i).order := by
  rw [D.card_componentSupport]
  simp [hsingle]

end SubcriticalDivision
end InducedStars
