import InducedStars.Structure.Subcritical.RetainedKeyCounts
import Mathlib.Order.Hom.Set

/-!
# Retaining every component is the identity

Literal inherited ordering is preserved, not merely equality of
the generated graph families or a permutation of component labels.
-/

noncomputable section
open Finset Set
namespace InducedStars

private theorem univ_orderIsoOfFin_val {c d : ℕ}
    (h : (Finset.univ : Finset (Fin c)).card = d) (i : Fin d) :
    ((Finset.univ : Finset (Fin c)).orderIsoOfFin h i).val =
      Fin.cast (by simpa using h.symm) i := by
  let e : Fin d ≃o Fin c :=
    ((Finset.univ : Finset (Fin c)).orderIsoOfFin h).trans
      ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)
  have he : e = Fin.castOrderIso (by simpa using h.symm) := Subsingleton.elim _ _
  exact congrArg (fun f : Fin d ≃o Fin c ↦ f i) he

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem division_cast_mk_eq (D : SubcriticalDivision k V)
    {c : ℕ} (hc : 0 < c) (h : c = D.componentCount)
    (f : Fin c → Fin D.componentCount) (hf : ∀ i, f i = Fin.cast h i)
    (hp : ∀ i j, (D.parts (f i) j).Nonempty)
    (hd : Set.PairwiseDisjoint (Set.univ : Set (Σ i, Fin (D.core (f i)).order))
      (fun a ↦ D.parts (f a.1) a.2)) :
    SubcriticalDivision.mk c hc (fun i ↦ D.core (f i))
      (fun i j ↦ D.parts (f i) j) hp hd = D := by
  subst c
  have he : f = id := funext hf
  subst f
  cases D
  rfl

theorem SubcriticalDivision.restrictComponents_univ (D : SubcriticalDivision k V)
    (h : (Finset.univ : Finset (Fin D.componentCount)).Nonempty) :
    D.restrictComponents Finset.univ h = D := by
  classical
  unfold SubcriticalDivision.restrictComponents
  apply division_cast_mk_eq D _ (by simp)
  intro i
  exact univ_orderIsoOfFin_val rfl i

theorem retainedKey_eq_some_of_retainedComponentIndices_eq_univ
    (D : SubcriticalDivision k V) {eta : ℝ} {R₀ : ℕ}
    (hall : D.retainedComponentIndices eta R₀ = Finset.univ) :
    retainedKey D eta R₀ = some D := by
  classical
  have hne : (D.retainedComponentIndices eta R₀).Nonempty := by
    rw [hall]
    exact ⟨⟨0, D.componentCount_pos⟩, Finset.mem_univ _⟩
  unfold retainedKey
  rw [dif_pos hne]
  congr 1
  subst_vars
  simpa only [hall] using D.restrictComponents_univ
    (show (Finset.univ : Finset (Fin D.componentCount)).Nonempty by
      exact ⟨⟨0, D.componentCount_pos⟩, Finset.mem_univ _⟩)

@[simp] theorem retainedKey_all (D : SubcriticalDivision k V) :
    retainedKey D 0 (Fintype.card V) = some D :=
  retainedKey_eq_some_of_retainedComponentIndices_eq_univ D D.retainedComponentIndices_all

theorem retainedKey_some_retains_all {D E : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (hkey : retainedKey D eta R₀ = some E) :
    E.retainedComponentIndices eta R₀ = Finset.univ := by
  classical
  unfold retainedKey at hkey
  split_ifs at hkey with hne
  · have hE := Option.some.inj hkey
    subst E
    ext i
    simp only [SubcriticalDivision.mem_retainedComponentIndices, Finset.mem_univ, iff_true]
    exact (D.mem_retainedComponentIndices eta R₀ _).mp
      ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl i).property

theorem retainedKey_some_idempotent {D E : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (hkey : retainedKey D eta R₀ = some E) :
    retainedKey E eta R₀ = some E :=
  retainedKey_eq_some_of_retainedComponentIndices_eq_univ E
    (retainedKey_some_retains_all hkey)

@[simp] theorem retainedKeyPartitionFunction_some (D : SubcriticalDivision k V)
    (m : ℕ) (delta : ℝ) (u : ℤ) :
    retainedKeyPartitionFunction (some D) m delta u =
      retainedPartitionFunction D 0 (Fintype.card V) m delta u := by
  rw [← retainedKey_all D, retainedKeyPartitionFunction_retainedKey]

end InducedStars
