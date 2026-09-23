import InducedStars.Structure.Subcritical.RetainedKeyGeometry

/-!
# Literal retained-coordinate transports

The inherited retained ordering preserves each core label and each
actual bipartite edge block. Empty retained keys have an empty index type.
The zero cutoff below is used only to view every component of a nonempty
key as retained; it is never the outer clean-remainder cutoff.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem SubcriticalDivision.retainedComponentIndices_all
    (D : SubcriticalDivision k V) :
    D.retainedComponentIndices 0 (Fintype.card V) = Finset.univ := by
  ext i
  simp [D.mem_retainedComponentIndices, D.core_order_le_card i]

@[simp] theorem SubcriticalDivision.retainedVertices_all
    (D : SubcriticalDivision k V) :
    D.retainedVertices 0 (Fintype.card V) = D.support := by
  rw [SubcriticalDivision.retainedVertices, D.retainedComponentIndices_all,
    ← D.support_eq_componentSupport_union]

namespace SubcriticalRetainedKey

def ActiveIndex (K : SubcriticalRetainedKey k V) : Type :=
  match K with
  | none => Empty
  | some D => RetainedActivePair D 0 (Fintype.card V)

instance (K : SubcriticalRetainedKey k V) : Fintype K.ActiveIndex := by
  cases K <;> dsimp [ActiveIndex] <;> infer_instance

def activeEdges (K : SubcriticalRetainedKey k V) : K.ActiveIndex → Finset (Sym2 V) :=
  match K with
  | none => Empty.elim
  | some D => retainedActivePotentialEdges D 0 (Fintype.card V)

def activeCapacity (K : SubcriticalRetainedKey k V) (e : K.ActiveIndex) : ℕ :=
  (K.activeEdges e).card

def cliqueEdges (K : SubcriticalRetainedKey k V) : Finset (Sym2 V) :=
  K.elim ∅ (fun D ↦ retainedCliquePotentialEdges D 0 (Fintype.card V))

def cliqueCapacity (K : SubcriticalRetainedKey k V) : ℕ := K.cliqueEdges.card

theorem mk_mem_cliqueEdges (K : SubcriticalRetainedKey k V) (x y : V) :
    s(x, y) ∈ K.cliqueEdges ↔ x ≠ y ∧ K.SamePart x y := by
  cases K with
  | none => simp [cliqueEdges, SamePart]
  | some D =>
    simp only [cliqueEdges, Option.elim_some, mk_mem_retainedCliquePotentialEdges_iff,
      D.retainedVertices_all, SamePart]
    exact ⟨fun h ↦ ⟨h.1, h.2.1⟩,
      fun h ↦ ⟨h.1, h.2, (SubcriticalDivision.samePart_imp_support h.2).1⟩⟩

end SubcriticalRetainedKey

private def restrictRetainedActivePairMap
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hI : (D.retainedComponentIndices eta R₀).Nonempty)
    (e : RetainedActivePair (D.restrictComponents (D.retainedComponentIndices eta R₀) hI)
      0 (Fintype.card V)) : RetainedActivePair D eta R₀ where
  component := ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl e.component).val
  component_retained :=
    ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl e.component).property
  left := e.left
  right := e.right
  left_lt_right := e.left_lt_right
  active := e.active

private theorem restrictRetainedActivePairMap_bijective
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (hI : (D.retainedComponentIndices eta R₀).Nonempty) :
    Function.Bijective (restrictRetainedActivePairMap D eta R₀ hI) := by
  constructor
  · intro e f h
    have hc : e.component = f.component :=
      ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl).injective
        (Subtype.ext (congrArg RetainedActivePair.component h))
    rcases e with ⟨i, hi, a, b, hab, hadj⟩
    rcases f with ⟨j, hj, c, d, hcd, hcadj⟩
    dsimp at hc
    subst j
    have hac : a = c := Fin.ext (congrArg (fun e ↦ e.left.val) h)
    have hbd : b = d := Fin.ext (congrArg (fun e ↦ e.right.val) h)
    subst c
    subst d
    rfl
  · rintro ⟨i, hi, a, b, hab, hadj⟩
    obtain ⟨j, hj⟩ := ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl).surjective
      ⟨i, hi⟩
    have hh := congrArg Subtype.val hj
    change ((D.retainedComponentIndices eta R₀).orderIsoOfFin rfl j).val = i at hh
    subst i
    refine ⟨{
      component := j
      component_retained := by
        rw [SubcriticalDivision.retainedComponentIndices_all]
        exact Finset.mem_univ _
      left := a
      right := b
      left_lt_right := hab
      active := hadj }, ?_⟩
    rfl

private theorem exists_retainedKeyActiveEquiv
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    ∃ f : (retainedKey D eta R₀).ActiveIndex ≃ RetainedActivePair D eta R₀,
      ∀ e, (retainedKey D eta R₀).activeEdges e =
        retainedActivePotentialEdges D eta R₀ (f e) := by
  let P : SubcriticalRetainedKey k V → Prop := fun K ↦
    ∃ f : K.ActiveIndex ≃ RetainedActivePair D eta R₀,
      ∀ e, K.activeEdges e = retainedActivePotentialEdges D eta R₀ (f e)
  change P (retainedKey D eta R₀)
  unfold retainedKey
  split_ifs with hI
  · change ∃ f : RetainedActivePair
        (D.restrictComponents (D.retainedComponentIndices eta R₀) hI)
        0 (Fintype.card V) ≃ RetainedActivePair D eta R₀,
      ∀ e, retainedActivePotentialEdges
        (D.restrictComponents (D.retainedComponentIndices eta R₀) hI)
        0 (Fintype.card V) e = retainedActivePotentialEdges D eta R₀ (f e)
    refine ⟨Equiv.ofBijective (restrictRetainedActivePairMap D eta R₀ hI)
      (restrictRetainedActivePairMap_bijective D eta R₀ hI), ?_⟩
    intro e
    rfl
  · change ∃ f : Empty ≃ RetainedActivePair D eta R₀,
      ∀ e : Empty, Empty.elim e = retainedActivePotentialEdges D eta R₀ (f e)
    letI : IsEmpty (RetainedActivePair D eta R₀) :=
      ⟨fun e ↦ hI ⟨e.component, e.component_retained⟩⟩
    let f : Empty ≃ RetainedActivePair D eta R₀ := Equiv.equivOfIsEmpty _ _
    exact ⟨f, fun e ↦ Empty.elim e⟩

/-- Each literal key active index corresponds to exactly one old retained
coordinate; the map preserves its actual potential edge set. -/
def retainedKeyActiveEquiv (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedKey D eta R₀).ActiveIndex ≃ RetainedActivePair D eta R₀ :=
  (exists_retainedKeyActiveEquiv D eta R₀).choose

theorem retainedKeyActiveEquiv_edges (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : (retainedKey D eta R₀).ActiveIndex) :
    (retainedKey D eta R₀).activeEdges e =
      retainedActivePotentialEdges D eta R₀ (retainedKeyActiveEquiv D eta R₀ e) :=
  (exists_retainedKeyActiveEquiv D eta R₀).choose_spec e

theorem retainedKeyActiveEquiv_capacity (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : (retainedKey D eta R₀).ActiveIndex) :
    (retainedKey D eta R₀).activeCapacity e =
      retainedActiveCapacity D eta R₀ (retainedKeyActiveEquiv D eta R₀ e) := by
  rw [SubcriticalRetainedKey.activeCapacity, retainedKeyActiveEquiv_edges,
    retainedActivePotentialEdges_card]

@[simp] theorem retainedKey_cliqueEdges (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    (retainedKey D eta R₀).cliqueEdges = retainedCliquePotentialEdges D eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    rw [SubcriticalRetainedKey.mk_mem_cliqueEdges, retainedKey_samePart,
      mk_mem_retainedCliquePotentialEdges_iff]

@[simp] theorem retainedKey_cliqueCapacity (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    (retainedKey D eta R₀).cliqueCapacity = retainedCliqueCapacity D eta R₀ := by
  rw [SubcriticalRetainedKey.cliqueCapacity, retainedKey_cliqueEdges,
    retainedCliquePotentialEdges_card]

end InducedStars
