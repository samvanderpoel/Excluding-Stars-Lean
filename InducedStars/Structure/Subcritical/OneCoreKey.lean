import InducedStars.Structure.Subcritical.RetainedKey
import InducedStars.Structure.Supercritical.CoverMultiplicity

/-!
# One-complete-core keys and ordinary ordered clique covers

This is a literal conversion of the stored core and parts, not a quotient
or a change to the historical subcritical division representation.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

theorem SubcriticalDivision.ofSupercritical_injective (hk : 3 ≤ k) :
    Function.Injective (@SubcriticalDivision.ofSupercritical k V _ _ hk) := by
  intro D E h
  rcases D with ⟨P, hp, hd⟩
  rcases E with ⟨Q, hq, hqd⟩
  have hparts : (fun (_ : Fin 1) j ↦ P j) = (fun (_ : Fin 1) j ↦ Q j) := by
    let data (D : SubcriticalDivision k V) :
        Σ c : ℕ, Σ C : Fin c → RegularBlockCore k,
          (i : Fin c) → Fin (C i).order → Finset V :=
      ⟨D.componentCount, D.core, D.parts⟩
    have hdata := congrArg data h
    dsimp only [data, SubcriticalDivision.ofSupercritical] at hdata
    have hrest := eq_of_heq (Sigma.mk.inj hdata).2
    exact eq_of_heq (Sigma.mk.inj hrest).2
  have hPQ : P = Q := congrFun hparts 0
  subst Q
  rfl

/-- Every stored one-complete-core division is literally the old
supercritical part record, including all actual ambient labels. -/
theorem SubcriticalDivision.exists_ofSupercritical_of_one_complete
    (hk : 3 ≤ k) (E : SubcriticalDivision k V) (hcount : E.componentCount = 1)
    (hcore : ∀ i, E.core i = RegularBlockCore.complete k hk) :
    ∃ D : SupercriticalDivision k V, SubcriticalDivision.ofSupercritical hk D = E := by
  rcases E with ⟨c, hc, C, P, hp, hd⟩
  dsimp at hcount hcore
  subst c
  have hC : C = fun _ ↦ RegularBlockCore.complete k hk := funext hcore
  subst C
  let D : SupercriticalDivision k V := {
    parts := P 0
    parts_nonempty := hp 0
    parts_pairwiseDisjoint := by
      intro a _ b _ hab
      apply hd (Set.mem_univ (⟨0, a⟩ : Sigma _)) (Set.mem_univ ⟨0, b⟩)
      intro heq
      exact hab (eq_of_heq (Sigma.mk.inj heq).2) }
  refine ⟨D, ?_⟩
  have hP : (fun (_ : Fin 1) j ↦ P 0 j) = P := by
    funext i j
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  simp only [SubcriticalDivision.ofSupercritical, D, hP]

@[simp] theorem SubcriticalDivision.ofSupercritical_support
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    (SubcriticalDivision.ofSupercritical hk D).support = D.support := by
  ext v
  simp only [SubcriticalDivision.mem_support_iff, SupercriticalDivision.mem_support,
    SubcriticalDivision.ofSupercritical]
  constructor
  · rintro ⟨_, j, hj⟩
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨0, j, hj⟩

/-- Once actual cover uniqueness has supplied the displayed reindexing
property, at most (k-1)! retained keys remain. The hypothesis concerns the
retained key alone, never its forgotten remainder completions. -/
theorem card_retainedKeys_le_factorial_of_reindexing
    (hk : 3 ≤ k) (D : SupercriticalDivision k V)
    (F : Finset (SubcriticalRetainedKey k V))
    (hF : ∀ K ∈ F, ∃ sigma : Equiv.Perm (Fin (k - 1)),
      K = some (SubcriticalDivision.ofSupercritical hk (D.reindexParts sigma))) :
    F.card ≤ (k - 1).factorial := by
  let target := Finset.univ.image fun sigma : Equiv.Perm (Fin (k - 1)) ↦
    some (SubcriticalDivision.ofSupercritical hk (D.reindexParts sigma))
  have hsub : F ⊆ target := by
    intro K hK
    obtain ⟨sigma, rfl⟩ := hF K hK
    exact Finset.mem_image.mpr ⟨sigma, Finset.mem_univ _, rfl⟩
  exact (Finset.card_le_card hsub).trans (by
    simpa only [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ)
        (f := fun sigma : Equiv.Perm (Fin (k - 1)) ↦
          some (SubcriticalDivision.ofSupercritical hk (D.reindexParts sigma)))))

end InducedStars
