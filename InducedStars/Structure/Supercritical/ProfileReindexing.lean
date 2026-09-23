import InducedStars.Structure.Supercritical.CountingSetup
import Mathlib.Tactic

/-!
# Reindexing supercritical cross-edge profiles

The main parts of a supercritical division carry labels only for bookkeeping.
This file defines the action of a permutation of those labels on divisions,
unordered part pairs, and feasible edge-count profiles, and proves that the
exact profile multiplicity is invariant under that action.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

namespace SupercriticalPartPair

variable {k : ℕ}

/-- Sort two distinct part labels into the canonical increasing orientation. -/
def ofDistinct (a b : Fin (k - 1)) (hab : a ≠ b) :
    SupercriticalPartPair k :=
  if h : a < b then
    ⟨a, b, h⟩
  else
    ⟨b, a, lt_of_le_of_ne (le_of_not_gt h) hab.symm⟩

@[simp] theorem ofDistinct_toSym2 (a b : Fin (k - 1)) (hab : a ≠ b) :
    (ofDistinct a b hab).toSym2 = s(a, b) := by
  by_cases h : a < b
  · simp [ofDistinct, h, toSym2]
  · simp [ofDistinct, h, toSym2]

theorem toSym2_injective :
    Function.Injective (@toSym2 k) := by
  intro e f hef
  rw [toSym2, toSym2, Sym2.eq_iff] at hef
  rcases hef with hef | hef
  · exact SupercriticalPartPair.ext hef.1 hef.2
  · exfalso
    have : f.right < f.left := by simpa [hef.1, hef.2] using e.left_lt_right
    exact (not_lt_of_ge f.left_lt_right.le) this

/-- Reindex an unordered pair by a permutation of the main-part labels,
then restore its canonical increasing orientation. -/
def reindex (σ : Equiv.Perm (Fin (k - 1)))
    (e : SupercriticalPartPair k) : SupercriticalPartPair k :=
  ofDistinct (σ e.left) (σ e.right)
    (σ.injective.ne e.left_ne_right)

@[simp] theorem reindex_toSym2 (σ : Equiv.Perm (Fin (k - 1)))
    (e : SupercriticalPartPair k) :
    (reindex σ e).toSym2 = Sym2.map σ e.toSym2 := by
  unfold reindex
  rw [ofDistinct_toSym2]
  simp [toSym2]

theorem reindex_injective (σ : Equiv.Perm (Fin (k - 1))) :
    Function.Injective (reindex σ) := by
  intro e f hef
  apply toSym2_injective
  have hsym := congrArg toSym2 hef
  simp only [reindex_toSym2] at hsym
  exact (Sym2.map.injective σ.injective) hsym

/-- A part-label permutation induces a genuine permutation of the canonical
unordered-pair index type. -/
noncomputable def reindexEquiv (σ : Equiv.Perm (Fin (k - 1))) :
    Equiv.Perm (SupercriticalPartPair k) :=
  Equiv.ofBijective (reindex σ)
    ((Fintype.bijective_iff_injective_and_card (reindex σ)).2
      ⟨reindex_injective σ, rfl⟩)

@[simp] theorem reindexEquiv_apply (σ : Equiv.Perm (Fin (k - 1)))
    (e : SupercriticalPartPair k) :
    reindexEquiv σ e = reindex σ e :=
  rfl

end SupercriticalPartPair

namespace SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Relabel the main parts by `σ`: the old part `i` receives the new label
`σ i`.  Thus the part at a new label `j` is the old part at `σ⁻¹ j`. -/
def reindexParts (D : SupercriticalDivision k V)
    (σ : Equiv.Perm (Fin (k - 1))) : SupercriticalDivision k V where
  parts i := D.parts (σ.symm i)
  parts_nonempty i := D.parts_nonempty (σ.symm i)
  parts_pairwiseDisjoint := by
    intro i _hi j _hj hij
    exact D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (fun h ↦ hij (σ.symm.injective h))

@[simp] theorem reindexParts_parts (D : SupercriticalDivision k V)
    (σ : Equiv.Perm (Fin (k - 1))) (i : Fin (k - 1)) :
    (D.reindexParts σ).parts i = D.parts (σ.symm i) :=
  rfl

end SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindexing a division and the corresponding unordered part pair preserves
the exact cross-edge capacity. -/
@[simp] theorem crossEdgeCapacity_reindexParts
    (D : SupercriticalDivision k V)
    (σ : Equiv.Perm (Fin (k - 1)))
    (e : SupercriticalPartPair k) :
    crossEdgeCapacity (D.reindexParts σ)
        (SupercriticalPartPair.reindexEquiv σ e) =
      crossEdgeCapacity D e := by
  change
    ((D.reindexParts σ).parts
        (SupercriticalPartPair.reindex σ e).left).card *
      ((D.reindexParts σ).parts
        (SupercriticalPartPair.reindex σ e).right).card =
      (D.parts e.left).card * (D.parts e.right).card
  unfold SupercriticalPartPair.reindex SupercriticalPartPair.ofDistinct
  by_cases h : σ e.left < σ e.right
  · simp [h]
  · simp [h, Nat.mul_comm]

namespace SupercriticalEdgeProfile

/-- Transport a feasible profile along a permutation of the main-part
labels. -/
def reindexParts {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D)
    (σ : Equiv.Perm (Fin (k - 1))) :
    SupercriticalEdgeProfile (D.reindexParts σ) where
  count e := p.count ((SupercriticalPartPair.reindexEquiv σ).symm e)
  count_le_capacity e := by
    have hp := p.count_le_capacity
      ((SupercriticalPartPair.reindexEquiv σ).symm e)
    calc
      p.count ((SupercriticalPartPair.reindexEquiv σ).symm e) ≤
          crossEdgeCapacity D
            ((SupercriticalPartPair.reindexEquiv σ).symm e) := hp
      _ = crossEdgeCapacity (D.reindexParts σ) e := by
        symm
        simpa using crossEdgeCapacity_reindexParts D σ
          ((SupercriticalPartPair.reindexEquiv σ).symm e)

@[simp] theorem reindexParts_count {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D)
    (σ : Equiv.Perm (Fin (k - 1)))
    (e : SupercriticalPartPair k) :
    (p.reindexParts σ).count
        (SupercriticalPartPair.reindexEquiv σ e) = p.count e := by
  change p.count
      ((SupercriticalPartPair.reindexEquiv σ).symm
        (SupercriticalPartPair.reindexEquiv σ e)) = p.count e
  rw [Equiv.symm_apply_apply]

end SupercriticalEdgeProfile

/-- Exact profile multiplicity is independent of the labeling of the main
parts. -/
theorem supercriticalProfileMultiplicity_reindexParts
    {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D)
    (σ : Equiv.Perm (Fin (k - 1))) :
    supercriticalProfileMultiplicity (p.reindexParts σ) =
      supercriticalProfileMultiplicity p := by
  unfold supercriticalProfileMultiplicity
  symm
  apply Fintype.prod_equiv (SupercriticalPartPair.reindexEquiv σ)
  intro e
  rw [crossEdgeCapacity_reindexParts,
    SupercriticalEdgeProfile.reindexParts_count]

end InducedStars
