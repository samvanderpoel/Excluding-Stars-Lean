import DenseGraph.Combinatorics.ExponentialSums
import InducedStars.Structure.Supercritical.CoverMultiplicity

/-!
# Preimages of sparse absorption

Sparse absorption forgets only two finite pieces of data: the selected main
part and the old sparse set.  This file makes that observation injective and
deduces the sharp `(k - 1) * choose n s` preimage bound.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance absorptionPreimageDivisionDecidableEq
    (k n : ℕ) : DecidableEq (SupercriticalDivision k (Fin n)) :=
  Classical.decEq _

/-! ## The finite fiber and its code -/

/-- Divisions with sparse size `s` which absorb to the prescribed full
division `E`. -/
def supercriticalAbsorptionPreimageFinset
    {k n : ℕ} (hk : 3 ≤ k) (E : SupercriticalDivision k (Fin n))
    (s : ℕ) : Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦
    D.sparse.card = s ∧ supercriticalAbsorbSparseDivision hk D = E

@[simp] theorem mem_supercriticalAbsorptionPreimageFinset
    {k n : ℕ} {hk : 3 ≤ k} {E : SupercriticalDivision k (Fin n)}
    {s : ℕ} {D : SupercriticalDivision k (Fin n)} :
    D ∈ supercriticalAbsorptionPreimageFinset hk E s ↔
      D.sparse.card = s ∧ supercriticalAbsorbSparseDivision hk D = E := by
  simp [supercriticalAbsorptionPreimageFinset]

/-- The data retained by the sharp preimage encoding: the part into which
the sparse set was absorbed and that sparse set itself. -/
def supercriticalAbsorptionPreimageCode
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n)) :
    Fin (k - 1) × Finset (Fin n) :=
  (supercriticalSmallestPartIndex hk D, D.sparse)

private theorem part_smallest_eq_absorbed_sdiff_sparse
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) (D : SupercriticalDivision k V) :
    D.parts (supercriticalSmallestPartIndex hk D) =
      (supercriticalAbsorbSparseDivision hk D).parts
          (supercriticalSmallestPartIndex hk D) \ D.sparse := by
  rw [supercriticalAbsorbSparseDivision_part_smallest]
  exact (Finset.union_sdiff_cancel_right
    (D.part_disjoint_sparse (supercriticalSmallestPartIndex hk D))).symm

private theorem absorbSparseDivision_eq_of_code_eq
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (hk : 3 ≤ k) {D E : SupercriticalDivision k V}
    (hindex : supercriticalSmallestPartIndex hk D =
      supercriticalSmallestPartIndex hk E)
    (hsparse : D.sparse = E.sparse)
    (habsorb : supercriticalAbsorbSparseDivision hk D =
      supercriticalAbsorbSparseDivision hk E) :
    D = E := by
  apply SupercriticalDivision.ext_parts
  funext i
  by_cases hi : i = supercriticalSmallestPartIndex hk D
  · subst i
    calc
      D.parts (supercriticalSmallestPartIndex hk D) =
          (supercriticalAbsorbSparseDivision hk D).parts
              (supercriticalSmallestPartIndex hk D) \ D.sparse :=
        part_smallest_eq_absorbed_sdiff_sparse hk D
      _ = (supercriticalAbsorbSparseDivision hk E).parts
              (supercriticalSmallestPartIndex hk E) \ E.sparse := by
        rw [habsorb, hindex, hsparse]
      _ = E.parts (supercriticalSmallestPartIndex hk E) :=
        (part_smallest_eq_absorbed_sdiff_sparse hk E).symm
      _ = E.parts (supercriticalSmallestPartIndex hk D) := by
        rw [hindex]
  · have hiE : i ≠ supercriticalSmallestPartIndex hk E := by
      intro hie
      exact hi (hie.trans hindex.symm)
    calc
      D.parts i = (supercriticalAbsorbSparseDivision hk D).parts i :=
        (supercriticalAbsorbSparseDivision_part_of_ne hk D hi).symm
      _ = (supercriticalAbsorbSparseDivision hk E).parts i := by
        rw [habsorb]
      _ = E.parts i :=
        supercriticalAbsorbSparseDivision_part_of_ne hk E hiE

/-- On a fixed absorption fiber, the selected part and sparse set determine
the original division. -/
theorem supercriticalAbsorptionPreimageCode_injectiveOn
    {k n : ℕ} (hk : 3 ≤ k) (E : SupercriticalDivision k (Fin n))
    (s : ℕ) :
    Set.InjOn (supercriticalAbsorptionPreimageCode hk)
      (supercriticalAbsorptionPreimageFinset hk E s :
        Set (SupercriticalDivision k (Fin n))) := by
  intro D hD F hF hcode
  have hindex : supercriticalSmallestPartIndex hk D =
      supercriticalSmallestPartIndex hk F :=
    congrArg Prod.fst hcode
  have hsparse : D.sparse = F.sparse :=
    congrArg Prod.snd hcode
  have hDabsorb := (mem_supercriticalAbsorptionPreimageFinset.mp hD).2
  have hFabsorb := (mem_supercriticalAbsorptionPreimageFinset.mp hF).2
  exact absorbSparseDivision_eq_of_code_eq hk hindex hsparse
    (hDabsorb.trans hFabsorb.symm)

/-- Sharp finite preimage bound for sparse absorption. -/
theorem card_supercriticalAbsorptionPreimageFinset_le
    {k n : ℕ} (hk : 3 ≤ k) (E : SupercriticalDivision k (Fin n))
    (s : ℕ) :
    (supercriticalAbsorptionPreimageFinset hk E s).card ≤
      (k - 1) * n.choose s := by
  classical
  let F := supercriticalAbsorptionPreimageFinset hk E s
  let encode : SupercriticalDivision k (Fin n) →
      Fin (k - 1) × Finset (Fin n) :=
    supercriticalAbsorptionPreimageCode hk
  let codes : Finset (Fin (k - 1) × Finset (Fin n)) :=
    (Finset.univ : Finset (Fin (k - 1))) ×ˢ
      (Finset.univ : Finset (Fin n)).powersetCard s
  have hinj : Set.InjOn encode (F : Set (SupercriticalDivision k (Fin n))) :=
    supercriticalAbsorptionPreimageCode_injectiveOn hk E s
  have hsubset : F.image encode ⊆ codes := by
    intro code hcode
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hcode
    have hcard := (mem_supercriticalAbsorptionPreimageFinset.mp hD).1
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩⟩
  calc
    F.card = (F.image encode).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ codes.card := Finset.card_le_card hsubset
    _ = (k - 1) * n.choose s := by
      simp [codes]

/-- Paper-facing alias for the sparse-absorption preimage bound. -/
theorem supercriticalAbsorptionPreimage_card_le
    {k n : ℕ} (hk : 3 ≤ k) (E : SupercriticalDivision k (Fin n))
    (s : ℕ) :
    (supercriticalAbsorptionPreimageFinset hk E s).card ≤
      (k - 1) * n.choose s :=
  card_supercriticalAbsorptionPreimageFinset_le hk E s

end InducedStars
