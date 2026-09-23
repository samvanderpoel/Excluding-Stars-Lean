import DenseGraph.FiniteModels.Janson
import InducedStars.Graphon.Star
import InducedStars.Structure.Supercritical.CountingSetup
import InducedStars.Structure.Supercritical.Reference
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# Medium-degree potential stars

This file isolates the deterministic and product-probability part of the
supercritical medium-degree argument.  The mixed edge/nonedge requirements
are encoded by one global orientation of the cross-edge coordinates.  Thus
every potential-copy event is a principal up-set after coordinate
complementation.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

universe u v

noncomputable local instance mediumCandidatesPropDecidable (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

/-! ## The distinguished and complementary sets -/

/-- The paper's set `N` for a medium witness.  At a main-part witness it is
the set of missing same-part neighbours; at a sparse witness it is the set of
present neighbours in the distinguished main part. -/
def supercriticalMediumN {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Finset (Fin n) := by
  classical
  exact if w.vertex ∈ D.parts w.part then
    (D.parts w.part).filter fun x ↦ x ≠ w.vertex ∧ ¬G.Adj w.vertex x
  else
    (D.parts w.part).filter fun x ↦ G.Adj w.vertex x

/-- The complementary set `Z` in the distinguished main part. -/
def supercriticalMediumZ {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Finset (Fin n) := by
  classical
  exact if w.vertex ∈ D.parts w.part then
    (D.parts w.part).filter fun x ↦ G.Adj w.vertex x
  else
    (D.parts w.part).filter fun x ↦ x ≠ w.vertex ∧ ¬G.Adj w.vertex x

/-- In another main part, `N_j` is the set of nonneighbours of the fixed
witness vertex. -/
def supercriticalMediumOtherN {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (j : Fin (k - 1)) :
    Finset (Fin n) := by
  classical
  exact (D.parts j).filter fun y ↦ y ≠ w.vertex ∧ ¬G.Adj w.vertex y

theorem supercriticalMediumN_subset_part
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    supercriticalMediumN w ⊆ D.parts w.part := by
  classical
  intro x hx
  by_cases hv : w.vertex ∈ D.parts w.part
  · have h : x ∈ D.parts w.part ∧ x ≠ w.vertex ∧
        ¬G.Adj w.vertex x := by simpa [supercriticalMediumN, hv] using hx
    exact h.1
  · have h : x ∈ D.parts w.part ∧ G.Adj w.vertex x := by
      simpa [supercriticalMediumN, hv] using hx
    exact h.1

theorem supercriticalMediumZ_subset_part
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    supercriticalMediumZ w ⊆ D.parts w.part := by
  classical
  intro x hx
  by_cases hv : w.vertex ∈ D.parts w.part
  · have h : x ∈ D.parts w.part ∧ G.Adj w.vertex x := by
      simpa [supercriticalMediumZ, hv] using hx
    exact h.1
  · have h : x ∈ D.parts w.part ∧ x ≠ w.vertex ∧
        ¬G.Adj w.vertex x := by simpa [supercriticalMediumZ, hv] using hx
    exact h.1

theorem supercriticalMediumOtherN_subset_part
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (j : Fin (k - 1)) :
    supercriticalMediumOtherN w j ⊆ D.parts j := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

theorem supercriticalMediumN_card_eq_defectDegree
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (supercriticalMediumN w).card =
      degreeInFinset (combinedSupercriticalDefectGraph G D)
        w.vertex (D.parts w.part) := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [degreeInFinset_combinedDefect_part_of_mem_same G D w.part hv]
    simp [supercriticalMediumN, hv, complementDegreeInFinset]
  · have hs : w.vertex ∈ D.sparse := w.location.resolve_left hv
    rw [degreeInFinset_combinedDefect_part_of_mem_sparse G D hs w.part]
    simp [supercriticalMediumN, hv, degreeInFinset]

theorem supercriticalMediumN_card_bounds
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    α * (D.parts w.part).card ≤ ((supercriticalMediumN w).card : ℝ) ∧
      ((supercriticalMediumN w).card : ℝ) ≤
        (1 - α) * (D.parts w.part).card := by
  have hm := w.medium
  unfold HasMediumDegreeInPart at hm
  rw [← supercriticalMediumN_card_eq_defectDegree w] at hm
  exact hm

theorem supercriticalMediumN_disjoint_Z
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Disjoint (supercriticalMediumN w) (supercriticalMediumZ w) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxN hxZ
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hN : x ∈ D.parts w.part ∧ x ≠ w.vertex ∧
        ¬G.Adj w.vertex x := by simpa [supercriticalMediumN, hv] using hxN
    have hZ : x ∈ D.parts w.part ∧ G.Adj w.vertex x := by
      simpa [supercriticalMediumZ, hv] using hxZ
    exact hN.2.2 hZ.2
  · have hN : x ∈ D.parts w.part ∧ G.Adj w.vertex x := by
      simpa [supercriticalMediumN, hv] using hxN
    have hZ : x ∈ D.parts w.part ∧ x ≠ w.vertex ∧
        ¬G.Adj w.vertex x := by simpa [supercriticalMediumZ, hv] using hxZ
    exact hZ.2.2 hN.2

/-- Exact natural-number partition identity.  This avoids treating natural
subtraction as integer subtraction in the main-part case. -/
theorem supercriticalMediumN_card_add_Z_card
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (supercriticalMediumN w).card + (supercriticalMediumZ w).card =
      if w.vertex ∈ D.parts w.part then (D.parts w.part).card - 1
      else (D.parts w.part).card := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hsum := degreeInFinset_add_complementDegreeInFinset G w.vertex
      (D.parts w.part)
    simpa [supercriticalMediumN, supercriticalMediumZ, hv,
      degreeInFinset, complementDegreeInFinset, Nat.add_comm,
      Finset.card_erase_of_mem hv] using hsum
  · have hvnot : w.vertex ∉ D.parts w.part := hv
    have hsum := degreeInFinset_add_complementDegreeInFinset G w.vertex
      (D.parts w.part)
    simpa [supercriticalMediumN, supercriticalMediumZ, hv,
      degreeInFinset, complementDegreeInFinset, Nat.add_comm,
      Finset.erase_eq_self.mpr hvnot] using hsum

/-- A uniform positive-size estimate for `Z`, with the unavoidable one-vertex
loss when the witness itself belongs to the distinguished main part. -/
theorem supercriticalMediumZ_card_lower
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    α * (D.parts w.part).card - 1 ≤
      ((supercriticalMediumZ w).card : ℝ) := by
  have hsum := supercriticalMediumN_card_add_Z_card w
  have hupper := (supercriticalMediumN_card_bounds w).2
  by_cases hv : w.vertex ∈ D.parts w.part
  · rw [if_pos hv] at hsum
    have hsumNat : (supercriticalMediumN w).card +
        (supercriticalMediumZ w).card + 1 = (D.parts w.part).card := by
      have hpart : 0 < (D.parts w.part).card := (D.parts_nonempty w.part).card_pos
      omega
    have hsumReal : ((supercriticalMediumN w).card : ℝ) +
        ((supercriticalMediumZ w).card : ℝ) + 1 =
          ((D.parts w.part).card : ℝ) := by exact_mod_cast hsumNat
    linarith
  · rw [if_neg hv] at hsum
    have hsumReal : ((supercriticalMediumN w).card : ℝ) +
        ((supercriticalMediumZ w).card : ℝ) =
          ((D.parts w.part).card : ℝ) := by exact_mod_cast hsum
    linarith

/-! ## Canonical minimality and the other parts -/

/-- The deterministic hypotheses used to compare a medium witness with
single-vertex moves of its division.  They are exactly pre-Janson structural
hypotheses: canonical minimality and the availability of a source-part
remainder for a main-part move. -/
structure SupercriticalMediumMoveData
    {k n : ℕ} (G : SimpleGraph (Fin n)) (α : ℝ)
    (D : SupercriticalDivision k (Fin n)) where
  witness : SupercriticalMediumWitness G α D
  minimal : ∀ E : SupercriticalDivision k (Fin n),
    supercriticalDefectCost G D ≤ supercriticalDefectCost G E
  main_remainder : witness.vertex ∈ D.parts witness.part →
    ((D.parts witness.part).erase witness.vertex).Nonempty

/-- Canonical minimality forces the number of nonneighbours of the witness
in any other main part to dominate `|N|`. -/
theorem supercriticalMediumN_card_le_otherN_card
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (C : SupercriticalMediumMoveData G α D)
    (j : Fin (k - 1)) (hji : j ≠ C.witness.part) :
    (supercriticalMediumN C.witness).card ≤
      (supercriticalMediumOtherN C.witness j).card := by
  classical
  let w := C.witness
  have hother : (supercriticalMediumOtherN w j).card =
      complementDegreeInFinset G w.vertex (D.parts j) := by
    simp [supercriticalMediumOtherN, complementDegreeInFinset]
  rw [hother]
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hN : (supercriticalMediumN w).card =
        complementDegreeInFinset G w.vertex (D.parts w.part) := by
      simp [supercriticalMediumN, hv, complementDegreeInFinset]
    rw [hN]
    have hmove :=
      SupercriticalDivision.supercriticalDefectCost_moveMainToMain_add
        G D w.vertex hv hji.symm (C.main_remainder hv)
    have hmin := C.minimal
      (D.moveMainToMain w.vertex hv hji.symm (C.main_remainder hv))
    omega
  · have hs : w.vertex ∈ D.sparse := w.location.resolve_left hv
    have hN : (supercriticalMediumN w).card =
        degreeInFinset G w.vertex (D.parts w.part) := by
      simp [supercriticalMediumN, hv, degreeInFinset]
    rw [hN]
    have hmove :=
      SupercriticalDivision.supercriticalDefectCost_moveSparseToMain_add
        G D j w.vertex hs
    have hmin := C.minimal (D.moveSparseToMain j w.vertex hs)
    have hmono := degreeInFinset_mono G w.vertex
      (D.part_subset_support w.part)
    omega

/-- With the explicit factor-two balance condition, every other-part
nonneighbour set has the paper's `α/2` lower bound. -/
theorem supercriticalMediumOtherN_card_lower
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (hα : 0 ≤ α) (C : SupercriticalMediumMoveData G α D)
    (j : Fin (k - 1)) (hji : j ≠ C.witness.part)
    (hbalance : (D.parts j).card ≤ 2 * (D.parts C.witness.part).card) :
    (α / 2) * (D.parts j).card ≤
      ((supercriticalMediumOtherN C.witness j).card : ℝ) := by
  have hNlower := (supercriticalMediumN_card_bounds C.witness).1
  have hNle := supercriticalMediumN_card_le_otherN_card C j hji
  have hbalanceReal : ((D.parts j).card : ℝ) ≤
      2 * ((D.parts C.witness.part).card : ℝ) := by exact_mod_cast hbalance
  have hNleReal : ((supercriticalMediumN C.witness).card : ℝ) ≤
      ((supercriticalMediumOtherN C.witness j).card : ℝ) := by
    exact_mod_cast hNle
  nlinarith

/-! ## Reindexing all parts except the distinguished one -/

/-- The main-part indices other than `i`. -/
abbrev OtherSupercriticalPart (k : ℕ) (i : Fin (k - 1)) :=
  {j : Fin (k - 1) // j ≠ i}

/-- A reusable indexing equivalence for the `k-2` main parts other than a
fixed distinguished part. -/
noncomputable def otherSupercriticalPartEquiv {k : ℕ} (hk : 3 ≤ k)
    (i : Fin (k - 1)) :
    Fin (k - 2) ≃ OtherSupercriticalPart k i := by
  classical
  apply Fintype.equivOfCardEq
  simp
  omega

@[simp] theorem otherSupercriticalPartEquiv_ne
    {k : ℕ} (hk : 3 ≤ k) (i : Fin (k - 1)) (r : Fin (k - 2)) :
    (otherSupercriticalPartEquiv hk i r : Fin (k - 1)) ≠ i :=
  (otherSupercriticalPartEquiv hk i r).property

/-! Short public names matching the notation used in the paper. -/

abbrev mediumNeighborSet := @supercriticalMediumN
abbrev mediumComplementSet := @supercriticalMediumZ
abbrev otherPartNonneighbors := @supercriticalMediumOtherN

/-! ## Potential-star selections -/

/-- Index of the center in the canonical copy of `inducedStar k`. -/
def mediumCenterIndex {k : ℕ} : Fin (k + 1) := 0

/-- Index of the fixed witness leaf. -/
def mediumWitnessIndex {k : ℕ} (hk : 3 ≤ k) : Fin (k + 1) :=
  ⟨1, by omega⟩

/-- Index of the second selected leaf in the distinguished main part. -/
def mediumCompanionIndex {k : ℕ} (hk : 3 ≤ k) : Fin (k + 1) :=
  ⟨2, by omega⟩

/-- The remaining `k-2` leaf indices. -/
def mediumOtherLeafIndex {k : ℕ} (hk : 3 ≤ k) (r : Fin (k - 2)) :
    Fin (k + 1) :=
  ⟨r.1 + 3, by omega⟩

/-- A selected potential star.  The embedding records all distinctness
conditions.  Its equations pin the center and leaves to `v,x,z,y_j`; the
last fields are precisely the deterministic edges and nonedges outside the
sampled cross-edge coordinates. -/
structure SupercriticalMediumStarCandidate
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) where
  x : Fin n
  z : Fin n
  y : Fin (k - 2) → Fin n
  x_mem : x ∈ mediumNeighborSet w
  z_mem : z ∈ mediumComplementSet w
  y_mem : ∀ r, y r ∈ otherPartNonneighbors w
    (otherSupercriticalPartEquiv hk w.part r)
  embedding : Fin (k + 1) ↪ Fin n
  embedding_center : embedding mediumCenterIndex =
    if w.vertex ∈ D.parts w.part then z else x
  embedding_witness : embedding (mediumWitnessIndex hk) = w.vertex
  embedding_companion : embedding (mediumCompanionIndex hk) =
    if w.vertex ∈ D.parts w.part then x else z
  embedding_other : ∀ r, embedding (mediumOtherLeafIndex hk r) = y r
  deterministic_center_witness :
    G.Adj (embedding mediumCenterIndex) (embedding (mediumWitnessIndex hk))
  deterministic_center_companion :
    G.Adj (embedding mediumCenterIndex) (embedding (mediumCompanionIndex hk))
  deterministic_witness_companion :
    ¬G.Adj (embedding (mediumWitnessIndex hk)) (embedding (mediumCompanionIndex hk))
  deterministic_witness_other : ∀ r,
    ¬G.Adj (embedding (mediumWitnessIndex hk)) (embedding (mediumOtherLeafIndex hk r))

namespace SupercriticalMediumStarCandidate

variable {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
  {D : SupercriticalDivision k (Fin n)}
  {w : SupercriticalMediumWitness G α D}

theorem selected_distinct (K : SupercriticalMediumStarCandidate hk w)
    {a b : Fin (k + 1)} (hab : a ≠ b) :
    K.embedding a ≠ K.embedding b :=
  K.embedding.injective.ne hab

/-- The exact injective vertex map into the ambient labeled vertex set. -/
def toStarEmbedding (K : SupercriticalMediumStarCandidate hk w) :
    Fin (k + 1) ↪ Fin n :=
  K.embedding

end SupercriticalMediumStarCandidate

/-! ## A single global orientation -/

/-- Distinguished-part vertices whose cross edges to the `N_j` sets must be
present. -/
def mediumPositiveDistinguishedSet
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Finset (Fin n) :=
  if w.vertex ∈ D.parts w.part then mediumComplementSet w
  else mediumNeighborSet w

/-- Union of all `N_j` with `j` different from the distinguished part. -/
def mediumOtherNonneighborUnion
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun j ↦
    if j = w.part then ∅ else otherPartNonneighbors w j

/-- Whether an unoriented pair succeeds by being present.  All other sampled
coordinates are complemented and therefore succeed by being absent. -/
def mediumSuccessPresent
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Sym2 (Fin n) → Prop :=
  Sym2.lift ⟨fun a b ↦
      (a ∈ mediumPositiveDistinguishedSet w ∧
          b ∈ mediumOtherNonneighborUnion w) ∨
        (b ∈ mediumPositiveDistinguishedSet w ∧
          a ∈ mediumOtherNonneighborUnion w),
    by aesop⟩

/-- The one global set of complemented coordinates. -/
def mediumGlobalFlipSet
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.filter fun e ↦ ¬mediumSuccessPresent w e

@[simp] theorem mem_mediumGlobalFlipSet
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) (e : Sym2 (Fin n)) :
    e ∈ mediumGlobalFlipSet w ↔ ¬mediumSuccessPresent w e := by
  classical
  simp [mediumGlobalFlipSet]

/-- The Bernoulli law after the global coordinate complementation. -/
def orientedMediumBernoulliProduct
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (P : DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n))) :
    DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n)) :=
  P.complementCoordinates (mediumGlobalFlipSet w)

@[simp] theorem orientedMediumBernoulliProduct_probability
    {k n : ℕ} {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (P : DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n)))
    (e : Sym2 (Fin n)) :
    (orientedMediumBernoulliProduct w P).probability e =
      if mediumSuccessPresent w e then P.probability e
      else 1 - P.probability e := by
  classical
  by_cases he : mediumSuccessPresent w e
  · simp [orientedMediumBernoulliProduct, he]
  · simp [orientedMediumBernoulliProduct, he]

/-! ## Required random pairs -/

/-- Random roles in one potential star: center--other leaf,
companion--other leaf, and a pair of distinct other-part leaves. -/
abbrev SupercriticalMediumRandomRole (k : ℕ) :=
  Fin (k - 2) ⊕ (Fin (k - 2) ⊕
    {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2})

/-- The corresponding pair of abstract star vertices. -/
def mediumRandomRoleAbstractPair {k : ℕ} (hk : 3 ≤ k) :
    SupercriticalMediumRandomRole k → Sym2 (Fin (k + 1))
  | Sum.inl r => s(mediumCenterIndex, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inl r) =>
      s(mediumCompanionIndex hk, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inr p) =>
      s(mediumOtherLeafIndex hk p.1.1, mediumOtherLeafIndex hk p.1.2)

/-- Ambient coordinate occupied by one random role. -/
def mediumRandomRoleCoordinate
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    SupercriticalMediumRandomRole k → Sym2 (Fin n)
  | Sum.inl r => s(K.embedding mediumCenterIndex,
      K.embedding (mediumOtherLeafIndex hk r))
  | Sum.inr (Sum.inl r) => s(K.embedding (mediumCompanionIndex hk),
      K.embedding (mediumOtherLeafIndex hk r))
  | Sum.inr (Sum.inr p) => s(K.embedding (mediumOtherLeafIndex hk p.1.1),
      K.embedding (mediumOtherLeafIndex hk p.1.2))

theorem mediumRandomRoleCoordinate_eq_map
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleCoordinate hk K r =
      Sym2.map K.embedding (mediumRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · rfl
  · rcases r with r | r <;> rfl

/-- Required oriented successes for a candidate. -/
def requiredSuccessCoordinates
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) : Finset (Sym2 (Fin n)) := by
  classical
  exact Finset.univ.image (mediumRandomRoleCoordinate hk K)

theorem candidate_other_mem_union
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    K.embedding (mediumOtherLeafIndex hk r) ∈
      mediumOtherNonneighborUnion w := by
  classical
  rw [K.embedding_other]
  let j : Fin (k - 1) := otherSupercriticalPartEquiv hk w.part r
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  simp [j, otherSupercriticalPartEquiv_ne hk w.part r, K.y_mem]

theorem candidate_center_mem_positive
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    K.embedding mediumCenterIndex ∈ mediumPositiveDistinguishedSet w := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · simpa [mediumPositiveDistinguishedSet, hv, K.embedding_center] using K.z_mem
  · simpa [mediumPositiveDistinguishedSet, hv, K.embedding_center] using K.x_mem

theorem candidate_companion_not_mem_positive
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    K.embedding (mediumCompanionIndex hk) ∉
      mediumPositiveDistinguishedSet w := by
  classical
  intro h
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hxZ : K.x ∈ mediumComplementSet w := by
      simpa [mediumPositiveDistinguishedSet, hv, K.embedding_companion] using h
    exact (Finset.disjoint_left.mp (supercriticalMediumN_disjoint_Z w)) K.x_mem hxZ
  · have hzN : K.z ∈ mediumNeighborSet w := by
      simpa [mediumPositiveDistinguishedSet, hv, K.embedding_companion] using h
    exact (Finset.disjoint_left.mp (supercriticalMediumN_disjoint_Z w)) hzN K.z_mem

theorem candidate_other_not_mem_positive
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    K.embedding (mediumOtherLeafIndex hk r) ∉
      mediumPositiveDistinguishedSet w := by
  classical
  intro hypos
  have hposPart : K.embedding (mediumOtherLeafIndex hk r) ∈ D.parts w.part := by
    by_cases hv : w.vertex ∈ D.parts w.part
    · exact supercriticalMediumZ_subset_part w (by
        simpa [mediumPositiveDistinguishedSet, hv] using hypos)
    · exact supercriticalMediumN_subset_part w (by
        simpa [mediumPositiveDistinguishedSet, hv] using hypos)
  have hyj : K.embedding (mediumOtherLeafIndex hk r) ∈
      D.parts (otherSupercriticalPartEquiv hk w.part r) := by
    rw [K.embedding_other]
    exact supercriticalMediumOtherN_subset_part w _ (K.y_mem r)
  exact (Finset.disjoint_left.mp
    (D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (otherSupercriticalPartEquiv_ne hk w.part r).symm)) hposPart hyj

/-- Center--other coordinates use the present orientation. -/
theorem mediumSuccessPresent_center_other
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    mediumSuccessPresent w
      s(K.embedding mediumCenterIndex,
        K.embedding (mediumOtherLeafIndex hk r)) := by
  change (_ ∧ _) ∨ (_ ∧ _)
  exact Or.inl ⟨candidate_center_mem_positive hk K,
    candidate_other_mem_union hk K r⟩

/-- Companion--other coordinates use the absent orientation. -/
theorem not_mediumSuccessPresent_companion_other
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    ¬mediumSuccessPresent w
      s(K.embedding (mediumCompanionIndex hk),
        K.embedding (mediumOtherLeafIndex hk r)) := by
  change ¬((_ ∧ _) ∨ (_ ∧ _))
  rintro (h | h)
  · exact candidate_companion_not_mem_positive hk K h.1
  · exact candidate_other_not_mem_positive hk K r h.1

/-- Every other--other coordinate uses the absent orientation. -/
theorem not_mediumSuccessPresent_other_other
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r s : Fin (k - 2)) :
    ¬mediumSuccessPresent w
      s(K.embedding (mediumOtherLeafIndex hk r),
        K.embedding (mediumOtherLeafIndex hk s)) := by
  change ¬((_ ∧ _) ∨ (_ ∧ _))
  rintro (h | h)
  · exact candidate_other_not_mem_positive hk K r h.1
  · exact candidate_other_not_mem_positive hk K s h.1

/-- Intended uncomplemented value of a random role. -/
def mediumRandomRoleSuccessPresent {k : ℕ} :
    SupercriticalMediumRandomRole k → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- The role orientation is exactly the adjacency value in the abstract
star. -/
theorem mediumRandomRoleSuccessPresent_iff_star
    {k : ℕ} (hk : 3 ≤ k) (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleSuccessPresent r ↔
      Sym2.lift ⟨(inducedStar k).Adj,
        fun a b ↦ propext ((inducedStar k).adj_comm a b)⟩
        (mediumRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · simp [mediumRandomRoleSuccessPresent, mediumRandomRoleAbstractPair,
      inducedStar_adj, mediumCenterIndex, mediumOtherLeafIndex]
  · rcases r with r | p
    · simp [mediumRandomRoleSuccessPresent, mediumRandomRoleAbstractPair,
        inducedStar_adj, mediumCompanionIndex, mediumOtherLeafIndex]
    · simp [mediumRandomRoleSuccessPresent, mediumRandomRoleAbstractPair,
        inducedStar_adj, mediumOtherLeafIndex]

theorem mediumRandomRole_orientation
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    mediumSuccessPresent w (mediumRandomRoleCoordinate hk K r) ↔
      mediumRandomRoleSuccessPresent r := by
  rcases r with r | r
  · simpa [mediumRandomRoleCoordinate, mediumRandomRoleSuccessPresent] using
      mediumSuccessPresent_center_other hk K r
  · rcases r with r | p
    · simpa [mediumRandomRoleCoordinate, mediumRandomRoleSuccessPresent] using
        not_mediumSuccessPresent_companion_other hk K r
    · simpa [mediumRandomRoleCoordinate, mediumRandomRoleSuccessPresent] using
        not_mediumSuccessPresent_other_other hk K p.1.1 p.1.2

/-- Substantive shared-coordinate compatibility: equal coordinates in two
potential stars have equal intended present/absent values. -/
theorem mediumSharedCoordinate_orientation_compatible
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K L : SupercriticalMediumStarCandidate hk w)
    (r s : SupercriticalMediumRandomRole k)
    (hrs : mediumRandomRoleCoordinate hk K r =
      mediumRandomRoleCoordinate hk L s) :
    (mediumRandomRoleSuccessPresent r ↔
      mediumRandomRoleSuccessPresent s) := by
  rw [← mediumRandomRole_orientation hk K r,
    hrs, mediumRandomRole_orientation hk L s]

/-- Every required ambient coordinate has the orientation prescribed by the
corresponding edge/nonedge of the abstract induced star. -/
theorem requiredCoordinate_orientation_correct
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    {a b : Fin (k + 1)}
    (hab : s(K.embedding a, K.embedding b) ∈
      requiredSuccessCoordinates hk K) :
    mediumSuccessPresent w s(K.embedding a, K.embedding b) ↔
      (inducedStar k).Adj a b := by
  classical
  rw [requiredSuccessCoordinates, Finset.mem_image] at hab
  obtain ⟨r, -, hr⟩ := hab
  have hmap : Sym2.map K.embedding s(a, b) =
      Sym2.map K.embedding (mediumRandomRoleAbstractPair hk r) := by
    simpa [mediumRandomRoleCoordinate_eq_map hk K r] using hr.symm
  have habstract : s(a, b) = mediumRandomRoleAbstractPair hk r :=
    Sym2.map.injective K.embedding.injective hmap
  calc
    mediumSuccessPresent w s(K.embedding a, K.embedding b) ↔
        mediumRandomRoleSuccessPresent r := by
      rw [← hr]
      exact mediumRandomRole_orientation hk K r
    _ ↔ Sym2.lift ⟨(inducedStar k).Adj,
        fun x y ↦ propext ((inducedStar k).adj_comm x y)⟩
        (mediumRandomRoleAbstractPair hk r) :=
      mediumRandomRoleSuccessPresent_iff_star hk r
    _ ↔ (inducedStar k).Adj a b := by
      rw [← habstract]
      rfl

theorem mediumRandomRoleCoordinate_mem_required
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleCoordinate hk K r ∈ requiredSuccessCoordinates hk K := by
  classical
  simp [requiredSuccessCoordinates]

/-- A robust constant-only bound for one event's coordinate support. -/
theorem requiredSuccessCoordinates_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    (requiredSuccessCoordinates hk K).card ≤
      2 * (k - 2) + (k - 2) ^ 2 := by
  classical
  calc
    (requiredSuccessCoordinates hk K).card ≤
        Fintype.card (SupercriticalMediumRandomRole k) := by
      simpa [requiredSuccessCoordinates] using
        (Finset.card_image_le :
          (Finset.univ.image (mediumRandomRoleCoordinate hk K)).card ≤
            (Finset.univ : Finset (SupercriticalMediumRandomRole k)).card)
    _ ≤ 2 * (k - 2) + (k - 2) ^ 2 := by
      simp only [SupercriticalMediumRandomRole, Fintype.card_sum,
        Fintype.card_fin]
      have hsub : Fintype.card
          {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
          Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      simp only [Fintype.card_prod, Fintype.card_fin] at hsub ⊢
      have h := Nat.add_le_add_left
        (Nat.add_le_add_left hsub (k - 2)) (k - 2)
      simpa [pow_two, two_mul, Nat.add_assoc] using h

/-! ## Deterministic completion of a potential star -/

/-- Every abstract star vertex is the center, one of the two distinguished
leaves, or one of the remaining `k-2` leaves. -/
theorem mediumStarIndex_cases {k : ℕ} (hk : 3 ≤ k) (a : Fin (k + 1)) :
    a = mediumCenterIndex ∨
      a = mediumWitnessIndex hk ∨
      a = mediumCompanionIndex hk ∨
      ∃ r : Fin (k - 2), a = mediumOtherLeafIndex hk r := by
  by_cases h0 : a.1 = 0
  · exact Or.inl (Fin.ext h0)
  by_cases h1 : a.1 = 1
  · exact Or.inr (Or.inl (Fin.ext h1))
  by_cases h2 : a.1 = 2
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h2)))
  · refine Or.inr (Or.inr (Or.inr ⟨⟨a.1 - 3, by omega⟩, ?_⟩))
    apply Fin.ext
    simp only [mediumOtherLeafIndex]
    omega

/-- Outside the explicitly sampled coordinates, the candidate fields already
give exactly the adjacencies of the canonical induced star. -/
theorem mediumCandidate_deterministicPair
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (a b : Fin (k + 1))
    (hab : s(K.embedding a, K.embedding b) ∉
      requiredSuccessCoordinates hk K) :
    (G.Adj (K.embedding a) (K.embedding b) ↔
      (inducedStar k).Adj a b) := by
  rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩ <;>
    rcases mediumStarIndex_cases hk b with hb | hb | hb | ⟨t, hb⟩ <;>
    subst a <;> subst b
  · simp
  · simpa [mediumCenterIndex, mediumWitnessIndex] using
      K.deterministic_center_witness
  · simpa [mediumCenterIndex, mediumCompanionIndex] using
      K.deterministic_center_companion
  · exfalso
    apply hab
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inl t)
  · simpa [mediumCenterIndex, mediumWitnessIndex] using
      K.deterministic_center_witness.symm
  · simp
  · simpa [mediumWitnessIndex, mediumCompanionIndex] using
      K.deterministic_witness_companion
  · simpa [mediumWitnessIndex, mediumOtherLeafIndex] using
      K.deterministic_witness_other t
  · simpa [mediumCenterIndex, mediumCompanionIndex] using
      K.deterministic_center_companion.symm
  · constructor
    · intro h
      exact (K.deterministic_witness_companion
        ((G.adj_comm _ _).mp h)).elim
    · intro hstar
      exfalso
      simpa [mediumCompanionIndex, mediumWitnessIndex] using hstar
  · simp
  · exfalso
    apply hab
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inr (Sum.inl t))
  · exfalso
    apply hab
    rw [Sym2.eq_swap]
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inl r)
  · constructor
    · intro h
      exact (K.deterministic_witness_other r
        ((G.adj_comm _ _).mp h)).elim
    · intro hstar
      exfalso
      simpa [mediumOtherLeafIndex, mediumWitnessIndex] using hstar
  · exfalso
    apply hab
    rw [Sym2.eq_swap]
    simpa [mediumRandomRoleCoordinate] using
      mediumRandomRoleCoordinate_mem_required hk K (Sum.inr (Sum.inl r))
  · by_cases hrt : r = t
    · subst t
      simp
    · exfalso
      apply hab
      rcases lt_or_gt_of_ne hrt with hlt | hgt
      · simpa [mediumRandomRoleCoordinate] using
          mediumRandomRoleCoordinate_mem_required hk K
            (Sum.inr (Sum.inr ⟨(r, t), hlt⟩))
      · simpa [mediumRandomRoleCoordinate, Sym2.eq_swap] using
          mediumRandomRoleCoordinate_mem_required hk K
            (Sum.inr (Sum.inr ⟨(t, r), hgt⟩))

/-- An oriented Boolean-cube outcome realizes a candidate when sampled
coordinates are decoded using the one global present/absent orientation, and
all other pairs retain their deterministic adjacency in `G`. -/
def MediumCandidateOutcomeRealizes
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (H : SimpleGraph (Fin n)) (outcome : Finset (Sym2 (Fin n))) : Prop :=
  ∀ a b : Fin (k + 1),
    H.Adj (K.embedding a) (K.embedding b) ↔
      if s(K.embedding a, K.embedding b) ∈
          requiredSuccessCoordinates hk K then
        (mediumSuccessPresent w s(K.embedding a, K.embedding b) ↔
          s(K.embedding a, K.embedding b) ∈ outcome)
      else G.Adj (K.embedding a) (K.embedding b)

/-- If every required oriented coordinate succeeds, the potential copy is a
genuine induced copy of `K_{1,k}` in the realized graph. -/
theorem mediumPotentialSuccess_inducedStar
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (H : SimpleGraph (Fin n)) (outcome : Finset (Sym2 (Fin n)))
    (hrealize : MediumCandidateOutcomeRealizes hk K H outcome)
    (hsuccess : requiredSuccessCoordinates hk K ⊆ outcome) :
    Regularity.InducedEmbeds (inducedStar k) H := by
  classical
  refine ⟨{
    toFun := K.embedding
    inj' := K.embedding.injective
    map_rel_iff' := ?_ }⟩
  intro a b
  change H.Adj (K.embedding a) (K.embedding b) ↔ (inducedStar k).Adj a b
  by_cases hab : s(K.embedding a, K.embedding b) ∈
      requiredSuccessCoordinates hk K
  · rw [hrealize a b, if_pos hab]
    have hout : s(K.embedding a, K.embedding b) ∈ outcome := hsuccess hab
    have horient := requiredCoordinate_orientation_correct hk K hab
    simpa [hout] using horient
  · rw [hrealize a b, if_neg hab]
    exact mediumCandidate_deterministicPair hk K a b hab

/-- Consequently an induced-star-free realization avoids the principal
success event of every individual candidate. -/
theorem inducedStarFree_implies_mediumCandidateAvoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (H : SimpleGraph (Fin n)) (outcome : Finset (Sym2 (Fin n)))
    (hrealize : MediumCandidateOutcomeRealizes hk K H outcome)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) H) :
    ¬requiredSuccessCoordinates hk K ⊆ outcome := by
  intro hsuccess
  exact hfree (mediumPotentialSuccess_inducedStar hk K H outcome hrealize hsuccess)

/-- A star-free realization belongs to the simultaneous Janson avoidance
event for any finite indexed family of candidates. -/
theorem inducedStarFree_implies_mediumPrincipalAvoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    {I : Type*} [Fintype I] [LinearOrder I]
    (K : I → SupercriticalMediumStarCandidate hk w)
    (H : SimpleGraph (Fin n)) (outcome : Finset (Sym2 (Fin n)))
    (hrealize : ∀ i, MediumCandidateOutcomeRealizes hk (K i) H outcome)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) H) :
    outcome ∈ DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
      (fun i ↦ requiredSuccessCoordinates hk (K i)) := by
  rw [DenseGraph.FiniteBernoulliProduct.mem_principalAvoidanceEvent]
  intro i
  exact inducedStarFree_implies_mediumCandidateAvoidance hk (K i) H outcome
    (hrealize i) hfree

/-- The event of oriented outcomes whose decoded graph is induced-star-free. -/
def mediumInducedStarFreeOutcomeEvent
    (k n : ℕ)
    (graphOfOutcome : Finset (Sym2 (Fin n)) → SimpleGraph (Fin n)) :
    Finset (Finset (Sym2 (Fin n))) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    ¬Regularity.InducedEmbeds (inducedStar k) (graphOfOutcome outcome)

@[simp] theorem mem_mediumInducedStarFreeOutcomeEvent
    {k n : ℕ}
    (graphOfOutcome : Finset (Sym2 (Fin n)) → SimpleGraph (Fin n))
    (outcome : Finset (Sym2 (Fin n))) :
    outcome ∈ mediumInducedStarFreeOutcomeEvent k n graphOfOutcome ↔
      ¬Regularity.InducedEmbeds (inducedStar k) (graphOfOutcome outcome) := by
  classical
  simp [mediumInducedStarFreeOutcomeEvent]

/-- Event-level form of star-free implies avoidance. -/
theorem mediumInducedStarFreeOutcomeEvent_subset_avoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    {I : Type*} [Fintype I] [LinearOrder I]
    (K : I → SupercriticalMediumStarCandidate hk w)
    (graphOfOutcome : Finset (Sym2 (Fin n)) → SimpleGraph (Fin n))
    (hrealize : ∀ outcome i,
      MediumCandidateOutcomeRealizes hk (K i) (graphOfOutcome outcome) outcome) :
    mediumInducedStarFreeOutcomeEvent k n graphOfOutcome ⊆
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
        (fun i ↦ requiredSuccessCoordinates hk (K i)) := by
  intro outcome houtcome
  exact inducedStarFree_implies_mediumPrincipalAvoidance hk K
    (graphOfOutcome outcome) outcome (hrealize outcome)
    ((mem_mediumInducedStarFreeOutcomeEvent graphOfOutcome outcome).mp houtcome)

/-- Probability-level bridge from induced-star-freeness to the Janson
avoidance event. -/
theorem mediumInducedStarFreeProbability_le_avoidance
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    {I : Type*} [Fintype I] [LinearOrder I]
    (K : I → SupercriticalMediumStarCandidate hk w)
    (P : DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n)))
    (graphOfOutcome : Finset (Sym2 (Fin n)) → SimpleGraph (Fin n))
    (hrealize : ∀ outcome i,
      MediumCandidateOutcomeRealizes hk (K i) (graphOfOutcome outcome) outcome) :
    P.eventProbability (mediumInducedStarFreeOutcomeEvent k n graphOfOutcome) ≤
      P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
          (fun i ↦ requiredSuccessCoordinates hk (K i))) :=
  P.eventProbability_mono
    (mediumInducedStarFreeOutcomeEvent_subset_avoidance hk K graphOfOutcome hrealize)

/-! ## Generic coordinate adapter

The fixed-cardinality model uses tagged block coordinates rather than
ambient `Sym2` pairs.  The following small structure lets that model reuse
the role-orientation proof without identifying the two coordinate types. -/

/-- A realization of the random roles of one candidate in an arbitrary
finite coordinate type. -/
structure SupercriticalMediumRoleCoordinates
    (k : ℕ) (hk : 3 ≤ k) (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  coordinate : SupercriticalMediumRandomRole k → Ω
  successPresent : Ω → Prop
  role_orientation : ∀ r,
    successPresent (coordinate r) ↔ mediumRandomRoleSuccessPresent r

namespace SupercriticalMediumRoleCoordinates

variable {k : ℕ} (hk : 3 ≤ k) {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Required coordinates in an arbitrary (in particular, tagged-block)
coordinate realization. -/
def required (C : SupercriticalMediumRoleCoordinates k hk Ω) : Finset Ω := by
  classical
  exact Finset.univ.image C.coordinate

theorem coordinate_mem_required
    (C : SupercriticalMediumRoleCoordinates k hk Ω)
    (r : SupercriticalMediumRandomRole k) : C.coordinate r ∈ C.required hk := by
  classical
  simp [required]

theorem required_card_le
    (C : SupercriticalMediumRoleCoordinates k hk Ω) :
    (C.required hk).card ≤ 2 * (k - 2) + (k - 2) ^ 2 := by
  classical
  calc
    (C.required hk).card ≤ Fintype.card (SupercriticalMediumRandomRole k) := by
      simpa [required] using
        (Finset.card_image_le :
          (Finset.univ.image C.coordinate).card ≤
            (Finset.univ : Finset (SupercriticalMediumRandomRole k)).card)
    _ ≤ 2 * (k - 2) + (k - 2) ^ 2 := by
      simp only [SupercriticalMediumRandomRole, Fintype.card_sum,
        Fintype.card_fin]
      have hsub : Fintype.card
          {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
          Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      simp only [Fintype.card_prod, Fintype.card_fin] at hsub ⊢
      have h := Nat.add_le_add_left
        (Nat.add_le_add_left hsub (k - 2)) (k - 2)
      simpa [pow_two, two_mul, Nat.add_assoc] using h

/-- Shared tagged coordinates cannot receive conflicting success values. -/
theorem compatible
    (C C' : SupercriticalMediumRoleCoordinates k hk Ω)
    (hsame : C.successPresent = C'.successPresent)
    (r s : SupercriticalMediumRandomRole k)
    (hrs : C.coordinate r = C'.coordinate s) :
    (mediumRandomRoleSuccessPresent r ↔ mediumRandomRoleSuccessPresent s) := by
  rw [← C.role_orientation r, hrs, hsame, C'.role_orientation s]

end SupercriticalMediumRoleCoordinates

/-! ## Uniform probability floors -/

/-- A fixed lower bound for both cross-edge outcomes in the supercritical
limit model. -/
def mediumSuccessProbabilityFloor (k : ℕ) (γ : ℝ) : ℝ :=
  min (supercriticalOffDiagonal k γ)
    (1 - supercriticalOffDiagonal k γ) / 2

theorem mediumSuccessProbabilityFloor_pos
    {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) :
    0 < mediumSuccessProbabilityFloor k γ := by
  have hp : 0 < supercriticalOffDiagonal k γ :=
    supercriticalOffDiagonal_pos hk hγ.1
  have hp1 : supercriticalOffDiagonal k γ < 1 :=
    supercriticalOffDiagonal_lt_one hk hγ.2
  simp only [mediumSuccessProbabilityFloor]
  positivity

theorem mediumSuccessProbabilityFloor_le_one
    {k : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) :
    mediumSuccessProbabilityFloor k γ ≤ 1 := by
  have hp : 0 < supercriticalOffDiagonal k γ :=
    supercriticalOffDiagonal_pos hk hγ.1
  have hp1 : supercriticalOffDiagonal k γ < 1 :=
    supercriticalOffDiagonal_lt_one hk hγ.2
  unfold mediumSuccessProbabilityFloor
  have hmin : min (supercriticalOffDiagonal k γ)
      (1 - supercriticalOffDiagonal k γ) ≤ 1 - supercriticalOffDiagonal k γ :=
    min_le_right _ _
  linarith

/-- Coordinatewise lower bounds give a uniform principal-event lower bound. -/
theorem principalSuccessEvent_probability_lower
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : DenseGraph.FiniteBernoulliProduct Ω) (required : Finset Ω)
    {p : ℝ} {R : ℕ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcard : required.card ≤ R)
    (hcoordinate : ∀ e ∈ required, p ≤ P.probability e) :
    p ^ R ≤ P.eventProbability
      (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent required) := by
  rw [DenseGraph.FiniteBernoulliProduct.eventProbability_principalSuccessEvent]
  calc
    p ^ R ≤ p ^ required.card :=
      pow_le_pow_of_le_one hp0 hp1 hcard
    _ = ∏ _e ∈ required, p := (Finset.prod_const p).symm
    _ ≤ ∏ e ∈ required, P.probability e := by
      exact Finset.prod_le_prod (fun _ _ ↦ hp0) hcoordinate

/-! ## Expectation and overlap estimates -/

/-- Disjoint required-coordinate sets give independent potential-star
events.  This is the precise dependency criterion used below. -/
theorem mediumPrincipalEvents_independent_of_disjoint
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    {A B : Finset Ω} (hAB : Disjoint A B) :
    P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent A ∩
          DenseGraph.FiniteBernoulliProduct.principalSuccessEvent B) =
      P.eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent A) *
        P.eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent B) :=
  P.eventProbability_principalSuccessEvent_inter_eq_mul_of_disjoint hAB

/-- Candidate abundance and a uniform event floor give the required lower
bound on Janson's expectation. -/
theorem mediumJansonMu_lower
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) {k n : ℕ} {c eventFloor : ℝ}
    (hevent0 : 0 ≤ eventFloor)
    (hevent : ∀ i, eventFloor ≤ P.eventProbability
      (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent (required i)))
    (hcard : c * (n : ℝ) ^ k ≤ (Fintype.card I : ℝ)) :
    c * eventFloor * (n : ℝ) ^ k ≤
      P.principalJansonMu required := by
  unfold DenseGraph.FiniteBernoulliProduct.principalJansonMu
  calc
    c * eventFloor * (n : ℝ) ^ k =
        eventFloor * (c * (n : ℝ) ^ k) := by ring
    _ ≤ eventFloor * (Fintype.card I : ℝ) :=
      mul_le_mul_of_nonneg_left hcard hevent0
    _ = ∑ _i : I, eventFloor := by simp [mul_comm]
    _ ≤ ∑ i : I, P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
          (required i)) := by
      exact Finset.sum_le_sum fun i _ ↦ hevent i

/-- The unordered dependency sum is at most the number of overlapping
unordered pairs; intersection probabilities are bounded by one. -/
theorem mediumJansonDelta_le_overlapPairCount
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) :
    P.principalJansonDelta required ≤
      ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        required).card : ℝ) := by
  unfold DenseGraph.FiniteBernoulliProduct.principalJansonDelta
  calc
    ∑ ij ∈ DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs required,
        P.eventProbability
          (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
            (required ij.1 ∪ required ij.2)) ≤
        ∑ _ij ∈ DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
          required, (1 : ℝ) := by
      exact Finset.sum_le_sum fun ij _ ↦ P.eventProbability_le_one _
    _ = ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        required).card : ℝ) := by simp

/-- A convenient real-valued dependency-sum upper bound from a purely
combinatorial overlapping-pair count. -/
theorem mediumJansonDelta_upper
    {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω) {B : ℝ}
    (hpairs : ((DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      required).card : ℝ) ≤ B) :
    P.principalJansonDelta required ≤ B :=
  (mediumJansonDelta_le_overlapPairCount P required).trans hpairs

/-! ## Janson avoidance -/

set_option maxHeartbeats 800000 in
/-- The exact medium-star Janson application.  The two displayed hypotheses
are the separately auditable expectation and overlap calculations; the
theorem also handles the zero-overlap case without division by zero. -/
theorem mediumStarJansonAvoidance
    {Ω : Type u} {I : Type v} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [LinearOrder I]
    (J : DenseGraph.PrincipalJansonInput.{u, v})
    (P : DenseGraph.FiniteBernoulliProduct Ω)
    (required : I → Finset Ω)
    {n : ℕ} {c : ℝ}
    (hμ : 0 < P.principalJansonMu required)
    (hμquad : c * (n : ℝ) ^ 2 ≤ P.principalJansonMu required / 2)
    (hΔquad : 0 < P.principalJansonDelta required →
      c * (n : ℝ) ^ 2 ≤
        (P.principalJansonMu required) ^ 2 /
          (4 * P.principalJansonDelta required)) :
    P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
      Real.exp (-(c * (n : ℝ) ^ 2)) := by
  by_cases hΔzero : P.principalJansonDelta required = 0
  · calc
        P.eventProbability
            (DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent required) ≤
            Real.exp (-P.principalJansonMu required) :=
          DenseGraph.PrincipalJansonInput.principalJanson_avoidance_le_exp_neg_of_delta_eq_zero
              J (P := P) (required := required) hμ hΔzero
        _ ≤ Real.exp (-(c * (n : ℝ) ^ 2)) := by
          apply Real.exp_le_exp.mpr
          apply neg_le_neg
          exact hμquad.trans (half_le_self hμ.le)
  · have hΔ : 0 < P.principalJansonDelta required :=
      lt_of_le_of_ne (P.principalJansonDelta_nonneg required) (Ne.symm hΔzero)
    exact DenseGraph.PrincipalJansonInput.avoidance_le_exp_neg_of_mu_lower_dependency_upper
        J (P := P) (required := required) hμ hΔ hμquad (hΔquad hΔ)

end InducedStars
