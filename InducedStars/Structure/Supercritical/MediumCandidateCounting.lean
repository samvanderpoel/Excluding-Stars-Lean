import InducedStars.Structure.Supercritical.MediumCandidates

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance mediumCandidateCountingPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

/-- Split the abstract star labels into its three distinguished labels and
the remaining `k-2` leaf labels. -/
def mediumStarVertexEquiv {k : ℕ} (hk : 3 ≤ k) :
    Fin (k + 1) ≃ Fin 3 ⊕ Fin (k - 2) :=
  (finCongr (by omega : k + 1 = 3 + (k - 2))).trans finSumFinEquiv.symm

@[simp] theorem mediumStarVertexEquiv_center
    {k : ℕ} (hk : 3 ≤ k) :
    mediumStarVertexEquiv hk mediumCenterIndex = Sum.inl 0 := by
  rw [mediumStarVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  rfl

@[simp] theorem mediumStarVertexEquiv_witness
    {k : ℕ} (hk : 3 ≤ k) :
    mediumStarVertexEquiv hk (mediumWitnessIndex hk) = Sum.inl 1 := by
  rw [mediumStarVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  rfl

@[simp] theorem mediumStarVertexEquiv_companion
    {k : ℕ} (hk : 3 ≤ k) :
    mediumStarVertexEquiv hk (mediumCompanionIndex hk) = Sum.inl 2 := by
  rw [mediumStarVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  rfl

@[simp] theorem mediumStarVertexEquiv_other
    {k : ℕ} (hk : 3 ≤ k) (r : Fin (k - 2)) :
    mediumStarVertexEquiv hk (mediumOtherLeafIndex hk r) = Sum.inr r := by
  rw [mediumStarVertexEquiv, Equiv.trans_apply, Equiv.symm_apply_eq]
  apply Fin.ext
  simp [mediumOtherLeafIndex]
  omega

/-- All raw choices before deleting pairs whose required deterministic
distinguished-part edge is absent. -/
abbrev SupercriticalMediumRawSelection
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :=
  {x : Fin n // x ∈ mediumNeighborSet w} ×
    {z : Fin n // z ∈ mediumComplementSet w} ×
      ((r : Fin (k - 2)) →
        {y : Fin n // y ∈ otherPartNonneighbors w
          (otherSupercriticalPartEquiv hk w.part r)})

namespace SupercriticalMediumRawSelection

variable {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
  {D : SupercriticalDivision k (Fin n)}
  {w : SupercriticalMediumWitness G α D}

def x (S : SupercriticalMediumRawSelection hk w) : Fin n := S.1.1
def z (S : SupercriticalMediumRawSelection hk w) : Fin n := S.2.1.1
def y (S : SupercriticalMediumRawSelection hk w) (r : Fin (k - 2)) : Fin n :=
  (S.2.2 r).1

@[simp] theorem x_mem (S : SupercriticalMediumRawSelection hk w) :
    S.x hk ∈ mediumNeighborSet w := S.1.2

@[simp] theorem z_mem (S : SupercriticalMediumRawSelection hk w) :
    S.z hk ∈ mediumComplementSet w := S.2.1.2

@[simp] theorem y_mem (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) :
    S.y hk r ∈ otherPartNonneighbors w
      (otherSupercriticalPartEquiv hk w.part r) :=
  (S.2.2 r).2

def center (S : SupercriticalMediumRawSelection hk w) : Fin n :=
  if w.vertex ∈ D.parts w.part then S.z hk else S.x hk

def companion (S : SupercriticalMediumRawSelection hk w) : Fin n :=
  if w.vertex ∈ D.parts w.part then S.x hk else S.z hk

/-- The selected abstract-star vertex map before its injectivity is bundled. -/
def vertexMap (S : SupercriticalMediumRawSelection hk w) :
    Fin (k + 1) → Fin n :=
  Sum.elim
    (fun j : Fin 3 ↦ ![S.center hk, w.vertex, S.companion hk] j)
    (S.y hk) ∘ mediumStarVertexEquiv hk

@[simp] theorem vertexMap_center (S : SupercriticalMediumRawSelection hk w) :
    S.vertexMap hk mediumCenterIndex = S.center hk := by
  simp [vertexMap]

@[simp] theorem vertexMap_witness (S : SupercriticalMediumRawSelection hk w) :
    S.vertexMap hk (mediumWitnessIndex hk) = w.vertex := by
  simp [vertexMap]

@[simp] theorem vertexMap_companion (S : SupercriticalMediumRawSelection hk w) :
    S.vertexMap hk (mediumCompanionIndex hk) = S.companion hk := by
  simp [vertexMap]

@[simp] theorem vertexMap_other (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) :
    S.vertexMap hk (mediumOtherLeafIndex hk r) = S.y hk r := by
  simp [vertexMap]

theorem x_mem_part (S : SupercriticalMediumRawSelection hk w) :
    S.x hk ∈ D.parts w.part :=
  supercriticalMediumN_subset_part w (S.x_mem hk)

theorem z_mem_part (S : SupercriticalMediumRawSelection hk w) :
    S.z hk ∈ D.parts w.part :=
  supercriticalMediumZ_subset_part w (S.z_mem hk)

theorem y_mem_part (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) :
    S.y hk r ∈ D.parts (otherSupercriticalPartEquiv hk w.part r) :=
  supercriticalMediumOtherN_subset_part w _ (S.y_mem hk r)

theorem x_ne_z (S : SupercriticalMediumRawSelection hk w) :
    S.x hk ≠ S.z hk := by
  intro h
  exact (Finset.disjoint_left.mp (supercriticalMediumN_disjoint_Z w))
    (S.x_mem hk) (h ▸ S.z_mem hk)

theorem x_ne_witness (S : SupercriticalMediumRawSelection hk w) :
    S.x hk ≠ w.vertex := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hx : S.x hk ∈ D.parts w.part ∧ S.x hk ≠ w.vertex ∧
        ¬G.Adj w.vertex (S.x hk) := by
      simpa [x, mediumNeighborSet, supercriticalMediumN, hv] using S.x_mem hk
    exact hx.2.1
  · have hwSparse : w.vertex ∈ D.sparse := w.location.resolve_left hv
    intro hxv
    exact (Finset.disjoint_left.mp (D.part_disjoint_sparse w.part))
      (S.x_mem_part hk) (hxv ▸ hwSparse)

theorem z_ne_witness (S : SupercriticalMediumRawSelection hk w) :
    S.z hk ≠ w.vertex := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hz : S.z hk ∈ D.parts w.part ∧ G.Adj w.vertex (S.z hk) := by
      simpa [z, mediumComplementSet, supercriticalMediumZ, hv] using S.z_mem hk
    exact (G.ne_of_adj hz.2).symm
  · have hwSparse : w.vertex ∈ D.sparse := w.location.resolve_left hv
    intro hzv
    exact (Finset.disjoint_left.mp (D.part_disjoint_sparse w.part))
      (S.z_mem_part hk) (hzv ▸ hwSparse)

theorem y_ne_witness (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) : S.y hk r ≠ w.vertex := by
  change (S.2.2 r).1 ≠ w.vertex
  have hy := (S.2.2 r).2
  simp only [otherPartNonneighbors, supercriticalMediumOtherN,
    Finset.mem_filter] at hy
  exact hy.2.1

theorem x_ne_y (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) : S.x hk ≠ S.y hk r := by
  intro hxy
  have hparts : w.part = otherSupercriticalPartEquiv hk w.part r :=
    D.mem_part_unique (S.x_mem_part hk) (hxy ▸ S.y_mem_part hk r)
  exact (otherSupercriticalPartEquiv_ne hk w.part r) hparts.symm

theorem z_ne_y (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) : S.z hk ≠ S.y hk r := by
  intro hzy
  have hparts : w.part = otherSupercriticalPartEquiv hk w.part r :=
    D.mem_part_unique (S.z_mem_part hk) (hzy ▸ S.y_mem_part hk r)
  exact (otherSupercriticalPartEquiv_ne hk w.part r) hparts.symm

theorem y_injective (S : SupercriticalMediumRawSelection hk w) :
    Function.Injective (S.y hk) := by
  intro r t hrt
  have ht := S.y_mem_part hk t
  rw [← hrt] at ht
  apply (otherSupercriticalPartEquiv hk w.part).injective
  apply Subtype.ext
  exact D.mem_part_unique (S.y_mem_part hk r) ht

theorem distinguishedTriple_injective
    (S : SupercriticalMediumRawSelection hk w) :
    Function.Injective
      (fun j : Fin 3 ↦ ![S.center hk, w.vertex, S.companion hk] j) := by
  classical
  intro a b
  have hxz := S.x_ne_z hk
  have hzx := hxz.symm
  have hxv := S.x_ne_witness hk
  have hvx := hxv.symm
  have hzv := S.z_ne_witness hk
  have hvz := hzv.symm
  by_cases hv : w.vertex ∈ D.parts w.part
  · fin_cases a <;> fin_cases b <;>
      simp [center, companion, hv, hxz, hzx, hxv, hvx, hzv, hvz]
  · fin_cases a <;> fin_cases b <;>
      simp [center, companion, hv, hxz, hzx, hxv, hvx, hzv, hvz]

theorem distinguishedTriple_ne_y
    (S : SupercriticalMediumRawSelection hk w) (j : Fin 3)
    (r : Fin (k - 2)) :
    ![S.center hk, w.vertex, S.companion hk] j ≠ S.y hk r := by
  classical
  have hwY : w.vertex ≠ S.y hk r := (S.y_ne_witness hk r).symm
  by_cases hv : w.vertex ∈ D.parts w.part
  · fin_cases j <;>
      simp [center, companion, hv, S.x_ne_y hk, S.z_ne_y hk,
        hwY]
  · fin_cases j <;>
      simp [center, companion, hv, S.x_ne_y hk, S.z_ne_y hk,
        hwY]

theorem vertexMap_injective (S : SupercriticalMediumRawSelection hk w) :
    Function.Injective (S.vertexMap hk) := by
  unfold vertexMap
  exact (S.distinguishedTriple_injective hk).sumElim (S.y_injective hk)
    (S.distinguishedTriple_ne_y hk) |>.comp (mediumStarVertexEquiv hk).injective

/-- The only additional deterministic condition is the edge joining the
chosen center and companion inside the distinguished main part. -/
def IsValid (S : SupercriticalMediumRawSelection hk w) : Prop :=
  G.Adj (S.center hk) (S.companion hk)

theorem center_adj_witness (S : SupercriticalMediumRawSelection hk w) :
    G.Adj (S.center hk) w.vertex := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hz := S.z_mem hk
    change S.z hk ∈ supercriticalMediumZ w at hz
    rw [supercriticalMediumZ, if_pos hv] at hz
    have hadj := (Finset.mem_filter.mp hz).2
    rw [center, if_pos hv]
    exact (G.adj_comm _ _).mpr hadj
  · have hx := S.x_mem hk
    change S.x hk ∈ supercriticalMediumN w at hx
    rw [supercriticalMediumN, if_neg hv] at hx
    have hadj := (Finset.mem_filter.mp hx).2
    rw [center, if_neg hv]
    exact (G.adj_comm _ _).mpr hadj

theorem witness_not_adj_companion
    (S : SupercriticalMediumRawSelection hk w) :
    ¬G.Adj w.vertex (S.companion hk) := by
  classical
  by_cases hv : w.vertex ∈ D.parts w.part
  · have hx := S.x_mem hk
    change S.x hk ∈ supercriticalMediumN w at hx
    rw [supercriticalMediumN, if_pos hv] at hx
    have hnon := (Finset.mem_filter.mp hx).2.2
    simpa [companion, hv] using hnon
  · have hz := S.z_mem hk
    change S.z hk ∈ supercriticalMediumZ w at hz
    rw [supercriticalMediumZ, if_neg hv] at hz
    have hnon := (Finset.mem_filter.mp hz).2.2
    simpa [companion, hv] using hnon

theorem witness_not_adj_y (S : SupercriticalMediumRawSelection hk w)
    (r : Fin (k - 2)) : ¬G.Adj w.vertex (S.y hk r) := by
  change ¬G.Adj w.vertex (S.2.2 r).1
  have hy := (S.2.2 r).2
  simp only [otherPartNonneighbors, supercriticalMediumOtherN,
    Finset.mem_filter] at hy
  exact hy.2.2

/-- Bundle a valid raw selection as an exact potential-star candidate. -/
def toCandidate (S : SupercriticalMediumRawSelection hk w)
    (hvalid : S.IsValid hk) : SupercriticalMediumStarCandidate hk w where
  x := S.x hk
  z := S.z hk
  y := S.y hk
  x_mem := S.x_mem hk
  z_mem := S.z_mem hk
  y_mem := S.y_mem hk
  embedding := ⟨S.vertexMap hk, S.vertexMap_injective hk⟩
  embedding_center := by simp [center]
  embedding_witness := by simp
  embedding_companion := by simp [companion]
  embedding_other := by simp
  deterministic_center_witness := by simpa using S.center_adj_witness hk
  deterministic_center_companion := by simpa [IsValid] using hvalid
  deterministic_witness_companion := by
    simpa using S.witness_not_adj_companion hk
  deterministic_witness_other := by
    intro r
    simpa using S.witness_not_adj_y hk r

end SupercriticalMediumRawSelection

/-! ## Raw, deleted, and valid candidate finsets -/

def mediumRawSelectionFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (SupercriticalMediumRawSelection hk w) :=
  Finset.univ

def mediumDeletedSelectionFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (SupercriticalMediumRawSelection hk w) := by
  classical
  exact Finset.univ.filter fun S ↦
    ¬SupercriticalMediumRawSelection.IsValid hk S

def mediumValidSelectionFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (SupercriticalMediumRawSelection hk w) := by
  classical
  exact Finset.univ.filter fun S ↦
    SupercriticalMediumRawSelection.IsValid hk S

@[simp] theorem mem_mediumDeletedSelectionFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : SupercriticalMediumRawSelection hk w) :
    S ∈ mediumDeletedSelectionFinset hk w ↔
      ¬SupercriticalMediumRawSelection.IsValid hk S := by
  classical
  simp [mediumDeletedSelectionFinset]

@[simp] theorem mem_mediumValidSelectionFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : SupercriticalMediumRawSelection hk w) :
    S ∈ mediumValidSelectionFinset hk w ↔
      SupercriticalMediumRawSelection.IsValid hk S := by
  classical
  simp [mediumValidSelectionFinset]

def mediumValidSelectionToCandidate
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : {S // S ∈ mediumValidSelectionFinset hk w}) :
    SupercriticalMediumStarCandidate hk w :=
  SupercriticalMediumRawSelection.toCandidate hk S.1
    ((mem_mediumValidSelectionFinset hk w S.1).mp S.2)

theorem mediumValidSelectionToCandidate_injective
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Function.Injective (mediumValidSelectionToCandidate hk w) := by
  intro S T hST
  apply Subtype.ext
  have hx : S.1.1.1 = T.1.1.1 := by
    simpa [mediumValidSelectionToCandidate,
      SupercriticalMediumRawSelection.toCandidate,
      SupercriticalMediumRawSelection.x] using
      congrArg SupercriticalMediumStarCandidate.x hST
  have hz : S.1.2.1.1 = T.1.2.1.1 := by
    simpa [mediumValidSelectionToCandidate,
      SupercriticalMediumRawSelection.toCandidate,
      SupercriticalMediumRawSelection.z] using
      congrArg SupercriticalMediumStarCandidate.z hST
  have hy : SupercriticalMediumRawSelection.y hk S.1 =
      SupercriticalMediumRawSelection.y hk T.1 := by
    simpa [mediumValidSelectionToCandidate,
      SupercriticalMediumRawSelection.toCandidate] using
      congrArg SupercriticalMediumStarCandidate.y hST
  apply Prod.ext
  · exact Subtype.ext hx
  · apply Prod.ext
    · exact Subtype.ext hz
    · funext r
      exact Subtype.ext (congrFun hy r)

def mediumValidSelectionToCandidateEmbedding
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    {S // S ∈ mediumValidSelectionFinset hk w} ↪
      SupercriticalMediumStarCandidate hk w :=
  ⟨mediumValidSelectionToCandidate hk w,
    mediumValidSelectionToCandidate_injective hk w⟩

/-- The concrete finite candidate family obtained after deletion. -/
def mediumStarCandidateFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Finset (SupercriticalMediumStarCandidate hk w) :=
  (mediumValidSelectionFinset hk w).attach.map
    (mediumValidSelectionToCandidateEmbedding hk w)

theorem mediumStarCandidateFinset_card
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumStarCandidateFinset hk w).card =
      (mediumValidSelectionFinset hk w).card := by
  simp [mediumStarCandidateFinset]

theorem mediumRawSelectionFinset_card
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumRawSelectionFinset hk w).card =
      (mediumNeighborSet w).card * (mediumComplementSet w).card *
        ∏ r : Fin (k - 2),
          (otherPartNonneighbors w
            (otherSupercriticalPartEquiv hk w.part r)).card := by
  classical
  simp [mediumRawSelectionFinset, SupercriticalMediumRawSelection,
    Nat.mul_assoc]

theorem mediumValidSelectionFinset_eq_sdiff
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    mediumValidSelectionFinset hk w =
      mediumRawSelectionFinset hk w \ mediumDeletedSelectionFinset hk w := by
  classical
  ext S
  simp [mediumRawSelectionFinset]

theorem mediumValidSelectionFinset_card_eq_raw_sub_deleted
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumValidSelectionFinset hk w).card =
      (mediumRawSelectionFinset hk w).card -
        (mediumDeletedSelectionFinset hk w).card := by
  rw [mediumValidSelectionFinset_eq_sdiff]
  exact Finset.card_sdiff_of_subset (by
    intro S _
    simp [mediumRawSelectionFinset])

theorem SupercriticalMediumRawSelection.ext
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    {S T : SupercriticalMediumRawSelection hk w}
    (hx : S.x hk = T.x hk) (hz : S.z hk = T.z hk)
    (hy : S.y hk = T.y hk) : S = T := by
  apply Prod.ext
  · exact Subtype.ext hx
  · apply Prod.ext
    · exact Subtype.ext hz
    · funext r
      exact Subtype.ext (congrFun hy r)

/-- The missing distinguished-part edge to which a deleted raw selection is
charged. -/
def mediumDeletedSelectionEdge
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (S : {S // S ∈ mediumDeletedSelectionFinset hk w}) :
    {p : Fin n × Fin n //
      p ∈ Gᶜ.interedges (D.parts w.part) (D.parts w.part)} := by
  classical
  let R := S.1
  have hbad : ¬SupercriticalMediumRawSelection.IsValid hk R :=
    (mem_mediumDeletedSelectionFinset hk w R).mp S.2
  have hnon : ¬G.Adj (R.x hk) (R.z hk) := by
    by_cases hv : w.vertex ∈ D.parts w.part
    · intro h
      apply hbad
      rw [SupercriticalMediumRawSelection.IsValid,
        SupercriticalMediumRawSelection.center,
        SupercriticalMediumRawSelection.companion, if_pos hv, if_pos hv]
      exact (G.adj_comm _ _).mpr h
    · simpa [SupercriticalMediumRawSelection.IsValid,
        SupercriticalMediumRawSelection.center,
        SupercriticalMediumRawSelection.companion, hv] using hbad
  refine ⟨(R.x hk, R.z hk), ?_⟩
  rw [SimpleGraph.mem_interedges_iff]
  refine ⟨R.x_mem_part hk, R.z_mem_part hk, ?_⟩
  simp [R.x_ne_z hk, hnon]

/-- A deleted selection is encoded by its charged ordered defect edge and
the remaining `k-2` selected vertices. -/
def mediumDeletedSelectionEncoding
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    {S // S ∈ mediumDeletedSelectionFinset hk w} →
      ({p : Fin n × Fin n //
        p ∈ Gᶜ.interedges (D.parts w.part) (D.parts w.part)} ×
        (Fin (k - 2) → Fin n)) :=
  fun S ↦ (mediumDeletedSelectionEdge hk w S, S.1.y hk)

theorem mediumDeletedSelectionEncoding_injective
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Function.Injective (mediumDeletedSelectionEncoding hk w) := by
  intro S T hST
  apply Subtype.ext
  have hedge := congrArg Prod.fst hST
  have hp := congrArg Subtype.val hedge
  have hx : S.1.x hk = T.1.x hk := congrArg Prod.fst hp
  have hz : S.1.z hk = T.1.z hk := congrArg Prod.snd hp
  have hy : S.1.y hk = T.1.y hk := congrArg Prod.snd hST
  exact SupercriticalMediumRawSelection.ext hk hx hz hy

/-- Every bad raw choice is charged to one ordered same-part defect edge;
after that edge is fixed there are at most `n^(k-2)` choices left. -/
theorem mediumDeletedSelectionFinset_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumDeletedSelectionFinset hk w).card ≤
      (Gᶜ.interedges (D.parts w.part) (D.parts w.part)).card *
        n ^ (k - 2) := by
  classical
  have hcard := Fintype.card_le_of_injective
    (mediumDeletedSelectionEncoding hk w)
    (mediumDeletedSelectionEncoding_injective hk w)
  rw [Fintype.card_coe, Fintype.card_prod, Fintype.card_coe,
    Fintype.card_fun] at hcard
  simpa using hcard

/-- The ordered same-part defect cell used in the deletion charge is at most
twice the total (unordered) combined-defect cost. -/
theorem mediumSamePartOrderedDefect_card_le_two_mul_cost
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (Gᶜ.interedges (D.parts w.part) (D.parts w.part)).card ≤
      2 * supercriticalDefectCost G D := by
  classical
  have hcell :
      (Gᶜ.interedges (D.parts w.part) (D.parts w.part)).card ≤
        ∑ i : Fin (k - 1),
          (Gᶜ.interedges (D.parts i) (D.parts i)).card := by
    exact Finset.single_le_sum
      (f := fun i : Fin (k - 1) ↦
        (Gᶜ.interedges (D.parts i) (D.parts i)).card)
      (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ w.part)
  have hcost := supercriticalDefectCost_eq_shift_components G D
  have hsupport :
      inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.support ≤
        supercriticalDefectCost G D := by
    omega
  calc
    (Gᶜ.interedges (D.parts w.part) (D.parts w.part)).card ≤
        ∑ i : Fin (k - 1),
          (Gᶜ.interedges (D.parts i) (D.parts i)).card := hcell
    _ = 2 * inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.support :=
      (two_mul_inducedEdgeCount_combined_support G D).symm
    _ ≤ 2 * supercriticalDefectCost G D := Nat.mul_le_mul_left 2 hsupport

theorem mediumDeletedSelectionFinset_card_le_cost
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumDeletedSelectionFinset hk w).card ≤
      2 * supercriticalDefectCost G D * n ^ (k - 2) := by
  exact (mediumDeletedSelectionFinset_card_le hk w).trans
    (Nat.mul_le_mul_right (n ^ (k - 2))
      (mediumSamePartOrderedDefect_card_le_two_mul_cost hk w))

/-- Exact raw-minus-deleted lower bound, before inserting analytic lower
bounds for `N`, `Z`, the `N_j`, and the defect budget. -/
theorem mediumStarCandidate_card_lower_raw
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumRawSelectionFinset hk w).card -
        (mediumDeletedSelectionFinset hk w).card ≤
      (mediumStarCandidateFinset hk w).card := by
  rw [mediumStarCandidateFinset_card,
    mediumValidSelectionFinset_card_eq_raw_sub_deleted]

/-- Concrete candidate-count lower bound: the exact raw product minus the
explicit defect-edge deletion budget.  Subsequent analytic bookkeeping only
has to insert the already-proved lower bounds on `N`, `Z`, and every `N_j`. -/
theorem mediumStarCandidate_card_lower
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    (mediumNeighborSet w).card * (mediumComplementSet w).card *
          (∏ r : Fin (k - 2),
            (otherPartNonneighbors w
              (otherSupercriticalPartEquiv hk w.part r)).card) -
        (2 * supercriticalDefectCost G D * n ^ (k - 2)) ≤
      (mediumStarCandidateFinset hk w).card := by
  have hdeleted := mediumDeletedSelectionFinset_card_le_cost hk w
  have hsub :
      (mediumRawSelectionFinset hk w).card -
          (2 * supercriticalDefectCost G D * n ^ (k - 2)) ≤
        (mediumRawSelectionFinset hk w).card -
          (mediumDeletedSelectionFinset hk w).card :=
    Nat.sub_le_sub_left hdeleted _
  rw [mediumRawSelectionFinset_card] at hsub
  have hraw := mediumStarCandidate_card_lower_raw hk w
  rw [mediumRawSelectionFinset_card] at hraw
  exact hsub.trans hraw

/-- A convenient uniform-cardinality specialization of the concrete lower
bound. -/
theorem mediumStarCandidate_card_lower_of_uniform
    {k n A B C : ℕ} (hk : 3 ≤ k)
    {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (hN : A ≤ (mediumNeighborSet w).card)
    (hZ : B ≤ (mediumComplementSet w).card)
    (hNj : ∀ r : Fin (k - 2), C ≤
      (otherPartNonneighbors w
        (otherSupercriticalPartEquiv hk w.part r)).card) :
    A * B * C ^ (k - 2) -
        (2 * supercriticalDefectCost G D * n ^ (k - 2)) ≤
      (mediumStarCandidateFinset hk w).card := by
  have hprod : C ^ (k - 2) ≤
      ∏ r : Fin (k - 2),
          (otherPartNonneighbors w
            (otherSupercriticalPartEquiv hk w.part r)).card := by
    have h := Finset.prod_le_prod
      (s := (Finset.univ : Finset (Fin (k - 2))))
      (f := fun _r ↦ C)
      (g := fun r ↦ (otherPartNonneighbors w
        (otherSupercriticalPartEquiv hk w.part r)).card)
      (fun _r _ ↦ Nat.zero_le _)
      (fun r _ ↦ hNj r)
    simpa using h
  have hraw : A * B * C ^ (k - 2) ≤
      (mediumNeighborSet w).card * (mediumComplementSet w).card *
        ∏ r : Fin (k - 2),
          (otherPartNonneighbors w
            (otherSupercriticalPartEquiv hk w.part r)).card := by
    exact Nat.mul_le_mul (Nat.mul_le_mul hN hZ) hprod
  exact (Nat.sub_le_sub_right hraw _).trans
    (mediumStarCandidate_card_lower hk w)

/-! ## Candidate encodings for overlap counting -/

/-- The `k` variable vertices of a candidate are `x`, `z`, and the `k-2`
other-part vertices; the witness itself is fixed. -/
def mediumCandidateVariableEquiv {k : ℕ} (hk : 3 ≤ k) :
    Fin k ≃ Fin 2 ⊕ Fin (k - 2) :=
  (finCongr (by omega : k = 2 + (k - 2))).trans finSumFinEquiv.symm

def mediumVariableXIndex {k : ℕ} (hk : 3 ≤ k) : Fin k :=
  (mediumCandidateVariableEquiv hk).symm (Sum.inl 0)

def mediumVariableZIndex {k : ℕ} (hk : 3 ≤ k) : Fin k :=
  (mediumCandidateVariableEquiv hk).symm (Sum.inl 1)

def mediumVariableOtherIndex {k : ℕ} (hk : 3 ≤ k)
    (r : Fin (k - 2)) : Fin k :=
  (mediumCandidateVariableEquiv hk).symm (Sum.inr r)

@[simp] theorem mediumCandidateVariableEquiv_x {k : ℕ} (hk : 3 ≤ k) :
    mediumCandidateVariableEquiv hk (mediumVariableXIndex hk) = Sum.inl 0 := by
  simp [mediumVariableXIndex]

@[simp] theorem mediumCandidateVariableEquiv_z {k : ℕ} (hk : 3 ≤ k) :
    mediumCandidateVariableEquiv hk (mediumVariableZIndex hk) = Sum.inl 1 := by
  simp [mediumVariableZIndex]

@[simp] theorem mediumCandidateVariableEquiv_other {k : ℕ} (hk : 3 ≤ k)
    (r : Fin (k - 2)) :
    mediumCandidateVariableEquiv hk (mediumVariableOtherIndex hk r) =
      Sum.inr r := by
  simp [mediumVariableOtherIndex]

theorem mediumVariableXIndex_ne_ZIndex {k : ℕ} (hk : 3 ≤ k) :
    mediumVariableXIndex hk ≠ mediumVariableZIndex hk := by
  intro h
  have := congrArg (mediumCandidateVariableEquiv hk) h
  simpa [mediumVariableXIndex, mediumVariableZIndex] using this

theorem mediumVariableXIndex_ne_other {k : ℕ} (hk : 3 ≤ k)
    (r : Fin (k - 2)) :
    mediumVariableXIndex hk ≠ mediumVariableOtherIndex hk r := by
  intro h
  have := congrArg (mediumCandidateVariableEquiv hk) h
  simpa [mediumVariableXIndex, mediumVariableOtherIndex] using this

theorem mediumVariableZIndex_ne_other {k : ℕ} (hk : 3 ≤ k)
    (r : Fin (k - 2)) :
    mediumVariableZIndex hk ≠ mediumVariableOtherIndex hk r := by
  intro h
  have := congrArg (mediumCandidateVariableEquiv hk) h
  simpa [mediumVariableZIndex, mediumVariableOtherIndex] using this

theorem mediumVariableOtherIndex_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (mediumVariableOtherIndex hk) := by
  intro r s h
  have := congrArg (mediumCandidateVariableEquiv hk) h
  simpa [mediumVariableOtherIndex] using this

/-- Encode a candidate by its `k` freely selected vertices. -/
def mediumCandidateChoiceVector
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) : Fin k → Fin n :=
  Sum.elim (fun j : Fin 2 ↦ ![K.x, K.z] j) K.y ∘
    mediumCandidateVariableEquiv hk

@[simp] theorem mediumCandidateChoiceVector_x
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    mediumCandidateChoiceVector hk K (mediumVariableXIndex hk) = K.x := by
  simp [mediumCandidateChoiceVector, mediumVariableXIndex]

@[simp] theorem mediumCandidateChoiceVector_z
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) :
    mediumCandidateChoiceVector hk K (mediumVariableZIndex hk) = K.z := by
  simp [mediumCandidateChoiceVector, mediumVariableZIndex]

@[simp] theorem mediumCandidateChoiceVector_other
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w) (r : Fin (k - 2)) :
    mediumCandidateChoiceVector hk K (mediumVariableOtherIndex hk r) = K.y r := by
  simp [mediumCandidateChoiceVector, mediumVariableOtherIndex]

theorem mediumCandidateChoiceVector_injective
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    Function.Injective
      (mediumCandidateChoiceVector hk :
        SupercriticalMediumStarCandidate hk w → (Fin k → Fin n)) := by
  intro K L hKL
  have hx : K.x = L.x := by
    simpa using congrFun hKL (mediumVariableXIndex hk)
  have hz : K.z = L.z := by
    simpa using congrFun hKL (mediumVariableZIndex hk)
  have hy : K.y = L.y := by
    funext r
    simpa using congrFun hKL (mediumVariableOtherIndex hk r)
  have hemb : K.embedding = L.embedding := by
    apply Function.Embedding.ext
    intro a
    rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩
    · subst a
      rw [K.embedding_center, L.embedding_center, hx, hz]
    · subst a
      rw [K.embedding_witness, L.embedding_witness]
    · subst a
      rw [K.embedding_companion, L.embedding_companion, hx, hz]
    · subst a
      rw [K.embedding_other, L.embedding_other, hy]
  cases K
  cases L
  simp_all

/-- There are at most `n^k` medium candidates, by their `k` freely selected
vertices. -/
theorem mediumStarCandidateFinset_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    (mediumStarCandidateFinset hk w).card ≤ n ^ k := by
  classical
  calc
    (mediumStarCandidateFinset hk w).card ≤
        (Finset.univ : Finset (Fin k → Fin n)).card :=
      Finset.card_le_card_of_injOn
        (mediumCandidateChoiceVector hk)
        (fun _ _ ↦ Finset.mem_univ _)
        (mediumCandidateChoiceVector_injective hk).injOn
    _ = n ^ k := by simp [Fintype.card_fun]

def mediumRandomRoleVariablePair
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    SupercriticalMediumRandomRole k → Sym2 (Fin k)
  | Sum.inl r =>
      s((if w.vertex ∈ D.parts w.part then mediumVariableZIndex hk
        else mediumVariableXIndex hk), mediumVariableOtherIndex hk r)
  | Sum.inr (Sum.inl r) =>
      s((if w.vertex ∈ D.parts w.part then mediumVariableXIndex hk
        else mediumVariableZIndex hk), mediumVariableOtherIndex hk r)
  | Sum.inr (Sum.inr p) =>
      s(mediumVariableOtherIndex hk p.1.1,
        mediumVariableOtherIndex hk p.1.2)

theorem mediumRandomRoleVariablePair_not_isDiag
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (r : SupercriticalMediumRandomRole k) :
    ¬(mediumRandomRoleVariablePair hk w r).IsDiag := by
  rcases r with r | r
  · by_cases hv : w.vertex ∈ D.parts w.part <;>
      simp [mediumRandomRoleVariablePair, hv, Sym2.mk_isDiag_iff,
        mediumVariableZIndex_ne_other hk r,
        mediumVariableXIndex_ne_other hk r]
  · rcases r with r | p
    · by_cases hv : w.vertex ∈ D.parts w.part <;>
        simp [mediumRandomRoleVariablePair, hv, Sym2.mk_isDiag_iff,
          mediumVariableZIndex_ne_other hk r,
          mediumVariableXIndex_ne_other hk r]
    · simp [mediumRandomRoleVariablePair, Sym2.mk_isDiag_iff,
        (mediumVariableOtherIndex_injective hk).ne (ne_of_lt p.2)]

/-- The two ordered variable positions used by a random role.  The random
coordinate itself forgets this order; retaining it here lets us count a
coordinate fiber by fixing two entries of the candidate choice vector. -/
def mediumRandomRoleVariableEndpoints
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    SupercriticalMediumRandomRole k → Fin k × Fin k
  | Sum.inl r =>
      (if w.vertex ∈ D.parts w.part then mediumVariableZIndex hk
        else mediumVariableXIndex hk,
       mediumVariableOtherIndex hk r)
  | Sum.inr (Sum.inl r) =>
      (if w.vertex ∈ D.parts w.part then mediumVariableXIndex hk
        else mediumVariableZIndex hk,
       mediumVariableOtherIndex hk r)
  | Sum.inr (Sum.inr p) =>
      (mediumVariableOtherIndex hk p.1.1,
       mediumVariableOtherIndex hk p.1.2)

theorem mediumRandomRoleVariablePair_eq_endpoints
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleVariablePair hk w r =
      s((mediumRandomRoleVariableEndpoints hk w r).1,
        (mediumRandomRoleVariableEndpoints hk w r).2) := by
  rcases r with r | r
  · rfl
  · rcases r with r | p <;> rfl

theorem mediumRandomRoleVariableEndpoints_ne
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D)
    (r : SupercriticalMediumRandomRole k) :
    (mediumRandomRoleVariableEndpoints hk w r).1 ≠
      (mediumRandomRoleVariableEndpoints hk w r).2 := by
  have hdiag := mediumRandomRoleVariablePair_not_isDiag hk w r
  rw [mediumRandomRoleVariablePair_eq_endpoints hk w r,
    Sym2.mk_isDiag_iff] at hdiag
  exact hdiag

theorem mediumRandomRoleCoordinate_eq_choiceVector_map
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumStarCandidate hk w)
    (r : SupercriticalMediumRandomRole k) :
    mediumRandomRoleCoordinate hk K r =
      Sym2.map (mediumCandidateChoiceVector hk K)
        (mediumRandomRoleVariablePair hk w r) := by
  rcases r with r | r
  · by_cases hv : w.vertex ∈ D.parts w.part
    · simp [mediumRandomRoleCoordinate, mediumRandomRoleVariablePair, hv,
        mediumCandidateChoiceVector, K.embedding_center, K.embedding_other]
    · simp [mediumRandomRoleCoordinate, mediumRandomRoleVariablePair, hv,
        mediumCandidateChoiceVector, K.embedding_center, K.embedding_other]
  · rcases r with r | p
    · by_cases hv : w.vertex ∈ D.parts w.part
      · simp [mediumRandomRoleCoordinate, mediumRandomRoleVariablePair, hv,
          mediumCandidateChoiceVector, K.embedding_companion, K.embedding_other]
      · simp [mediumRandomRoleCoordinate, mediumRandomRoleVariablePair, hv,
          mediumCandidateChoiceVector, K.embedding_companion, K.embedding_other]
    · simp [mediumRandomRoleCoordinate, mediumRandomRoleVariablePair,
        mediumCandidateChoiceVector, K.embedding_other]

/-! ### Two-coordinate fibers of the full function space -/

def twoFixedFunctionFinset {k n : ℕ}
    (a b : Fin k) (u v : Fin n) : Finset (Fin k → Fin n) := by
  classical
  exact Finset.univ.filter fun f ↦ f a = u ∧ f b = v

@[simp] theorem mem_twoFixedFunctionFinset {k n : ℕ}
    (a b : Fin k) (u v : Fin n) (f : Fin k → Fin n) :
    f ∈ twoFixedFunctionFinset a b u v ↔ f a = u ∧ f b = v := by
  classical
  simp [twoFixedFunctionFinset]

def twoFixedFunctionRestriction {k n : ℕ}
    (a b : Fin k) (u v : Fin n) :
    {f // f ∈ twoFixedFunctionFinset a b u v} →
      ({i : Fin k // i ≠ a ∧ i ≠ b} → Fin n) :=
  fun f i ↦ f.1 i.1

theorem twoFixedFunctionRestriction_injective {k n : ℕ}
    (a b : Fin k) (u v : Fin n) :
    Function.Injective (twoFixedFunctionRestriction a b u v) := by
  intro f g hfg
  apply Subtype.ext
  funext i
  have hf := (mem_twoFixedFunctionFinset a b u v f.1).mp f.2
  have hg := (mem_twoFixedFunctionFinset a b u v g.1).mp g.2
  by_cases hia : i = a
  · subst i
    exact hf.1.trans hg.1.symm
  by_cases hib : i = b
  · subst i
    exact hf.2.trans hg.2.symm
  exact congrFun hfg ⟨i, hia, hib⟩

theorem card_fin_subtype_ne_two {k : ℕ} (a b : Fin k) (hab : a ≠ b) :
    Fintype.card {i : Fin k // i ≠ a ∧ i ≠ b} = k - 2 := by
  classical
  rw [Fintype.card_subtype]
  have heq : (Finset.univ.filter fun i : Fin k ↦ i ≠ a ∧ i ≠ b) =
      (Finset.univ.erase a).erase b := by
    ext i
    simp [and_comm]
  rw [heq, Finset.card_erase_of_mem (by simp [hab.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ a)]
  simp
  omega

theorem twoFixedFunctionFinset_card_le {k n : ℕ}
    (a b : Fin k) (u v : Fin n) (hab : a ≠ b) :
    (twoFixedFunctionFinset a b u v).card ≤ n ^ (k - 2) := by
  classical
  have h := Fintype.card_le_of_injective
    (twoFixedFunctionRestriction a b u v)
    (twoFixedFunctionRestriction_injective a b u v)
  rw [Fintype.card_coe, Fintype.card_fun,
    card_fin_subtype_ne_two a b hab] at h
  simpa using h

def unorderedPairFunctionFinset {k n : ℕ}
    (a b : Fin k) (u v : Fin n) : Finset (Fin k → Fin n) := by
  classical
  exact Finset.univ.filter fun f ↦ s(f a, f b) = s(u, v)

@[simp] theorem mem_unorderedPairFunctionFinset {k n : ℕ}
    (a b : Fin k) (u v : Fin n) (f : Fin k → Fin n) :
    f ∈ unorderedPairFunctionFinset a b u v ↔
      s(f a, f b) = s(u, v) := by
  classical
  simp [unorderedPairFunctionFinset]

theorem unorderedPairFunctionFinset_eq_union {k n : ℕ}
    (a b : Fin k) (u v : Fin n) :
    unorderedPairFunctionFinset a b u v =
      twoFixedFunctionFinset a b u v ∪ twoFixedFunctionFinset a b v u := by
  classical
  ext f
  simp [Sym2.eq_iff]

theorem unorderedPairFunctionFinset_card_le {k n : ℕ}
    (a b : Fin k) (u v : Fin n) (hab : a ≠ b) :
    (unorderedPairFunctionFinset a b u v).card ≤ 2 * n ^ (k - 2) := by
  rw [unorderedPairFunctionFinset_eq_union]
  calc
    (twoFixedFunctionFinset a b u v ∪
        twoFixedFunctionFinset a b v u).card ≤
      (twoFixedFunctionFinset a b u v).card +
        (twoFixedFunctionFinset a b v u).card :=
      Finset.card_union_le _ _
    _ ≤ n ^ (k - 2) + n ^ (k - 2) :=
      Nat.add_le_add (twoFixedFunctionFinset_card_le a b u v hab)
        (twoFixedFunctionFinset_card_le a b v u hab)
    _ = 2 * n ^ (k - 2) := by omega

/-- A generous explicit bound for the number of random roles in one
potential star. -/
theorem mediumRandomRole_card_le {k : ℕ} :
    Fintype.card (SupercriticalMediumRandomRole k) ≤
      2 * (k - 2) + (k - 2) ^ 2 := by
  simp only [SupercriticalMediumRandomRole, Fintype.card_sum,
    Fintype.card_fin]
  have hpairs : Fintype.card
      {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
      Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_prod, Fintype.card_fin] at hpairs ⊢
  have h := Nat.add_le_add_left
    (Nat.add_le_add_left hpairs (k - 2)) (k - 2)
  simpa [pow_two, two_mul, Nat.add_assoc] using h

/-! ### Concrete overlap enumeration for medium-star candidates -/

/-- Candidates surviving the deterministic deletion, as a finite index type
for the Janson family. -/
abbrev SupercriticalMediumCandidateIndex
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :=
  {K : SupercriticalMediumStarCandidate hk w //
    K ∈ mediumStarCandidateFinset hk w}

/-- A canonical finite order on the concrete candidate index.  Janson's
unordered-pair convention needs an order only to choose one orientation. -/
noncomputable instance supercriticalMediumCandidateIndexLinearOrder
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    LinearOrder (SupercriticalMediumCandidateIndex hk w) :=
  LinearOrder.lift' (Fintype.equivFin _)
    (Fintype.equivFin _).injective

@[simp] theorem card_supercriticalMediumCandidateIndex
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    (w : SupercriticalMediumWitness G α D) :
    Fintype.card (SupercriticalMediumCandidateIndex hk w) =
      (mediumStarCandidateFinset hk w).card := by
  simp [SupercriticalMediumCandidateIndex]

/-- For a fixed candidate and a fixed pair of roles, the candidates whose
second role occupies the fixed candidate's first-role coordinate. -/
def mediumRoleOverlapCandidateFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w)
    (r s : SupercriticalMediumRandomRole k) :
    Finset (SupercriticalMediumCandidateIndex hk w) := by
  classical
  exact Finset.univ.filter fun L ↦
    mediumRandomRoleCoordinate hk L.1 s =
      mediumRandomRoleCoordinate hk K.1 r

@[simp] theorem mem_mediumRoleOverlapCandidateFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K L : SupercriticalMediumCandidateIndex hk w)
    (r s : SupercriticalMediumRandomRole k) :
    L ∈ mediumRoleOverlapCandidateFinset hk K r s ↔
      mediumRandomRoleCoordinate hk L.1 s =
        mediumRandomRoleCoordinate hk K.1 r := by
  classical
  simp [mediumRoleOverlapCandidateFinset]

/-- Fixing an ambient coordinate and a role leaves at most two orientations
of the remaining `k-2` free candidate choices. -/
theorem mediumRoleOverlapCandidateFinset_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w)
    (r s : SupercriticalMediumRandomRole k) :
    (mediumRoleOverlapCandidateFinset hk K r s).card ≤
      2 * n ^ (k - 2) := by
  classical
  let a := (mediumRandomRoleVariableEndpoints hk w s).1
  let b := (mediumRandomRoleVariableEndpoints hk w s).2
  let u := mediumCandidateChoiceVector hk K.1
      (mediumRandomRoleVariableEndpoints hk w r).1
  let v := mediumCandidateChoiceVector hk K.1
      (mediumRandomRoleVariableEndpoints hk w r).2
  have hmem : ∀ L ∈ mediumRoleOverlapCandidateFinset hk K r s,
      mediumCandidateChoiceVector hk L.1 ∈
        unorderedPairFunctionFinset a b u v := by
    intro L hL
    have hcoord := (mem_mediumRoleOverlapCandidateFinset hk K L r s).mp hL
    rw [mediumRandomRoleCoordinate_eq_choiceVector_map hk L.1 s,
      mediumRandomRoleCoordinate_eq_choiceVector_map hk K.1 r,
      mediumRandomRoleVariablePair_eq_endpoints hk w s,
      mediumRandomRoleVariablePair_eq_endpoints hk w r] at hcoord
    simpa [a, b, u, v] using hcoord
  have hinj : Set.InjOn
      (fun L : SupercriticalMediumCandidateIndex hk w ↦
        mediumCandidateChoiceVector hk L.1)
      (mediumRoleOverlapCandidateFinset hk K r s :
        Set (SupercriticalMediumCandidateIndex hk w)) := by
    intro L _ M _ hLM
    apply Subtype.ext
    exact mediumCandidateChoiceVector_injective hk hLM
  calc
    (mediumRoleOverlapCandidateFinset hk K r s).card ≤
        (unorderedPairFunctionFinset a b u v).card :=
      Finset.card_le_card_of_injOn
        (fun L : SupercriticalMediumCandidateIndex hk w ↦
          mediumCandidateChoiceVector hk L.1) hmem hinj
    _ ≤ 2 * n ^ (k - 2) :=
      unorderedPairFunctionFinset_card_le a b u v
        (mediumRandomRoleVariableEndpoints_ne hk w s)

/-- The candidates sharing at least one required random coordinate with a
fixed candidate. -/
def mediumOverlappingCandidateFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w) :
    Finset (SupercriticalMediumCandidateIndex hk w) := by
  classical
  exact Finset.univ.filter fun L ↦
    ¬Disjoint (requiredSuccessCoordinates hk K.1)
      (requiredSuccessCoordinates hk L.1)

@[simp] theorem mem_mediumOverlappingCandidateFinset
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K L : SupercriticalMediumCandidateIndex hk w) :
    L ∈ mediumOverlappingCandidateFinset hk K ↔
      ¬Disjoint (requiredSuccessCoordinates hk K.1)
        (requiredSuccessCoordinates hk L.1) := by
  classical
  simp [mediumOverlappingCandidateFinset]

/-- The explicit union over the two roles witnessing a shared coordinate. -/
def mediumRoleOverlapUnion
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w) :
    Finset (SupercriticalMediumCandidateIndex hk w) := by
  classical
  exact Finset.univ.biUnion fun r ↦
    Finset.univ.biUnion fun s ↦ mediumRoleOverlapCandidateFinset hk K r s

theorem mediumOverlappingCandidateFinset_subset_roleUnion
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w) :
    mediumOverlappingCandidateFinset hk K ⊆ mediumRoleOverlapUnion hk K := by
  classical
  intro L hL
  have hoverlap := (mem_mediumOverlappingCandidateFinset hk K L).mp hL
  obtain ⟨e, heK, heL⟩ := Finset.not_disjoint_iff.mp hoverlap
  rw [requiredSuccessCoordinates, Finset.mem_image] at heK heL
  obtain ⟨r, -, hr⟩ := heK
  obtain ⟨s, -, hs⟩ := heL
  rw [mediumRoleOverlapUnion, Finset.mem_biUnion]
  refine ⟨r, Finset.mem_univ r, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_univ s, ?_⟩
  rw [mem_mediumRoleOverlapCandidateFinset]
  exact hs.trans hr.symm

/-- Concrete dependency-degree bound: a fixed candidate overlaps at most a
constant (depending only on `k`) times `n^(k-2)` candidates. -/
theorem mediumOverlappingCandidateFinset_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w) :
    (mediumOverlappingCandidateFinset hk K).card ≤
      Fintype.card (SupercriticalMediumRandomRole k) *
        (Fintype.card (SupercriticalMediumRandomRole k) *
          (2 * n ^ (k - 2))) := by
  classical
  calc
    (mediumOverlappingCandidateFinset hk K).card ≤
        (mediumRoleOverlapUnion hk K).card :=
      Finset.card_le_card
        (mediumOverlappingCandidateFinset_subset_roleUnion hk K)
    _ ≤ ∑ r : SupercriticalMediumRandomRole k,
          (Finset.univ.biUnion fun s : SupercriticalMediumRandomRole k ↦
            mediumRoleOverlapCandidateFinset hk K r s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ r : SupercriticalMediumRandomRole k,
          ∑ s : SupercriticalMediumRandomRole k,
            (mediumRoleOverlapCandidateFinset hk K r s).card := by
      exact Finset.sum_le_sum fun r _ ↦ Finset.card_biUnion_le
    _ ≤ ∑ _r : SupercriticalMediumRandomRole k,
          ∑ _s : SupercriticalMediumRandomRole k,
            2 * n ^ (k - 2) := by
      exact Finset.sum_le_sum fun r _ ↦
        Finset.sum_le_sum fun s _ ↦
          mediumRoleOverlapCandidateFinset_card_le hk K r s
    _ = Fintype.card (SupercriticalMediumRandomRole k) *
          (Fintype.card (SupercriticalMediumRandomRole k) *
            (2 * n ^ (k - 2))) := by simp

/-- Dependency degree with a closed-form role-count coefficient. -/
theorem mediumOverlappingCandidateFinset_card_le_explicit
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (K : SupercriticalMediumCandidateIndex hk w) :
    (mediumOverlappingCandidateFinset hk K).card ≤
      2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 * n ^ (k - 2) := by
  calc
    (mediumOverlappingCandidateFinset hk K).card ≤
        Fintype.card (SupercriticalMediumRandomRole k) *
          (Fintype.card (SupercriticalMediumRandomRole k) *
            (2 * n ^ (k - 2))) :=
      mediumOverlappingCandidateFinset_card_le hk K
    _ ≤ (2 * (k - 2) + (k - 2) ^ 2) *
          ((2 * (k - 2) + (k - 2) ^ 2) *
            (2 * n ^ (k - 2))) := by
      gcongr <;> exact mediumRandomRole_card_le
    _ = 2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 *
          n ^ (k - 2) := by ring

/-- Ordered candidate pairs obtained by choosing a first candidate and one
of the candidates sharing a required coordinate with it. -/
def mediumOrderedOverlapUnion
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    Finset (SupercriticalMediumCandidateIndex hk w ×
      SupercriticalMediumCandidateIndex hk w) := by
  classical
  exact Finset.univ.biUnion fun K ↦
    (mediumOverlappingCandidateFinset hk K).map
      ⟨fun L ↦ (K, L), fun _ _ h ↦ Prod.mk.inj h |>.2⟩

/-- Every unordered overlapping pair in the Janson sum occurs in the
ordered overlap union (the latter intentionally also permits the diagonal). -/
theorem mediumUnorderedOverlappingPairs_subset_orderedUnion
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1) ⊆
      mediumOrderedOverlapUnion hk := by
  classical
  intro KL hKL
  have hoverlap :=
    (DenseGraph.FiniteBernoulliProduct.mem_unorderedOverlappingPairs
      (fun K : SupercriticalMediumCandidateIndex hk w ↦
        requiredSuccessCoordinates hk K.1) KL.1 KL.2).mp hKL
  rw [mediumOrderedOverlapUnion, Finset.mem_biUnion]
  refine ⟨KL.1, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_map]
  refine ⟨KL.2, ?_, rfl⟩
  exact (mem_mediumOverlappingCandidateFinset hk KL.1 KL.2).mpr hoverlap.2

/-- Concrete unordered dependency-pair bound before collecting the powers
of `n`. -/
theorem mediumUnorderedOverlappingPairs_card_le_product
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      (fun K : SupercriticalMediumCandidateIndex hk w ↦
        requiredSuccessCoordinates hk K.1)).card ≤
      n ^ k *
        (Fintype.card (SupercriticalMediumRandomRole k) *
          (Fintype.card (SupercriticalMediumRandomRole k) *
            (2 * n ^ (k - 2)))) := by
  classical
  let B := Fintype.card (SupercriticalMediumRandomRole k) *
    (Fintype.card (SupercriticalMediumRandomRole k) *
      (2 * n ^ (k - 2)))
  calc
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1)).card ≤
        (mediumOrderedOverlapUnion hk).card :=
      Finset.card_le_card
        (mediumUnorderedOverlappingPairs_subset_orderedUnion hk)
    _ ≤ ∑ K : SupercriticalMediumCandidateIndex hk w,
          (mediumOverlappingCandidateFinset hk K).card := by
      calc
        (mediumOrderedOverlapUnion hk).card ≤
            ∑ K : SupercriticalMediumCandidateIndex hk w,
              ((mediumOverlappingCandidateFinset hk K).map
                ⟨fun L ↦ (K, L), fun _ _ h ↦ Prod.mk.inj h |>.2⟩).card := by
          unfold mediumOrderedOverlapUnion
          exact Finset.card_biUnion_le
        _ = ∑ K : SupercriticalMediumCandidateIndex hk w,
              (mediumOverlappingCandidateFinset hk K).card := by simp
    _ ≤ ∑ _K : SupercriticalMediumCandidateIndex hk w, B := by
      exact Finset.sum_le_sum fun K _ ↦
        mediumOverlappingCandidateFinset_card_le hk K
    _ = (mediumStarCandidateFinset hk w).card * B := by
      simp [SupercriticalMediumCandidateIndex]
    _ ≤ n ^ k * B :=
      Nat.mul_le_mul_right B (mediumStarCandidateFinset_card_le hk)
    _ = n ^ k *
        (Fintype.card (SupercriticalMediumRandomRole k) *
          (Fintype.card (SupercriticalMediumRandomRole k) *
            (2 * n ^ (k - 2)))) := rfl

/-- The explicit `O_k(n^(2k-2))` unordered dependency-pair estimate. -/
theorem mediumUnorderedOverlappingPairs_card_le
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      (fun K : SupercriticalMediumCandidateIndex hk w ↦
        requiredSuccessCoordinates hk K.1)).card ≤
      2 * (Fintype.card (SupercriticalMediumRandomRole k)) ^ 2 *
        n ^ (2 * k - 2) := by
  calc
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1)).card ≤
        n ^ k *
          (Fintype.card (SupercriticalMediumRandomRole k) *
            (Fintype.card (SupercriticalMediumRandomRole k) *
              (2 * n ^ (k - 2)))) :=
      mediumUnorderedOverlappingPairs_card_le_product hk
    _ = 2 * (Fintype.card (SupercriticalMediumRandomRole k)) ^ 2 *
          (n ^ k * n ^ (k - 2)) := by ring
    _ = 2 * (Fintype.card (SupercriticalMediumRandomRole k)) ^ 2 *
          n ^ (k + (k - 2)) := by rw [pow_add]
    _ = 2 * (Fintype.card (SupercriticalMediumRandomRole k)) ^ 2 *
          n ^ (2 * k - 2) := by congr 2 <;> omega

/-- The same `O_k(n^(2k-2))` estimate with a closed-form coefficient. -/
theorem mediumUnorderedOverlappingPairs_card_le_explicit
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D} :
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
      (fun K : SupercriticalMediumCandidateIndex hk w ↦
        requiredSuccessCoordinates hk K.1)).card ≤
      2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 *
        n ^ (2 * k - 2) := by
  calc
    (DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1)).card ≤
        2 * (Fintype.card (SupercriticalMediumRandomRole k)) ^ 2 *
          n ^ (2 * k - 2) :=
      mediumUnorderedOverlappingPairs_card_le hk
    _ ≤ 2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 *
          n ^ (2 * k - 2) := by
      gcongr
      exact mediumRandomRole_card_le

/-! ### Concrete expectation and dependency-sum adapters -/

/-- Candidate abundance and a uniform event probability give the concrete
Janson expectation bound for the selected medium-star family. -/
theorem mediumCandidateJansonMu_lower
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (P : DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n)))
    {c eventFloor : ℝ}
    (hevent0 : 0 ≤ eventFloor)
    (hevent : ∀ K : SupercriticalMediumCandidateIndex hk w,
      eventFloor ≤ P.eventProbability
        (DenseGraph.FiniteBernoulliProduct.principalSuccessEvent
          (requiredSuccessCoordinates hk K.1)))
    (hcard : c * (n : ℝ) ^ k ≤
      ((mediumStarCandidateFinset hk w).card : ℝ)) :
    c * eventFloor * (n : ℝ) ^ k ≤
      P.principalJansonMu
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1) := by
  apply mediumJansonMu_lower P
    (fun K : SupercriticalMediumCandidateIndex hk w ↦
      requiredSuccessCoordinates hk K.1) hevent0 hevent
  simpa using hcard

/-- The concrete candidate overlap enumeration supplies the Janson
dependency-sum estimate, using only the trivial intersection-probability
upper bound one. -/
theorem mediumCandidateJansonDelta_upper
    {k n : ℕ} (hk : 3 ≤ k) {G : SimpleGraph (Fin n)} {α : ℝ}
    {D : SupercriticalDivision k (Fin n)}
    {w : SupercriticalMediumWitness G α D}
    (P : DenseGraph.FiniteBernoulliProduct (Sym2 (Fin n))) :
    P.principalJansonDelta
        (fun K : SupercriticalMediumCandidateIndex hk w ↦
          requiredSuccessCoordinates hk K.1) ≤
      ((2 * (2 * (k - 2) + (k - 2) ^ 2) ^ 2 : ℕ) : ℝ) *
        (n : ℝ) ^ (2 * k - 2) := by
  apply mediumJansonDelta_upper P
  exact_mod_cast mediumUnorderedOverlappingPairs_card_le_explicit hk

end InducedStars
