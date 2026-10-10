import InducedStars.Structure.Supercritical.MatchingCandidates
import InducedStars.Structure.Supercritical.MediumCandidateAbundance
import Mathlib.Tactic

/-!
# Finite counting for matching-defect candidates

This module constructs the exact finite candidate family used by the
supercritical matching penalty.  Candidates are tagged by their selected
matching edge, so summing the per-anchor counts never assumes that two
unlabelled star copies have different anchors.  The final section gives the
choice-vector and overlap-counting interfaces used by the Janson layer.
-/

noncomputable section

open Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance matchingCandidateCountingPropDecidable (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

variable {k n : ℕ} (hk : 3 ≤ k)
  {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
  {M : SupercriticalHomogeneousMatching k (Fin n) D T}

/-! ## Available vertex sets -/

/-- Valid centers for an internal matching edge. -/
def internalMatchingCenterSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) : Finset (Fin n) :=
  (D.parts i).filter fun z ↦
    z ∉ M.endpointFinset ∧
      ¬T.Adj z (M.orientedFirstEndpoint e) ∧
      ¬T.Adj z (M.orientedSecondEndpoint e)

@[simp] theorem mem_internalMatchingCenterSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) (z : Fin n) :
    z ∈ internalMatchingCenterSet M i e ↔
      z ∈ D.parts i ∧ z ∉ M.endpointFinset ∧
        ¬T.Adj z (M.orientedFirstEndpoint e) ∧
        ¬T.Adj z (M.orientedSecondEndpoint e) := by
  simp [internalMatchingCenterSet]

/-- Valid same-part leaves for a support--sparse matching edge. -/
def supportMatchingCompanionSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) : Finset (Fin n) :=
  (D.parts i).filter fun z ↦
    z ∉ M.endpointFinset ∧
      ¬T.Adj (M.orientedFirstEndpoint e) z ∧
      ¬T.Adj (M.orientedSecondEndpoint e) z

@[simp] theorem mem_supportMatchingCompanionSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) (z : Fin n) :
    z ∈ supportMatchingCompanionSet M i e ↔
      z ∈ D.parts i ∧ z ∉ M.endpointFinset ∧
        ¬T.Adj (M.orientedFirstEndpoint e) z ∧
        ¬T.Adj (M.orientedSecondEndpoint e) z := by
  simp [supportMatchingCompanionSet]

/-- In the support--sparse geometry, available leaves in another main part
are precisely the non-neighbours of the sparse matching endpoint in `T`. -/
def supportMatchingOtherSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges})
    (r : Fin (k - 2)) : Finset (Fin n) :=
  (D.parts (otherSupercriticalPartEquiv hk i r)).filter fun y ↦
    ¬T.Adj (M.orientedSecondEndpoint e) y

@[simp] theorem mem_supportMatchingOtherSet
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges})
    (r : Fin (k - 2)) (y : Fin n) :
    y ∈ supportMatchingOtherSet hk M i e r ↔
      y ∈ D.parts (otherSupercriticalPartEquiv hk i r) ∧
        ¬T.Adj (M.orientedSecondEndpoint e) y := by
  simp [supportMatchingOtherSet]

/-! ## Raw selections -/

abbrev SupercriticalInternalMatchingRawSelection
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :=
  {z : Fin n // z ∈ internalMatchingCenterSet M i e} ×
    ((r : Fin (k - 2)) →
      {y : Fin n // y ∈ D.parts (otherSupercriticalPartEquiv hk i r)})

abbrev SupercriticalSupportMatchingRawSelection
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :=
  {z : Fin n // z ∈ supportMatchingCompanionSet M i e} ×
    ((r : Fin (k - 2)) →
      {y : Fin n // y ∈ supportMatchingOtherSet hk M i e r})

namespace SupercriticalInternalMatchingRawSelection

variable {i : Fin (k - 1)} {e : {e : Sym2 (Fin n) // e ∈ M.edges}}

def center (S : SupercriticalInternalMatchingRawSelection hk M i e) : Fin n :=
  S.1.1

def other (S : SupercriticalInternalMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) : Fin n :=
  (S.2 r).1

@[simp] theorem center_mem_set
    (S : SupercriticalInternalMatchingRawSelection hk M i e) :
    S.center hk ∈ internalMatchingCenterSet M i e :=
  S.1.2

@[simp] theorem other_mem_part
    (S : SupercriticalInternalMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) :
    S.other hk r ∈ D.parts (otherSupercriticalPartEquiv hk i r) :=
  (S.2 r).2

def vertexMap (S : SupercriticalInternalMatchingRawSelection hk M i e) :
    Fin (k + 1) → Fin n :=
  Sum.elim
      (fun j : Fin 3 ↦
        ![S.center hk, M.orientedFirstEndpoint e,
          M.orientedSecondEndpoint e] j)
      (S.other hk) ∘ mediumStarVertexEquiv hk

@[simp] theorem vertexMap_center
    (S : SupercriticalInternalMatchingRawSelection hk M i e) :
    S.vertexMap hk mediumCenterIndex = S.center hk := by
  simp [vertexMap]

@[simp] theorem vertexMap_witness
    (S : SupercriticalInternalMatchingRawSelection hk M i e) :
    S.vertexMap hk (mediumWitnessIndex hk) = M.orientedFirstEndpoint e := by
  simp [vertexMap]

@[simp] theorem vertexMap_companion
    (S : SupercriticalInternalMatchingRawSelection hk M i e) :
    S.vertexMap hk (mediumCompanionIndex hk) = M.orientedSecondEndpoint e := by
  simp [vertexMap]

@[simp] theorem vertexMap_other
    (S : SupercriticalInternalMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) :
    S.vertexMap hk (mediumOtherLeafIndex hk r) = S.other hk r := by
  simp [vertexMap]

theorem vertexMap_injective
    (S : SupercriticalInternalMatchingRawSelection hk M i e)
    (hloc : M.location = .internal i) :
    Function.Injective (S.vertexMap hk) := by
  have hend := M.endpoints_mem_internalPart hloc e
  have hcenter := (mem_internalMatchingCenterSet M i e (S.center hk)).mp
    S.center_mem_set
  have h12 : M.orientedFirstEndpoint e ≠ M.orientedSecondEndpoint e :=
    T.ne_of_adj (M.orientedEndpoints_adj_pattern e)
  have hc1 : S.center hk ≠ M.orientedFirstEndpoint e := by
    intro h
    exact hcenter.2.1 (h ▸ M.orientedFirstEndpoint_mem_endpointFinset e)
  have hc2 : S.center hk ≠ M.orientedSecondEndpoint e := by
    intro h
    exact hcenter.2.1 (h ▸ M.orientedSecondEndpoint_mem_endpointFinset e)
  have htriple : Function.Injective
      (fun j : Fin 3 ↦ ![S.center hk, M.orientedFirstEndpoint e,
        M.orientedSecondEndpoint e] j) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hc1, hc2, h12, hc1.symm, hc2.symm, h12.symm]
  have hother : Function.Injective (S.other hk) := by
    intro r s hrs
    apply (otherSupercriticalPartEquiv hk i).injective
    apply Subtype.ext
    exact D.mem_part_unique (S.other_mem_part hk r)
      (hrs ▸ S.other_mem_part hk s)
  have hcross : ∀ (j : Fin 3) (r : Fin (k - 2)),
      ![S.center hk, M.orientedFirstEndpoint e,
        M.orientedSecondEndpoint e] j ≠ S.other hk r := by
    intro j r
    have hpart : ∀ x ∈ D.parts i, x ≠ S.other hk r := by
      intro x hx hxy
      have hiother : i = otherSupercriticalPartEquiv hk i r :=
        D.mem_part_unique hx (hxy ▸ S.other_mem_part hk r)
      exact (otherSupercriticalPartEquiv_ne hk i r) hiother.symm
    fin_cases j
    · exact hpart _ hcenter.1
    · exact hpart _ hend.1
    · exact hpart _ hend.2
  unfold vertexMap
  exact htriple.sumElim hother hcross |>.comp
    (mediumStarVertexEquiv hk).injective

/-- Bundle a raw internal choice as an exact matching-star candidate. -/
def toCandidate
    (S : SupercriticalInternalMatchingRawSelection hk M i e)
    (hloc : M.location = .internal i) :
    SupercriticalInternalMatchingStarCandidate hk M where
  part := i
  location_eq := hloc
  edge := e
  center := S.center hk
  other := S.other hk
  center_mem :=
    ((mem_internalMatchingCenterSet M i e (S.center hk)).mp
      S.center_mem_set).1
  center_not_endpoint :=
    ((mem_internalMatchingCenterSet M i e (S.center hk)).mp
      S.center_mem_set).2.1
  other_mem := S.other_mem_part hk
  pattern_center_first :=
    ((mem_internalMatchingCenterSet M i e (S.center hk)).mp
      S.center_mem_set).2.2.1
  pattern_center_second :=
    ((mem_internalMatchingCenterSet M i e (S.center hk)).mp
      S.center_mem_set).2.2.2
  embedding := ⟨S.vertexMap hk, S.vertexMap_injective hk hloc⟩
  embedding_center := by simp
  embedding_witness := by simp
  embedding_companion := by simp
  embedding_other := by simp

end SupercriticalInternalMatchingRawSelection

namespace SupercriticalSupportMatchingRawSelection

variable {i : Fin (k - 1)} {e : {e : Sym2 (Fin n) // e ∈ M.edges}}

def companion (S : SupercriticalSupportMatchingRawSelection hk M i e) : Fin n :=
  S.1.1

def other (S : SupercriticalSupportMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) : Fin n :=
  (S.2 r).1

@[simp] theorem companion_mem_set
    (S : SupercriticalSupportMatchingRawSelection hk M i e) :
    S.companion hk ∈ supportMatchingCompanionSet M i e :=
  S.1.2

@[simp] theorem other_mem_set
    (S : SupercriticalSupportMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) :
    S.other hk r ∈ supportMatchingOtherSet hk M i e r :=
  (S.2 r).2

def vertexMap (S : SupercriticalSupportMatchingRawSelection hk M i e) :
    Fin (k + 1) → Fin n :=
  Sum.elim
      (fun j : Fin 3 ↦
        ![M.orientedFirstEndpoint e, M.orientedSecondEndpoint e,
          S.companion hk] j)
      (S.other hk) ∘ mediumStarVertexEquiv hk

@[simp] theorem vertexMap_center
    (S : SupercriticalSupportMatchingRawSelection hk M i e) :
    S.vertexMap hk mediumCenterIndex = M.orientedFirstEndpoint e := by
  simp [vertexMap]

@[simp] theorem vertexMap_witness
    (S : SupercriticalSupportMatchingRawSelection hk M i e) :
    S.vertexMap hk (mediumWitnessIndex hk) = M.orientedSecondEndpoint e := by
  simp [vertexMap]

@[simp] theorem vertexMap_companion
    (S : SupercriticalSupportMatchingRawSelection hk M i e) :
    S.vertexMap hk (mediumCompanionIndex hk) = S.companion hk := by
  simp [vertexMap]

@[simp] theorem vertexMap_other
    (S : SupercriticalSupportMatchingRawSelection hk M i e)
    (r : Fin (k - 2)) :
    S.vertexMap hk (mediumOtherLeafIndex hk r) = S.other hk r := by
  simp [vertexMap]

theorem vertexMap_injective
    (S : SupercriticalSupportMatchingRawSelection hk M i e)
    (hloc : M.location = .supportSparse i) :
    Function.Injective (S.vertexMap hk) := by
  have hfirst := M.orientedFirstEndpoint_mem_supportPart hloc e
  have hsecond := M.orientedSecondEndpoint_mem_sparse hloc e
  have hcomp := (mem_supportMatchingCompanionSet M i e (S.companion hk)).mp
    S.companion_mem_set
  have h12 : M.orientedFirstEndpoint e ≠ M.orientedSecondEndpoint e :=
    T.ne_of_adj (M.orientedEndpoints_adj_pattern e)
  have hc1 : S.companion hk ≠ M.orientedFirstEndpoint e := by
    intro h
    exact hcomp.2.1 (h ▸ M.orientedFirstEndpoint_mem_endpointFinset e)
  have hc2 : S.companion hk ≠ M.orientedSecondEndpoint e := by
    intro h
    exact hcomp.2.1 (h ▸ M.orientedSecondEndpoint_mem_endpointFinset e)
  have htriple : Function.Injective
      (fun j : Fin 3 ↦ ![M.orientedFirstEndpoint e,
        M.orientedSecondEndpoint e, S.companion hk] j) := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [hc1, hc2, h12, hc1.symm, hc2.symm, h12.symm]
  have hotherMem : ∀ r, S.other hk r ∈
      D.parts (otherSupercriticalPartEquiv hk i r) := by
    intro r
    exact (mem_supportMatchingOtherSet hk M i e r (S.other hk r)).mp
      (S.other_mem_set hk r) |>.1
  have hother : Function.Injective (S.other hk) := by
    intro r s hrs
    apply (otherSupercriticalPartEquiv hk i).injective
    apply Subtype.ext
    exact D.mem_part_unique (hotherMem r) (hrs ▸ hotherMem s)
  have hcross : ∀ (j : Fin 3) (r : Fin (k - 2)),
      ![M.orientedFirstEndpoint e, M.orientedSecondEndpoint e,
        S.companion hk] j ≠ S.other hk r := by
    intro j r
    have hmain : ∀ x ∈ D.parts i, x ≠ S.other hk r := by
      intro x hx hxy
      have hiother : i = otherSupercriticalPartEquiv hk i r :=
        D.mem_part_unique hx (hxy ▸ hotherMem r)
      exact (otherSupercriticalPartEquiv_ne hk i r) hiother.symm
    have hsparse : M.orientedSecondEndpoint e ≠ S.other hk r := by
      intro h
      exact (Finset.disjoint_left.mp
        (D.part_disjoint_sparse (otherSupercriticalPartEquiv hk i r)))
          (h ▸ hotherMem r) hsecond
    fin_cases j
    · exact hmain _ hfirst
    · exact hsparse
    · exact hmain _ hcomp.1
  unfold vertexMap
  exact htriple.sumElim hother hcross |>.comp
    (mediumStarVertexEquiv hk).injective

/-- Bundle a raw support--sparse choice as an exact matching-star candidate. -/
def toCandidate
    (S : SupercriticalSupportMatchingRawSelection hk M i e)
    (hloc : M.location = .supportSparse i) :
    SupercriticalSupportMatchingStarCandidate hk M where
  part := i
  location_eq := hloc
  edge := e
  companion := S.companion hk
  other := S.other hk
  companion_mem :=
    ((mem_supportMatchingCompanionSet M i e (S.companion hk)).mp
      S.companion_mem_set).1
  companion_not_endpoint :=
    ((mem_supportMatchingCompanionSet M i e (S.companion hk)).mp
      S.companion_mem_set).2.1
  other_mem := fun r ↦
    ((mem_supportMatchingOtherSet hk M i e r (S.other hk r)).mp
      (S.other_mem_set hk r)).1
  pattern_center_companion :=
    ((mem_supportMatchingCompanionSet M i e (S.companion hk)).mp
      S.companion_mem_set).2.2.1
  pattern_sparse_companion :=
    ((mem_supportMatchingCompanionSet M i e (S.companion hk)).mp
      S.companion_mem_set).2.2.2
  pattern_sparse_other := fun r ↦
    ((mem_supportMatchingOtherSet hk M i e r (S.other hk r)).mp
      (S.other_mem_set hk r)).2
  embedding := ⟨S.vertexMap hk, S.vertexMap_injective hk hloc⟩
  embedding_center := by simp
  embedding_witness := by simp
  embedding_companion := by simp
  embedding_other := by simp

end SupercriticalSupportMatchingRawSelection

/-! ## Per-anchor and tagged total candidate finsets -/

def internalRawSelectionToCandidateEmbedding
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .internal i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    SupercriticalInternalMatchingRawSelection hk M i e ↪
      SupercriticalMatchingStarCandidate hk M where
  toFun S := Sum.inl (S.toCandidate hk hloc)
  inj' := by
    intro S R hSR
    have h' : S.toCandidate hk hloc = R.toCandidate hk hloc :=
      Sum.inl.inj hSR
    apply Prod.ext
    · exact Subtype.ext (congrArg
        SupercriticalInternalMatchingStarCandidate.center h')
    · funext r
      exact Subtype.ext (congrFun
        (congrArg SupercriticalInternalMatchingStarCandidate.other h') r)

def supportRawSelectionToCandidateEmbedding
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .supportSparse i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    SupercriticalSupportMatchingRawSelection hk M i e ↪
      SupercriticalMatchingStarCandidate hk M where
  toFun S := Sum.inr (S.toCandidate hk hloc)
  inj' := by
    intro S R hSR
    have h' : S.toCandidate hk hloc = R.toCandidate hk hloc :=
      Sum.inr.inj hSR
    apply Prod.ext
    · exact Subtype.ext (congrArg
        SupercriticalSupportMatchingStarCandidate.companion h')
    · funext r
      exact Subtype.ext (congrFun
        (congrArg SupercriticalSupportMatchingStarCandidate.other h') r)

def internalMatchingStarCandidateFinset
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .internal i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    Finset (SupercriticalMatchingStarCandidate hk M) :=
  Finset.univ.map (internalRawSelectionToCandidateEmbedding hk M i hloc e)

def supportMatchingStarCandidateFinset
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .supportSparse i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    Finset (SupercriticalMatchingStarCandidate hk M) :=
  Finset.univ.map (supportRawSelectionToCandidateEmbedding hk M i hloc e)

@[simp] theorem internalMatchingStarCandidateFinset_card
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .internal i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (internalMatchingStarCandidateFinset hk M i hloc e).card =
      (internalMatchingCenterSet M i e).card *
        ∏ r : Fin (k - 2),
          (D.parts (otherSupercriticalPartEquiv hk i r)).card := by
  classical
  rw [internalMatchingStarCandidateFinset, Finset.card_map,
    Finset.card_univ]
  change Fintype.card
      (↑(internalMatchingCenterSet M i e) ×
        ((r : Fin (k - 2)) →
          ↑(D.parts (otherSupercriticalPartEquiv hk i r)))) = _
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [Fintype.card_coe]

@[simp] theorem supportMatchingStarCandidateFinset_card
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (hloc : M.location = .supportSparse i)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (supportMatchingStarCandidateFinset hk M i hloc e).card =
      (supportMatchingCompanionSet M i e).card *
        ∏ r : Fin (k - 2),
          (supportMatchingOtherSet hk M i e r).card := by
  classical
  rw [supportMatchingStarCandidateFinset, Finset.card_map,
    Finset.card_univ]
  change Fintype.card
      (↑(supportMatchingCompanionSet M i e) ×
        ((r : Fin (k - 2)) →
          ↑(supportMatchingOtherSet hk M i e r))) = _
  rw [Fintype.card_prod, Fintype.card_pi]
  simp only [Fintype.card_coe]

/-- The exact per-anchor family.  The dependent match supplies the proof of
the matching's common location to the corresponding constructor. -/
def matchingStarCandidatesForAnchor
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    Finset (SupercriticalMatchingStarCandidate hk M) :=
  match hloc : M.location with
  | .internal i => internalMatchingStarCandidateFinset hk M i hloc e
  | .supportSparse i => supportMatchingStarCandidateFinset hk M i hloc e

/-- A candidate retaining its matching anchor as a genuine tag.  This is the
index type used by the probability argument. -/
abbrev SupercriticalMatchingCandidateIndex
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :=
  Σ e : {e : Sym2 (Fin n) // e ∈ M.edges},
    {K : SupercriticalMatchingStarCandidate hk M //
      K ∈ matchingStarCandidatesForAnchor hk M e}

/-- The finite tagged candidate family. -/
def matchingStarCandidateFinset
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :
    Finset (SupercriticalMatchingCandidateIndex hk M) :=
  Finset.univ

@[simp] theorem matchingStarCandidateFinset_card_eq_sum
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :
    (matchingStarCandidateFinset hk M).card =
      ∑ e : {e : Sym2 (Fin n) // e ∈ M.edges},
        (matchingStarCandidatesForAnchor hk M e).card := by
  classical
  simp [matchingStarCandidateFinset, SupercriticalMatchingCandidateIndex]

/-- Forgetting the anchor tag exposes the exact potential-star structure. -/
def SupercriticalMatchingCandidateIndex.candidate
    (K : SupercriticalMatchingCandidateIndex hk M) :
    SupercriticalMatchingStarCandidate hk M :=
  K.2.1

/-- The tag is the source matching edge, independently of whether two
unlabelled embeddings happen to use the same selected vertices. -/
def SupercriticalMatchingCandidateIndex.anchor
    (K : SupercriticalMatchingCandidateIndex hk M) :
    {e : Sym2 (Fin n) // e ∈ M.edges} :=
  K.1

/-! ## Elementary cardinality upper bounds -/

theorem card_internalMatchingCenterSet_le
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (internalMatchingCenterSet M i e).card ≤ n := by
  simpa using (Finset.card_le_univ (s := internalMatchingCenterSet M i e))

theorem card_supportMatchingCompanionSet_le
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (supportMatchingCompanionSet M i e).card ≤ n := by
  simpa using (Finset.card_le_univ (s := supportMatchingCompanionSet M i e))

theorem card_supportMatchingOtherSet_le
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) (r : Fin (k - 2)) :
    (supportMatchingOtherSet hk M i e r).card ≤ n := by
  simpa using
    (Finset.card_le_univ (s := supportMatchingOtherSet hk M i e r))

theorem matchingStarCandidatesForAnchor_card_le
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (matchingStarCandidatesForAnchor hk M e).card ≤ n ^ (k - 1) := by
  classical
  have hprod (A : Finset (Fin n)) (B : Fin (k - 2) → Finset (Fin n)) :
      A.card * (∏ r, (B r).card) ≤ n ^ (k - 1) := by
    calc
      _ ≤ n * ∏ _r : Fin (k - 2), n := by
        gcongr
        · simpa using Finset.card_le_univ A
        · simpa using Finset.card_le_univ (B r)
      _ = _ := by
        simp [show k - 1 = (k - 2) + 1 by omega, pow_succ, Nat.mul_comm]
  unfold matchingStarCandidatesForAnchor
  split
  next i hloc =>
    rw [internalMatchingStarCandidateFinset_card]
    exact hprod _ _
  next i hloc =>
    rw [supportMatchingStarCandidateFinset_card]
    exact hprod _ _

theorem matchingStarCandidateFinset_card_le
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :
    (matchingStarCandidateFinset hk M).card ≤
      M.edges.card * n ^ (k - 1) := by
  rw [matchingStarCandidateFinset_card_eq_sum]
  calc
    (∑ e : {e : Sym2 (Fin n) // e ∈ M.edges},
        (matchingStarCandidatesForAnchor hk M e).card) ≤
        ∑ _e : {e : Sym2 (Fin n) // e ∈ M.edges}, n ^ (k - 1) := by
      exact Finset.sum_le_sum fun e _ ↦
        matchingStarCandidatesForAnchor_card_le hk M e
    _ = M.edges.card * n ^ (k - 1) := by simp

/-! ## Endpoint estimates for the selected half-matching -/

/-- Endpoint union of an arbitrary finite subfamily of matching edges. -/
def matchingEdgeEndpointFinset (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  E.biUnion Sym2.toFinset

@[simp] theorem mem_matchingEdgeEndpointFinset
    (E : Finset (Sym2 (Fin n))) (v : Fin n) :
    v ∈ matchingEdgeEndpointFinset E ↔ ∃ e ∈ E, v ∈ e := by
  simp [matchingEdgeEndpointFinset, Sym2.mem_toFinset]

/-- Every subfamily of the canonical matching has exactly two endpoints per
edge. -/
theorem card_matchingEdgeEndpointFinset_of_subset_canonical
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (E : Finset (Sym2 (Fin n)))
    (hE : E ⊆ supercriticalCanonicalMatchingEdges D T) :
    (matchingEdgeEndpointFinset E).card = 2 * E.card := by
  classical
  have hpairwise : (E : Set (Sym2 (Fin n))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    have he' := hE he
    have hf' := hE hf
    rw [supercriticalCanonicalMatchingEdges,
      DenseGraph.mem_matchingEdgeFinset] at he' hf'
    have hdisjoint := DenseGraph.matching_edges_endpoint_disjoint
      (supercriticalCanonicalMatching_isMatching D T) he' hf' hef
    change Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact Set.disjoint_left.mp hdisjoint
      (by simpa [Sym2.mem_toFinset] using hve)
      (by simpa [Sym2.mem_toFinset] using hvf)
  rw [matchingEdgeEndpointFinset, Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ E, e.toFinset.card) = ∑ _e ∈ E, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      have he' := hE he
      rw [supercriticalCanonicalMatchingEdges,
        DenseGraph.mem_matchingEdgeFinset] at he'
      exact Sym2.card_toFinset_of_not_isDiag e
        ((supercriticalSupportIncidentGraph D T).not_isDiag_of_mem_edgeSet
          ((supercriticalCanonicalMatching D T).edgeSet_subset he'))
    _ = 2 * E.card := by simp [Nat.mul_comm]

/-- Every edge in the largest location fiber has that location. -/
theorem dominantLocationMatching_contains_dominant
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    {e : Sym2 (Fin n)} (he : e ∈ dominantLocationMatching hk D T) :
    (dominantMatchingLocation hk D T).Contains D e := by
  have heCanonical := dominantLocationMatching_subset hk D T he
  have heSupport := supercriticalCanonicalMatchingEdges_subset D T heCanonical
  have hexists :=
    (existsUnique_supercriticalMatchingLocation_of_mem_pattern hT heSupport).exists
  have hcontains :=
    supercriticalMatchingLocationOfEdge_contains hk D hexists
  have hlocation :=
    (mem_matchingInLocation hk D T (dominantMatchingLocation hk D T) e).mp
      he |>.2
  rw [hlocation] at hcontains
  exact hcontains

theorem dominantMatchingEndpointFinset_subset_part_of_internal
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (i : Fin (k - 1))
    (hloc : dominantMatchingLocation hk D T = .internal i) :
    matchingEdgeEndpointFinset (dominantLocationMatching hk D T) ⊆
      D.parts i := by
  intro v hv
  rw [mem_matchingEdgeEndpointFinset] at hv
  obtain ⟨e, he, hve⟩ := hv
  have hcontains := dominantLocationMatching_contains_dominant hk D T hT he
  rw [hloc] at hcontains
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp only [SupercriticalMatchingLocation.contains_pair_internal] at hcontains
      rw [Sym2.mem_iff] at hve
      exact hve.elim (· ▸ hcontains.1) (· ▸ hcontains.2)

/-- In the internal location the dominant matching has two distinct
same-part endpoints per edge. -/
theorem two_mul_dominantLocationMatching_card_le_part_of_internal
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (i : Fin (k - 1))
    (hloc : dominantMatchingLocation hk D T = .internal i) :
    2 * (dominantLocationMatching hk D T).card ≤ (D.parts i).card := by
  rw [← card_matchingEdgeEndpointFinset_of_subset_canonical D T
    (dominantLocationMatching hk D T)
    (dominantLocationMatching_subset hk D T)]
  exact Finset.card_le_card
    (dominantMatchingEndpointFinset_subset_part_of_internal
      hk D T hT i hloc)

/-- The selected family has ceiling-half the number of edges of the dominant
fiber, hence twice its size is at most the dominant size plus one. -/
theorem twice_selectedHomogeneousMatching_card_le_dominant_add_one
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n)) :
    2 * (selectedHomogeneousMatching hk D T).card ≤
      (dominantLocationMatching hk D T).card + 1 := by
  rw [selectedHomogeneousMatching_card]
  omega

/-- In a support--sparse location, every selected endpoint which lies in the
distinguished part is the globally oriented first endpoint of a unique
matching edge. -/
theorem part_inter_selectedEndpoint_card_le_selected_card_of_support
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (i : Fin (k - 1))
    (hloc : dominantMatchingLocation hk D T = .supportSparse i) :
    (D.parts i ∩
        (selectedSupercriticalHomogeneousMatching D T hT).endpointFinset).card ≤
      (selectedHomogeneousMatching hk D T).card := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  let X : Finset (Fin n) := M.edges.attach.image fun e ↦
    M.orientedFirstEndpoint e
  have hsubset : D.parts i ∩ M.endpointFinset ⊆ X := by
    intro v hv
    have hvPart := (Finset.mem_inter.mp hv).1
    have hvEnd := (Finset.mem_inter.mp hv).2
    rw [M.mem_endpointFinset] at hvEnd
    obtain ⟨e, he, hve⟩ := hvEnd
    let esub : {e : Sym2 (Fin n) // e ∈ M.edges} := ⟨e, he⟩
    have hlocM : M.location = .supportSparse i := by
      simpa [M, selectedSupercriticalHomogeneousMatching] using hloc
    have hsecond := M.orientedSecondEndpoint_mem_sparse hlocM esub
    change v ∈ esub.1 at hve
    rw [M.edge_eq_orientedEndpoints esub, Sym2.mem_iff] at hve
    have hvFirst : v = M.orientedFirstEndpoint esub := by
      rcases hve with h | h
      · exact h
      · exfalso
        exact (Finset.disjoint_left.mp (D.part_disjoint_sparse i)) hvPart
          (h ▸ hsecond)
    change v ∈ M.edges.attach.image fun e ↦ M.orientedFirstEndpoint e
    rw [Finset.mem_image]
    refine ⟨esub, by simp, ?_⟩
    exact hvFirst.symm
  calc
    (D.parts i ∩ M.endpointFinset).card ≤ X.card :=
      Finset.card_le_card hsubset
    _ ≤ M.edges.attach.card := Finset.card_image_le
    _ = (selectedHomogeneousMatching hk D T).card := by
      simp [M, selectedSupercriticalHomogeneousMatching]

theorem exists_part_endpoint_of_supportSparse_contains
    (D : SupercriticalDivision k (Fin n)) (i : Fin (k - 1))
    {e : Sym2 (Fin n)}
    (he : (SupercriticalMatchingLocation.supportSparse i).Contains D e) :
    ∃ v : Fin n, v ∈ D.parts i ∧ v ∈ (e : Set (Fin n)) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SupercriticalMatchingLocation.contains_pair_supportSparse] at he
      rcases he with h | h
      · exact ⟨x, h.1, by simp⟩
      · exact ⟨y, h.1, by simp⟩

/-- The halving construction leaves at most half a distinguished part (up
to the one-vertex ceiling loss) among selected endpoints. -/
theorem twice_part_inter_selectedEndpoint_card_le_part_add_two
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    let M := selectedSupercriticalHomogeneousMatching D T hT
    2 * (D.parts M.location.part ∩ M.endpointFinset).card ≤
      (D.parts M.location.part).card + 2 := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  cases hloc : dominantMatchingLocation hk D T with
  | internal i =>
      have hlocM : M.location = .internal i := by
        simpa [M, selectedSupercriticalHomogeneousMatching] using hloc
      have hinter : (D.parts i ∩ M.endpointFinset).card ≤
          M.endpointFinset.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hendpoint : M.endpointFinset.card =
          2 * (selectedHomogeneousMatching hk D T).card := by
        simpa [M, selectedSupercriticalHomogeneousMatching] using
          M.card_endpointFinset
      have hhalf := twice_selectedHomogeneousMatching_card_le_dominant_add_one
        hk D T
      have hdom :=
        two_mul_dominantLocationMatching_card_le_part_of_internal
          hk D T hT i hloc
      have hgoal : 2 * (D.parts i ∩ M.endpointFinset).card ≤
          (D.parts i).card + 2 := by omega
      simpa [M, selectedSupercriticalHomogeneousMatching, hloc,
        SupercriticalMatchingLocation.part] using hgoal
  | supportSparse i =>
      have hlocM : M.location = .supportSparse i := by
        simpa [M, selectedSupercriticalHomogeneousMatching] using hloc
      have hinter :=
        part_inter_selectedEndpoint_card_le_selected_card_of_support
          hk D T hT i hloc
      have hhalf := twice_selectedHomogeneousMatching_card_le_dominant_add_one
        hk D T
      have hdom : (dominantLocationMatching hk D T).card ≤
          (D.parts i).card := by
        let E := dominantLocationMatching hk D T
        have hexists : ∀ e : {e : Sym2 (Fin n) // e ∈ E},
            ∃ v : Fin n, v ∈ D.parts i ∧ v ∈ (e.1 : Set (Fin n)) := by
          intro e
          have hc := dominantLocationMatching_contains_dominant hk D T hT e.2
          change (dominantMatchingLocation hk D T).Contains D e.1 at hc
          rw [hloc] at hc
          exact exists_part_endpoint_of_supportSparse_contains D i hc
        let g : {e : Sym2 (Fin n) // e ∈ E} → Fin n := fun e ↦
          Classical.choose (hexists e)
        have hgmem : ∀ e, g e ∈ D.parts i := by
          intro e
          exact (Classical.choose_spec (hexists e)).1
        have hgedge : ∀ e, g e ∈ (e.1 : Set (Fin n)) := by
          intro e
          exact (Classical.choose_spec (hexists e)).2
        have hginj : Function.Injective g := by
          intro e f hef
          by_contra hne
          have heCanonical := dominantLocationMatching_subset hk D T e.2
          have hfCanonical := dominantLocationMatching_subset hk D T f.2
          rw [supercriticalCanonicalMatchingEdges,
            DenseGraph.mem_matchingEdgeFinset] at heCanonical hfCanonical
          have hdis := DenseGraph.matching_edges_endpoint_disjoint
            (supercriticalCanonicalMatching_isMatching D T)
            heCanonical hfCanonical
            (by exact fun h ↦ hne (Subtype.ext h))
          exact Set.disjoint_left.mp hdis
            (hgedge e)
            (hef ▸ hgedge f)
        have hcard := Fintype.card_le_of_injective
          (fun e : {e : Sym2 (Fin n) // e ∈ E} ↦
            (⟨g e, hgmem e⟩ : ↑(D.parts i))) (by
            intro e f h
            apply hginj
            exact congrArg Subtype.val h)
        simpa [E] using hcard
      have hinterM : (D.parts i ∩ M.endpointFinset).card ≤
          (selectedHomogeneousMatching hk D T).card := by
        simpa [M] using hinter
      have hgoal : 2 * (D.parts i ∩ M.endpointFinset).card ≤
          (D.parts i).card + 2 := by omega
      simpa [M, selectedSupercriticalHomogeneousMatching, hloc,
        SupercriticalMatchingLocation.part] using hgoal

/-! ## Available-set lower bounds -/

theorem card_le_filter_not_mem_not_not_add_forbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    (S E : Finset V) (P Q : V → Prop) [DecidablePred P] [DecidablePred Q] :
    S.card ≤
      (S.filter fun z ↦ z ∉ E ∧ ¬P z ∧ ¬Q z).card +
        (S ∩ E).card + (S.filter P).card + (S.filter Q).card := by
  have hpartition := S.card_filter_add_card_filter_not
    (fun z ↦ z ∉ E ∧ ¬P z ∧ ¬Q z)
  have hbad : (S.filter fun z ↦ ¬(z ∉ E ∧ ¬P z ∧ ¬Q z)) =
      (S ∩ E) ∪ (S.filter P) ∪ (S.filter Q) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
    tauto
  rw [hbad] at hpartition
  have hfirst := Finset.card_union_le (S ∩ E) (S.filter P)
  have hsecond := Finset.card_union_le ((S ∩ E) ∪ S.filter P) (S.filter Q)
  omega

theorem card_le_filter_not_add_filter
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (P : V → Prop) [DecidablePred P] :
    S.card ≤ (S.filter fun z ↦ ¬P z).card + (S.filter P).card := by
  exact (S.card_filter_add_card_filter_not P).symm.le.trans_eq (Nat.add_comm _ _)

theorem part_card_le_internalCenter_add_forbidden
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (D.parts i).card ≤
      (internalMatchingCenterSet M i e).card +
        (D.parts i ∩ M.endpointFinset).card +
        degreeInFinset T (M.orientedFirstEndpoint e) (D.parts i) +
        degreeInFinset T (M.orientedSecondEndpoint e) (D.parts i) := by
  simpa [internalMatchingCenterSet, degreeInFinset, T.adj_comm] using
    (card_le_filter_not_mem_not_not_add_forbidden
      (D.parts i) M.endpointFinset
      (fun z ↦ T.Adj (M.orientedFirstEndpoint e) z)
      (fun z ↦ T.Adj (M.orientedSecondEndpoint e) z))

theorem part_card_le_supportCompanion_add_forbidden
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) :
    (D.parts i).card ≤
      (supportMatchingCompanionSet M i e).card +
        (D.parts i ∩ M.endpointFinset).card +
        degreeInFinset T (M.orientedFirstEndpoint e) (D.parts i) +
        degreeInFinset T (M.orientedSecondEndpoint e) (D.parts i) := by
  simpa [supportMatchingCompanionSet, degreeInFinset] using
    (card_le_filter_not_mem_not_not_add_forbidden
      (D.parts i) M.endpointFinset
      (fun z ↦ T.Adj (M.orientedFirstEndpoint e) z)
      (fun z ↦ T.Adj (M.orientedSecondEndpoint e) z))

theorem part_card_le_supportOther_add_degree
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) (r : Fin (k - 2)) :
    (D.parts (otherSupercriticalPartEquiv hk i r)).card ≤
      (supportMatchingOtherSet hk M i e r).card +
        degreeInFinset T (M.orientedSecondEndpoint e)
          (D.parts (otherSupercriticalPartEquiv hk i r)) := by
  simpa [supportMatchingOtherSet, degreeInFinset] using
    (card_le_filter_not_add_filter
      (D.parts (otherSupercriticalPartEquiv hk i r))
      (fun z ↦ T.Adj (M.orientedSecondEndpoint e) z))

/-! ## Uniform quantitative abundance -/

/-- A deliberately crude `k`-only density for the `k-1` free selections of
one matching anchor. -/
def supercriticalMatchingCandidateRate (k : ℕ) : ℝ :=
  (1 / (100 * (k : ℝ))) ^ (k - 1)

theorem supercriticalMatchingCandidateRate_pos (hk : 3 ≤ k) :
    0 < supercriticalMatchingCandidateRate k := by
  unfold supercriticalMatchingCandidateRate
  positivity

theorem matchingPart_card_lower_common
    (hk : 3 ≤ k)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (i : Fin (k - 1)) :
    (n : ℝ) / (2 * (k : ℝ)) ≤ ((D.parts i).card : ℝ) := by
  have hbase := supercriticalPart_card_lower_of_abs_close
    hk hdelta0 hdelta hclose i
  have hkpos : (0 : ℝ) < k := by positivity
  have hsubpos : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hden1 : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  have hden2 : (0 : ℝ) < 2 * ((k - 1 : ℕ) : ℝ) := by positivity
  have hcoeff : (n : ℝ) / (2 * (k : ℝ)) ≤
      (n : ℝ) / (2 * ((k - 1 : ℕ) : ℝ)) := by
    apply div_le_div_of_nonneg_left (by positivity) hden2
    exact_mod_cast (Nat.mul_le_mul_left 2 (Nat.sub_le k 1))
  exact hcoeff.trans hbase

theorem low_degree_real_le_commonScale
    (hk : 3 ≤ k)
    {alpha : ℝ} (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (v : Fin n) (i : Fin (k - 1)) :
    (degreeInFinset T v (D.parts i) : ℝ) ≤
      (n : ℝ) / (100 * (k : ℝ)) := by
  have hdegree := hlow v i
  unfold HasLowDegreeInPart at hdegree
  have hpart : ((D.parts i).card : ℝ) ≤ n := by
    have h := Finset.card_le_univ (s := D.parts i)
    simp only [Fintype.card_fin] at h
    exact_mod_cast h
  calc
    (degreeInFinset T v (D.parts i) : ℝ) ≤
        alpha * ((D.parts i).card : ℝ) := hdegree.le
    _ ≤ (1 / (100 * (k : ℝ))) * (n : ℝ) := by
      exact mul_le_mul halpha.2.le hpart (by positivity) (by positivity)
    _ = (n : ℝ) / (100 * (k : ℝ)) := by ring

/-- The same endpoint-cleaning estimate applies to either matching location;
only degrees into the specified main part are used. -/
private theorem matchingCompanionSet_card_lower_of_bounds
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1)) (e : {e : Sym2 (Fin n) // e ∈ M.edges})
    {q : ℝ} (hq : 1 ≤ q)
    (hpart : 50 * q ≤ ((D.parts i).card : ℝ))
    (hendpoint : 2 * ((D.parts i ∩ M.endpointFinset).card : ℝ) ≤
      ((D.parts i).card : ℝ) + 2)
    (hdegree : ∀ v, (degreeInFinset T v (D.parts i) : ℝ) ≤ q) :
    q ≤ ((supportMatchingCompanionSet M i e).card : ℝ) := by
  have hcount : ((D.parts i).card : ℝ) ≤
      ((supportMatchingCompanionSet M i e).card : ℝ) +
        ((D.parts i ∩ M.endpointFinset).card : ℝ) +
        (degreeInFinset T (M.orientedFirstEndpoint e) (D.parts i) : ℝ) +
        (degreeInFinset T (M.orientedSecondEndpoint e) (D.parts i) : ℝ) := by
    exact_mod_cast part_card_le_supportCompanion_add_forbidden M i e
  linarith [hdegree (M.orientedFirstEndpoint e), hdegree (M.orientedSecondEndpoint e)]

theorem internalMatchingCenterSet_card_lower_common
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {alpha delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hnlarge : (100 * (k : ℝ)) ≤ (n : ℝ))
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (i : Fin (k - 1))
    (hloc : (selectedSupercriticalHomogeneousMatching D T hT).location =
      .internal i)
    (e : {e : Sym2 (Fin n) //
      e ∈ (selectedSupercriticalHomogeneousMatching D T hT).edges}) :
    (n : ℝ) / (100 * (k : ℝ)) ≤
      ((internalMatchingCenterSet
        (selectedSupercriticalHomogeneousMatching D T hT) i e).card : ℝ) := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  let q : ℝ := (n : ℝ) / (100 * (k : ℝ))
  have hpart := matchingPart_card_lower_common hk hdelta0 hdelta hclose i
  have hscale : (n : ℝ) / (2 * (k : ℝ)) = 50 * q := by
    dsimp [q]
    ring
  rw [hscale] at hpart
  have hendpoint : 2 * (D.parts i ∩ M.endpointFinset).card ≤
      (D.parts i).card + 2 := by
    simpa [M, hloc, SupercriticalMatchingLocation.part] using
      twice_part_inter_selectedEndpoint_card_le_part_add_two hk D T hT
  have hq1 : 1 ≤ q :=
    (le_div_iff₀ (by positivity)).2 (by simpa [mul_comm] using hnlarge)
  simpa [M, q, internalMatchingCenterSet, supportMatchingCompanionSet, T.adj_comm] using
    matchingCompanionSet_card_lower_of_bounds M i e hq1 hpart
      (by exact_mod_cast hendpoint) (fun v ↦ low_degree_real_le_commonScale hk halpha hlow v i)

theorem supportMatchingCompanionSet_card_lower_common
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {alpha delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hnlarge : (100 * (k : ℝ)) ≤ (n : ℝ))
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (i : Fin (k - 1))
    (hloc : (selectedSupercriticalHomogeneousMatching D T hT).location =
      .supportSparse i)
    (e : {e : Sym2 (Fin n) //
      e ∈ (selectedSupercriticalHomogeneousMatching D T hT).edges}) :
    (n : ℝ) / (100 * (k : ℝ)) ≤
      ((supportMatchingCompanionSet
        (selectedSupercriticalHomogeneousMatching D T hT) i e).card : ℝ) := by
  let M := selectedSupercriticalHomogeneousMatching D T hT
  let q : ℝ := (n : ℝ) / (100 * (k : ℝ))
  have hpart := matchingPart_card_lower_common hk hdelta0 hdelta hclose i
  have hscale : (n : ℝ) / (2 * (k : ℝ)) = 50 * q := by
    dsimp [q]
    ring
  rw [hscale] at hpart
  have hendpoint : 2 * (D.parts i ∩ M.endpointFinset).card ≤
      (D.parts i).card + 2 := by
    simpa [M, hloc, SupercriticalMatchingLocation.part] using
      twice_part_inter_selectedEndpoint_card_le_part_add_two hk D T hT
  have hq1 : 1 ≤ q :=
    (le_div_iff₀ (by positivity)).2 (by simpa [mul_comm] using hnlarge)
  exact matchingCompanionSet_card_lower_of_bounds M i e hq1 hpart
    (by exact_mod_cast hendpoint) (fun v ↦ low_degree_real_le_commonScale hk halpha hlow v i)

theorem supportMatchingOtherSet_card_lower_common
    {alpha delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (i : Fin (k - 1))
    (e : {e : Sym2 (Fin n) // e ∈ M.edges}) (r : Fin (k - 2)) :
    (n : ℝ) / (100 * (k : ℝ)) ≤
      ((supportMatchingOtherSet hk M i e r).card : ℝ) := by
  let j := otherSupercriticalPartEquiv hk i r
  let q : ℝ := (n : ℝ) / (100 * (k : ℝ))
  have hpart := matchingPart_card_lower_common hk hdelta0 hdelta hclose j
  have hscale : (n : ℝ) / (2 * (k : ℝ)) = 50 * q := by
    dsimp [q]
    field_simp
    ring
  have hdeg := low_degree_real_le_commonScale hk halpha hlow
    (M.orientedSecondEndpoint e) j
  have hcountNat := part_card_le_supportOther_add_degree hk M i e r
  have hcount : ((D.parts j).card : ℝ) ≤
      ((supportMatchingOtherSet hk M i e r).card : ℝ) +
        (degreeInFinset T (M.orientedSecondEndpoint e) (D.parts j) : ℝ) := by
    exact_mod_cast hcountNat
  rw [hscale] at hpart
  change q ≤ ((supportMatchingOtherSet hk M i e r).card : ℝ)
  nlinarith

/-! ## Per-anchor and total quantitative abundance -/

/-- Every selected matching edge supports at least the advertised `k`-only
fraction of the `n^(k-1)` possible free selections. -/
theorem matchingStarCandidatesForAnchor_card_lower_rate
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {alpha delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hnlarge : (100 * (k : ℝ)) ≤ (n : ℝ))
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i)
    (e : {e : Sym2 (Fin n) //
      e ∈ (selectedSupercriticalHomogeneousMatching D T hT).edges}) :
    supercriticalMatchingCandidateRate k * (n : ℝ) ^ (k - 1) ≤
      ((matchingStarCandidatesForAnchor hk
        (selectedSupercriticalHomogeneousMatching D T hT) e).card : ℝ) := by
  classical
  let M := selectedSupercriticalHomogeneousMatching D T hT
  let q : ℝ := (n : ℝ) / (100 * (k : ℝ))
  have hq0 : 0 ≤ q := by positivity
  have hscale : (n : ℝ) / (2 * (k : ℝ)) = 50 * q := by
    dsimp [q]
    field_simp
    ring
  have hrate : q ^ (k - 1) =
      supercriticalMatchingCandidateRate k * (n : ℝ) ^ (k - 1) := by
    dsimp [q, supercriticalMatchingCandidateRate]
    ring
  have hprod (a : ℝ) (b : Fin (k - 2) → ℝ)
      (ha : q ≤ a) (hb : ∀ r, q ≤ b r) : q ^ (k - 1) ≤ a * ∏ r, b r := by
    calc
      _ = q * ∏ _r : Fin (k - 2), q := by
        simp [show k - 1 = (k - 2) + 1 by omega, pow_succ, mul_comm]
      _ ≤ _ := mul_le_mul ha
        (Finset.prod_le_prod (fun _ _ ↦ hq0) (fun r _ ↦ hb r))
        (Finset.prod_nonneg fun _ _ ↦ hq0) (hq0.trans ha)
  change supercriticalMatchingCandidateRate k * (n : ℝ) ^ (k - 1) ≤
    ((matchingStarCandidatesForAnchor hk M e).card : ℝ)
  unfold matchingStarCandidatesForAnchor
  split
  next i hloc =>
    rw [internalMatchingStarCandidateFinset_card, Nat.cast_mul,
      Nat.cast_prod]
    have hcenter : q ≤
        ((internalMatchingCenterSet M i e).card : ℝ) := by
      simpa [M, q] using internalMatchingCenterSet_card_lower_common hk
        halpha hdelta0 hdelta hnlarge D T hT hclose hlow i hloc e
    have hother : ∀ r : Fin (k - 2), q ≤
        ((D.parts (otherSupercriticalPartEquiv hk i r)).card : ℝ) := by
      intro r
      have hr := matchingPart_card_lower_common hk hdelta0 hdelta hclose
        (otherSupercriticalPartEquiv hk i r)
      rw [hscale] at hr
      nlinarith
    rw [← hrate]
    exact hprod _ _ hcenter hother
  next i hloc =>
    rw [supportMatchingStarCandidateFinset_card, Nat.cast_mul,
      Nat.cast_prod]
    have hcompanion : q ≤
        ((supportMatchingCompanionSet M i e).card : ℝ) := by
      simpa [M, q] using supportMatchingCompanionSet_card_lower_common hk
        halpha hdelta0 hdelta hnlarge D T hT hclose hlow i hloc e
    have hother : ∀ r : Fin (k - 2), q ≤
        ((supportMatchingOtherSet hk M i e r).card : ℝ) := by
      intro r
      simpa [q] using supportMatchingOtherSet_card_lower_common hk
        halpha hdelta0 hdelta hclose hlow M i e r
    rw [← hrate]
    exact hprod _ _ hcompanion hother

/-- Summing the exact tagged per-anchor families gives the lower bound in the
form consumed by the matching Janson estimate. -/
theorem matchingStarCandidateFinset_card_lower_rate
    {gamma : ℝ} {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {alpha delta : ℝ}
    (halpha : alpha ∈ Set.Ioo (0 : ℝ)
      (1 / (100 * (k : ℝ))))
    (hdelta0 : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (6 * ((k - 1 : ℕ) : ℝ)))
    (hnlarge : (100 * (k : ℝ)) ≤ (n : ℝ))
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D)
    (hclose : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T alpha D v i) :
    supercriticalMatchingCandidateRate k *
        (((selectedSupercriticalHomogeneousMatching D T hT).edges.card : ℕ) : ℝ) *
        (n : ℝ) ^ (k - 1) ≤
      ((matchingStarCandidateFinset hk
        (selectedSupercriticalHomogeneousMatching D T hT)).card : ℝ) := by
  classical
  have hsum := Finset.sum_le_sum fun e (_ : e ∈ Finset.univ) ↦
    matchingStarCandidatesForAnchor_card_lower_rate hk
      halpha hdelta0 hdelta hnlarge D T hT hclose hlow e
  simpa [matchingStarCandidateFinset_card_eq_sum, Nat.cast_sum,
    mul_assoc, mul_left_comm, mul_comm] using hsum

/-! ## Tagged-anchor audit and overlap encodings -/

/-- The matching edge stored in either geometric candidate. -/
def SupercriticalMatchingStarCandidate.matchingEdge
    (K : SupercriticalMatchingStarCandidate hk M) :
    {e : Sym2 (Fin n) // e ∈ M.edges} :=
  match K with
  | Sum.inl L => L.edge
  | Sum.inr L => L.edge

/-- The `k-2` other-part choices, independent of the geometry. -/
def SupercriticalMatchingStarCandidate.matchingOther
    (K : SupercriticalMatchingStarCandidate hk M) : Fin (k - 2) → Fin n :=
  match K with
  | Sum.inl L => L.other
  | Sum.inr L => L.other

/-- The one non-anchor distinguished free choice: the center in the internal
geometry and the same-part companion in the support--sparse geometry. -/
def SupercriticalMatchingStarCandidate.matchingDistinguishedFree
    (K : SupercriticalMatchingStarCandidate hk M) : Fin n :=
  match K with
  | Sum.inl L => L.center
  | Sum.inr L => L.companion

/-- Membership in the exact per-anchor enumeration certifies that the edge
stored in the candidate is literally its sigma tag.  Thus the construction
does not rely on an unproved uniqueness assertion for untagged stars. -/
theorem SupercriticalMatchingCandidateIndex.matchingEdge_eq_anchor
    (K : SupercriticalMatchingCandidateIndex hk M) :
    (K.candidate hk).matchingEdge hk = K.anchor hk := by
  classical
  rcases K with ⟨e, ⟨K, hK⟩⟩
  unfold matchingStarCandidatesForAnchor at hK
  split at hK
  next i hloc =>
    rw [internalMatchingStarCandidateFinset, Finset.mem_map] at hK
    obtain ⟨S, -, rfl⟩ := hK
    rfl
  next i hloc =>
    rw [supportMatchingStarCandidateFinset, Finset.mem_map] at hK
    obtain ⟨S, -, rfl⟩ := hK
    rfl

/-- Two selected matching edges sharing any endpoint are the same tagged
edge. -/
theorem matchingAnchor_eq_of_common_endpoint
    (M : SupercriticalHomogeneousMatching k (Fin n) D T)
    (e f : {e : Sym2 (Fin n) // e ∈ M.edges}) (v : Fin n)
    (he : v ∈ (e.1 : Set (Fin n))) (hf : v ∈ (f.1 : Set (Fin n))) :
    e = f := by
  apply Subtype.ext
  by_contra hef
  exact Set.disjoint_left.mp (M.endpoint_disjoint e.2 f.2 hef) he hf

/-- A canonical order on the tagged candidate type, used only to select one
orientation of unordered Janson pairs. -/
noncomputable instance supercriticalMatchingCandidateIndexLinearOrder
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :
    LinearOrder (SupercriticalMatchingCandidateIndex hk M) :=
  LinearOrder.lift' (Fintype.equivFin _)
    (Fintype.equivFin _).injective

@[simp] theorem card_supercriticalMatchingCandidateIndex
    (M : SupercriticalHomogeneousMatching k (Fin n) D T) :
    Fintype.card (SupercriticalMatchingCandidateIndex hk M) =
      (matchingStarCandidateFinset hk M).card := by
  simp [matchingStarCandidateFinset]

/-- A common finite role type.  The outer tag records which of the two
geometries supplies the role. -/
abbrev SupercriticalMatchingRandomRole (k : ℕ) :=
  SupercriticalInternalMatchingRandomRole k ⊕
    SupercriticalSupportMatchingRandomRole k

/-- The explicit `k`-only coefficient in the final matching dependency
bound. -/
def supercriticalMatchingDependencyCoefficient (k : ℕ) : ℕ :=
  8 * (supercriticalMatchingRandomRoleBound k) ^ 2

theorem supercriticalMatchingDependencyCoefficient_pos (hk : 3 ≤ k) :
    0 < supercriticalMatchingDependencyCoefficient k := by
  unfold supercriticalMatchingDependencyCoefficient
  unfold supercriticalMatchingRandomRoleBound
  have hsub : 0 < k - 2 := by omega
  positivity

theorem supercriticalMatchingDependencyCoefficient_cast_pos (hk : 3 ≤ k) :
    (0 : ℝ) < (supercriticalMatchingDependencyCoefficient k : ℝ) := by
  exact_mod_cast supercriticalMatchingDependencyCoefficient_pos hk

/-- The only role for which the choice-vector anchor coordinate uses the
second oriented endpoint.  For every other role either the first endpoint is
the random endpoint, or the anchor coordinate is not used by that role. -/
def matchingRandomRoleUsesSecond {k : ℕ} :
    SupercriticalMatchingRandomRole k → Prop
  | Sum.inl (Sum.inr (Sum.inr (Sum.inl _))) => True
  | _ => False

/-- Role-adapted `k`-coordinate encoding: one endpoint determining the
matching edge, one distinguished free vertex, and the `k-2` other-part
vertices. -/
def matchingCandidateChoiceVector
    (s : SupercriticalMatchingRandomRole k)
    (K : SupercriticalMatchingCandidateIndex hk M) : Fin k → Fin n :=
  Sum.elim
      (fun j : Fin 2 ↦
        ![if matchingRandomRoleUsesSecond s then
            M.orientedSecondEndpoint (K.anchor hk)
          else M.orientedFirstEndpoint (K.anchor hk),
          (K.candidate hk).matchingDistinguishedFree hk] j)
      ((K.candidate hk).matchingOther hk) ∘
    mediumCandidateVariableEquiv hk

@[simp] theorem matchingCandidateChoiceVector_anchor
    (s : SupercriticalMatchingRandomRole k)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    matchingCandidateChoiceVector hk s K (mediumVariableXIndex hk) =
      if matchingRandomRoleUsesSecond s then
        M.orientedSecondEndpoint (K.anchor hk)
      else M.orientedFirstEndpoint (K.anchor hk) := by
  simp [matchingCandidateChoiceVector, mediumVariableXIndex]

@[simp] theorem matchingCandidateChoiceVector_distinguished
    (s : SupercriticalMatchingRandomRole k)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    matchingCandidateChoiceVector hk s K (mediumVariableZIndex hk) =
      (K.candidate hk).matchingDistinguishedFree hk := by
  simp [matchingCandidateChoiceVector, mediumVariableZIndex]

@[simp] theorem matchingCandidateChoiceVector_other
    (s : SupercriticalMatchingRandomRole k)
    (K : SupercriticalMatchingCandidateIndex hk M) (r : Fin (k - 2)) :
    matchingCandidateChoiceVector hk s K (mediumVariableOtherIndex hk r) =
      (K.candidate hk).matchingOther hk r := by
  simp [matchingCandidateChoiceVector, mediumVariableOtherIndex]

theorem matchingCandidateChoiceVector_anchor_mem
    (s : SupercriticalMatchingRandomRole k)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    matchingCandidateChoiceVector hk s K (mediumVariableXIndex hk) ∈
      ((K.anchor hk).1 : Set (Fin n)) := by
  rw [matchingCandidateChoiceVector_anchor]
  by_cases hs : matchingRandomRoleUsesSecond s
  · simp only [if_pos hs]
    rw [M.edge_eq_orientedEndpoints (K.anchor hk)]
    simp
  · simp only [if_neg hs]
    rw [M.edge_eq_orientedEndpoints (K.anchor hk)]
    simp

/-- The two choice-vector positions occupied by an internal random role. -/
def internalMatchingRandomRoleVariableEndpoints
    (r : SupercriticalInternalMatchingRandomRole k) : Fin k × Fin k :=
  match r with
  | Sum.inl t => (mediumVariableZIndex hk, mediumVariableOtherIndex hk t)
  | Sum.inr (Sum.inl t) =>
      (mediumVariableXIndex hk, mediumVariableOtherIndex hk t)
  | Sum.inr (Sum.inr (Sum.inl t)) =>
      (mediumVariableXIndex hk, mediumVariableOtherIndex hk t)
  | Sum.inr (Sum.inr (Sum.inr p)) =>
      (mediumVariableOtherIndex hk p.1.1,
        mediumVariableOtherIndex hk p.1.2)

/-- The two choice-vector positions occupied by a support--sparse role. -/
def supportMatchingRandomRoleVariableEndpoints
    (r : SupercriticalSupportMatchingRandomRole k) : Fin k × Fin k :=
  match r with
  | Sum.inl t =>
      (mediumVariableXIndex hk, mediumVariableOtherIndex hk t)
  | Sum.inr (Sum.inl t) =>
      (mediumVariableZIndex hk, mediumVariableOtherIndex hk t)
  | Sum.inr (Sum.inr p) =>
      (mediumVariableOtherIndex hk p.1.1,
        mediumVariableOtherIndex hk p.1.2)

theorem internalMatchingRandomRoleVariableEndpoints_ne
    (r : SupercriticalInternalMatchingRandomRole k) :
    (internalMatchingRandomRoleVariableEndpoints hk r).1 ≠
      (internalMatchingRandomRoleVariableEndpoints hk r).2 := by
  rcases r with r | r
  · exact mediumVariableZIndex_ne_other hk r
  · rcases r with r | r
    · exact mediumVariableXIndex_ne_other hk r
    · rcases r with r | p
      · exact mediumVariableXIndex_ne_other hk r
      · exact (mediumVariableOtherIndex_injective hk).ne (ne_of_lt p.2)

theorem supportMatchingRandomRoleVariableEndpoints_ne
    (r : SupercriticalSupportMatchingRandomRole k) :
    (supportMatchingRandomRoleVariableEndpoints hk r).1 ≠
      (supportMatchingRandomRoleVariableEndpoints hk r).2 := by
  rcases r with r | r
  · exact mediumVariableXIndex_ne_other hk r
  · rcases r with r | p
    · exact mediumVariableZIndex_ne_other hk r
    · exact (mediumVariableOtherIndex_injective hk).ne (ne_of_lt p.2)

theorem internalMatchingCandidate_ext_of_selections_eq
    (K L : SupercriticalInternalMatchingStarCandidate hk M)
    (hpart : K.part = L.part) (hedge : K.edge = L.edge)
    (hcenter : K.center = L.center) (hother : K.other = L.other) :
    K = L := by
  have hemb : K.embedding = L.embedding := by
    apply Function.Embedding.ext
    intro a
    rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩
    · subst a
      rw [K.embedding_center, L.embedding_center, hcenter]
    · subst a
      rw [K.embedding_witness, L.embedding_witness, hedge]
    · subst a
      rw [K.embedding_companion, L.embedding_companion, hedge]
    · subst a
      rw [K.embedding_other, L.embedding_other, hother]
  cases K
  cases L
  simp_all

theorem supportMatchingCandidate_ext_of_selections_eq
    (K L : SupercriticalSupportMatchingStarCandidate hk M)
    (hpart : K.part = L.part) (hedge : K.edge = L.edge)
    (hcompanion : K.companion = L.companion) (hother : K.other = L.other) :
    K = L := by
  have hemb : K.embedding = L.embedding := by
    apply Function.Embedding.ext
    intro a
    rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩
    · subst a
      rw [K.embedding_center, L.embedding_center, hedge]
    · subst a
      rw [K.embedding_witness, L.embedding_witness, hedge]
    · subst a
      rw [K.embedding_companion, L.embedding_companion, hcompanion]
    · subst a
      rw [K.embedding_other, L.embedding_other, hother]
  cases K
  cases L
  simp_all

/-- For each target role, its adapted choice-vector encoding is injective on
the exact tagged candidate family. -/
theorem matchingCandidateChoiceVector_injective
    (s : SupercriticalMatchingRandomRole k) :
    Function.Injective
      (matchingCandidateChoiceVector hk s :
        SupercriticalMatchingCandidateIndex hk M → (Fin k → Fin n)) := by
  intro K L hKL
  let x := mediumVariableXIndex hk
  have hx := congrFun hKL x
  have hanchor : K.anchor hk = L.anchor hk := by
    apply matchingAnchor_eq_of_common_endpoint M (K.anchor hk) (L.anchor hk)
      (matchingCandidateChoiceVector hk s K x)
      (matchingCandidateChoiceVector_anchor_mem hk s K)
    have hmem := matchingCandidateChoiceVector_anchor_mem hk s L
    exact hx ▸ hmem
  have hdist : (K.candidate hk).matchingDistinguishedFree hk =
      (L.candidate hk).matchingDistinguishedFree hk := by
    simpa using congrFun hKL (mediumVariableZIndex hk)
  have hother : (K.candidate hk).matchingOther hk =
      (L.candidate hk).matchingOther hk := by
    funext r
    simpa using congrFun hKL (mediumVariableOtherIndex hk r)
  have hedgeK := K.matchingEdge_eq_anchor hk
  have hedgeL := L.matchingEdge_eq_anchor hk
  have hedge : (K.candidate hk).matchingEdge hk =
      (L.candidate hk).matchingEdge hk := hedgeK.trans (hanchor.trans hedgeL.symm)
  have hcand : K.candidate hk = L.candidate hk := by
    cases hK : K.candidate hk with
    | inl A =>
        cases hL : L.candidate hk with
        | inl B =>
            apply congrArg Sum.inl
            have hpart : A.part = B.part := by
              have h := A.location_eq.symm.trans B.location_eq
              simpa using h
            apply internalMatchingCandidate_ext_of_selections_eq hk A B hpart
            · simpa [hK, hL, SupercriticalMatchingStarCandidate.matchingEdge]
                using hedge
            · simpa [hK, hL,
                SupercriticalMatchingStarCandidate.matchingDistinguishedFree]
                using hdist
            · simpa [hK, hL, SupercriticalMatchingStarCandidate.matchingOther]
                using hother
        | inr B =>
            exfalso
            have h := A.location_eq.symm.trans B.location_eq
            simp at h
    | inr A =>
        cases hL : L.candidate hk with
        | inl B =>
            exfalso
            have h := A.location_eq.symm.trans B.location_eq
            simp at h
        | inr B =>
            apply congrArg Sum.inr
            have hpart : A.part = B.part := by
              have h := A.location_eq.symm.trans B.location_eq
              simpa using h
            apply supportMatchingCandidate_ext_of_selections_eq hk A B hpart
            · simpa [hK, hL, SupercriticalMatchingStarCandidate.matchingEdge]
                using hedge
            · simpa [hK, hL,
                SupercriticalMatchingStarCandidate.matchingDistinguishedFree]
                using hdist
            · simpa [hK, hL, SupercriticalMatchingStarCandidate.matchingOther]
                using hother
  rcases K with ⟨e, K⟩
  rcases L with ⟨f, L⟩
  change e = f at hanchor
  subst f
  congr 1
  exact Subtype.ext hcand

theorem internalMatchingRandomRoleCoordinate_eq_choiceVector_map
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (A : SupercriticalInternalMatchingStarCandidate hk M)
    (hK : K.candidate hk = Sum.inl A)
    (r : SupercriticalInternalMatchingRandomRole k) :
    supercriticalProfileCoordinateSym2 D profile
        (internalMatchingRandomRoleCoordinate hk profile A r) =
      Sym2.map (matchingCandidateChoiceVector hk (Sum.inl r) K)
        s((internalMatchingRandomRoleVariableEndpoints hk r).1,
          (internalMatchingRandomRoleVariableEndpoints hk r).2) := by
  rw [internalMatchingRandomRoleCoordinate_sym2 hk profile A r]
  have hedge : A.edge = K.anchor hk := by
    have h := K.matchingEdge_eq_anchor hk
    simpa [hK, SupercriticalMatchingStarCandidate.matchingEdge] using h
  rcases r with r | r
  · simp [internalMatchingRandomRoleAbstractPair,
      internalMatchingRandomRoleVariableEndpoints,
      matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
      SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
      SupercriticalMatchingStarCandidate.matchingOther,
      hK, A.embedding_center, A.embedding_other]
  · rcases r with r | r
    · simp [internalMatchingRandomRoleAbstractPair,
        internalMatchingRandomRoleVariableEndpoints,
        matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
        SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
        SupercriticalMatchingStarCandidate.matchingOther,
        hK, A.embedding_witness, A.embedding_other, hedge]
    · rcases r with r | p
      · simp [internalMatchingRandomRoleAbstractPair,
          internalMatchingRandomRoleVariableEndpoints,
          matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
          SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
          SupercriticalMatchingStarCandidate.matchingOther,
          hK, A.embedding_companion, A.embedding_other, hedge]
      · simp [internalMatchingRandomRoleAbstractPair,
          internalMatchingRandomRoleVariableEndpoints,
          matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
          SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
          SupercriticalMatchingStarCandidate.matchingOther,
          hK, A.embedding_other]

theorem supportMatchingRandomRoleCoordinate_eq_choiceVector_map
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (A : SupercriticalSupportMatchingStarCandidate hk M)
    (hK : K.candidate hk = Sum.inr A)
    (r : SupercriticalSupportMatchingRandomRole k) :
    supercriticalProfileCoordinateSym2 D profile
        (supportMatchingRandomRoleCoordinate hk profile A r) =
      Sym2.map (matchingCandidateChoiceVector hk (Sum.inr r) K)
        s((supportMatchingRandomRoleVariableEndpoints hk r).1,
          (supportMatchingRandomRoleVariableEndpoints hk r).2) := by
  rw [supportMatchingRandomRoleCoordinate_sym2 hk profile A r]
  have hedge : A.edge = K.anchor hk := by
    have h := K.matchingEdge_eq_anchor hk
    simpa [hK, SupercriticalMatchingStarCandidate.matchingEdge] using h
  rcases r with r | r
  · simp [supportMatchingRandomRoleAbstractPair,
      supportMatchingRandomRoleVariableEndpoints,
      matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
      SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
      SupercriticalMatchingStarCandidate.matchingOther,
      hK, A.embedding_center, A.embedding_other, hedge]
  · rcases r with r | p
    · simp [supportMatchingRandomRoleAbstractPair,
        supportMatchingRandomRoleVariableEndpoints,
        matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
        SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
        SupercriticalMatchingStarCandidate.matchingOther,
        hK, A.embedding_companion, A.embedding_other]
    · simp [supportMatchingRandomRoleAbstractPair,
        supportMatchingRandomRoleVariableEndpoints,
        matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
        SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
        SupercriticalMatchingStarCandidate.matchingOther,
        hK, A.embedding_other]

end InducedStars
