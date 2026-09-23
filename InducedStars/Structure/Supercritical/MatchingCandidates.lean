import InducedStars.Structure.Supercritical.MatchingSetup
import InducedStars.Structure.Supercritical.MatchingParameters
import InducedStars.Structure.Supercritical.ProfileProbability
import InducedStars.Structure.Supercritical.MediumCandidates
import Mathlib.Tactic

/-!
# Matching-defect potential stars

This module implements the two deterministic geometries in the proof of the
supercritical matching penalty.  A homogeneous matching edge is completed to
an induced star either by using an internal missing edge as two leaves, or by
using a support--sparse edge as the center--leaf edge.  All random requirements
are tagged coordinates of the exact full-profile model.

One global orientation is used for every candidate.  In the internal geometry
the positive distinguished vertices are the unused vertices of the selected
part; in the support--sparse geometry they are the main-part endpoints of the
matching.  Complementing every other coordinate makes every candidate event a
principal up-set.
-/

noncomputable section

open Finset Set

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance matchingCandidatesPropDecidable (p : Prop) :
    Decidable p :=
  Classical.propDecidable p

/-! ## Transparent selections in the two geometries -/

/-- A potential star based at an internal edge of the homogeneous matching.
The center is an unused vertex of the same main part, and the remaining
`k-2` leaves choose one vertex from every other main part. -/
structure SupercriticalInternalMatchingStarCandidate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) where
  part : Fin (k - 1)
  location_eq : M.location = .internal part
  edge : {e : Sym2 V // e ∈ M.edges}
  center : V
  other : Fin (k - 2) → V
  center_mem : center ∈ D.parts part
  center_not_endpoint : center ∉ M.endpointFinset
  other_mem : ∀ r,
    other r ∈ D.parts (otherSupercriticalPartEquiv hk part r)
  pattern_center_first : ¬T.Adj center (M.orientedFirstEndpoint edge)
  pattern_center_second : ¬T.Adj center (M.orientedSecondEndpoint edge)
  embedding : Fin (k + 1) ↪ V
  embedding_center : embedding mediumCenterIndex = center
  embedding_witness :
    embedding (mediumWitnessIndex hk) = M.orientedFirstEndpoint edge
  embedding_companion :
    embedding (mediumCompanionIndex hk) = M.orientedSecondEndpoint edge
  embedding_other : ∀ r,
    embedding (mediumOtherLeafIndex hk r) = other r

/-- A potential star based at a support--sparse edge.  Its main endpoint is
the center; its sparse endpoint, one unused same-part vertex, and one vertex
from every other main part are the leaves. -/
structure SupercriticalSupportMatchingStarCandidate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) where
  part : Fin (k - 1)
  location_eq : M.location = .supportSparse part
  edge : {e : Sym2 V // e ∈ M.edges}
  companion : V
  other : Fin (k - 2) → V
  companion_mem : companion ∈ D.parts part
  companion_not_endpoint : companion ∉ M.endpointFinset
  other_mem : ∀ r,
    other r ∈ D.parts (otherSupercriticalPartEquiv hk part r)
  pattern_center_companion :
    ¬T.Adj (M.orientedFirstEndpoint edge) companion
  pattern_sparse_companion :
    ¬T.Adj (M.orientedSecondEndpoint edge) companion
  pattern_sparse_other : ∀ r,
    ¬T.Adj (M.orientedSecondEndpoint edge) (other r)
  embedding : Fin (k + 1) ↪ V
  embedding_center :
    embedding mediumCenterIndex = M.orientedFirstEndpoint edge
  embedding_witness :
    embedding (mediumWitnessIndex hk) = M.orientedSecondEndpoint edge
  embedding_companion :
    embedding (mediumCompanionIndex hk) = companion
  embedding_other : ∀ r,
    embedding (mediumOtherLeafIndex hk r) = other r

/-- The common tagged candidate type for the internal and support--sparse
geometries. -/
abbrev SupercriticalMatchingStarCandidate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :=
  SupercriticalInternalMatchingStarCandidate hk M ⊕
    SupercriticalSupportMatchingStarCandidate hk M

namespace SupercriticalInternalMatchingStarCandidate

variable (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
  {M : SupercriticalHomogeneousMatching k V D T}

/-- The exact pairwise-distinct vertex map selected by an internal candidate. -/
def toStarEmbedding (K : SupercriticalInternalMatchingStarCandidate hk M) :
    Fin (k + 1) ↪ V :=
  K.embedding

theorem selected_distinct (K : SupercriticalInternalMatchingStarCandidate hk M)
    {a b : Fin (k + 1)} (hab : a ≠ b) :
    K.embedding a ≠ K.embedding b :=
  K.embedding.injective.ne hab

end SupercriticalInternalMatchingStarCandidate

namespace SupercriticalSupportMatchingStarCandidate

variable (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
  {M : SupercriticalHomogeneousMatching k V D T}

/-- The exact pairwise-distinct vertex map selected by a support--sparse
candidate. -/
def toStarEmbedding (K : SupercriticalSupportMatchingStarCandidate hk M) :
    Fin (k + 1) ↪ V :=
  K.embedding

theorem selected_distinct (K : SupercriticalSupportMatchingStarCandidate hk M)
    {a b : Fin (k + 1)} (hab : a ≠ b) :
    K.embedding a ≠ K.embedding b :=
  K.embedding.injective.ne hab

end SupercriticalSupportMatchingStarCandidate

namespace SupercriticalMatchingStarCandidate

variable (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
  {M : SupercriticalHomogeneousMatching k V D T}

/-- The common exact embedding, independent of which matching geometry was
used. -/
def toStarEmbedding (K : SupercriticalMatchingStarCandidate hk M) :
    Fin (k + 1) ↪ V :=
  match K with
  | Sum.inl L => L.embedding
  | Sum.inr L => L.embedding

theorem selected_distinct (K : SupercriticalMatchingStarCandidate hk M)
    {a b : Fin (k + 1)} (hab : a ≠ b) :
    K.toStarEmbedding hk a ≠ K.toStarEmbedding hk b := by
  rcases K with K | K
  · exact K.embedding.injective.ne hab
  · exact K.embedding.injective.ne hab

end SupercriticalMatchingStarCandidate

/-! ## Matching endpoints and their deterministic pattern edge -/

namespace SupercriticalHomogeneousMatching

theorem orientedFirstEndpoint_mem_endpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e : Sym2 V // e ∈ M.edges}) :
    M.orientedFirstEndpoint e ∈ M.endpointFinset := by
  rw [M.mem_endpointFinset]
  refine ⟨e.1, e.2, ?_⟩
  rw [M.edge_eq_orientedEndpoints e]
  simp

theorem orientedSecondEndpoint_mem_endpointFinset
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e : Sym2 V // e ∈ M.edges}) :
    M.orientedSecondEndpoint e ∈ M.endpointFinset := by
  rw [M.mem_endpointFinset]
  refine ⟨e.1, e.2, ?_⟩
  rw [M.edge_eq_orientedEndpoints e]
  simp

/-- Every selected matching edge remains an edge of the displayed combined
defect pattern. -/
theorem orientedEndpoints_adj_pattern
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (e : {e : Sym2 V // e ∈ M.edges}) :
    T.Adj (M.orientedFirstEndpoint e) (M.orientedSecondEndpoint e) := by
  have he := M.edges_subset e.2
  rw [supercriticalCanonicalMatchingEdges,
    DenseGraph.mem_matchingEdgeFinset] at he
  have heSupport : e.1 ∈ (supercriticalSupportIncidentGraph D T).edgeSet :=
    (supercriticalCanonicalMatching D T).edgeSet_subset he
  rw [M.edge_eq_orientedEndpoints e] at heSupport
  apply supercriticalSupportIncidentGraph_le D T
  simpa only [SimpleGraph.mem_edgeSet] using heSupport

end SupercriticalHomogeneousMatching

/-! ## One global orientation -/

/-- The distinguished main part attached to a homogeneous matching. -/
def SupercriticalMatchingLocation.part :
    SupercriticalMatchingLocation k → Fin (k - 1)
  | .internal i => i
  | .supportSparse i => i

/-- The vertices in the distinguished part whose cross edges must be present.
For internal matching edges these are unused vertices; for support--sparse
matching edges these are exactly the main-part matching endpoints. -/
def matchingPositiveDistinguishedSet
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) : Finset V :=
  match M.location with
  | .internal i => D.parts i \ M.endpointFinset
  | .supportSparse i => D.parts i ∩ M.endpointFinset

/-- The union of all main parts other than the matching's distinguished
part. -/
def matchingOtherMainUnion
    (D : SupercriticalDivision k V) (i : Fin (k - 1)) : Finset V :=
  Finset.univ.biUnion fun j ↦ if j = i then ∅ else D.parts j

/-- Whether an unordered full-profile pair succeeds by being present.  Every
other coordinate is globally complemented. -/
def matchingSuccessPresent
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) : Sym2 V → Prop :=
  Sym2.lift ⟨fun x y ↦
      (x ∈ matchingPositiveDistinguishedSet M ∧
          y ∈ matchingOtherMainUnion D M.location.part) ∨
        (y ∈ matchingPositiveDistinguishedSet M ∧
          x ∈ matchingOtherMainUnion D M.location.part),
    by aesop⟩

/-- Present-success status of one tagged full-profile coordinate. -/
def matchingCoordinateSuccessPresent
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) : Prop :=
  matchingSuccessPresent M (supercriticalProfileCoordinateSym2 D profile c)

/-- The one global set of complemented tagged coordinates. -/
def matchingGlobalFlipSet
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D) :
    Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  Finset.univ.filter fun c ↦ ¬matchingCoordinateSuccessPresent M profile c

@[simp] theorem mem_matchingGlobalFlipSet
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    c ∈ matchingGlobalFlipSet M profile ↔
      ¬matchingCoordinateSuccessPresent M profile c := by
  simp [matchingGlobalFlipSet]

/-- Associated Bernoulli law after the matching-wide coordinate
complementation. -/
def orientedMatchingBernoulliProduct
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D) :=
  (supercriticalProfileBernoulliModel D profile).complementCoordinates
    (matchingGlobalFlipSet M profile)

@[simp] theorem orientedMatchingBernoulliProduct_probability
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (orientedMatchingBernoulliProduct M profile).probability c =
      if matchingCoordinateSuccessPresent M profile c then
        (supercriticalProfileBernoulliModel D profile).probability c
      else 1 - (supercriticalProfileBernoulliModel D profile).probability c := by
  classical
  by_cases hc : matchingCoordinateSuccessPresent M profile c <;>
    simp [orientedMatchingBernoulliProduct, hc]

/-! ## Geometry membership in the global orientation -/

theorem matchingOther_mem_union (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    (r : Fin (k - 2)) {x : V}
    (hx : x ∈ D.parts (otherSupercriticalPartEquiv hk i r)) :
    x ∈ matchingOtherMainUnion D i := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨otherSupercriticalPartEquiv hk i r, Finset.mem_univ _, ?_⟩
  simp [otherSupercriticalPartEquiv_ne hk i r, hx]

theorem internal_center_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    K.center ∈ matchingPositiveDistinguishedSet M := by
  rw [matchingPositiveDistinguishedSet, K.location_eq]
  simp [K.center_mem, K.center_not_endpoint]

theorem internal_first_not_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    M.orientedFirstEndpoint K.edge ∉ matchingPositiveDistinguishedSet M := by
  rw [matchingPositiveDistinguishedSet, K.location_eq]
  simp [M.orientedFirstEndpoint_mem_endpointFinset K.edge]

theorem internal_second_not_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    M.orientedSecondEndpoint K.edge ∉ matchingPositiveDistinguishedSet M := by
  rw [matchingPositiveDistinguishedSet, K.location_eq]
  simp [M.orientedSecondEndpoint_mem_endpointFinset K.edge]

theorem support_center_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalSupportMatchingStarCandidate hk M) :
    M.orientedFirstEndpoint K.edge ∈ matchingPositiveDistinguishedSet M := by
  rw [matchingPositiveDistinguishedSet, K.location_eq]
  exact Finset.mem_inter.mpr ⟨
    M.orientedFirstEndpoint_mem_supportPart K.location_eq K.edge,
    M.orientedFirstEndpoint_mem_endpointFinset K.edge⟩

theorem support_companion_not_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalSupportMatchingStarCandidate hk M) :
    K.companion ∉ matchingPositiveDistinguishedSet M := by
  rw [matchingPositiveDistinguishedSet, K.location_eq]
  simp [K.companion_not_endpoint]

/-- Every positive distinguished vertex lies in the part selected by the
homogeneous matching location. -/
theorem matchingPositiveDistinguishedSet_subset_part
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T) :
    matchingPositiveDistinguishedSet M ⊆ D.parts M.location.part := by
  intro x hx
  cases hloc : M.location with
  | internal i =>
      change x ∈ D.parts i
      rw [matchingPositiveDistinguishedSet, hloc] at hx
      exact (Finset.mem_sdiff.mp hx).1
  | supportSparse i =>
      change x ∈ D.parts i
      rw [matchingPositiveDistinguishedSet, hloc] at hx
      exact (Finset.mem_inter.mp hx).1

theorem internal_other_not_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (r : Fin (k - 2)) :
    K.other r ∉ matchingPositiveDistinguishedSet M := by
  intro hpos
  have hi : K.other r ∈ D.parts K.part := by
    simpa [K.location_eq, SupercriticalMatchingLocation.part] using
      matchingPositiveDistinguishedSet_subset_part M hpos
  exact (Finset.disjoint_left.mp
    (D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (otherSupercriticalPartEquiv_ne hk K.part r).symm))
    hi (K.other_mem r)

theorem support_other_not_mem_positive (hk : 3 ≤ k)
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (r : Fin (k - 2)) :
    K.other r ∉ matchingPositiveDistinguishedSet M := by
  intro hpos
  have hi : K.other r ∈ D.parts K.part := by
    simpa [K.location_eq, SupercriticalMatchingLocation.part] using
      matchingPositiveDistinguishedSet_subset_part M hpos
  exact (Finset.disjoint_left.mp
    (D.parts_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (otherSupercriticalPartEquiv_ne hk K.part r).symm))
    hi (K.other_mem r)

/-! ## Tagged random roles and required coordinates -/

/-- Random roles in an internal-edge candidate: center--other,
first-anchor--other, second-anchor--other, and other--other. -/
abbrev SupercriticalInternalMatchingRandomRole (k : ℕ) :=
  Fin (k - 2) ⊕ (Fin (k - 2) ⊕ (Fin (k - 2) ⊕
    {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2}))

/-- Random roles in a support--sparse candidate: center--other,
same-part-companion--other, and other--other. -/
abbrev SupercriticalSupportMatchingRandomRole (k : ℕ) :=
  Fin (k - 2) ⊕ (Fin (k - 2) ⊕
    {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2})

/-- Abstract star pair represented by one internal random role. -/
def internalMatchingRandomRoleAbstractPair {k : ℕ} (hk : 3 ≤ k) :
    SupercriticalInternalMatchingRandomRole k → Sym2 (Fin (k + 1))
  | Sum.inl r => s(mediumCenterIndex, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inl r) =>
      s(mediumWitnessIndex hk, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inr (Sum.inl r)) =>
      s(mediumCompanionIndex hk, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inr (Sum.inr p)) =>
      s(mediumOtherLeafIndex hk p.1.1, mediumOtherLeafIndex hk p.1.2)

/-- Abstract star pair represented by one support--sparse random role. -/
def supportMatchingRandomRoleAbstractPair {k : ℕ} (hk : 3 ≤ k) :
    SupercriticalSupportMatchingRandomRole k → Sym2 (Fin (k + 1))
  | Sum.inl r => s(mediumCenterIndex, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inl r) =>
      s(mediumCompanionIndex hk, mediumOtherLeafIndex hk r)
  | Sum.inr (Sum.inr p) =>
      s(mediumOtherLeafIndex hk p.1.1, mediumOtherLeafIndex hk p.1.2)

theorem matchingOtherParts_ne_of_lt (hk : 3 ≤ k)
    (i : Fin (k - 1))
    {r s : Fin (k - 2)} (hrs : r < s) :
    (otherSupercriticalPartEquiv hk i r : Fin (k - 1)) ≠
      otherSupercriticalPartEquiv hk i s := by
  intro h
  have hrs' : otherSupercriticalPartEquiv hk i r =
      otherSupercriticalPartEquiv hk i s := Subtype.ext h
  exact (ne_of_lt hrs) ((otherSupercriticalPartEquiv hk i).injective hrs')

/-- Tagged full-profile coordinate occupied by an internal candidate role. -/
def internalMatchingRandomRoleCoordinate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    SupercriticalInternalMatchingRandomRole k →
      (supercriticalFixedProfileBlockModel D profile).Coordinate
  | Sum.inl r =>
      supercriticalProfileCoordinateOfCrossPair D profile K.center (K.other r)
        (D.isCrossPair_of_mem_distinct_parts
          (otherSupercriticalPartEquiv_ne hk K.part r).symm
          K.center_mem (K.other_mem r))
  | Sum.inr (Sum.inl r) =>
      supercriticalProfileCoordinateOfCrossPair D profile
        (M.orientedFirstEndpoint K.edge) (K.other r)
        (D.isCrossPair_of_mem_distinct_parts
          (otherSupercriticalPartEquiv_ne hk K.part r).symm
          (M.endpoints_mem_internalPart K.location_eq K.edge).1
          (K.other_mem r))
  | Sum.inr (Sum.inr (Sum.inl r)) =>
      supercriticalProfileCoordinateOfCrossPair D profile
        (M.orientedSecondEndpoint K.edge) (K.other r)
        (D.isCrossPair_of_mem_distinct_parts
          (otherSupercriticalPartEquiv_ne hk K.part r).symm
          (M.endpoints_mem_internalPart K.location_eq K.edge).2
          (K.other_mem r))
  | Sum.inr (Sum.inr (Sum.inr p)) =>
      supercriticalProfileCoordinateOfCrossPair D profile
        (K.other p.1.1) (K.other p.1.2)
        (D.isCrossPair_of_mem_distinct_parts
          (matchingOtherParts_ne_of_lt hk K.part p.2)
          (K.other_mem p.1.1) (K.other_mem p.1.2))

/-- Tagged full-profile coordinate occupied by a support--sparse candidate
role. -/
def supportMatchingRandomRoleCoordinate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M) :
    SupercriticalSupportMatchingRandomRole k →
      (supercriticalFixedProfileBlockModel D profile).Coordinate
  | Sum.inl r =>
      supercriticalProfileCoordinateOfCrossPair D profile
        (M.orientedFirstEndpoint K.edge) (K.other r)
        (D.isCrossPair_of_mem_distinct_parts
          (otherSupercriticalPartEquiv_ne hk K.part r).symm
          (M.orientedFirstEndpoint_mem_supportPart K.location_eq K.edge)
          (K.other_mem r))
  | Sum.inr (Sum.inl r) =>
      supercriticalProfileCoordinateOfCrossPair D profile
        K.companion (K.other r)
        (D.isCrossPair_of_mem_distinct_parts
          (otherSupercriticalPartEquiv_ne hk K.part r).symm
          K.companion_mem (K.other_mem r))
  | Sum.inr (Sum.inr p) =>
      supercriticalProfileCoordinateOfCrossPair D profile
        (K.other p.1.1) (K.other p.1.2)
        (D.isCrossPair_of_mem_distinct_parts
          (matchingOtherParts_ne_of_lt hk K.part p.2)
          (K.other_mem p.1.1) (K.other_mem p.1.2))

theorem internalMatchingRandomRoleCoordinate_sym2
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (r : SupercriticalInternalMatchingRandomRole k) :
    supercriticalProfileCoordinateSym2 D profile
        (internalMatchingRandomRoleCoordinate hk profile K r) =
      Sym2.map K.embedding (internalMatchingRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · simpa [internalMatchingRandomRoleCoordinate,
      internalMatchingRandomRoleAbstractPair, K.embedding_center,
      K.embedding_other] using
      supercriticalProfileCoordinateOfCrossPair_spec D profile K.center
        (K.other r) _
  · rcases r with r | r
    · simpa [internalMatchingRandomRoleCoordinate,
        internalMatchingRandomRoleAbstractPair, K.embedding_witness,
        K.embedding_other] using
        supercriticalProfileCoordinateOfCrossPair_spec D profile
          (M.orientedFirstEndpoint K.edge) (K.other r) _
    · rcases r with r | p
      · simpa [internalMatchingRandomRoleCoordinate,
          internalMatchingRandomRoleAbstractPair, K.embedding_companion,
          K.embedding_other] using
          supercriticalProfileCoordinateOfCrossPair_spec D profile
            (M.orientedSecondEndpoint K.edge) (K.other r) _
      · simpa [internalMatchingRandomRoleCoordinate,
          internalMatchingRandomRoleAbstractPair, K.embedding_other] using
          supercriticalProfileCoordinateOfCrossPair_spec D profile
            (K.other p.1.1) (K.other p.1.2) _

theorem supportMatchingRandomRoleCoordinate_sym2
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (r : SupercriticalSupportMatchingRandomRole k) :
    supercriticalProfileCoordinateSym2 D profile
        (supportMatchingRandomRoleCoordinate hk profile K r) =
      Sym2.map K.embedding (supportMatchingRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · simpa [supportMatchingRandomRoleCoordinate,
      supportMatchingRandomRoleAbstractPair, K.embedding_center,
      K.embedding_other] using
      supercriticalProfileCoordinateOfCrossPair_spec D profile
        (M.orientedFirstEndpoint K.edge) (K.other r) _
  · rcases r with r | p
    · simpa [supportMatchingRandomRoleCoordinate,
        supportMatchingRandomRoleAbstractPair, K.embedding_companion,
        K.embedding_other] using
        supercriticalProfileCoordinateOfCrossPair_spec D profile K.companion
          (K.other r) _
    · simpa [supportMatchingRandomRoleCoordinate,
        supportMatchingRandomRoleAbstractPair, K.embedding_other] using
        supercriticalProfileCoordinateOfCrossPair_spec D profile
          (K.other p.1.1) (K.other p.1.2) _

/-- Required tagged successes for one internal candidate. -/
def internalMatchingRequiredSuccessCoordinates
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  Finset.univ.image (internalMatchingRandomRoleCoordinate hk profile K)

/-- Required tagged successes for one support--sparse candidate. -/
def supportMatchingRequiredSuccessCoordinates
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M) :
    Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  Finset.univ.image (supportMatchingRandomRoleCoordinate hk profile K)

/-- Required tagged successes for either matching geometry. -/
def matchingRequiredSuccessCoordinates
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingStarCandidate hk M) :
    Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  match K with
  | Sum.inl L => internalMatchingRequiredSuccessCoordinates hk profile L
  | Sum.inr L => supportMatchingRequiredSuccessCoordinates hk profile L

theorem internalMatchingRandomRoleCoordinate_mem_required
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (r : SupercriticalInternalMatchingRandomRole k) :
    internalMatchingRandomRoleCoordinate hk profile K r ∈
      internalMatchingRequiredSuccessCoordinates hk profile K := by
  classical
  simp [internalMatchingRequiredSuccessCoordinates]

theorem supportMatchingRandomRoleCoordinate_mem_required
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (r : SupercriticalSupportMatchingRandomRole k) :
    supportMatchingRandomRoleCoordinate hk profile K r ∈
      supportMatchingRequiredSuccessCoordinates hk profile K := by
  classical
  simp [supportMatchingRequiredSuccessCoordinates]

/-! ## Orientation and consistency -/

/-- Intended uncomplemented value of an internal random role. -/
def internalMatchingRandomRoleSuccessPresent {k : ℕ} :
    SupercriticalInternalMatchingRandomRole k → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

/-- Intended uncomplemented value of a support--sparse random role. -/
def supportMatchingRandomRoleSuccessPresent {k : ℕ} :
    SupercriticalSupportMatchingRandomRole k → Prop
  | Sum.inl _ => True
  | Sum.inr _ => False

theorem internalMatchingRandomRole_orientation
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (r : SupercriticalInternalMatchingRandomRole k) :
    matchingCoordinateSuccessPresent M profile
        (internalMatchingRandomRoleCoordinate hk profile K r) ↔
      internalMatchingRandomRoleSuccessPresent r := by
  rw [matchingCoordinateSuccessPresent,
    internalMatchingRandomRoleCoordinate_sym2 hk profile K r]
  rcases r with r | r
  · rw [internalMatchingRandomRoleAbstractPair, Sym2.map_mk,
      K.embedding_center, K.embedding_other]
    change ((_ ∧ _) ∨ (_ ∧ _)) ↔ True
    rw [iff_true]
    left
    exact ⟨internal_center_mem_positive hk K,
      by simpa [K.location_eq, SupercriticalMatchingLocation.part] using
        matchingOther_mem_union hk D K.part r (K.other_mem r)⟩
  · rcases r with r | r
    · rw [internalMatchingRandomRoleAbstractPair, Sym2.map_mk,
        K.embedding_witness, K.embedding_other]
      change ((_ ∧ _) ∨ (_ ∧ _)) ↔ False
      rw [iff_false]
      rintro (h | h)
      · exact internal_first_not_mem_positive hk K h.1
      · exact internal_other_not_mem_positive hk K r h.1
    · rcases r with r | p
      · rw [internalMatchingRandomRoleAbstractPair, Sym2.map_mk,
          K.embedding_companion, K.embedding_other]
        change ((_ ∧ _) ∨ (_ ∧ _)) ↔ False
        rw [iff_false]
        rintro (h | h)
        · exact internal_second_not_mem_positive hk K h.1
        · exact internal_other_not_mem_positive hk K r h.1
      · rw [internalMatchingRandomRoleAbstractPair, Sym2.map_mk,
          K.embedding_other p.1.1, K.embedding_other p.1.2]
        change ((_ ∧ _) ∨ (_ ∧ _)) ↔ False
        rw [iff_false]
        rintro (h | h)
        · exact internal_other_not_mem_positive hk K p.1.1 h.1
        · exact internal_other_not_mem_positive hk K p.1.2 h.1

theorem supportMatchingRandomRole_orientation
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (r : SupercriticalSupportMatchingRandomRole k) :
    matchingCoordinateSuccessPresent M profile
        (supportMatchingRandomRoleCoordinate hk profile K r) ↔
      supportMatchingRandomRoleSuccessPresent r := by
  rw [matchingCoordinateSuccessPresent,
    supportMatchingRandomRoleCoordinate_sym2 hk profile K r]
  rcases r with r | r
  · rw [supportMatchingRandomRoleAbstractPair, Sym2.map_mk,
      K.embedding_center, K.embedding_other]
    change ((_ ∧ _) ∨ (_ ∧ _)) ↔ True
    rw [iff_true]
    left
    exact ⟨support_center_mem_positive hk K,
      by simpa [K.location_eq, SupercriticalMatchingLocation.part] using
        matchingOther_mem_union hk D K.part r (K.other_mem r)⟩
  · rcases r with r | p
    · rw [supportMatchingRandomRoleAbstractPair, Sym2.map_mk,
        K.embedding_companion, K.embedding_other]
      change ((_ ∧ _) ∨ (_ ∧ _)) ↔ False
      rw [iff_false]
      rintro (h | h)
      · exact support_companion_not_mem_positive hk K h.1
      · exact support_other_not_mem_positive hk K r h.1
    · rw [supportMatchingRandomRoleAbstractPair, Sym2.map_mk,
        K.embedding_other p.1.1, K.embedding_other p.1.2]
      change ((_ ∧ _) ∨ (_ ∧ _)) ↔ False
      rw [iff_false]
      rintro (h | h)
      · exact support_other_not_mem_positive hk K p.1.1 h.1
      · exact support_other_not_mem_positive hk K p.1.2 h.1

theorem internalMatchingRandomRoleSuccessPresent_iff_star
    {k : ℕ} (hk : 3 ≤ k) (r : SupercriticalInternalMatchingRandomRole k) :
    internalMatchingRandomRoleSuccessPresent r ↔
      Sym2.lift ⟨(inducedStar k).Adj,
        fun a b ↦ propext ((inducedStar k).adj_comm a b)⟩
        (internalMatchingRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · simp [internalMatchingRandomRoleSuccessPresent,
      internalMatchingRandomRoleAbstractPair, inducedStar_adj,
      mediumCenterIndex, mediumOtherLeafIndex]
  · rcases r with r | r
    · simp [internalMatchingRandomRoleSuccessPresent,
        internalMatchingRandomRoleAbstractPair, inducedStar_adj,
        mediumWitnessIndex, mediumOtherLeafIndex]
    · rcases r with r | p
      · simp [internalMatchingRandomRoleSuccessPresent,
          internalMatchingRandomRoleAbstractPair, inducedStar_adj,
          mediumCompanionIndex, mediumOtherLeafIndex]
      · simp [internalMatchingRandomRoleSuccessPresent,
          internalMatchingRandomRoleAbstractPair, inducedStar_adj,
          mediumOtherLeafIndex]

theorem supportMatchingRandomRoleSuccessPresent_iff_star
    {k : ℕ} (hk : 3 ≤ k) (r : SupercriticalSupportMatchingRandomRole k) :
    supportMatchingRandomRoleSuccessPresent r ↔
      Sym2.lift ⟨(inducedStar k).Adj,
        fun a b ↦ propext ((inducedStar k).adj_comm a b)⟩
        (supportMatchingRandomRoleAbstractPair hk r) := by
  rcases r with r | r
  · simp [supportMatchingRandomRoleSuccessPresent,
      supportMatchingRandomRoleAbstractPair, inducedStar_adj,
      mediumCenterIndex, mediumOtherLeafIndex]
  · rcases r with r | p
    · simp [supportMatchingRandomRoleSuccessPresent,
        supportMatchingRandomRoleAbstractPair, inducedStar_adj,
        mediumCompanionIndex, mediumOtherLeafIndex]
    · simp [supportMatchingRandomRoleSuccessPresent,
        supportMatchingRandomRoleAbstractPair, inducedStar_adj,
        mediumOtherLeafIndex]

/-- Shared tagged coordinates have a candidate-independent orientation. -/
theorem matchingSharedCoordinate_orientation_compatible
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    {c d : (supercriticalFixedProfileBlockModel D profile).Coordinate}
    (hcd : c = d) :
    (matchingCoordinateSuccessPresent M profile c ↔
      matchingCoordinateSuccessPresent M profile d) := by
  subst d
  rfl

/-- Two internal roles sharing a tagged coordinate prescribe the same
uncomplemented edge value. -/
theorem internalMatchingSharedRole_orientation_compatible
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalInternalMatchingStarCandidate hk M)
    (r s : SupercriticalInternalMatchingRandomRole k)
    (hrs : internalMatchingRandomRoleCoordinate hk profile K r =
      internalMatchingRandomRoleCoordinate hk profile L s) :
    (internalMatchingRandomRoleSuccessPresent r ↔
      internalMatchingRandomRoleSuccessPresent s) := by
  rw [← internalMatchingRandomRole_orientation hk profile K r,
    hrs, internalMatchingRandomRole_orientation hk profile L s]

/-- Two support--sparse roles sharing a tagged coordinate prescribe the same
uncomplemented edge value. -/
theorem supportMatchingSharedRole_orientation_compatible
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalSupportMatchingStarCandidate hk M)
    (r s : SupercriticalSupportMatchingRandomRole k)
    (hrs : supportMatchingRandomRoleCoordinate hk profile K r =
      supportMatchingRandomRoleCoordinate hk profile L s) :
    (supportMatchingRandomRoleSuccessPresent r ↔
      supportMatchingRandomRoleSuccessPresent s) := by
  rw [← supportMatchingRandomRole_orientation hk profile K r,
    hrs, supportMatchingRandomRole_orientation hk profile L s]

/-- Orientation is also consistent when an internal and a support--sparse
candidate happen to share a tagged coordinate. -/
theorem internalSupportMatchingSharedRole_orientation_compatible
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (L : SupercriticalSupportMatchingStarCandidate hk M)
    (r : SupercriticalInternalMatchingRandomRole k)
    (s : SupercriticalSupportMatchingRandomRole k)
    (hrs : internalMatchingRandomRoleCoordinate hk profile K r =
      supportMatchingRandomRoleCoordinate hk profile L s) :
    (internalMatchingRandomRoleSuccessPresent r ↔
      supportMatchingRandomRoleSuccessPresent s) := by
  rw [← internalMatchingRandomRole_orientation hk profile K r,
    hrs, supportMatchingRandomRole_orientation hk profile L s]

/-- Robust constant-only support bound for an internal event. -/
theorem internalMatchingRequiredSuccessCoordinates_card_le
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M) :
    (internalMatchingRequiredSuccessCoordinates hk profile K).card ≤
      3 * (k - 2) + (k - 2) ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (SupercriticalInternalMatchingRandomRole k) := by
      simpa [internalMatchingRequiredSuccessCoordinates] using
        (Finset.card_image_le :
          (Finset.univ.image
            (internalMatchingRandomRoleCoordinate hk profile K)).card ≤
          (Finset.univ :
            Finset (SupercriticalInternalMatchingRandomRole k)).card)
    _ ≤ 3 * (k - 2) + (k - 2) ^ 2 := by
      simp only [SupercriticalInternalMatchingRandomRole, Fintype.card_sum,
        Fintype.card_fin]
      have hpairs : Fintype.card
          {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
          Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      simp only [Fintype.card_prod, Fintype.card_fin] at hpairs ⊢
      simp only [pow_two] at hpairs ⊢
      omega

/-- Robust constant-only support bound for a support--sparse event. -/
theorem supportMatchingRequiredSuccessCoordinates_card_le
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M) :
    (supportMatchingRequiredSuccessCoordinates hk profile K).card ≤
      3 * (k - 2) + (k - 2) ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (SupercriticalSupportMatchingRandomRole k) := by
      simpa [supportMatchingRequiredSuccessCoordinates] using
        (Finset.card_image_le :
          (Finset.univ.image
            (supportMatchingRandomRoleCoordinate hk profile K)).card ≤
          (Finset.univ :
            Finset (SupercriticalSupportMatchingRandomRole k)).card)
    _ ≤ 3 * (k - 2) + (k - 2) ^ 2 := by
      simp only [SupercriticalSupportMatchingRandomRole, Fintype.card_sum,
        Fintype.card_fin]
      have hpairs : Fintype.card
          {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
          Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
        Fintype.card_le_of_injective Subtype.val Subtype.val_injective
      simp only [Fintype.card_prod, Fintype.card_fin] at hpairs ⊢
      simp only [pow_two] at hpairs ⊢
      omega

/-- Uniform support bound for either matching geometry. -/
theorem matchingRequiredSuccessCoordinates_card_le
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingStarCandidate hk M) :
    (matchingRequiredSuccessCoordinates hk profile K).card ≤
      3 * (k - 2) + (k - 2) ^ 2 := by
  rcases K with K | K
  · exact internalMatchingRequiredSuccessCoordinates_card_le hk profile K
  · exact supportMatchingRequiredSuccessCoordinates_card_le hk profile K

theorem matchingRequiredSuccessCoordinates_card_le_roleBound
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingStarCandidate hk M) :
    (matchingRequiredSuccessCoordinates hk profile K).card ≤
      supercriticalMatchingRandomRoleBound k :=
  matchingRequiredSuccessCoordinates_card_le hk profile K

/-! ## Decoding globally oriented successes -/

theorem SupercriticalDivision.not_isCrossPair_of_mem_same_part
    (D : SupercriticalDivision k V) (i : Fin (k - 1))
    {x y : V} (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    ¬D.IsCrossPair x y := by
  rintro ⟨e, h | h⟩
  · exact e.left_ne_right
      ((D.mem_part_unique h.1 hx).trans (D.mem_part_unique h.2 hy).symm)
  · exact e.left_ne_right
      ((D.mem_part_unique h.1 hy).trans (D.mem_part_unique h.2 hx).symm)

theorem SupercriticalDivision.not_isCrossPair_support_sparse
    (D : SupercriticalDivision k V) {x y : V}
    (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    ¬D.IsCrossPair x y := by
  rintro ⟨e, h | h⟩
  · exact (SupercriticalDivision.mem_sparse.mp hy)
      (D.part_subset_support e.right h.2)
  · exact (SupercriticalDivision.mem_sparse.mp hy)
      (D.part_subset_support e.left h.1)

theorem supercriticalGraphFromDefectPattern_adj_of_mem_same_part
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (i : Fin (k - 1)) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    (supercriticalGraphFromDefectPattern D T).Adj x y ↔
      x ≠ y ∧ ¬T.Adj x y := by
  rw [supercriticalGraphFromDefectPattern_adj]
  have hsame : D.SameMainPart x y := ⟨i, hx, hy⟩
  have hxs : x ∈ D.support := D.part_subset_support i hx
  have hys : y ∈ D.support := D.part_subset_support i hy
  have hxns : x ∉ D.sparse := by simpa using hxs
  have hyns : y ∉ D.sparse := by simpa using hys
  simp [hsame, SupercriticalDivision.IsSupportSparsePair,
    hxs, hys, hxns, hyns]

theorem supercriticalGraphFromDefectPattern_adj_support_sparse
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    (supercriticalGraphFromDefectPattern D T).Adj x y ↔ T.Adj x y := by
  rw [supercriticalGraphFromDefectPattern_adj]
  have hne : x ≠ y := fun h ↦
    (SupercriticalDivision.mem_sparse.mp hy) (h ▸ hx)
  have hsame : ¬D.SameMainPart x y := fun h ↦
    (SupercriticalDivision.mem_sparse.mp hy)
      (D.sameMainPart_imp_support h).2
  have hxns : x ∉ D.sparse := by simpa using hx
  simp [hne, hsame, SupercriticalDivision.IsSupportSparsePair,
    hx, hy, hxns]

theorem supercriticalGraphFromCrossOutcome_adj_of_mem_same_part
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (i : Fin (k - 1)) {x y : V}
    (hx : x ∈ D.parts i) (hy : y ∈ D.parts i) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      x ≠ y ∧ ¬T.Adj x y := by
  rw [supercriticalGraphFromCrossOutcome_adj_of_not_cross D T profile outcome
      (D.not_isCrossPair_of_mem_same_part i hx hy),
    supercriticalGraphFromDefectPattern_adj_of_mem_same_part D T i hx hy]

theorem supercriticalGraphFromCrossOutcome_adj_support_sparse
    (D : SupercriticalDivision k V) (T : SimpleGraph V)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V} (hx : x ∈ D.support) (hy : y ∈ D.sparse) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      T.Adj x y := by
  rw [supercriticalGraphFromCrossOutcome_adj_of_not_cross D T profile outcome
      (D.not_isCrossPair_support_sparse hx hy),
    supercriticalGraphFromDefectPattern_adj_support_sparse D T hx hy]

/-- An actual outcome has the prescribed uncomplemented value at every
coordinate that succeeds in the globally flipped outcome. -/
theorem matchingCoordinate_mem_outcome_iff_success_of_mem_flipped
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hc : c ∈ DenseGraph.FiniteBernoulliProduct.flipOutcome
      (matchingGlobalFlipSet M profile) outcome) :
    (c ∈ outcome ↔ matchingCoordinateSuccessPresent M profile c) := by
  rw [DenseGraph.FiniteBernoulliProduct.mem_flipOutcome] at hc
  by_cases hs : matchingCoordinateSuccessPresent M profile c
  · have hnf : c ∉ matchingGlobalFlipSet M profile := by simp [hs]
    have hout : c ∈ outcome := by
      rcases hc with h | h
      · exact h.1
      · exact False.elim (hnf h.1)
    simp [hs, hout]
  · have hf : c ∈ matchingGlobalFlipSet M profile := by simp [hs]
    have hout : c ∉ outcome := by
      rcases hc with h | h
      · exact False.elim (h.2 hf)
      · exact h.2
    simp [hs, hout]

theorem supercriticalProfileCoordinate_isCrossPair
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    D.IsCrossPair c.2.1.1 c.2.1.2 := by
  rcases c with ⟨e, xy⟩
  have hxy : xy.1.1 ∈ D.parts e.left ∧
      xy.1.2 ∈ D.parts e.right := by
    simpa using xy.2
  exact ⟨e, Or.inl hxy⟩

theorem isCrossPair_of_profileCoordinateSym2_eq
    (D : SupercriticalDivision k V) (profile : SupercriticalEdgeProfile D)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V}
    (hc : supercriticalProfileCoordinateSym2 D profile c = s(x, y)) :
    D.IsCrossPair x y := by
  have hcross := supercriticalProfileCoordinate_isCrossPair D profile c
  rcases Sym2.eq_iff.mp hc with h | h
  · simpa [h.1, h.2] using hcross
  · rw [← D.isCrossPair_comm]
    simpa [h.1, h.2] using hcross

/-- A successful flipped coordinate decodes to the global present/absent
orientation in the realized graph. -/
theorem supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate)
    {x y : V}
    (hpair : supercriticalProfileCoordinateSym2 D profile c = s(x, y))
    (hc : c ∈ DenseGraph.FiniteBernoulliProduct.flipOutcome
      (matchingGlobalFlipSet M profile) outcome) :
    ((supercriticalGraphFromCrossOutcome D T profile outcome).Adj x y ↔
      matchingCoordinateSuccessPresent M profile c) := by
  have hcross := isCrossPair_of_profileCoordinateSym2_eq D profile c hpair
  rw [supercriticalGraphFromCrossOutcome_adj_of_cross D T profile outcome hcross,
    supercriticalProfileIsSelectedTaggedPair_iff_coordinate_mem
      D profile outcome hcross]
  have hcEq : supercriticalProfileCoordinateOfCrossPair D profile x y hcross = c :=
    supercriticalProfileCoordinateSym2_injective D profile
      ((supercriticalProfileCoordinateOfCrossPair_spec D profile x y hcross).trans
        hpair.symm)
  rw [hcEq]
  exact matchingCoordinate_mem_outcome_iff_success_of_mem_flipped
    M profile outcome c hc

/-- Every internal random role is decoded as exactly its abstract star
edge/nonedge once its oriented coordinate succeeds. -/
theorem internalMatchingRandomRole_realized
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hsuccess : internalMatchingRequiredSuccessCoordinates hk profile K ⊆
      DenseGraph.FiniteBernoulliProduct.flipOutcome
        (matchingGlobalFlipSet M profile) outcome)
    (r : SupercriticalInternalMatchingRandomRole k) :
    Sym2.lift ⟨fun a b ↦
        (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
          (K.embedding a) (K.embedding b),
      fun a b ↦ propext
        ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm _ _)⟩
        (internalMatchingRandomRoleAbstractPair hk r) ↔
      Sym2.lift ⟨(inducedStar k).Adj,
        fun a b ↦ propext ((inducedStar k).adj_comm a b)⟩
        (internalMatchingRandomRoleAbstractPair hk r) := by
  let c := internalMatchingRandomRoleCoordinate hk profile K r
  have hc : c ∈ DenseGraph.FiniteBernoulliProduct.flipOutcome
      (matchingGlobalFlipSet M profile) outcome :=
    hsuccess (internalMatchingRandomRoleCoordinate_mem_required
      hk profile K r)
  have hpair := internalMatchingRandomRoleCoordinate_sym2 hk profile K r
  rcases r with r | r
  · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
      M profile outcome c hpair hc).trans
      ((internalMatchingRandomRole_orientation hk profile K (Sum.inl r)).trans
        (internalMatchingRandomRoleSuccessPresent_iff_star hk (Sum.inl r)))
  · rcases r with r | r
    · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
        M profile outcome c hpair hc).trans
        ((internalMatchingRandomRole_orientation hk profile K
          (Sum.inr (Sum.inl r))).trans
          (internalMatchingRandomRoleSuccessPresent_iff_star hk
            (Sum.inr (Sum.inl r))))
    · rcases r with r | p
      · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
          M profile outcome c hpair hc).trans
          ((internalMatchingRandomRole_orientation hk profile K
            (Sum.inr (Sum.inr (Sum.inl r)))).trans
            (internalMatchingRandomRoleSuccessPresent_iff_star hk
              (Sum.inr (Sum.inr (Sum.inl r)))))
      · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
          M profile outcome c hpair hc).trans
          ((internalMatchingRandomRole_orientation hk profile K
            (Sum.inr (Sum.inr (Sum.inr p)))).trans
            (internalMatchingRandomRoleSuccessPresent_iff_star hk
              (Sum.inr (Sum.inr (Sum.inr p)))))

/-- Every support--sparse random role is decoded as exactly its abstract star
edge/nonedge once its oriented coordinate succeeds. -/
theorem supportMatchingRandomRole_realized
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hsuccess : supportMatchingRequiredSuccessCoordinates hk profile K ⊆
      DenseGraph.FiniteBernoulliProduct.flipOutcome
        (matchingGlobalFlipSet M profile) outcome)
    (r : SupercriticalSupportMatchingRandomRole k) :
    Sym2.lift ⟨fun a b ↦
        (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
          (K.embedding a) (K.embedding b),
      fun a b ↦ propext
        ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm _ _)⟩
        (supportMatchingRandomRoleAbstractPair hk r) ↔
      Sym2.lift ⟨(inducedStar k).Adj,
        fun a b ↦ propext ((inducedStar k).adj_comm a b)⟩
        (supportMatchingRandomRoleAbstractPair hk r) := by
  let c := supportMatchingRandomRoleCoordinate hk profile K r
  have hc : c ∈ DenseGraph.FiniteBernoulliProduct.flipOutcome
      (matchingGlobalFlipSet M profile) outcome :=
    hsuccess (supportMatchingRandomRoleCoordinate_mem_required hk profile K r)
  have hpair := supportMatchingRandomRoleCoordinate_sym2 hk profile K r
  rcases r with r | r
  · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
      M profile outcome c hpair hc).trans
      ((supportMatchingRandomRole_orientation hk profile K (Sum.inl r)).trans
        (supportMatchingRandomRoleSuccessPresent_iff_star hk (Sum.inl r)))
  · rcases r with r | p
    · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
        M profile outcome c hpair hc).trans
        ((supportMatchingRandomRole_orientation hk profile K
          (Sum.inr (Sum.inl r))).trans
          (supportMatchingRandomRoleSuccessPresent_iff_star hk
            (Sum.inr (Sum.inl r))))
    · exact (supercriticalGraphFromCrossOutcome_adj_iff_matchingSuccess
        M profile outcome c hpair hc).trans
        ((supportMatchingRandomRole_orientation hk profile K
          (Sum.inr (Sum.inr p))).trans
          (supportMatchingRandomRoleSuccessPresent_iff_star hk
            (Sum.inr (Sum.inr p))))

/-! ## Deterministic pairs in the two candidate geometries -/

theorem internalMatchingCandidate_center_witness
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding mediumCenterIndex)
      (K.embedding (mediumWitnessIndex hk)) := by
  rw [K.embedding_center, K.embedding_witness,
    supercriticalGraphFromCrossOutcome_adj_of_mem_same_part
      D T profile outcome K.part K.center_mem
        (M.endpoints_mem_internalPart K.location_eq K.edge).1]
  have hneEmbed : K.embedding mediumCenterIndex ≠
      K.embedding (mediumWitnessIndex hk) :=
    K.embedding.injective.ne (by
      simp [mediumCenterIndex, mediumWitnessIndex])
  have hne : K.center ≠ M.orientedFirstEndpoint K.edge := by
    simpa only [K.embedding_center, K.embedding_witness] using hneEmbed
  exact ⟨hne, K.pattern_center_first⟩

theorem internalMatchingCandidate_center_companion
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding mediumCenterIndex)
      (K.embedding (mediumCompanionIndex hk)) := by
  rw [K.embedding_center, K.embedding_companion,
    supercriticalGraphFromCrossOutcome_adj_of_mem_same_part
      D T profile outcome K.part K.center_mem
        (M.endpoints_mem_internalPart K.location_eq K.edge).2]
  have hneEmbed : K.embedding mediumCenterIndex ≠
      K.embedding (mediumCompanionIndex hk) :=
    K.embedding.injective.ne (by
      simp [mediumCenterIndex, mediumCompanionIndex])
  have hne : K.center ≠ M.orientedSecondEndpoint K.edge := by
    simpa only [K.embedding_center, K.embedding_companion] using hneEmbed
  exact ⟨hne, K.pattern_center_second⟩

theorem internalMatchingCandidate_witness_companion_nonadj
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    ¬(supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding (mediumWitnessIndex hk))
      (K.embedding (mediumCompanionIndex hk)) := by
  rw [K.embedding_witness, K.embedding_companion,
    supercriticalGraphFromCrossOutcome_adj_of_mem_same_part
      D T profile outcome K.part
        (M.endpoints_mem_internalPart K.location_eq K.edge).1
        (M.endpoints_mem_internalPart K.location_eq K.edge).2]
  exact fun h ↦ h.2 (M.orientedEndpoints_adj_pattern K.edge)

theorem supportMatchingCandidate_center_witness
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding mediumCenterIndex)
      (K.embedding (mediumWitnessIndex hk)) := by
  rw [K.embedding_center, K.embedding_witness,
    supercriticalGraphFromCrossOutcome_adj_support_sparse
      D T profile outcome
        (D.part_subset_support K.part
          (M.orientedFirstEndpoint_mem_supportPart K.location_eq K.edge))
        (M.orientedSecondEndpoint_mem_sparse K.location_eq K.edge)]
  exact M.orientedEndpoints_adj_pattern K.edge

theorem supportMatchingCandidate_center_companion
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding mediumCenterIndex)
      (K.embedding (mediumCompanionIndex hk)) := by
  rw [K.embedding_center, K.embedding_companion,
    supercriticalGraphFromCrossOutcome_adj_of_mem_same_part
      D T profile outcome K.part
        (M.orientedFirstEndpoint_mem_supportPart K.location_eq K.edge)
        K.companion_mem]
  have hneEmbed : K.embedding mediumCenterIndex ≠
      K.embedding (mediumCompanionIndex hk) :=
    K.embedding.injective.ne (by
      simp [mediumCenterIndex, mediumCompanionIndex])
  have hne : M.orientedFirstEndpoint K.edge ≠ K.companion := by
    simpa only [K.embedding_center, K.embedding_companion] using hneEmbed
  exact ⟨hne, K.pattern_center_companion⟩

theorem supportMatchingCandidate_witness_companion_nonadj
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    ¬(supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding (mediumWitnessIndex hk))
      (K.embedding (mediumCompanionIndex hk)) := by
  rw [K.embedding_witness, K.embedding_companion]
  intro h
  have h' := ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm
    _ _).mp h
  have hT := (supercriticalGraphFromCrossOutcome_adj_support_sparse
    D T profile outcome (D.part_subset_support K.part K.companion_mem)
      (M.orientedSecondEndpoint_mem_sparse K.location_eq K.edge)).mp h'
  exact K.pattern_sparse_companion ((T.adj_comm _ _).mp hT)

theorem supportMatchingCandidate_witness_other_nonadj
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (r : Fin (k - 2)) :
    ¬(supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding (mediumWitnessIndex hk))
      (K.embedding (mediumOtherLeafIndex hk r)) := by
  rw [K.embedding_witness, K.embedding_other]
  intro h
  have h' := ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm
    _ _).mp h
  have hT := (supercriticalGraphFromCrossOutcome_adj_support_sparse
    D T profile outcome
      (D.part_subset_support (otherSupercriticalPartEquiv hk K.part r)
        (K.other_mem r))
      (M.orientedSecondEndpoint_mem_sparse K.location_eq K.edge)).mp h'
  exact K.pattern_sparse_other r ((T.adj_comm _ _).mp hT)

/-! ## Successful candidates are induced stars -/

theorem internalMatchingPotentialSuccess_inducedStar
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalInternalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hsuccess : internalMatchingRequiredSuccessCoordinates hk profile K ⊆
      DenseGraph.FiniteBernoulliProduct.flipOutcome
        (matchingGlobalFlipSet M profile) outcome) :
    Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome) := by
  classical
  refine ⟨{
    toFun := K.embedding
    inj' := K.embedding.injective
    map_rel_iff' := ?_ }⟩
  intro a b
  change (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding a) (K.embedding b) ↔ (inducedStar k).Adj a b
  rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩ <;>
    rcases mediumStarIndex_cases hk b with hb | hb | hb | ⟨t, hb⟩ <;>
    subst a <;> subst b
  · simp
  · simpa [inducedStar_adj, mediumCenterIndex, mediumWitnessIndex] using
      internalMatchingCandidate_center_witness hk profile K outcome
  · simpa [inducedStar_adj, mediumCenterIndex, mediumCompanionIndex] using
      internalMatchingCandidate_center_companion hk profile K outcome
  · simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inl t)
  · simpa [inducedStar_adj, mediumCenterIndex, mediumWitnessIndex] using
      (internalMatchingCandidate_center_witness hk profile K outcome).symm
  · simp
  · simpa [inducedStar_adj, mediumWitnessIndex, mediumCompanionIndex] using
      internalMatchingCandidate_witness_companion_nonadj hk profile K outcome
  · simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inl t))
  · simpa [inducedStar_adj, mediumCenterIndex, mediumCompanionIndex] using
      (internalMatchingCandidate_center_companion hk profile K outcome).symm
  · constructor
    · intro h
      exact (internalMatchingCandidate_witness_companion_nonadj
        hk profile K outcome
        ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm
          _ _ |>.mp h)).elim
    · intro hstar
      exfalso
      simpa [inducedStar_adj, mediumCompanionIndex, mediumWitnessIndex] using hstar
  · simp
  · simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inr (Sum.inl t)))
  · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
      (inducedStar k).adj_comm]
    simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inl r)
  · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
      (inducedStar k).adj_comm]
    simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inl r))
  · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
      (inducedStar k).adj_comm]
    simpa [internalMatchingRandomRoleAbstractPair] using
      internalMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inr (Sum.inl r)))
  · by_cases hrt : r = t
    · subst t
      simp
    · rcases lt_or_gt_of_ne hrt with hlt | hgt
      · simpa [internalMatchingRandomRoleAbstractPair] using
          internalMatchingRandomRole_realized hk profile K outcome hsuccess
            (Sum.inr (Sum.inr (Sum.inr ⟨(r, t), hlt⟩)))
      · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
          (inducedStar k).adj_comm]
        simpa [internalMatchingRandomRoleAbstractPair] using
          internalMatchingRandomRole_realized hk profile K outcome hsuccess
            (Sum.inr (Sum.inr (Sum.inr ⟨(t, r), hgt⟩)))

theorem supportMatchingPotentialSuccess_inducedStar
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalSupportMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hsuccess : supportMatchingRequiredSuccessCoordinates hk profile K ⊆
      DenseGraph.FiniteBernoulliProduct.flipOutcome
        (matchingGlobalFlipSet M profile) outcome) :
    Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome) := by
  classical
  refine ⟨{
    toFun := K.embedding
    inj' := K.embedding.injective
    map_rel_iff' := ?_ }⟩
  intro a b
  change (supercriticalGraphFromCrossOutcome D T profile outcome).Adj
      (K.embedding a) (K.embedding b) ↔ (inducedStar k).Adj a b
  rcases mediumStarIndex_cases hk a with ha | ha | ha | ⟨r, ha⟩ <;>
    rcases mediumStarIndex_cases hk b with hb | hb | hb | ⟨t, hb⟩ <;>
    subst a <;> subst b
  · simp
  · simpa [inducedStar_adj, mediumCenterIndex, mediumWitnessIndex] using
      supportMatchingCandidate_center_witness hk profile K outcome
  · simpa [inducedStar_adj, mediumCenterIndex, mediumCompanionIndex] using
      supportMatchingCandidate_center_companion hk profile K outcome
  · simpa [supportMatchingRandomRoleAbstractPair] using
      supportMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inl t)
  · simpa [inducedStar_adj, mediumCenterIndex, mediumWitnessIndex] using
      (supportMatchingCandidate_center_witness hk profile K outcome).symm
  · simp
  · simpa [inducedStar_adj, mediumWitnessIndex, mediumCompanionIndex] using
      supportMatchingCandidate_witness_companion_nonadj hk profile K outcome
  · simpa [inducedStar_adj, mediumWitnessIndex, mediumOtherLeafIndex] using
      supportMatchingCandidate_witness_other_nonadj hk profile K outcome t
  · simpa [inducedStar_adj, mediumCenterIndex, mediumCompanionIndex] using
      (supportMatchingCandidate_center_companion hk profile K outcome).symm
  · constructor
    · intro h
      exact (supportMatchingCandidate_witness_companion_nonadj
        hk profile K outcome
        ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm
          _ _ |>.mp h)).elim
    · intro hstar
      exfalso
      simpa [inducedStar_adj, mediumCompanionIndex, mediumWitnessIndex] using hstar
  · simp
  · simpa [supportMatchingRandomRoleAbstractPair] using
      supportMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inl t))
  · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
      (inducedStar k).adj_comm]
    simpa [supportMatchingRandomRoleAbstractPair] using
      supportMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inl r)
  · have hnon := supportMatchingCandidate_witness_other_nonadj
        hk profile K outcome r
    constructor
    · intro h
      exact hnon
        ((supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm
          _ _ |>.mp h) |>.elim
    · intro hstar
      exfalso
      simpa [inducedStar_adj, mediumOtherLeafIndex, mediumWitnessIndex] using hstar
  · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
      (inducedStar k).adj_comm]
    simpa [supportMatchingRandomRoleAbstractPair] using
      supportMatchingRandomRole_realized hk profile K outcome hsuccess
        (Sum.inr (Sum.inl r))
  · by_cases hrt : r = t
    · subst t
      simp
    · rcases lt_or_gt_of_ne hrt with hlt | hgt
      · simpa [supportMatchingRandomRoleAbstractPair] using
          supportMatchingRandomRole_realized hk profile K outcome hsuccess
            (Sum.inr (Sum.inr ⟨(r, t), hlt⟩))
      · rw [(supercriticalGraphFromCrossOutcome D T profile outcome).adj_comm,
          (inducedStar k).adj_comm]
        simpa [supportMatchingRandomRoleAbstractPair] using
          supportMatchingRandomRole_realized hk profile K outcome hsuccess
            (Sum.inr (Sum.inr ⟨(t, r), hgt⟩))

/-- Common candidate-to-induced-star bridge for both matching geometries. -/
theorem matchingPotentialSuccess_inducedStar
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hsuccess : matchingRequiredSuccessCoordinates hk profile K ⊆
      DenseGraph.FiniteBernoulliProduct.flipOutcome
        (matchingGlobalFlipSet M profile) outcome) :
    Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome) := by
  rcases K with K | K
  · exact internalMatchingPotentialSuccess_inducedStar
      hk profile K outcome hsuccess
  · exact supportMatchingPotentialSuccess_inducedStar
      hk profile K outcome hsuccess

/-! ## Principal avoidance consequences -/

/-- The globally oriented version of an actual full-profile outcome. -/
def matchingOrientedOutcome
    {D : SupercriticalDivision k V} {T : SimpleGraph V}
    (M : SupercriticalHomogeneousMatching k V D T)
    (profile : SupercriticalEdgeProfile D)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate) :
    Finset (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  DenseGraph.FiniteBernoulliProduct.flipOutcome
    (matchingGlobalFlipSet M profile) outcome

/-- An induced-star-free realized graph avoids the principal success event
of every individual matching candidate. -/
theorem inducedStarFree_implies_matchingCandidateAvoidance
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome)) :
    ¬matchingRequiredSuccessCoordinates hk profile K ⊆
      matchingOrientedOutcome M profile outcome := by
  intro hsuccess
  exact hfree (matchingPotentialSuccess_inducedStar
    hk profile K outcome hsuccess)

/-- Simultaneous principal-avoidance form for any finite indexed family of
matching candidates. -/
theorem inducedStarFree_implies_matchingPrincipalAvoidance
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    {I : Type*} [Fintype I] [LinearOrder I]
    (K : I → SupercriticalMatchingStarCandidate hk M)
    (outcome : Finset
      (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k)
      (supercriticalGraphFromCrossOutcome D T profile outcome)) :
    matchingOrientedOutcome M profile outcome ∈
      DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
        (fun i ↦ matchingRequiredSuccessCoordinates hk profile (K i)) := by
  rw [DenseGraph.FiniteBernoulliProduct.mem_principalAvoidanceEvent]
  intro i
  exact inducedStarFree_implies_matchingCandidateAvoidance
    hk profile (K i) outcome hfree

/-- Exact tagged-coordinate dependency predicate used by Janson. -/
def MatchingCandidatesShareRandomCoordinate
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalMatchingStarCandidate hk M) : Prop :=
  ¬Disjoint (matchingRequiredSuccessCoordinates hk profile K)
    (matchingRequiredSuccessCoordinates hk profile L)

@[simp] theorem matchingCandidatesShareRandomCoordinate_iff
    (hk : 3 ≤ k) {D : SupercriticalDivision k V} {T : SimpleGraph V}
    {M : SupercriticalHomogeneousMatching k V D T}
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalMatchingStarCandidate hk M) :
    MatchingCandidatesShareRandomCoordinate hk profile K L ↔
      ¬Disjoint (matchingRequiredSuccessCoordinates hk profile K)
        (matchingRequiredSuccessCoordinates hk profile L) :=
  Iff.rfl

end InducedStars
