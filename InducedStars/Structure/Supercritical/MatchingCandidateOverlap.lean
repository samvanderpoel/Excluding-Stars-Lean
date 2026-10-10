import InducedStars.Structure.Supercritical.MatchingCandidateCounting

/-!
# Fallback overlap enumeration for matching candidates

This module gives an independent implementation of the matching-candidate
overlap count.  A role-adapted choice vector records one endpoint of the
matching anchor and the `k - 1` freely selected vertices.  Fixing one random
coordinate fixes two distinct entries of this vector, leaving at most
`2 * n^(k-2)` choices.
-/

noncomputable section

open Finset Set

namespace InducedStars

variable {k n : ℕ} (hk : 3 ≤ k)
  {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
  {M : SupercriticalHomogeneousMatching k (Fin n) D T}

/-! The injective role-adapted choice vector itself is supplied by
`MatchingCandidateCounting`; this file independently counts its coordinate
fibers and assembles the overlap graph. -/

/-! ## A common partial role-coordinate map -/

/-- A common role is active only in the geometry to which its outer tag
belongs. -/
def matchingCandidateRoleCoordinateFallback
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (r : SupercriticalMatchingRandomRole k) :
    Option (supercriticalFixedProfileBlockModel D profile).Coordinate :=
  match K.candidate hk, r with
  | Sum.inl A, Sum.inl s =>
      some (internalMatchingRandomRoleCoordinate hk profile A s)
  | Sum.inr A, Sum.inr s =>
      some (supportMatchingRandomRoleCoordinate hk profile A s)
  | _, _ => none

/-- The two role-adapted choice-vector entries occupied by a common role. -/
def matchingRandomRoleVariableEndpointsFallback :
    SupercriticalMatchingRandomRole k → Fin k × Fin k
  | Sum.inl r => internalMatchingRandomRoleVariableEndpoints hk r
  | Sum.inr r => supportMatchingRandomRoleVariableEndpoints hk r

theorem matchingRandomRoleVariableEndpointsFallback_ne
    (r : SupercriticalMatchingRandomRole k) :
    (matchingRandomRoleVariableEndpointsFallback hk r).1 ≠
      (matchingRandomRoleVariableEndpointsFallback hk r).2 := by
  rcases r with r | r
  · exact internalMatchingRandomRoleVariableEndpoints_ne hk r
  · exact supportMatchingRandomRoleVariableEndpoints_ne hk r

/-- Whenever the common role is active, its tagged graph coordinate is the
unordered pair of the two advertised choice-vector entries. -/
theorem matchingCandidateRoleCoordinateFallback_sym2
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (r : SupercriticalMatchingRandomRole k)
    (c : (supercriticalFixedProfileBlockModel D profile).Coordinate)
    (hc : matchingCandidateRoleCoordinateFallback hk profile K r = some c) :
    supercriticalProfileCoordinateSym2 D profile c =
      s(matchingCandidateChoiceVector hk r K
          (matchingRandomRoleVariableEndpointsFallback hk r).1,
        matchingCandidateChoiceVector hk r K
          (matchingRandomRoleVariableEndpointsFallback hk r).2) := by
  have hedge := K.matchingEdge_eq_anchor hk
  cases hK : K.candidate hk with
  | inl A =>
      have hedgeA : A.edge = K.anchor hk := by
        simpa [hK, SupercriticalMatchingStarCandidate.matchingEdge] using hedge
      cases r with
      | inl r =>
          simp only [matchingCandidateRoleCoordinateFallback, hK,
            Option.some.injEq] at hc
          subst c
          rcases r with r | r
          · simpa [matchingRandomRoleVariableEndpointsFallback,
              internalMatchingRandomRoleVariableEndpoints,
              internalMatchingRandomRoleAbstractPair,
              matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
              SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
              SupercriticalMatchingStarCandidate.matchingOther,
              hK, A.embedding_center, A.embedding_other] using
              internalMatchingRandomRoleCoordinate_sym2 hk profile A (Sum.inl r)
          · rcases r with r | r
            · simpa [matchingRandomRoleVariableEndpointsFallback,
                internalMatchingRandomRoleVariableEndpoints,
                internalMatchingRandomRoleAbstractPair,
                matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
                SupercriticalMatchingStarCandidate.matchingOther,
                hK, hedgeA, A.embedding_witness, A.embedding_other] using
                internalMatchingRandomRoleCoordinate_sym2 hk profile A
                  (Sum.inr (Sum.inl r))
            · rcases r with r | p
              · simpa [matchingRandomRoleVariableEndpointsFallback,
                  internalMatchingRandomRoleVariableEndpoints,
                  internalMatchingRandomRoleAbstractPair,
                  matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
                  SupercriticalMatchingStarCandidate.matchingOther,
                  hK, hedgeA, A.embedding_companion, A.embedding_other] using
                  internalMatchingRandomRoleCoordinate_sym2 hk profile A
                    (Sum.inr (Sum.inr (Sum.inl r)))
              · simpa [matchingRandomRoleVariableEndpointsFallback,
                  internalMatchingRandomRoleVariableEndpoints,
                  internalMatchingRandomRoleAbstractPair,
                  matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
                  SupercriticalMatchingStarCandidate.matchingOther,
                  hK, A.embedding_other] using
                  internalMatchingRandomRoleCoordinate_sym2 hk profile A
                    (Sum.inr (Sum.inr (Sum.inr p)))
      | inr r => simp [matchingCandidateRoleCoordinateFallback, hK] at hc
  | inr A =>
      have hedgeA : A.edge = K.anchor hk := by
        simpa [hK, SupercriticalMatchingStarCandidate.matchingEdge] using hedge
      cases r with
      | inl r => simp [matchingCandidateRoleCoordinateFallback, hK] at hc
      | inr r =>
          simp only [matchingCandidateRoleCoordinateFallback, hK,
            Option.some.injEq] at hc
          subst c
          rcases r with r | r
          · simpa [matchingRandomRoleVariableEndpointsFallback,
              supportMatchingRandomRoleVariableEndpoints,
              supportMatchingRandomRoleAbstractPair,
              matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
              SupercriticalMatchingStarCandidate.matchingOther,
              hK, hedgeA, A.embedding_center, A.embedding_other] using
              supportMatchingRandomRoleCoordinate_sym2 hk profile A (Sum.inl r)
          · rcases r with r | p
            · simpa [matchingRandomRoleVariableEndpointsFallback,
                supportMatchingRandomRoleVariableEndpoints,
                supportMatchingRandomRoleAbstractPair,
                matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
                SupercriticalMatchingStarCandidate.matchingDistinguishedFree,
                SupercriticalMatchingStarCandidate.matchingOther,
                hK, A.embedding_companion, A.embedding_other] using
                supportMatchingRandomRoleCoordinate_sym2 hk profile A
                  (Sum.inr (Sum.inl r))
            · simpa [matchingRandomRoleVariableEndpointsFallback,
                supportMatchingRandomRoleVariableEndpoints,
                supportMatchingRandomRoleAbstractPair,
                matchingCandidateChoiceVector, matchingRandomRoleUsesSecond,
                SupercriticalMatchingStarCandidate.matchingOther,
                hK, A.embedding_other] using
                supportMatchingRandomRoleCoordinate_sym2 hk profile A
                  (Sum.inr (Sum.inr p))

/-! ## One role-coordinate fiber -/

/-- Candidates whose role `s` occupies the same active coordinate as role
`r` of `K`.  Requiring a `some` coordinate prevents inactive outer tags from
creating spurious overlaps. -/
def matchingRoleOverlapCandidateFinsetFallback
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (r s : SupercriticalMatchingRandomRole k) :
    Finset (SupercriticalMatchingCandidateIndex hk M) := by
  classical
  exact Finset.univ.filter fun L ↦ ∃ c,
    matchingCandidateRoleCoordinateFallback hk profile K r = some c ∧
      matchingCandidateRoleCoordinateFallback hk profile L s = some c

@[simp] theorem mem_matchingRoleOverlapCandidateFinsetFallback
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalMatchingCandidateIndex hk M)
    (r s : SupercriticalMatchingRandomRole k) :
    L ∈ matchingRoleOverlapCandidateFinsetFallback hk profile K r s ↔
      ∃ c,
        matchingCandidateRoleCoordinateFallback hk profile K r = some c ∧
        matchingCandidateRoleCoordinateFallback hk profile L s = some c := by
  classical
  simp [matchingRoleOverlapCandidateFinsetFallback]

/-- Fixing an active random coordinate and a target role leaves at most two
orientations of the remaining `k - 2` choice-vector entries. -/
theorem matchingRoleOverlapCandidateFinsetFallback_card_le
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    (r s : SupercriticalMatchingRandomRole k) :
    (matchingRoleOverlapCandidateFinsetFallback hk profile K r s).card ≤
      2 * n ^ (k - 2) := by
  classical
  cases hKr : matchingCandidateRoleCoordinateFallback hk profile K r with
  | none =>
      have hempty : matchingRoleOverlapCandidateFinsetFallback
          hk profile K r s = ∅ := by
        ext L
        simp [hKr]
      simp [hempty]
  | some c =>
      let a := (matchingRandomRoleVariableEndpointsFallback hk s).1
      let b := (matchingRandomRoleVariableEndpointsFallback hk s).2
      let u := matchingCandidateChoiceVector hk r K
        (matchingRandomRoleVariableEndpointsFallback hk r).1
      let v := matchingCandidateChoiceVector hk r K
        (matchingRandomRoleVariableEndpointsFallback hk r).2
      have hmem : ∀ L ∈ matchingRoleOverlapCandidateFinsetFallback
          hk profile K r s,
          matchingCandidateChoiceVector hk s L ∈
            unorderedPairFunctionFinset a b u v := by
        intro L hL
        obtain ⟨d, hdK, hdL⟩ :=
          (mem_matchingRoleOverlapCandidateFinsetFallback
            hk profile K L r s).mp hL
        have hcd : c = d := by simpa [hKr] using hdK
        have hdc : d = c := hcd.symm
        subst d
        have hpairK := matchingCandidateRoleCoordinateFallback_sym2
          hk profile K r c hKr
        have hpairL := matchingCandidateRoleCoordinateFallback_sym2
          hk profile L s c hdL
        rw [mem_unorderedPairFunctionFinset]
        exact hpairL.symm.trans hpairK
      have hinj : Set.InjOn
          (fun L : SupercriticalMatchingCandidateIndex hk M ↦
            matchingCandidateChoiceVector hk s L)
          (matchingRoleOverlapCandidateFinsetFallback hk profile K r s :
            Set (SupercriticalMatchingCandidateIndex hk M)) :=
        (matchingCandidateChoiceVector_injective hk s).injOn
      calc
        (matchingRoleOverlapCandidateFinsetFallback
            hk profile K r s).card ≤
            (unorderedPairFunctionFinset a b u v).card :=
          Finset.card_le_card_of_injOn
            (fun L : SupercriticalMatchingCandidateIndex hk M ↦
              matchingCandidateChoiceVector hk s L) hmem hinj
        _ ≤ 2 * n ^ (k - 2) :=
          unorderedPairFunctionFinset_card_le a b u v
            (matchingRandomRoleVariableEndpointsFallback_ne hk s)

/-! ## Per-candidate overlap degree -/

/-- Every required coordinate has an active common-role witness. -/
theorem matchingRequiredSuccessCoordinates_mem_exists_fallbackRole
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M)
    {c : (supercriticalFixedProfileBlockModel D profile).Coordinate}
    (hc : c ∈ matchingRequiredSuccessCoordinates hk profile (K.candidate hk)) :
    ∃ r : SupercriticalMatchingRandomRole k,
      matchingCandidateRoleCoordinateFallback hk profile K r = some c := by
  cases hK : K.candidate hk with
  | inl A =>
      have hc' : c ∈ internalMatchingRequiredSuccessCoordinates hk profile A := by
        simpa only [matchingRequiredSuccessCoordinates.eq_def, hK] using hc
      rw [internalMatchingRequiredSuccessCoordinates, Finset.mem_image] at hc'
      obtain ⟨r, _hr, hrc⟩ := hc'
      exact ⟨Sum.inl r, by
        simp [matchingCandidateRoleCoordinateFallback, hK, hrc]⟩
  | inr A =>
      have hc' : c ∈ supportMatchingRequiredSuccessCoordinates hk profile A := by
        simpa only [matchingRequiredSuccessCoordinates.eq_def, hK] using hc
      rw [supportMatchingRequiredSuccessCoordinates, Finset.mem_image] at hc'
      obtain ⟨r, _hr, hrc⟩ := hc'
      exact ⟨Sum.inr r, by
        simp [matchingCandidateRoleCoordinateFallback, hK, hrc]⟩

/-- Candidates sharing at least one tagged required coordinate with `K`. -/
def matchingOverlappingCandidateFinsetFallback
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    Finset (SupercriticalMatchingCandidateIndex hk M) := by
  classical
  exact Finset.univ.filter fun L ↦
    ¬Disjoint
      (matchingRequiredSuccessCoordinates hk profile (K.candidate hk))
      (matchingRequiredSuccessCoordinates hk profile (L.candidate hk))

@[simp] theorem mem_matchingOverlappingCandidateFinsetFallback
    (profile : SupercriticalEdgeProfile D)
    (K L : SupercriticalMatchingCandidateIndex hk M) :
    L ∈ matchingOverlappingCandidateFinsetFallback hk profile K ↔
      ¬Disjoint
        (matchingRequiredSuccessCoordinates hk profile (K.candidate hk))
        (matchingRequiredSuccessCoordinates hk profile (L.candidate hk)) := by
  classical
  simp [matchingOverlappingCandidateFinsetFallback]

def matchingRoleOverlapUnionFallback
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    Finset (SupercriticalMatchingCandidateIndex hk M) := by
  classical
  exact Finset.univ.biUnion fun r ↦ Finset.univ.biUnion fun s ↦
    matchingRoleOverlapCandidateFinsetFallback hk profile K r s

theorem matchingOverlappingCandidateFinsetFallback_subset_roleUnion
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    matchingOverlappingCandidateFinsetFallback hk profile K ⊆
      matchingRoleOverlapUnionFallback hk profile K := by
  classical
  intro L hL
  have hoverlap :=
    (mem_matchingOverlappingCandidateFinsetFallback hk profile K L).mp hL
  obtain ⟨c, hcK, hcL⟩ := Finset.not_disjoint_iff.mp hoverlap
  obtain ⟨r, hr⟩ :=
    matchingRequiredSuccessCoordinates_mem_exists_fallbackRole
      hk profile K hcK
  obtain ⟨s, hs⟩ :=
    matchingRequiredSuccessCoordinates_mem_exists_fallbackRole
      hk profile L hcL
  rw [matchingRoleOverlapUnionFallback, Finset.mem_biUnion]
  refine ⟨r, Finset.mem_univ r, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨s, Finset.mem_univ s, ?_⟩
  rw [mem_matchingRoleOverlapCandidateFinsetFallback]
  exact ⟨c, hr, hs⟩

/-- Fallback per-candidate dependency-degree estimate. -/
theorem matchingOverlappingCandidateFinsetFallback_card_le
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    (matchingOverlappingCandidateFinsetFallback hk profile K).card ≤
      Fintype.card (SupercriticalMatchingRandomRole k) *
        (Fintype.card (SupercriticalMatchingRandomRole k) *
          (2 * n ^ (k - 2))) := by
  classical
  calc
    (matchingOverlappingCandidateFinsetFallback hk profile K).card ≤
        (matchingRoleOverlapUnionFallback hk profile K).card :=
      Finset.card_le_card
        (matchingOverlappingCandidateFinsetFallback_subset_roleUnion
          hk profile K)
    _ ≤ ∑ r : SupercriticalMatchingRandomRole k,
          (Finset.univ.biUnion fun s : SupercriticalMatchingRandomRole k ↦
            matchingRoleOverlapCandidateFinsetFallback
              hk profile K r s).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ r : SupercriticalMatchingRandomRole k,
          ∑ s : SupercriticalMatchingRandomRole k,
            (matchingRoleOverlapCandidateFinsetFallback
              hk profile K r s).card := by
      exact Finset.sum_le_sum fun r _ ↦ Finset.card_biUnion_le
    _ ≤ ∑ _r : SupercriticalMatchingRandomRole k,
          ∑ _s : SupercriticalMatchingRandomRole k,
            2 * n ^ (k - 2) := by
      exact Finset.sum_le_sum fun r _ ↦
        Finset.sum_le_sum fun s _ ↦
          matchingRoleOverlapCandidateFinsetFallback_card_le
            hk profile K r s
    _ = Fintype.card (SupercriticalMatchingRandomRole k) *
          (Fintype.card (SupercriticalMatchingRandomRole k) *
            (2 * n ^ (k - 2))) := by simp

end InducedStars
