import InducedStars.Structure.Supercritical.MatchingCandidateOverlap

/-!
# Collected matching-candidate dependency bounds

This module collects the role-fiber estimate into the per-candidate and
unordered-pair bounds used by the Janson argument.
-/

noncomputable section

open Finset Set

namespace InducedStars

variable {k n : ℕ} (hk : 3 ≤ k)
  {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
  {M : SupercriticalHomogeneousMatching k (Fin n) D T}

theorem supercriticalMatchingRandomRole_card_le_twice_roleBound :
    Fintype.card (SupercriticalMatchingRandomRole k) ≤
      2 * supercriticalMatchingRandomRoleBound k := by
  have hpairs : Fintype.card
      {p : Fin (k - 2) × Fin (k - 2) // p.1 < p.2} ≤
      Fintype.card (Fin (k - 2) × Fin (k - 2)) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [SupercriticalMatchingRandomRole,
    SupercriticalInternalMatchingRandomRole,
    SupercriticalSupportMatchingRandomRole, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_prod] at ⊢ hpairs
  unfold supercriticalMatchingRandomRoleBound
  simp only [pow_two] at hpairs ⊢
  omega

/-- A fixed tagged matching candidate shares a required coordinate with at
most the explicit `k`-only multiple of `n^(k-2)` other candidates. -/
theorem matchingOverlappingCandidateFinset_card_le
    (profile : SupercriticalEdgeProfile D)
    (K : SupercriticalMatchingCandidateIndex hk M) :
    (matchingOverlappingCandidateFinsetFallback hk profile K).card ≤
      supercriticalMatchingDependencyCoefficient k * n ^ (k - 2) := by
  let R := supercriticalMatchingRandomRoleBound k
  have hrole := supercriticalMatchingRandomRole_card_le_twice_roleBound
    (k := k)
  calc
    (matchingOverlappingCandidateFinsetFallback hk profile K).card ≤
        Fintype.card (SupercriticalMatchingRandomRole k) *
          (Fintype.card (SupercriticalMatchingRandomRole k) *
            (2 * n ^ (k - 2))) :=
      matchingOverlappingCandidateFinsetFallback_card_le hk profile K
    _ ≤ (2 * R) * ((2 * R) * (2 * n ^ (k - 2))) := by
      gcongr
    _ = 8 * R ^ 2 * n ^ (k - 2) := by ring
    _ = supercriticalMatchingDependencyCoefficient k * n ^ (k - 2) := by
      rfl

/-- Ordered enlargement of all overlapping pairs.  It intentionally permits
the diagonal; this only makes the upper bound more robust. -/
def matchingOrderedOverlapUnion
    (profile : SupercriticalEdgeProfile D) :
    Finset (SupercriticalMatchingCandidateIndex hk M ×
      SupercriticalMatchingCandidateIndex hk M) := by
  classical
  exact Finset.univ.biUnion fun K ↦
    (matchingOverlappingCandidateFinsetFallback hk profile K).map
      ⟨fun L ↦ (K, L), fun _ _ h ↦ Prod.mk.inj h |>.2⟩

theorem matchingUnorderedOverlappingPairs_subset_orderedUnion
    (profile : SupercriticalEdgeProfile D) :
    DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
        (fun K : SupercriticalMatchingCandidateIndex hk M ↦
          matchingRequiredSuccessCoordinates hk profile (K.candidate hk)) ⊆
      matchingOrderedOverlapUnion hk profile := by
  classical
  intro KL hKL
  have hoverlap :=
    (DenseGraph.FiniteBernoulliProduct.mem_unorderedOverlappingPairs
      (fun K : SupercriticalMatchingCandidateIndex hk M ↦
        matchingRequiredSuccessCoordinates hk profile (K.candidate hk))
      KL.1 KL.2).mp hKL
  rw [matchingOrderedOverlapUnion, Finset.mem_biUnion]
  refine ⟨KL.1, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_map]
  refine ⟨KL.2, ?_, rfl⟩
  exact (mem_matchingOverlappingCandidateFinsetFallback
    hk profile KL.1 KL.2).mpr hoverlap.2

/-- The exact unordered dependency-pair finset used by Janson. -/
abbrev matchingOverlappingCandidatePairFinset
    (profile : SupercriticalEdgeProfile D) :=
  DenseGraph.FiniteBernoulliProduct.unorderedOverlappingPairs
    (fun K : SupercriticalMatchingCandidateIndex hk M ↦
      matchingRequiredSuccessCoordinates hk profile (K.candidate hk))

/-- Final `C_k |M'| n^(2k-3)` unordered dependency count. -/
theorem matchingOverlappingCandidatePairFinset_card_le
    (profile : SupercriticalEdgeProfile D) :
    (matchingOverlappingCandidatePairFinset (M := M) hk profile).card ≤
      supercriticalMatchingDependencyCoefficient k * M.edges.card *
        n ^ (2 * k - 3) := by
  classical
  let B := supercriticalMatchingDependencyCoefficient k * n ^ (k - 2)
  calc
    (matchingOverlappingCandidatePairFinset (M := M) hk profile).card ≤
        (matchingOrderedOverlapUnion hk profile).card :=
      Finset.card_le_card
        (matchingUnorderedOverlappingPairs_subset_orderedUnion hk profile)
    _ ≤ ∑ K : SupercriticalMatchingCandidateIndex hk M,
          (matchingOverlappingCandidateFinsetFallback hk profile K).card := by
      unfold matchingOrderedOverlapUnion
      calc
        _ ≤ ∑ K : SupercriticalMatchingCandidateIndex hk M,
            ((matchingOverlappingCandidateFinsetFallback hk profile K).map
              ⟨fun L ↦ (K, L), fun _ _ h ↦ Prod.mk.inj h |>.2⟩).card :=
          Finset.card_biUnion_le
        _ = ∑ K : SupercriticalMatchingCandidateIndex hk M,
            (matchingOverlappingCandidateFinsetFallback hk profile K).card := by
          simp
    _ ≤ ∑ _K : SupercriticalMatchingCandidateIndex hk M, B := by
      exact Finset.sum_le_sum fun K _ ↦
        matchingOverlappingCandidateFinset_card_le hk profile K
    _ = (matchingStarCandidateFinset hk M).card * B := by
      simp [B]
    _ ≤ (M.edges.card * n ^ (k - 1)) * B :=
      Nat.mul_le_mul_right B (matchingStarCandidateFinset_card_le hk M)
    _ = supercriticalMatchingDependencyCoefficient k * M.edges.card *
          n ^ (2 * k - 3) := by
      dsimp [B]
      rw [show 2 * k - 3 = (k - 1) + (k - 2) by omega, pow_add]
      ring

/-- Real-cast form consumed directly by quantitative probability bounds. -/
theorem matchingOverlappingCandidatePairFinset_card_cast_le
    (profile : SupercriticalEdgeProfile D) :
    ((matchingOverlappingCandidatePairFinset (M := M) hk profile).card : ℝ) ≤
      (supercriticalMatchingDependencyCoefficient k : ℝ) *
        (M.edges.card : ℝ) * (n : ℝ) ^ (2 * k - 3) := by
  exact_mod_cast matchingOverlappingCandidatePairFinset_card_le hk profile

end InducedStars
