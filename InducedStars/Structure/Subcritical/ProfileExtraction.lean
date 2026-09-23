import InducedStars.Structure.Subcritical.ProfileData

/-!
# Canonical extraction of finite subcritical profiles

The construction uses the actual full-target bad-root tests and stores only
trimmed counts. It applies to arbitrary finite graphs, with no closeness,
canonical-division, or induced-star-freeness hypothesis.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The existing canonical matching number obeys the endpoint bound. -/
theorem subcritical_two_mul_matchingNumber_le_card (H : SimpleGraph V) :
    2 * DenseGraph.matchingNumber H ≤ Fintype.card V := by
  rw [← DenseGraph.canonicalMaximumMatching_endpoint_ncard]
  simpa only [Nat.card_eq_fintype_card] using
    Set.ncard_le_card (DenseGraph.canonicalMaximumMatching H).verts

/-- A positive division part cannot satisfy both weak tail thresholds when
`alpha < 1/2`. No lower bound on its order beyond nonemptiness is needed. -/
theorem subcritical_tail_thresholds_disjoint (G : SimpleGraph V)
    (D : SubcriticalDivision k V) {alpha : ℝ} (halpha : alpha < 1 / 2)
    (v : V) (a : D.PartIndex) :
    ¬ ((1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) ∧
      (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card) := by
  have hp : (0 : ℝ) < (D.part a).card := by
    exact_mod_cast (D.part_nonempty a).card_pos
  have hsep : alpha * (D.part a).card < (1 - alpha) * (D.part a).card := by
    nlinarith [mul_pos (show 0 < 1 - 2 * alpha by linarith) hp]
  rintro ⟨hu, hl⟩
  linarith

/-- Select and count every recorded row using the actual root sets. The
full-target test remains distinct from the trimmed stored count. -/
def subcriticalProfileRowsOfGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (v : V) (a : D.PartIndex) : Option (Fin (Fintype.card V + 1)) :=
  if ((v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha ∧
        D.EligibleProfileTarget eta R₀ theta v a) ∨
      (v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha ∧
        a ∈ D.retainedPartIndices eta R₀)) ∧
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
    then some (subcriticalBoundedDegree G v
      (D.part a \ subcriticalBadRoots G D eta R₀ theta alpha))
    else none

/-- Own counts are normalized to zero away from retained roots; an own
part is recovered only under the corresponding retained-membership proof. -/
def subcriticalProfileOwnCountsOfGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (v : V) : Fin (Fintype.card V + 1) :=
  if hv : v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha then
    subcriticalBoundedComplementDegree G v
      (D.part (D.retainedVertexPart eta R₀ v
        (subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha hv)) \
          subcriticalBadRoots G D eta R₀ theta alpha)
  else 0

/-- Exact full-part upper and lower labels on active-neighbor parts.
Exclusivity in the intended range is proved separately. -/
def subcriticalProfileTailsOfGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (v : V) (a : D.PartIndex) : Option SubcriticalTailDirection :=
  if hv : v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha then
    if D.ActivePart (D.retainedVertexPart eta R₀ v
        (subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha hv)) a then
      if (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) then
        some .upper
      else if (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card then
        some .lower
      else none
    else none
  else none

/-- Paper: the canonical data used in the proof of
`lemma:profile-covering-K1k`. This uses no geometric regularity hypotheses. -/
def subcriticalProfileOfGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (_halpha : 0 < alpha) (_halpha_half : alpha < 1 / 2) :
    SubcriticalProfile D eta R₀ theta where
  b := inducedEdgeCount G (D.nonretainedVertices eta R₀)
  b_le := by
    have h := inducedEdgeCount_add_compl G (D.nonretainedVertices eta R₀)
    omega
  ell := DenseGraph.matchingNumber (subcriticalResidualDefectGraph G D eta R₀ theta alpha)
  two_mul_ell_le := subcritical_two_mul_matchingNumber_le_card _
  retainedRoots := subcriticalBadRetainedRoots G D eta R₀ theta alpha
  outsideRoots := subcriticalBadOutsideRoots G D eta R₀ theta alpha
  retainedRoots_subset := subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha
  outsideRoots_subset := subcriticalBadOutsideRoots_subset G D eta R₀ theta alpha
  rows := subcriticalProfileRowsOfGraph G D eta R₀ theta alpha
  rows_valid := by
    intro v a r h
    unfold subcriticalProfileRowsOfGraph at h
    split_ifs at h with hrow
    · have hr := Option.some.inj h
      subst r
      exact ⟨hrow.1, Finset.card_filter_le _ _⟩
  ownCount := subcriticalProfileOwnCountsOfGraph G D eta R₀ theta alpha
  ownCount_zero := by
    intro v hv
    simp [subcriticalProfileOwnCountsOfGraph, hv]
  ownCount_capacity := by
    intro v hv
    simp only [subcriticalProfileOwnCountsOfGraph, dif_pos hv,
      subcriticalBoundedComplementDegree_val]
    exact Finset.card_filter_le _ _
  tails := subcriticalProfileTailsOfGraph G D eta R₀ theta alpha
  tails_valid := by
    intro v a t h
    unfold subcriticalProfileTailsOfGraph at h
    split_ifs at h with hv ha hu hl
    · exact ⟨hv, ha⟩
    · exact ⟨hv, ha⟩

/-- Every graph realizes its extracted data. Full-part tests determine
which rows and tails occur; the degree coordinates count after trimming. -/
theorem realizes_subcriticalProfileOfGraph (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ)
    (halpha : 0 < alpha) (halpha_half : alpha < 1 / 2) :
    RealizesSubcriticalProfile G alpha
      (subcriticalProfileOfGraph G D eta R₀ theta alpha halpha halpha_half) := by
  constructor
  · rfl
  · rfl
  · rfl
  · intro v hv a
    have hout : v ∉ subcriticalBadOutsideRoots G D eta R₀ theta alpha := by
      exact fun ho ↦ Finset.disjoint_left.mp
        (subcriticalBadRoots_disjoint G D eta R₀ theta alpha) hv ho
    simp only [subcriticalProfileOfGraph, subcriticalProfileRowsOfGraph,
      SubcriticalProfile.roots, subcriticalBadRoots] at hv ⊢
    simp only [hv, hout, true_and, false_and, or_false]
  · intro v hv
    simp only [subcriticalProfileOfGraph, subcriticalProfileOwnCountsOfGraph,
      SubcriticalProfile.roots, subcriticalBadRoots] at hv ⊢
    simp only [dif_pos hv, subcriticalBoundedComplementDegree_val]
  · intro v hv a
    have hret : v ∉ subcriticalBadRetainedRoots G D eta R₀ theta alpha := by
      exact fun hr ↦ Finset.disjoint_left.mp
        (subcriticalBadRoots_disjoint G D eta R₀ theta alpha) hr hv
    simp only [subcriticalProfileOfGraph, subcriticalProfileRowsOfGraph,
      SubcriticalProfile.roots, subcriticalBadRoots] at hv ⊢
    simp only [hv, hret, true_and, false_and, false_or]
  · intro v hv a ha
    change v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha at hv
    change D.ActivePart (D.retainedVertexPart eta R₀ v
      (subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha hv)) a at ha
    change
      (subcriticalProfileTailsOfGraph G D eta R₀ theta alpha v a = some .upper ↔ _) ∧
      (subcriticalProfileTailsOfGraph G D eta R₀ theta alpha v a = some .lower ↔ _)
    have hdis := subcritical_tail_thresholds_disjoint G D halpha_half v a
    unfold subcriticalProfileTailsOfGraph
    rw [dif_pos hv, if_pos ha]
    by_cases hu : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
    · have hl : ¬ (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card :=
        fun hl ↦ hdis ⟨hu, hl⟩
      simp [hu, hl]
    · by_cases hl : (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card <;>
        simp [hu, hl]
  · rfl

end InducedStars
