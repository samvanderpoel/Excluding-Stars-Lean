import InducedStars.Structure.Subcritical.ProfileData

/-!
# Exact rooted-edge accounting

The rooted graph contains one edge per recorded neighbor. Distinct target
indices denote disjoint division parts, and own-part missing edges are
disjoint from the actual edges in recorded rows.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private def partRowNeighbors (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (B : Finset V) (v : V) (A : Finset D.PartIndex) : Finset V :=
  A.biUnion fun a ↦ (D.part a \ B).filter (G.Adj v)

private theorem card_partRowNeighbors (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (B : Finset V) (v : V)
    (A : Finset D.PartIndex) :
    (partRowNeighbors G D B v A).card =
      ∑ a ∈ A, degreeInFinset G v (D.part a \ B) := by
  rw [partRowNeighbors, Finset.card_biUnion]
  · rfl
  · intro a _ b _ hab
    exact (D.part_disjoint hab).mono
      (Finset.filter_subset _ _ |>.trans Finset.sdiff_subset)
      (Finset.filter_subset _ _ |>.trans Finset.sdiff_subset)

private theorem ownMissing_disjoint_partRowNeighbors (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (B : Finset V) (v : V)
    (P : Finset V) (A : Finset D.PartIndex) :
    Disjoint ((P \ B).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y)
      (partRowNeighbors G D B v A) := by
  apply Finset.disjoint_left.mpr
  intro y hy hrow
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hrow
  exact (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp ha).2

/-- At a bad retained root, the recorded-neighbor count is precisely the
own-part missing degree plus the degrees in all selected eligible rows.
Global target indices occur only once, and their parts are disjoint. -/
theorem subcriticalRecordedRootNeighbors_card_retained
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v : V)
    (hv : v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha) :
    (subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v).card =
      complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v
          (subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha hv)) \
            subcriticalBadRoots G D eta R₀ theta alpha) +
      ∑ a : D.PartIndex,
        if D.EligibleProfileTarget eta R₀ theta v a ∧
            4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
          then degreeInFinset G v (D.part a \ subcriticalBadRoots G D eta R₀ theta alpha)
          else 0 := by
  let B := subcriticalBadRoots G D eta R₀ theta alpha
  let hvret := subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha hv
  let P := D.part (D.retainedVertexPart eta R₀ v hvret)
  let A := Finset.univ.filter fun a : D.PartIndex ↦
    D.EligibleProfileTarget eta R₀ theta v a ∧
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
  have hout : v ∉ subcriticalBadOutsideRoots G D eta R₀ theta alpha :=
    Finset.disjoint_left.mp (subcriticalBadRoots_disjoint G D eta R₀ theta alpha) hv
  have hneighbors : subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v =
      ((P \ B).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y) ∪ partRowNeighbors G D B v A := by
    ext y
    simp only [subcriticalRecordedRootNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, hv, hout, false_and, or_false, Finset.mem_union,
      Finset.mem_sdiff, partRowNeighbors, Finset.mem_biUnion, B, P, A]
    constructor
    · rintro ⟨hyB, ⟨_, hyP, hne, hG⟩ | ⟨a, ha, hhigh, hya, hG⟩⟩
      · exact Or.inl ⟨⟨hyP, hyB⟩, hne, hG⟩
      · exact Or.inr ⟨a, ⟨ha, hhigh⟩, ⟨hya, hyB⟩, hG⟩
    · rintro (⟨⟨hyP, hyB⟩, hne, hG⟩ | ⟨a, ⟨ha, hhigh⟩, ⟨hya, hyB⟩, hG⟩)
      · exact ⟨hyB, Or.inl ⟨hvret, hyP, hne, hG⟩⟩
      · exact ⟨hyB, Or.inr ⟨a, ha, hhigh, hya, hG⟩⟩
  rw [hneighbors, Finset.card_union_of_disjoint
    (ownMissing_disjoint_partRowNeighbors G D B v P A), card_partRowNeighbors]
  change complementDegreeInFinset G v (P \ B) +
    ∑ a ∈ A, degreeInFinset G v (D.part a \ B) = _
  simp only [A, Finset.sum_filter]
  rfl

/-- At an outside bad root, all recorded neighbors come from the distinct
retained target parts passing the full-target test. -/
theorem subcriticalRecordedRootNeighbors_card_outside
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v : V)
    (hv : v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha) :
    (subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v).card =
      ∑ a : D.PartIndex,
        if a ∈ D.retainedPartIndices eta R₀ ∧
            4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
          then degreeInFinset G v (D.part a \ subcriticalBadRoots G D eta R₀ theta alpha)
          else 0 := by
  let B := subcriticalBadRoots G D eta R₀ theta alpha
  let A := Finset.univ.filter fun a : D.PartIndex ↦
    a ∈ D.retainedPartIndices eta R₀ ∧
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
  have hret : v ∉ subcriticalBadRetainedRoots G D eta R₀ theta alpha :=
    Finset.disjoint_right.mp (subcriticalBadRoots_disjoint G D eta R₀ theta alpha) hv
  have hneighbors : subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v =
      partRowNeighbors G D B v A := by
    ext y
    simp only [subcriticalRecordedRootNeighbors, Finset.mem_filter, Finset.mem_univ,
      true_and, hv, hret, false_and, false_or, partRowNeighbors,
      Finset.mem_biUnion, Finset.mem_sdiff, B, A]
    constructor
    · rintro ⟨hyB, a, ha, hhigh, hya, hG⟩
      exact ⟨a, ⟨ha, hhigh⟩, ⟨hya, hyB⟩, hG⟩
    · rintro ⟨a, ⟨ha, hhigh⟩, ⟨hya, hyB⟩, hG⟩
      exact ⟨hyB, a, ha, hhigh, hya, hG⟩
  rw [hneighbors, card_partRowNeighbors]
  simp only [A, Finset.sum_filter]
  rfl

namespace SubcriticalProfile

variable {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The numerical contribution of a row. An absent row contributes zero,
without identifying absence with a recorded row whose remaining count is zero. -/
def rowCount (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) : ℕ :=
  ((p.rows v a).getD 0).val

/-- The paper's exact rooted-edge mass: own-part missing edges and eligible
rows at retained roots, then retained-target rows at outside roots. -/
def rootedEdgeMass (p : SubcriticalProfile D eta R₀ theta) : ℕ :=
  (∑ v ∈ p.retainedRoots, ((p.ownCount v).val + ∑ a : D.PartIndex, p.rowCount v a)) +
    ∑ v ∈ p.outsideRoots, ∑ a : D.PartIndex, p.rowCount v a

end SubcriticalProfile

namespace RealizesSubcriticalProfile

variable {G : SimpleGraph V} {D : SubcriticalDivision k V}
  {eta theta alpha : ℝ} {R₀ : ℕ} {p : SubcriticalProfile D eta R₀ theta}

theorem recordedNeighbors_card_retained (h : RealizesSubcriticalProfile G alpha p)
    {v : V} (hv : v ∈ p.retainedRoots) :
    (subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v).card =
      (p.ownCount v).val + ∑ a : D.PartIndex, p.rowCount v a := by
  have hvbad : v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha := by
    rwa [← h.retained_roots]
  rw [subcriticalRecordedRootNeighbors_card_retained G D eta R₀ theta alpha v hvbad,
    ← h.roots_eq, ← h.own_counts v hv]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [SubcriticalProfile.rowCount, h.retained_rows v hv a]
  split_ifs <;> simp

theorem recordedNeighbors_card_outside (h : RealizesSubcriticalProfile G alpha p)
    {v : V} (hv : v ∈ p.outsideRoots) :
    (subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v).card =
      ∑ a : D.PartIndex, p.rowCount v a := by
  have hvbad : v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha := by
    rwa [← h.outside_roots]
  rw [subcriticalRecordedRootNeighbors_card_outside G D eta R₀ theta alpha v hvbad,
    ← h.roots_eq]
  apply Finset.sum_congr rfl
  intro a _
  rw [SubcriticalProfile.rowCount, h.outside_rows v hv a]
  split_ifs <;> simp

/-- Exact unordered rooted-edge accounting for a realized profile. The
unique root orientation prevents counting an edge twice; the per-root
formulas use disjoint target parts and disjoint missing/present edges. -/
theorem rooted_edge_count_eq (h : RealizesSubcriticalProfile G alpha p) :
    (finiteGraphEdges (subcriticalRootedDefectGraph G D eta R₀ theta alpha)).card =
      p.rootedEdgeMass := by
  rw [subcriticalRootedDefectGraph_card_eq_sum_neighbors, ← h.roots_eq,
    SubcriticalProfile.roots, Finset.sum_union p.roots_disjoint,
    SubcriticalProfile.rootedEdgeMass]
  congr 1
  · exact Finset.sum_congr rfl fun v hv ↦ h.recordedNeighbors_card_retained hv
  · exact Finset.sum_congr rfl fun v hv ↦ h.recordedNeighbors_card_outside hv

end RealizesSubcriticalProfile

end InducedStars
