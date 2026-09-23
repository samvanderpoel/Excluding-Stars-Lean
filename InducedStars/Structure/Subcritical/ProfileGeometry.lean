import InducedStars.Structure.Subcritical.Retained
import InducedStars.Structure.Subcritical.Defect

/-!
# Own parts, eligible targets, and actual profile roots

Paper: the opening of `subsec:subcritical-profiles-K1k`. Root tests use
full target parts, before deleting roots. The own-part accessor is defined
only for retained vertices. Nonretained vertices have no fictitious own part.
-/

noncomputable section
open Finset
open scoped Classical BigOperators

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

namespace SubcriticalDivision

theorem exists_retained_part_of_mem (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) (hv : v ∈ D.retainedVertices eta R₀) :
    ∃ a : D.PartIndex, a ∈ D.retainedPartIndices eta R₀ ∧ v ∈ D.part a := by
  rw [D.retainedVertices_eq_part_union] at hv
  exact Finset.mem_biUnion.mp hv

/-- The unique actual part of a retained vertex. -/
def retainedVertexPart (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (v : V) (hv : v ∈ D.retainedVertices eta R₀) : D.PartIndex :=
  Classical.choose (D.exists_retained_part_of_mem eta R₀ v hv)

theorem retainedVertexPart_mem_retained (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) (hv : v ∈ D.retainedVertices eta R₀) :
    D.retainedVertexPart eta R₀ v hv ∈ D.retainedPartIndices eta R₀ :=
  (Classical.choose_spec (D.exists_retained_part_of_mem eta R₀ v hv)).1

theorem mem_retainedVertexPart (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) (hv : v ∈ D.retainedVertices eta R₀) :
    v ∈ D.part (D.retainedVertexPart eta R₀ v hv) :=
  (Classical.choose_spec (D.exists_retained_part_of_mem eta R₀ v hv)).2

theorem retainedVertexPart_eq_of_mem (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (v : V) (hv : v ∈ D.retainedVertices eta R₀)
    {a : D.PartIndex} (ha : v ∈ D.part a) : D.retainedVertexPart eta R₀ v hv = a :=
  D.mem_part_unique (D.mem_retainedVertexPart eta R₀ v hv) ha

/-- Visible targets other than the own part and its active core neighbors.
Visible nonretained components are deliberately allowed. -/
def eligibleVisibleTargets (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta : ℝ) (v : V) (hv : v ∈ D.retainedVertices eta R₀) : Finset D.PartIndex :=
  (D.visiblePartIndices theta).filter fun a ↦
    a ≠ D.retainedVertexPart eta R₀ v hv ∧
      ¬ D.ActivePart (D.retainedVertexPart eta R₀ v hv) a

@[simp] theorem mem_eligibleVisibleTargets (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (v : V)
    (hv : v ∈ D.retainedVertices eta R₀) (a : D.PartIndex) :
    a ∈ D.eligibleVisibleTargets eta R₀ theta v hv ↔
      a ∈ D.visiblePartIndices theta ∧ a ≠ D.retainedVertexPart eta R₀ v hv ∧
        ¬ D.ActivePart (D.retainedVertexPart eta R₀ v hv) a := by
  simp [eligibleVisibleTargets]

/-- Proof-independent target predicate for finite normalized profile fields. -/
def EligibleProfileTarget (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta : ℝ) (v : V) (a : D.PartIndex) : Prop :=
  ∃ hv : v ∈ D.retainedVertices eta R₀, a ∈ D.eligibleVisibleTargets eta R₀ theta v hv

theorem eligibleVisibleTarget_root_not_mem (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (v : V)
    (hv : v ∈ D.retainedVertices eta R₀) {a : D.PartIndex}
    (ha : a ∈ D.eligibleVisibleTargets eta R₀ theta v hv) : v ∉ D.part a := by
  intro h
  exact ((D.mem_eligibleVisibleTargets eta R₀ theta v hv a).mp ha).2.1
    (D.mem_part_unique h (D.mem_retainedVertexPart eta R₀ v hv))

end SubcriticalDivision

/-- Retained roots are tested against full eligible parts and the full own part. -/
def subcriticalBadRetainedRoots (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) : Finset V :=
  Finset.univ.filter fun v ↦ ∃ hv : v ∈ D.retainedVertices eta R₀,
    (∃ a ∈ D.eligibleVisibleTargets eta R₀ theta v hv,
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) ∨
    4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hv)).card ≤
      (complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hv)) : ℝ)

/-- Outside roots are tested only against retained target parts. -/
def subcriticalBadOutsideRoots (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (_theta alpha : ℝ) : Finset V :=
  (D.nonretainedVertices eta R₀).filter fun v ↦
    ∃ a ∈ D.retainedPartIndices eta R₀,
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)

def subcriticalBadRoots (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) : Finset V :=
  subcriticalBadRetainedRoots G D eta R₀ theta alpha ∪
    subcriticalBadOutsideRoots G D eta R₀ theta alpha

@[simp] theorem mem_subcriticalBadRetainedRoots (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) (v : V) :
    v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha ↔
      ∃ hv : v ∈ D.retainedVertices eta R₀,
        (∃ a ∈ D.eligibleVisibleTargets eta R₀ theta v hv,
          4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) ∨
        4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hv)).card ≤
          (complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hv)) : ℝ) := by
  simp [subcriticalBadRetainedRoots]

@[simp] theorem mem_subcriticalBadOutsideRoots (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) (v : V) :
    v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha ↔
      v ∈ D.nonretainedVertices eta R₀ ∧ ∃ a ∈ D.retainedPartIndices eta R₀,
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  simp [subcriticalBadOutsideRoots]

@[simp] theorem mem_subcriticalBadRoots (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) (v : V) :
    v ∈ subcriticalBadRoots G D eta R₀ theta alpha ↔
      v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha ∨
        v ∈ subcriticalBadOutsideRoots G D eta R₀ theta alpha := Finset.mem_union

theorem subcriticalBadRetainedRoots_subset (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    subcriticalBadRetainedRoots G D eta R₀ theta alpha ⊆ D.retainedVertices eta R₀ := by
  intro v hv
  exact ((mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mp hv).choose

theorem subcriticalBadOutsideRoots_subset (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    subcriticalBadOutsideRoots G D eta R₀ theta alpha ⊆ D.nonretainedVertices eta R₀ :=
  Finset.filter_subset _ _

theorem subcriticalBadRoots_disjoint (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    Disjoint (subcriticalBadRetainedRoots G D eta R₀ theta alpha)
      (subcriticalBadOutsideRoots G D eta R₀ theta alpha) :=
  (D.retainedVertices_disjoint_nonretainedVertices eta R₀).mono
    (subcriticalBadRetainedRoots_subset G D eta R₀ theta alpha)
    (subcriticalBadOutsideRoots_subset G D eta R₀ theta alpha)

theorem eligibleVisibleTarget_edge_is_defect (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (theta : ℝ) (v : V)
    (hv : v ∈ D.retainedVertices eta R₀) {a : D.PartIndex} {y : V}
    (ha : a ∈ D.eligibleVisibleTargets eta R₀ theta v hv)
    (hy : y ∈ D.part a) (hG : G.Adj v y) : (subcriticalDefectGraph G D).Adj v y := by
  have hp := D.mem_retainedVertexPart eta R₀ v hv
  obtain ⟨_, hne, hnactive⟩ := (D.mem_eligibleVisibleTargets eta R₀ theta v hv a).mp ha
  apply (subcriticalDefectGraph_adj_iff G D).mpr
  refine ⟨⟨hG.ne, Or.inr ⟨?_, ?_, hG⟩⟩, ?_⟩
  · exact fun h ↦ hne ((D.samePart_iff_of_mem_parts hp hy).mp h).symm
  · exact fun h ↦ hnactive ((D.activePair_iff_of_mem_parts hp hy).mp h)
  · exact fun h ↦ (D.mem_sparse.mp h.1) (D.retainedVertices_subset_support eta R₀ hv)

theorem retainedOwn_missing_edge_is_defect (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) (v : V)
    (hv : v ∈ D.retainedVertices eta R₀) {y : V}
    (hy : y ∈ D.part (D.retainedVertexPart eta R₀ v hv))
    (hne : y ≠ v) (hG : ¬ G.Adj v y) : (subcriticalDefectGraph G D).Adj v y := by
  apply (subcriticalDefectGraph_adj_iff G D).mpr
  refine ⟨⟨hne.symm, Or.inl ⟨⟨_, D.mem_retainedVertexPart eta R₀ v hv, hy⟩, hG⟩⟩, ?_⟩
  exact fun h ↦ (D.mem_sparse.mp h.1) (D.retainedVertices_subset_support eta R₀ hv)

theorem outside_retainedTarget_edge_is_defect (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) {v y : V} {a : D.PartIndex}
    (hv : v ∈ D.nonretainedVertices eta R₀) (ha : a ∈ D.retainedPartIndices eta R₀)
    (hy : y ∈ D.part a) (hG : G.Adj v y) : (subcriticalDefectGraph G D).Adj v y := by
  have hvnot := (D.mem_nonretainedVertices eta R₀ v).mp hv
  have hyret := D.part_subset_retainedVertices ha hy
  apply (subcriticalDefectGraph_adj_iff G D).mpr
  refine ⟨⟨hG.ne, Or.inr ⟨?_, ?_, hG⟩⟩, ?_⟩
  · rintro ⟨b, hvb, hyb⟩
    have hba := D.mem_part_unique hyb hy
    subst b
    exact hvnot (D.part_subset_retainedVertices ha hvb)
  · rintro ⟨i, u, w, _, hvi, hyi⟩
    have hci : i = a.1 := D.mem_componentSupport_unique
      (D.mem_componentSupport.mpr ⟨w, hyi⟩) (D.mem_componentSupport.mpr ⟨a.2, hy⟩)
    have hi : i ∈ D.retainedComponentIndices eta R₀ := by
      rw [hci]
      exact (D.mem_retainedPartIndices eta R₀ a).mp ha
    exact hvnot ((D.mem_retainedVertices eta R₀ v).mpr
      ⟨i, hi, D.mem_componentSupport.mpr ⟨u, hvi⟩⟩)
  · exact fun h ↦ (D.mem_sparse.mp h.2) (D.retainedVertices_subset_support eta R₀ hyret)

end InducedStars
