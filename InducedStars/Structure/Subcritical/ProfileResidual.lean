import InducedStars.Structure.Subcritical.ProfileData
import InducedStars.Structure.Subcritical.ProfileRootBounds

/-!
# Realized profile low rows and finite controls

Paper: Lemma `lemma:profile-residual-low-rows-K1k`. The original-graph
own-part clause is stated only for retained vertices, as in the paper's retained-domain condition.
The residual graph inequalities follow by ordinary-defect edge containment.
-/

noncomputable section

open Finset
open scoped Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}

/-- Paper: Lemma `lemma:profile-residual-low-rows-K1k`, with the explicit
retained domain of its own-part clause. All three degrees use full
target parts in the original graph; the thresholds remain exactly `4 * alpha`. -/
theorem subcriticalProfileResidualLowRows (h : RealizesSubcriticalProfile G alpha p) :
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      ∀ a ∈ D.eligibleVisibleTargets eta R₀ theta v hvret,
        (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card) ∧
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      (complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) <
          4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hvret)).card) ∧
    (∀ v ∈ D.nonretainedVertices eta R₀, v ∉ p.roots →
      ∀ a ∈ D.retainedPartIndices eta R₀,
        (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hvret hv a ha
    apply lt_of_not_ge
    intro hhigh
    apply hv
    rw [h.roots_eq]
    apply Finset.mem_union_left
    exact (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mpr
      ⟨hvret, Or.inl ⟨a, ha, hhigh⟩⟩
  · intro v hvret hv
    apply lt_of_not_ge
    intro hhigh
    apply hv
    rw [h.roots_eq]
    apply Finset.mem_union_left
    exact (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mpr
      ⟨hvret, Or.inr hhigh⟩
  · intro v hvout hv a ha
    apply lt_of_not_ge
    intro hhigh
    apply hv
    rw [h.roots_eq]
    apply Finset.mem_union_right
    exact (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mpr
      ⟨hvout, a, ha, hhigh⟩

/-- In an eligible row, an ordinary defect must be an original graph edge.
Own-part missing edges are excluded by the target index. -/
theorem subcriticalResidual_eligible_degree_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v : V) (hvret : v ∈ D.retainedVertices eta R₀)
    {a : D.PartIndex} (ha : a ∈ D.eligibleVisibleTargets eta R₀ theta v hvret) :
    degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v (D.part a) ≤
      degreeInFinset G v (D.part a) := by
  unfold degreeInFinset
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy, hres⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hy, ?_⟩
  have hdefect := ((subcriticalDefectGraph_adj_iff G D).mp hres.1.1).1.2
  rcases hdefect with hown | hedge
  · have hne := ((D.mem_eligibleVisibleTargets eta R₀ theta v hvret a).mp ha).2.1
    exact (hne ((D.samePart_iff_of_mem_parts
      (D.mem_retainedVertexPart eta R₀ v hvret) hy).mp hown.1).symm).elim
  · exact hedge.2.2

/-- In a retained own part, residual defects are loopless complementary
edges. This is precisely the own-part domain specified in the paper. -/
theorem subcriticalResidual_own_degree_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v : V) (hvret : v ∈ D.retainedVertices eta R₀) :
    degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
        (D.part (D.retainedVertexPart eta R₀ v hvret)) ≤
      complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) := by
  unfold degreeInFinset complementDegreeInFinset
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy, hres⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hy, hres.ne.symm, ?_⟩
  have hdefect := ((subcriticalDefectGraph_adj_iff G D).mp hres.1.1).1.2
  rcases hdefect with hown | hedge
  · exact hown.2
  · exact (hedge.1 ⟨_, D.mem_retainedVertexPart eta R₀ v hvret, hy⟩).elim

/-- A residual defect from the nonretained side into a retained target
must be an original graph edge: its endpoints cannot share a part. -/
theorem subcriticalResidual_outside_degree_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (theta alpha : ℝ) (v : V) (hvout : v ∈ D.nonretainedVertices eta R₀)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀) :
    degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v (D.part a) ≤
      degreeInFinset G v (D.part a) := by
  unfold degreeInFinset
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy, hres⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hy, ?_⟩
  have hdefect := ((subcriticalDefectGraph_adj_iff G D).mp hres.1.1).1.2
  rcases hdefect with hown | hedge
  · obtain ⟨b, hvb, hyb⟩ := hown.1
    have hba := D.mem_part_unique hyb hy
    subst b
    exact ((D.mem_nonretainedVertices eta R₀ v).mp hvout
      (D.part_subset_retainedVertices ha hvb)).elim
  · exact hedge.2.2

/-- The three relevant rows of the residual defect graph inherit the
original-graph low-row thresholds. The own-part clause has the retained
domain specified in the paper; active-pair degrees in the original graph are
not among these inequalities. -/
theorem subcriticalProfileResidualDefectLowRows
    (h : RealizesSubcriticalProfile G alpha p) :
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      ∀ a ∈ D.eligibleVisibleTargets eta R₀ theta v hvret,
        (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
          (D.part a) : ℝ) < 4 * alpha * (D.part a).card) ∧
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
        (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) <
          4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hvret)).card) ∧
    (∀ v ∈ D.nonretainedVertices eta R₀, v ∉ p.roots →
      ∀ a ∈ D.retainedPartIndices eta R₀,
        (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
          (D.part a) : ℝ) < 4 * alpha * (D.part a).card) := by
  have hlow := subcriticalProfileResidualLowRows h
  refine ⟨?_, ?_, ?_⟩
  · intro v hvret hv a ha
    have hle := subcriticalResidual_eligible_degree_le G D eta R₀ theta alpha v hvret ha
    exact (show (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.part a) : ℝ) ≤ degreeInFinset G v (D.part a) by exact_mod_cast hle).trans_lt
        (hlow.1 v hvret hv a ha)
  · intro v hvret hv
    have hle := subcriticalResidual_own_degree_le G D eta R₀ theta alpha v hvret
    exact (show (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) ≤
        complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) by
          exact_mod_cast hle).trans_lt (hlow.2.1 v hvret hv)
  · intro v hvout hv a ha
    have hle := subcriticalResidual_outside_degree_le G D eta R₀ theta alpha v hvout ha
    exact (show (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.part a) : ℝ) ≤ degreeInFinset G v (D.part a) by exact_mod_cast hle).trans_lt
        (hlow.2.2 v hvout hv a ha)

/-- The complete finite elementary controls for one realized profile:
the paper's root bound, all three original-graph low rows, and their residual
defect versions. The own-part domain in both bundles is restricted to retained vertices.
Only explicit finite geometry and the ordinary defect count are used. -/
theorem subcriticalProfileFiniteControls
    (h : RealizesSubcriticalProfile G alpha p) {epsilon : ℝ}
    (halpha : 0 < alpha) (htheta : 0 < theta) (hn : 0 < Fintype.card V)
    (hretained : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ))
    (hedges : ((subcriticalDefectGraph G D).edgeFinset.card : ℝ) ≤
      epsilon * (Fintype.card V : ℝ) ^ 2) :
    (p.roots.card : ℝ) ≤
        subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V ∧
    ((∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      ∀ a ∈ D.eligibleVisibleTargets eta R₀ theta v hvret,
        (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card) ∧
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      (complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) <
          4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hvret)).card) ∧
    (∀ v ∈ D.nonretainedVertices eta R₀, v ∉ p.roots →
      ∀ a ∈ D.retainedPartIndices eta R₀,
        (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card)) ∧
    ((∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      ∀ a ∈ D.eligibleVisibleTargets eta R₀ theta v hvret,
        (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
          (D.part a) : ℝ) < 4 * alpha * (D.part a).card) ∧
    (∀ (v : V) (hvret : v ∈ D.retainedVertices eta R₀), v ∉ p.roots →
      (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
        (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) <
          4 * alpha * (D.part (D.retainedVertexPart eta R₀ v hvret)).card) ∧
    (∀ v ∈ D.nonretainedVertices eta R₀, v ∉ p.roots →
      ∀ a ∈ D.retainedPartIndices eta R₀,
        (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
          (D.part a) : ℝ) < 4 * alpha * (D.part a).card)) := by
  refine ⟨?_, subcriticalProfileResidualLowRows h, subcriticalProfileResidualDefectLowRows h⟩
  rw [h.roots_eq]
  exact subcriticalBadRoots_card_le_finite G D eta R₀ halpha htheta hn
    hretained hvisible hedges

end InducedStars
