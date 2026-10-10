import InducedStars.Structure.Subcritical.ProfileResidual
import InducedStars.Structure.Subcritical.ProfileLeftoverRows
import InducedStars.Structure.Subcritical.SparseSide

/-!
# Uniform residual-defect degree bounds

The visible rows are residual rows, including missing edges in the own
part and zero rows on active pairs. The small-side row is bounded in the
actual generating graph. No remainder graph is fixed or counted here.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def subcriticalResidualDegreeCoefficient (k : ℕ) (alpha theta : ℝ) : ℝ :=
  4 * alpha + subcriticalSparseSideConstant k * theta

theorem subcriticalResidualDegreeCoefficient_nonneg (k : ℕ)
    {alpha theta : ℝ} (ha : 0 ≤ alpha) (ht : 0 ≤ theta) :
    0 ≤ subcriticalResidualDegreeCoefficient k alpha theta := by
  unfold subcriticalResidualDegreeCoefficient subcriticalSparseSideConstant
  positivity

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}

theorem subcriticalResidual_no_active {x y : V}
    (hxy : (subcriticalResidualDefectGraph G D eta R₀ theta alpha).Adj x y) :
    ¬ D.ActivePair x y := by
  rcases ((subcriticalDefectGraph_adj_iff G D).mp hxy.1.1).1.2 with ho | he
  · exact D.not_activePair_of_samePart ho.1
  · exact he.2.1

theorem subcriticalResidual_roots_degree_zero
    (hp : RealizesSubcriticalProfile G alpha p) {v : V} (hv : v ∈ p.roots)
    (A : Finset V) :
    degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v A = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact (Finset.mem_filter.mp hy).2.2.1 (hp.roots_eq ▸ hv)

theorem subcriticalResidual_visible_row_degree_le
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 ≤ alpha)
    (v : V) (a : D.PartIndex) (hvis : a ∈ D.visiblePartIndices theta) :
    (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.part a) : ℝ) ≤ 4 * alpha * (D.part a).card := by
  by_cases hvB : v ∈ p.roots
  · rw [subcriticalResidual_roots_degree_zero hp hvB, Nat.cast_zero]
    positivity
  have hlow := subcriticalProfileResidualDefectLowRows hp
  by_cases hvret : v ∈ D.retainedVertices eta R₀
  · by_cases hown : a = D.retainedVertexPart eta R₀ v hvret
    · subst a
      exact (hlow.2.1 v hvret hvB).le
    by_cases hact : D.ActivePart (D.retainedVertexPart eta R₀ v hvret) a
    · have hz : degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha)
          v (D.part a) = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hy
        exact subcriticalResidual_no_active hxy
          ((D.activePair_iff_of_mem_parts (D.mem_retainedVertexPart eta R₀ v hvret) hy).mpr hact)
      rw [hz, Nat.cast_zero]
      positivity
    exact (hlow.1 v hvret hvB a
      ((D.mem_eligibleVisibleTargets eta R₀ theta v hvret a).mpr ⟨hvis, hown, hact⟩)).le
  · have hvout := (D.mem_nonretainedVertices eta R₀ v).mpr hvret
    by_cases haret : a ∈ D.retainedPartIndices eta R₀
    · exact (hlow.2.2 v hvout hvB a haret).le
    have hz : degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha)
        v (D.part a) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hy
      have hyret := hxy.1.2.resolve_left hvret
      obtain ⟨b, hb, hyb⟩ := D.exists_retained_part_of_mem eta R₀ y hyret
      exact haret (D.mem_part_unique hyb hy ▸ hb)
    rw [hz, Nat.cast_zero]
    positivity

theorem subcriticalResidual_visible_degree_le
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 ≤ alpha) (v : V) :
    (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.visibleVertices theta) : ℝ) ≤ 4 * alpha * Fintype.card V := by
  have heq := D.degree_visibleVertices_sdiff theta
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v ∅
  simp only [Finset.sdiff_empty] at heq
  rw [heq, Nat.cast_sum]
  calc
    _ ≤ ∑ a ∈ D.visiblePartIndices theta, 4 * alpha * ((D.part a).card : ℝ) :=
      Finset.sum_le_sum (fun a hmem ↦ subcriticalResidual_visible_row_degree_le hp ha v a hmem)
    _ = 4 * alpha * ((D.visibleVertices theta).card : ℝ) := by
      rw [← Finset.mul_sum, ← Nat.cast_sum]
      congr 2
      rw [SubcriticalDivision.visibleVertices, Finset.card_biUnion]
      intro a _ b _ hab
      exact D.part_disjoint hab
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_univ (D.visibleVertices theta)) (by positivity)

theorem subcriticalResidual_small_degree_le (v : V) :
    degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.nonretainedSmallVertices eta R₀ theta) ≤
        degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) := by
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hy, hxy⟩ := Finset.mem_filter.mp hy
  refine Finset.mem_filter.mpr ⟨hy, ?_⟩
  have hyout := (D.mem_nonretainedVertices eta R₀ y).mp
    ((D.mem_nonretainedSmallVertices eta R₀ theta y).mp hy).1
  have hvret := hxy.1.2.resolve_right hyout
  rcases ((subcriticalDefectGraph_adj_iff G D).mp hxy.1.1).1.2 with ho | he
  · obtain ⟨a, hva, hya⟩ := ho.1
    obtain ⟨b, hb, hvb⟩ := D.exists_retained_part_of_mem eta R₀ v hvret
    have hab := D.mem_part_unique hva hvb
    subst a
    exact (hyout (D.part_subset_retainedVertices hb hya)).elim
  · exact he.2.2

/-- Full degree bound obtained from actual profile low rows and an actual
small-side row estimate, including vertices in the root set (degree zero). -/
theorem subcriticalResidual_degree_le
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hsmall : ∀ v, (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      subcriticalSparseSideConstant k * theta * Fintype.card V) (v : V) :
    (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      Finset.univ : ℝ) ≤ subcriticalResidualDegreeCoefficient k alpha theta * Fintype.card V := by
  have heq := degreeInFinset_union
    (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
    (D.visibleVertices_disjoint_nonretainedSmall eta theta R₀)
  rw [D.visibleVertices_union_nonretainedSmall hret] at heq
  rw [heq, Nat.cast_add]
  have hs : (degreeInFinset (subcriticalResidualDefectGraph G D eta R₀ theta alpha) v
      (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) := by
    exact_mod_cast subcriticalResidual_small_degree_le (G := G) (D := D)
      (eta := eta) (R₀ := R₀) (theta := theta) (alpha := alpha) v
  have hv := subcriticalResidual_visible_degree_le hp ha v
  unfold subcriticalResidualDegreeCoefficient
  nlinarith [hsmall v]

/-- The needed small-side degree bound requires only the original finite
defect estimate and star-freeness, not alignment or a fixed remainder. -/
theorem subcriticalResidual_smallSide_bound_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) (G : SimpleGraph (Fin n))
    (D : SubcriticalDivision k (Fin n)) {eta theta epsilon : ℝ} {R₀ : ℕ}
    (ht : 0 ≤ theta) (he : 0 ≤ epsilon) (heTheta : epsilon ≤ theta ^ 2)
    (hscale : 1 ≤ theta * n)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hdefect : (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ)^2) (v : Fin n) :
    (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      subcriticalSparseSideConstant k * theta * n := by
  have hs := subcritical_smallSide_degree_le_raw hk G D (eta := eta) (R₀ := R₀)
    ht he hfree hdefect v
  have hroot : Real.sqrt epsilon ≤ theta := (Real.sqrt_le_iff).mpr ⟨ht, heTheta⟩
  have hm := mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg n)
  have hcoef : 0 ≤ (k : ℝ)^2 := sq_nonneg _
  have hh := mul_le_mul_of_nonneg_left
    (show theta * n + Real.sqrt epsilon * n + 1 ≤ 3 * (theta * n) by linarith)
    (show 0 ≤ 4 * (k : ℝ)^2 by positivity)
  have hb := mul_nonneg hcoef (show 0 ≤ theta * n by positivity)
  unfold subcriticalSparseSideConstant
  nlinarith

end InducedStars
