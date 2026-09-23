import InducedStars.Structure.Subcritical.ProfileComplexity
import InducedStars.Structure.Subcritical.ProfileMatchingZero

/-!
# The exact clean/nonclean partition

Clean means that the ordinary defect graph has no edge incident with a
retained vertex. The nonretained induced graph is unrestricted by this
predicate; in particular it is not the sparse part of the division.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

def subcriticalCleanDivisionGraphFinset (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : Finset (SimpleGraph V) :=
  F.filter fun G ↦ subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥

def subcriticalNoncleanDivisionGraphFinset (F : Finset (SimpleGraph V))
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) : Finset (SimpleGraph V) :=
  F.filter fun G ↦ subcriticalRetainedIncidentDefectGraph G D eta R₀ ≠ ⊥

@[simp] theorem mem_subcriticalCleanDivisionGraphFinset
    (F : Finset (SimpleGraph V)) (G : SimpleGraph V) :
    G ∈ subcriticalCleanDivisionGraphFinset F D eta R₀ ↔
      G ∈ F ∧ subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥ :=
  Finset.mem_filter

@[simp] theorem mem_subcriticalNoncleanDivisionGraphFinset
    (F : Finset (SimpleGraph V)) (G : SimpleGraph V) :
    G ∈ subcriticalNoncleanDivisionGraphFinset F D eta R₀ ↔
      G ∈ F ∧ subcriticalRetainedIncidentDefectGraph G D eta R₀ ≠ ⊥ :=
  Finset.mem_filter

theorem subcriticalCleanNonclean_disjoint (F : Finset (SimpleGraph V)) :
    Disjoint (subcriticalCleanDivisionGraphFinset F D eta R₀)
      (subcriticalNoncleanDivisionGraphFinset F D eta R₀) := by
  apply Finset.disjoint_left.mpr
  intro G hG hN
  exact (mem_subcriticalNoncleanDivisionGraphFinset F G |>.mp hN).2
    (mem_subcriticalCleanDivisionGraphFinset F G |>.mp hG).2

theorem subcriticalCleanNonclean_union (F : Finset (SimpleGraph V)) :
    subcriticalCleanDivisionGraphFinset F D eta R₀ ∪
      subcriticalNoncleanDivisionGraphFinset F D eta R₀ = F := by
  ext G
  simp only [Finset.mem_union, mem_subcriticalCleanDivisionGraphFinset,
    mem_subcriticalNoncleanDivisionGraphFinset]
  tauto

theorem card_subcriticalClean_add_nonclean (F : Finset (SimpleGraph V)) :
    (subcriticalCleanDivisionGraphFinset F D eta R₀).card +
      (subcriticalNoncleanDivisionGraphFinset F D eta R₀).card = F.card := by
  rw [← Finset.card_union_of_disjoint (subcriticalCleanNonclean_disjoint F),
    subcriticalCleanNonclean_union]

theorem subcriticalBadRoots_eq_empty_of_clean (G : SimpleGraph V)
    (ha : 0 < alpha) (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥) :
    subcriticalBadRoots G D eta R₀ theta alpha = ∅ := by
  have hno {x y : V}
      (hxy : (subcriticalDefectGraph G D).Adj x y)
      (hret : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀) : False := by
    have hh : (subcriticalRetainedIncidentDefectGraph G D eta R₀).Adj x y := ⟨hxy, hret⟩
    simpa [hclean] using hh
  have hpos (a : D.PartIndex) : 0 < 4 * alpha * (D.part a).card := by
    exact mul_pos (mul_pos (by norm_num) ha)
      (by exact_mod_cast (D.part_nonempty a).card_pos)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_subcriticalBadRoots G D eta R₀ theta alpha v).mp hv with hv | hv
  · obtain ⟨hvret, hv⟩ := (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mp hv
    rcases hv with ⟨a, ha, hh⟩ | hh
    · have hz : degreeInFinset G v (D.part a) = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hy, hG⟩ := Finset.mem_filter.mp hy
        exact hno (eligibleVisibleTarget_edge_is_defect G D eta R₀ theta v hvret ha hy hG)
          (Or.inl hvret)
      rw [hz, Nat.cast_zero] at hh
      exact (not_le_of_gt (hpos a)) hh
    · have hz : complementDegreeInFinset G v
          (D.part (D.retainedVertexPart eta R₀ v hvret)) = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        obtain ⟨hy, hne, hG⟩ := Finset.mem_filter.mp hy
        exact hno (retainedOwn_missing_edge_is_defect G D eta R₀ v hvret hy hne hG)
          (Or.inl hvret)
      rw [hz, Nat.cast_zero] at hh
      exact (not_le_of_gt (hpos _)) hh
  · obtain ⟨hvout, a, ha, hh⟩ :=
      (mem_subcriticalBadOutsideRoots G D eta R₀ theta alpha v).mp hv
    have hz : degreeInFinset G v (D.part a) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨hy, hG⟩ := Finset.mem_filter.mp hy
      exact hno (outside_retainedTarget_edge_is_defect G D eta R₀ hvout ha hy hG)
        (Or.inr (D.part_subset_retainedVertices ha hy))
    rw [hz, Nat.cast_zero] at hh
    exact (not_le_of_gt (hpos a)) hh

theorem RealizesSubcriticalProfile.clean_iff
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 < alpha) :
    subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥ ↔
      p.roots = ∅ ∧ p.ell = 0 := by
  constructor
  · intro hclean
    refine ⟨hp.roots_eq.trans (subcriticalBadRoots_eq_empty_of_clean G ha hclean), ?_⟩
    have hr : subcriticalResidualDefectGraph G D eta R₀ theta alpha = ⊥ :=
      bot_unique (hclean ▸ subcriticalResidualDefectGraph_le G D eta R₀ theta alpha)
    rw [← hp.matching, hr, DenseGraph.matchingNumber_bot]
  · rintro ⟨hroots, hell⟩
    have hrootsG := hp.roots_eq.symm.trans hroots
    have hr := (DenseGraph.matchingNumber_eq_zero_iff _).mp (hp.matching.trans hell)
    have heq : subcriticalResidualDefectGraph G D eta R₀ theta alpha =
        subcriticalRetainedIncidentDefectGraph G D eta R₀ := by
      ext x y
      simp [subcriticalResidualDefectGraph_adj, hrootsG]
    exact heq.symm.trans hr

theorem RealizesSubcriticalProfile.complexity_pos_of_nonclean
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 < alpha)
    (h : subcriticalRetainedIncidentDefectGraph G D eta R₀ ≠ ⊥) :
    1 ≤ subcriticalProfileComplexity p := by
  have hnot : ¬ (p.roots = ∅ ∧ p.ell = 0) := fun hh ↦ h ((hp.clean_iff ha).mpr hh)
  simp only [← Finset.card_eq_zero] at hnot
  unfold subcriticalProfileComplexity
  omega

end InducedStars
