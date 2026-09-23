import InducedStars.Structure.Subcritical.ProfileLeftoverRows
import InducedStars.Structure.Subcritical.ProfileLeftoverAlgebra
import InducedStars.Structure.Supercritical.SupportPatternCounting

/-!
# Finite edge and signed-size bounds for leftovers

Every leftover edge meets a root. Each root row is covered by trimmed
visible vertices, trimmed small-side vertices, and roots. This edge bound
does not require a fixed remainder graph: the fixed-remainder restriction belongs
only to the separate cardinality estimate.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}

/-- All graph choices whose edges have both endpoints in the root set. -/
def subcriticalRootRootGraphFinset (B : Finset V) : Finset (SimpleGraph V) :=
  Finset.univ.filter (fun T ↦ ∀ x y, T.Adj x y → x ∈ B ∧ y ∈ B)

@[simp] theorem mem_subcriticalRootRootGraphFinset (B : Finset V) (T : SimpleGraph V) :
    T ∈ subcriticalRootRootGraphFinset B ↔ ∀ x y, T.Adj x y → x ∈ B ∧ y ∈ B := by
  simp [subcriticalRootRootGraphFinset]

/-- Root-root choices need only one bit per unordered pair, even though
the final row encoding permits the harmless coarser ordered-row bound. -/
theorem card_subcriticalRootRootGraphFinset_le (B : Finset V) :
    (subcriticalRootRootGraphFinset B).card ≤ 2^(B.card.choose 2) := by
  let E := (⊤ : SimpleGraph B).edgeFinset.powerset
  let f : SimpleGraph V → Finset (Sym2 B) := fun T ↦ (T.induce (B : Set V)).edgeFinset
  have hmap : ∀ T ∈ subcriticalRootRootGraphFinset B, f T ∈ E := by
    intro T _
    apply Finset.mem_powerset.mpr
    exact SimpleGraph.edgeFinset_mono le_top
  have hinj : Set.InjOn f (subcriticalRootRootGraphFinset B : Set (SimpleGraph V)) := by
    intro T hT U hU heq
    have hTU : T.induce (B : Set V) = U.induce (B : Set V) :=
      SimpleGraph.edgeFinset_inj.mp heq
    have hTs := (mem_subcriticalRootRootGraphFinset B T).mp hT
    have hUs := (mem_subcriticalRootRootGraphFinset B U).mp hU
    ext x y
    constructor
    · intro hxy
      obtain ⟨hx, hy⟩ := hTs x y hxy
      have hxy' : (T.induce (B : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
      rw [hTU] at hxy'
      exact hxy'
    · intro hxy
      obtain ⟨hx, hy⟩ := hUs x y hxy
      have hxy' : (U.induce (B : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hxy
      rw [← hTU] at hxy'
      exact hxy'
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa only [E, Finset.card_powerset,
    SimpleGraph.card_edgeFinset_top_eq_card_choose_two, Fintype.card_coe] using hc

/-- The roots cover the actual leftover graph, since the residual graph
contains every retained-incident edge with both endpoints outside them. -/
theorem subcriticalActualLeftover_roots_vertexCover
    (h : RealizesSubcriticalProfile G alpha p) :
    (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).IsVertexCover
      (p.roots : Set V) := by
  intro x y hxy
  obtain ⟨hT, _, hR⟩ := (subcriticalLeftoverDefectGraph_adj _ _ _ x y).mp hxy
  by_contra hnot
  have hn := not_or.mp hnot
  apply hR
  exact ⟨hT, (by simpa [← h.roots_eq] using hn.1),
    (by simpa [← h.roots_eq] using hn.2)⟩

private theorem degreeInFinset_univ_le_three
    (L : SimpleGraph V) (v : V) (A S B : Finset V)
    (hcover : A ∪ S ∪ B = Finset.univ) :
    degreeInFinset L v Finset.univ ≤
      degreeInFinset L v A + degreeInFinset L v S + degreeInFinset L v B := by
  have hsub : Finset.univ.filter (L.Adj v) ⊆
      (A.filter (L.Adj v) ∪ S.filter (L.Adj v)) ∪ B.filter (L.Adj v) := by
    intro y hy
    have hycover : y ∈ A ∪ S ∪ B := by rw [hcover]; exact Finset.mem_univ _
    have hLy := (Finset.mem_filter.mp hy).2
    simp only [Finset.mem_union, Finset.mem_filter] at hycover ⊢
    tauto
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))

/-- A root's small-side nonroot leftover neighbors are genuine neighbors
of the generating graph. Missing own-part edges have already been recorded. -/
theorem subcriticalActualLeftover_small_trimmed_degree_le
    (h : RealizesSubcriticalProfile G alpha p) {v : V} (hv : v ∈ p.roots) :
    degreeInFinset (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha) v
      (D.nonretainedSmallVertices eta R₀ theta \ p.roots) ≤
      degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) := by
  apply Finset.card_le_card
  intro y hy
  obtain ⟨hyS, hLy⟩ := Finset.mem_filter.mp hy
  obtain ⟨hyS, hyB⟩ := Finset.mem_sdiff.mp hyS
  exact Finset.mem_filter.mpr ⟨hyS, (subcriticalActualLeftover_positive h hv hyB hLy).1⟩

/-- Exact finite row bound for a root, with no target-count overhead. -/
theorem subcriticalActualLeftover_root_degree_le
    (h : RealizesSubcriticalProfile G alpha p)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (ha : 0 ≤ alpha) (haFifth : alpha ≤ 1 / 5)
    (hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hsmall : ∀ v, (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      subcriticalSparseSideConstant k * theta * Fintype.card V)
    {v : V} (hv : v ∈ p.roots) :
    (degreeInFinset (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)
      v Finset.univ : ℝ) ≤
      5 * alpha * Fintype.card V +
        subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card := by
  let L := subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha
  have hcover : (D.visibleVertices theta \ p.roots) ∪
      (D.nonretainedSmallVertices eta R₀ theta \ p.roots) ∪ p.roots = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro y
    by_cases hyB : y ∈ p.roots
    · exact Finset.mem_union_right _ hyB
    have hy : y ∈ D.visibleVertices theta ∪ D.nonretainedSmallVertices eta R₀ theta := by
      rw [D.visibleVertices_union_nonretainedSmall hret]
      exact Finset.mem_univ _
    rcases Finset.mem_union.mp hy with hy | hy
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hy, hyB⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hy, hyB⟩))
  have hthree := degreeInFinset_univ_le_three L v
    (D.visibleVertices theta \ p.roots)
    (D.nonretainedSmallVertices eta R₀ theta \ p.roots) p.roots hcover
  have hthreeR : (degreeInFinset L v Finset.univ : ℝ) ≤
      (degreeInFinset L v (D.visibleVertices theta \ p.roots) : ℝ) +
      degreeInFinset L v (D.nonretainedSmallVertices eta R₀ theta \ p.roots) +
      degreeInFinset L v p.roots := by exact_mod_cast hthree
  have hvis := subcriticalActualLeftover_visible_degree_le h hv ha haFifth hB
  have hsmallR : (degreeInFinset L v
      (D.nonretainedSmallVertices eta R₀ theta \ p.roots) : ℝ) ≤
      degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) := by
    exact_mod_cast subcriticalActualLeftover_small_trimmed_degree_le h hv
  have hroot : (degreeInFinset L v p.roots : ℝ) ≤ p.roots.card := by
    exact_mod_cast (Finset.card_filter_le p.roots (L.Adj v))
  linarith [hsmall v]

/-- Every unordered leftover edge is charged to a root row. The bound is
valid for each generating graph separately, without fixing its remainder. -/
theorem subcriticalActualLeftover_edgeCount_le
    (h : RealizesSubcriticalProfile G alpha p)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (ha : 0 ≤ alpha) (haFifth : alpha ≤ 1 / 5)
    (hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hsmall : ∀ v, (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      subcriticalSparseSideConstant k * theta * Fintype.card V) :
    ((finiteGraphEdges
      (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)).card : ℝ) ≤
      (p.roots.card : ℝ) * (5 * alpha * Fintype.card V +
        subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card) := by
  let L := subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha
  have hcover := card_edgeFinset_le_sum_degreeInFinset_of_vertexCover L p.roots
    (subcriticalActualLeftover_roots_vertexCover h)
  have hcoverR : ((finiteGraphEdges L).card : ℝ) ≤
      ∑ v ∈ p.roots, (degreeInFinset L v Finset.univ : ℝ) := by
    exact_mod_cast hcover
  calc
    _ ≤ ∑ v ∈ p.roots, (degreeInFinset L v Finset.univ : ℝ) := hcoverR
    _ ≤ ∑ _v ∈ p.roots, (5 * alpha * Fintype.card V +
        subcriticalSparseSideConstant k * theta * Fintype.card V + (p.roots.card : ℝ)) := by
      exact Finset.sum_le_sum (fun v hv ↦
        subcriticalActualLeftover_root_degree_le h hret ha haFifth hB hsmall hv)
    _ = _ := by simp; ring

/-- Both the ordinary edge cardinality and the absolute signed defect size
are bounded by the profile error budget. Unlike the cardinality-of-patterns
estimate, this assertion does not need the fixed-remainder condition. -/
theorem subcriticalActualLeftover_edgeCount_signedSize_le_errorBudget
    {delta epsilon : ℝ} (h : RealizesSubcriticalProfile G alpha p)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2)
    (ht : 0 ≤ theta) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (hsmall : ∀ v, (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
      subcriticalSparseSideConstant k * theta * Fintype.card V) :
    ((finiteGraphEdges
      (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)).card : ℝ) ≤
        subcriticalProfileErrorBudget alpha delta epsilon p ∧
      |(subcriticalSignedDefectSize D eta R₀
        (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha) : ℝ)| ≤
        subcriticalProfileErrorBudget alpha delta epsilon p := by
  have hecard := (subcriticalActualLeftover_edgeCount_le h hret ha
    (by linarith) hB hsmall).trans
      (subcriticalLeftoverEdgeBudget_le_errorBudget p ha haHalf ht hd he hroot)
  refine ⟨hecard, ?_⟩
  have habs : |(subcriticalSignedDefectSize D eta R₀
      (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha) : ℝ)| ≤
      ((finiteGraphEdges
        (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)).card : ℝ) := by
    exact_mod_cast abs_subcriticalSignedDefectSize_le D eta R₀
      (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)
  exact habs.trans hecard

end InducedStars
