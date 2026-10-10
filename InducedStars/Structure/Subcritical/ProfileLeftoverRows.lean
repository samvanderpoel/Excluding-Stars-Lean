import InducedStars.Structure.Subcritical.ProfileLeftover
import InducedStars.Structure.Subcritical.ProfileResidual

/-!
# Unrecorded leftover rows

Full-target tests select the recorded rows. These lemmas do not replace them
by trimmed tests. The counted fiber keeps the entire remainder fixed.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}

theorem subcriticalActualLeftoverDefectGraph_le
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) (theta alpha : ℝ) :
    subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha ≤
      subcriticalRetainedIncidentDefectGraph G D eta R₀ := by
  intro x y h
  exact ((subcriticalLeftoverDefectGraph_adj _ _ _ x y).mp h).1

theorem subcriticalActualLeftover_not_recorded
    {v y : V}
    (hL : (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v y) :
    y ∉ subcriticalRecordedRootNeighbors G D eta R₀ theta alpha v := by
  intro hy
  exact ((subcriticalLeftoverDefectGraph_adj _ _ _ v y).mp hL).2.1 (Or.inl hy)

/-- Missing own-part edges of a retained root have already been recorded. -/
theorem subcriticalActualLeftover_not_own
    (h : RealizesSubcriticalProfile G alpha p) {v y : V}
    (hv : v ∈ p.retainedRoots) (hyB : y ∉ p.roots)
    (hy : y ∈ D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) :
    ¬ (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v y := by
  intro hL
  have hT := subcriticalActualLeftoverDefectGraph_le G D eta R₀ theta alpha hL
  have hsame : D.SamePart v y :=
    ⟨_, D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv), hy⟩
  have hnon : ¬ G.Adj v y := by
    rcases ((subcriticalDefectGraph_adj_iff G D).mp hT.1).1.2 with ho | he
    · exact ho.2
    · exact (he.1 hsame).elim
  apply subcriticalActualLeftover_not_recorded hL
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, Or.inl ⟨?_, Or.inl ?_⟩⟩
  · simpa [← h.roots_eq] using hyB
  · simpa [← h.retained_roots] using hv
  · exact ⟨p.retainedRoots_subset hv, hy, hL.ne.symm, hnon⟩

/-- A leftover edge from a root to a nonroot is a positive defect; all
missing own-part edges have already been put into the rooted graph. -/
theorem subcriticalActualLeftover_positive
    (h : RealizesSubcriticalProfile G alpha p) {v y : V}
    (hv : v ∈ p.roots) (hyB : y ∉ p.roots)
    (hL : (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v y) :
    G.Adj v y ∧ ¬ D.SamePart v y ∧ ¬ D.ActivePair v y := by
  have hT := subcriticalActualLeftoverDefectGraph_le G D eta R₀ theta alpha hL
  have hdef := ((subcriticalDefectGraph_adj_iff G D).mp hT.1).1.2
  rcases hdef with ho | he
  · rcases Finset.mem_union.mp hv with hv | hv
    · have hyown : y ∈ D.part (D.retainedVertexPart eta R₀ v
        (p.retainedRoots_subset hv)) := by
        obtain ⟨a, hva, hya⟩ := ho.1
        rwa [D.retainedVertexPart_eq_of_mem eta R₀ v (p.retainedRoots_subset hv) hva]
      exact (subcriticalActualLeftover_not_own h hv hyB hyown hL).elim
    · have hvout := (D.mem_nonretainedVertices eta R₀ v).mp (p.outsideRoots_subset hv)
      rcases hT.2 with hvret | hyret
      · exact (hvout hvret).elim
      · obtain ⟨a, hva, hya⟩ := ho.1
        have ha := (D.mem_retainedVertices_iff_of_mem_componentSupport
          (D.mem_componentSupport.mpr ⟨a.2, hya⟩)).mp hyret
        exact (hvout ((D.mem_retainedVertices eta R₀ v).mpr
          ⟨a.1, ha, D.mem_componentSupport.mpr ⟨a.2, hva⟩⟩)).elim
  · exact ⟨he.2.2, he.1, he.2.1⟩

/-- Every visible target which actually carries a leftover root-to-nonroot
edge failed its full-target high test. -/
theorem subcriticalActualLeftover_visible_full_low
    (h : RealizesSubcriticalProfile G alpha p) {v y : V} {a : D.PartIndex}
    (hv : v ∈ p.roots) (hyB : y ∉ p.roots)
    (ha : a ∈ D.visiblePartIndices theta) (hy : y ∈ D.part a)
    (hL : (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v y) :
    (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card := by
  have hpos := subcriticalActualLeftover_positive h hv hyB hL
  apply lt_of_not_ge
  intro hhigh
  apply subcriticalActualLeftover_not_recorded hL
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · simpa [← h.roots_eq] using hyB
  rcases Finset.mem_union.mp hv with hv | hv
  · refine Or.inl ⟨by simpa [← h.retained_roots] using hv, Or.inr ?_⟩
    refine ⟨a, ⟨p.retainedRoots_subset hv, ?_⟩, hhigh, hy, hpos.1⟩
    apply (D.mem_eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) a).mpr
    refine ⟨ha, ?_, ?_⟩
    · intro heq
      apply hpos.2.1
      refine ⟨a, ?_, hy⟩
      rw [heq]
      exact D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
    · intro hac
      apply hpos.2.2
      exact (D.activePair_iff_of_mem_parts
        (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hy).mpr hac
  · refine Or.inr ⟨by simpa [← h.outside_roots] using hv, a, ?_, hhigh, hy, hpos.1⟩
    have hT := subcriticalActualLeftoverDefectGraph_le G D eta R₀ theta alpha hL
    have hyret := hT.2.resolve_left
      ((D.mem_nonretainedVertices eta R₀ v).mp (p.outsideRoots_subset hv))
    exact (D.mem_retainedPartIndices eta R₀ a).mpr
      ((D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a.2, hy⟩)).mp hyret)

/-- Finite trimming of a low full-target row, with the original and trimmed
capacities kept distinct. -/
theorem subcriticalLowRow_trimmed_le_five
    (G : SimpleGraph V) (v : V) (Y B : Finset V) {alpha : ℝ}
    (halpha : 0 ≤ alpha) (halpha_fifth : alpha ≤ 1 / 5)
    (hB : (B.card : ℝ) ≤ alpha * Y.card)
    (hfull : (degreeInFinset G v Y : ℝ) ≤ 4 * alpha * Y.card) :
    (degreeInFinset G v (Y \ B) : ℝ) ≤ 5 * alpha * (Y \ B).card := by
  have hdeg : degreeInFinset G v (Y \ B) ≤ degreeInFinset G v Y := by
    unfold degreeInFinset
    exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
  have hcard : ((Y \ B).card : ℝ) ≥ (Y.card : ℝ) - B.card := by
    have hc : Y.card ≤ (Y \ B).card + B.card :=
      (Finset.card_le_card (show Y ⊆ (Y \ B) ∪ B by
        intro x hx; by_cases hb : x ∈ B <;> simp_all)).trans (Finset.card_union_le _ _)
    have hcR : (Y.card : ℝ) ≤ ((Y \ B).card : ℝ) + B.card := by exact_mod_cast hc
    linarith
  have haY := mul_le_mul_of_nonneg_right halpha_fifth (Nat.cast_nonneg Y.card)
  have hremain : (4 : ℝ) / 5 * Y.card ≤ ((Y \ B).card : ℝ) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hremain (show 0 ≤ 5 * alpha by positivity)
  have hdegR : (degreeInFinset G v (Y \ B) : ℝ) ≤ degreeInFinset G v Y := by
    exact_mod_cast hdeg
  nlinarith

/-- A visible leftover row has at most `5 alpha` of its trimmed capacity,
under the explicit root/target scale inequality. Empty rows are included. -/
theorem subcriticalActualLeftover_visible_trimmed_degree_le
    (h : RealizesSubcriticalProfile G alpha p) {v : V} {a : D.PartIndex}
    (hv : v ∈ p.roots) (ha : a ∈ D.visiblePartIndices theta)
    (halpha : 0 ≤ alpha) (halpha_fifth : alpha ≤ 1 / 5)
    (hB : (p.roots.card : ℝ) ≤ alpha * (D.part a).card) :
    (degreeInFinset (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha)
      v (D.part a \ p.roots) : ℝ) ≤ 5 * alpha * (D.part a \ p.roots).card := by
  let L := subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha
  by_cases hempty : ((D.part a \ p.roots).filter (L.Adj v)).Nonempty
  · obtain ⟨y, hy⟩ := hempty
    obtain ⟨hyA, hLy⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyA, hyB⟩ := Finset.mem_sdiff.mp hyA
    have hfull := subcriticalActualLeftover_visible_full_low h hv hyB ha hyA hLy
    have hbound := subcriticalLowRow_trimmed_le_five G v (D.part a) p.roots
      halpha halpha_fifth hB hfull.le
    have hsub : degreeInFinset L v (D.part a \ p.roots) ≤
        degreeInFinset G v (D.part a \ p.roots) := by
      apply Finset.card_le_card
      intro z hz
      obtain ⟨hzA, hLz⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hzA,
        (subcriticalActualLeftover_positive h hv (Finset.mem_sdiff.mp hzA).2 hLz).1⟩
    exact (show (degreeInFinset L v (D.part a \ p.roots) : ℝ) ≤
      degreeInFinset G v (D.part a \ p.roots) by exact_mod_cast hsub).trans hbound
  · have hz : degreeInFinset L v (D.part a \ p.roots) = 0 := by
      exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)
    rw [show degreeInFinset
      (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha) v
      (D.part a \ p.roots) = 0 from hz, Nat.cast_zero]
    positivity

/-- Root-cardinality and visible-part lower bounds imply the trimming
reserve with no asymptotic notation. -/
theorem subcriticalProfile_roots_card_le_alpha_target
    {rho : ℝ} (halpha : 0 ≤ alpha)
    (hroot : (p.roots.card : ℝ) ≤ rho * Fintype.card V)
    (hrho : rho ≤ alpha * theta / 2) {a : D.PartIndex}
    (hpart : theta * Fintype.card V / 2 ≤ ((D.part a).card : ℝ)) :
    (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
  have h₁ := mul_le_mul_of_nonneg_right hrho (Nat.cast_nonneg (Fintype.card V))
  have h₂ := mul_le_mul_of_nonneg_left hpart halpha
  nlinarith

namespace SubcriticalDivision

/-- The union of all parts in visible components. -/
def visibleVertices (D : SubcriticalDivision k V) (theta : ℝ) : Finset V :=
  (D.visiblePartIndices theta).biUnion D.part

theorem visibleVertices_union_nonretainedSmall
    (D : SubcriticalDivision k V) {eta theta : ℝ} {R₀ : ℕ}
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta) :
    D.visibleVertices theta ∪ D.nonretainedSmallVertices eta R₀ theta = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  by_cases hv : v ∈ D.visibleVertices theta
  · exact Finset.mem_union_left _ hv
  apply Finset.mem_union_right
  apply (D.mem_nonretainedSmallVertices eta R₀ theta v).mpr
  constructor
  · apply (D.mem_nonretainedVertices eta R₀ v).mpr
    intro hvret
    obtain ⟨a, ha, hva⟩ := D.exists_retained_part_of_mem eta R₀ v hvret
    exact hv (Finset.mem_biUnion.mpr ⟨a, hret ha, hva⟩)
  · intro hvs
    obtain ⟨i, hi, _, hvi⟩ := (D.mem_nonretainedVisibleVertices eta R₀ theta v).mp hvs
    obtain ⟨j, hvj⟩ := D.mem_componentSupport.mp hvi
    exact hv (Finset.mem_biUnion.mpr
      ⟨⟨i, j⟩, (D.mem_visiblePartIndices theta ⟨i, j⟩).mpr hi, hvj⟩)

theorem visibleVertices_disjoint_nonretainedSmall
    (D : SubcriticalDivision k V) (eta theta : ℝ) (R₀ : ℕ) :
    Disjoint (D.visibleVertices theta) (D.nonretainedSmallVertices eta R₀ theta) := by
  apply Finset.disjoint_left.mpr
  intro v hv hs
  obtain ⟨a, ha, hva⟩ := Finset.mem_biUnion.mp hv
  exact (D.not_visible_of_mem_nonretainedSmallVertices_of_mem_part hva hs)
    ((D.mem_visiblePartIndices theta a).mp ha)

theorem degree_visibleVertices_sdiff
    (D : SubcriticalDivision k V) (theta : ℝ) (L : SimpleGraph V) (v : V) (B : Finset V) :
    degreeInFinset L v (D.visibleVertices theta \ B) =
      ∑ a ∈ D.visiblePartIndices theta, degreeInFinset L v (D.part a \ B) := by
  have heq : (D.visibleVertices theta \ B).filter (L.Adj v) =
      (D.visiblePartIndices theta).biUnion fun a ↦ (D.part a \ B).filter (L.Adj v) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, visibleVertices, Finset.mem_biUnion]
    aesop
  change ((D.visibleVertices theta \ B).filter (L.Adj v)).card = _
  rw [heq, Finset.card_biUnion]
  · rfl
  · intro a _ b _ hab
    exact (D.part_disjoint hab).mono
      (Finset.filter_subset _ _ |>.trans Finset.sdiff_subset)
      (Finset.filter_subset _ _ |>.trans Finset.sdiff_subset)

end SubcriticalDivision

/-- Summing the disjoint trimmed visible rows loses no target-count factor. -/
theorem subcriticalActualLeftover_visible_degree_le
    (h : RealizesSubcriticalProfile G alpha p) {v : V}
    (hv : v ∈ p.roots) (halpha : 0 ≤ alpha) (halpha_fifth : alpha ≤ 1 / 5)
    (hB : ∀ a ∈ D.visiblePartIndices theta,
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card) :
    (degreeInFinset (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha) v
      (D.visibleVertices theta \ p.roots) : ℝ) ≤ 5 * alpha * Fintype.card V := by
  rw [D.degree_visibleVertices_sdiff, Nat.cast_sum]
  calc
    _ ≤ ∑ a ∈ D.visiblePartIndices theta, 5 * alpha * ((D.part a \ p.roots).card : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact subcriticalActualLeftover_visible_trimmed_degree_le h hv ha
        halpha halpha_fifth (hB a ha)
    _ ≤ ∑ a ∈ D.visiblePartIndices theta, 5 * alpha * ((D.part a).card : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Finset.card_le_card
        (show D.part a \ p.roots ⊆ D.part a from Finset.sdiff_subset)
    _ = 5 * alpha * ((D.visibleVertices theta).card : ℝ) := by
      rw [← Finset.mul_sum, ← Nat.cast_sum]
      congr 2
      rw [SubcriticalDivision.visibleVertices, Finset.card_biUnion]
      intro a _ b _ hab
      exact D.part_disjoint hab
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_le_univ (D.visibleVertices theta)) (by positivity)

/-- An independent subset of a star-free graph neighborhood has fewer than
`k` vertices. The root and all leaves are actual distinct vertices. -/
theorem subcritical_independent_neighborhood_card_le
    (G : SimpleGraph V) (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (v : V) (I : Finset V) (hadj : ∀ y ∈ I, G.Adj v y)
    (hind : G.IsIndepSet (I : Set V)) : I.card ≤ k - 1 := by
  suffices h : I.card < k by omega
  by_contra h
  have hki : Fintype.card (Fin k) ≤ I.card := by simpa using (le_of_not_gt h)
  obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hki
  apply hfree
  apply inducedEmbeds_inducedStar_of_fixed_center G v f
  · intro i
    exact hadj _ (hf ⟨i, rfl⟩)
  · intro i j
    by_cases hij : i = j
    · subst j
      exact G.irrefl
    · exact hind (hf ⟨i, rfl⟩) (hf ⟨j, rfl⟩) (fun hh ↦ hij (f.injective hh))

/-- No retained-incident leftover edge joins two nonretained vertices. -/
theorem subcriticalActualLeftover_outside_small_empty
    (h : RealizesSubcriticalProfile G alpha p) {v y : V}
    (hv : v ∈ p.outsideRoots) (hy : y ∈ D.nonretainedSmallVertices eta R₀ theta) :
    ¬ (subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v y := by
  intro hL
  have hT := subcriticalActualLeftoverDefectGraph_le G D eta R₀ theta alpha hL
  rcases hT.2 with hvret | hyret
  · exact ((D.mem_nonretainedVertices eta R₀ v).mp (p.outsideRoots_subset hv)) hvret
  · exact ((D.mem_nonretainedVertices eta R₀ y).mp
      ((D.mem_nonretainedSmallVertices eta R₀ theta y).mp hy).1) hyret

/-- Fixed-remainder adjacency on the small side, used by the encoding. -/
theorem subcriticalRemainderGraph_small_adj
    {H : SubcriticalRemainderGraph D eta R₀}
    (hH : subcriticalRemainderGraph G D eta R₀ = H) {x y : V}
    (hx : x ∈ D.nonretainedSmallVertices eta R₀ theta)
    (hy : y ∈ D.nonretainedSmallVertices eta R₀ theta) :
    (subcriticalRemainderGraphSpanningCoe H).Adj x y ↔ G.Adj x y := by
  rw [← hH, subcriticalRemainderGraph_adj]
  exact and_iff_left ((D.mem_nonretainedSmallVertices eta R₀ theta x).mp hx |>.1 |>
    fun hx ↦ ⟨hx, ((D.mem_nonretainedSmallVertices eta R₀ theta y).mp hy).1⟩)

/-- The small-side leftover row has bounded independence in the fixed
remainder graph, not in an unspecified varying graph. -/
theorem subcriticalActualLeftover_small_independence
    (h : RealizesSubcriticalProfile G alpha p)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    {H : SubcriticalRemainderGraph D eta R₀}
    (hH : subcriticalRemainderGraph G D eta R₀ = H) {v : V} (hv : v ∈ p.roots)
    (I : Finset V)
    (hI : I ⊆ (D.nonretainedSmallVertices eta R₀ theta \ p.roots).filter
      ((subcriticalActualLeftoverDefectGraph G D eta R₀ theta alpha).Adj v))
    (hind : (subcriticalRemainderGraphSpanningCoe H).IsIndepSet (I : Set V)) :
    I.card ≤ k - 1 := by
  apply subcritical_independent_neighborhood_card_le G hfree v I
  · intro y hy
    obtain ⟨hyS, hLy⟩ := Finset.mem_filter.mp (hI hy)
    exact (subcriticalActualLeftover_positive h hv (Finset.mem_sdiff.mp hyS).2 hLy).1
  · intro x hx y hy hne hxy
    apply hind hx hy hne
    exact (subcriticalRemainderGraph_small_adj hH
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hI hx)).1).1
      (Finset.mem_sdiff.mp (Finset.mem_filter.mp (hI hy)).1).1).mpr hxy

end InducedStars
