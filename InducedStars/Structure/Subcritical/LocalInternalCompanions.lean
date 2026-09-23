import InducedStars.Structure.Subcritical.LocalRowCompanions

/-!
# Auxiliary same-component companion interfaces

These retained interfaces use actual part indices and the loopless full
complementary degree of the own part, supplied by finite own-count adapters.
The current unified compensation proof uses the full high/medium support
directly and does not depend on these auxiliary interfaces.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

theorem subcriticalOwnComponent_visible
    (p : SubcriticalProfile D eta R₀ theta) (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {a : D.PartIndex}
    (hai : a.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1) :
    a ∈ D.visiblePartIndices theta := by
  apply hret
  apply (D.mem_retainedPartIndices eta R₀ a).mpr
  rw [hai]
  exact (D.mem_retainedPartIndices eta R₀ _).mp
    (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))

/-- A full-high companion of an eligible inside target is either an upper
active neighbor of the own part or a high recorded inside target. It
cannot be the own part, by the actual core adjacency relation. -/
theorem subcriticalInsideMedium_high_or_upper
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots) {a : D.PartIndex}
    (ha : a ∈ subcriticalProfileInsideRows p v hv)
    (han : a ∉ subcriticalProfileHighInsideRows p alpha v hv) :
    ∃ b : D.PartIndex, D.ActivePart a b ∧
      (b ∈ subcriticalProfileHighInsideRows p alpha v hv ∨
        b ∈ subcriticalUpperNeighborIndices p v hv) := by
  obtain ⟨har', hai⟩ := (mem_subcriticalProfileInsideRows p v hv a).mp ha
  have har : a ∈ subcriticalProfileRowIndices p v :=
    (mem_subcriticalProfileRowIndices p v a).mpr har'
  have ham : (p.rowCount v a : ℝ) < (1 - 2 * alpha) * (D.part a \ p.roots).card := by
    apply lt_of_not_ge
    intro hh
    exact han ((mem_subcriticalProfileHighInsideRows p alpha v hv a).mpr ⟨ha, hh⟩)
  obtain ⟨b, hab, hhigh⟩ := subcriticalRecordedMedium_high_companion R hfree homega halpha
    htheta hdelta hscale hret h har (htrim a (h.recorded_row_visible hret har)) ham
  have hbi : b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 :=
    (SubcriticalDivision.activePart_same_component hab).symm.trans hai
  by_cases hbact : D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) b
  · exact ⟨b, hab, Or.inr ((h.upperNeighborIndices_iff v hv b).mpr ⟨hbact, hhigh⟩)⟩
  have hbvis := subcriticalOwnComponent_visible p v hv hret hbi
  have hbne : b ≠ D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv) := by
    intro he
    have hna := ((D.mem_eligibleVisibleTargets eta R₀ theta v
      (p.retainedRoots_subset hv) a).mp ((h.retained_row_iff v hv a).mp har).1).2.2
    exact hna (he ▸ subcriticalActivePart_symm hab)
  have hallowed : D.EligibleProfileTarget eta R₀ theta v b :=
    ⟨p.retainedRoots_subset hv, (D.mem_eligibleVisibleTargets eta R₀ theta v
      (p.retainedRoots_subset hv) b).mpr ⟨hbvis, hbne, hbact⟩⟩
  have hb := h.high_allowed_recorded halpha.le halphaFifth (htrim b hbvis)
    (Or.inl ⟨hv, hallowed⟩) hhigh
  exact ⟨b, hab, Or.inl ((mem_subcriticalProfileHighInsideRows p alpha v hv b).mpr
    ⟨(mem_subcriticalProfileInsideRows p v hv b).mpr
      ⟨(mem_subcriticalProfileRowIndices p v b).mp hb.1, hbi⟩, hb.2⟩)⟩

/-- An inside target other than the own part, carrying neither an upper
label nor a high recorded row, has enough actual loopless nonneighbors.
Recorded low-count rows remain present in this case distinction. -/
theorem RealizesSubcriticalProfile.inside_not_high_complement_lower
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (halpha : 0 ≤ alpha) (halphaFifth : 5 * alpha ≤ 1)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (v : Fin n) (hv : v ∈ p.retainedRoots) {a : D.PartIndex}
    (hai : a.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1)
    (hane : a ≠ D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
    (htrim : 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hnu : a ∉ subcriticalUpperNeighborIndices p v hv)
    (hnh : a ∉ subcriticalProfileHighInsideRows p alpha v hv) :
    alpha * (D.part a).card ≤ (complementDegreeInFinset G v (D.part a) : ℝ) := by
  have hvis := subcriticalOwnComponent_visible p v hv hret hai
  have hvnot : v ∉ D.part a := fun ha ↦
    hane (D.mem_part_unique ha (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)))
  have hsum : (degreeInFinset G v (D.part a) : ℝ) +
      complementDegreeInFinset G v (D.part a) = (D.part a).card := by
    exact_mod_cast degreeInFinset_add_complementDegreeInFinset_of_notMem G v (D.part a) hvnot
  have hupper : (degreeInFinset G v (D.part a) : ℝ) < (1 - alpha) * (D.part a).card := by
    by_cases hact : D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) a
    · apply lt_of_not_ge
      intro hh
      exact hnu ((h.upperNeighborIndices_iff v hv a).mpr ⟨hact, hh⟩)
    by_cases har : a ∈ subcriticalProfileRowIndices p v
    · apply (h.medium_recorded_full_degree har halpha htrim ?_).2
      apply lt_of_not_ge
      intro hh
      exact hnh ((mem_subcriticalProfileHighInsideRows p alpha v hv a).mpr
        ⟨(mem_subcriticalProfileInsideRows p v hv a).mpr
          ⟨(mem_subcriticalProfileRowIndices p v a).mp har, hai⟩, hh⟩)
    · have helig := (D.mem_eligibleVisibleTargets eta R₀ theta v
        (p.retainedRoots_subset hv) a).mpr ⟨hvis, hane, hact⟩
      have hfour : (degreeInFinset G v (D.part a) : ℝ) < 4 * alpha * (D.part a).card := by
        apply lt_of_not_ge
        intro hh
        exact har ((h.retained_row_iff v hv a).mpr ⟨helig, hh⟩)
      have hm := mul_le_mul_of_nonneg_right halphaFifth (Nat.cast_nonneg (D.part a).card)
      nlinarith
  linarith

/-- Every medium active neighbor has an adjacent high inside target or an
upper neighbor, once the own missing degree is non-low. This is the exact
opposite-row contradiction underlying both negative-root exceptional cases. -/
theorem subcriticalMediumNeighbor_high_or_upper
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hown : alpha * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ≤
      (complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ))
    {s : D.PartIndex} (hs : s ∈ subcriticalMediumNeighborIndices p v hv) :
    ∃ b : D.PartIndex, D.ActivePart s b ∧
      (b ∈ subcriticalProfileHighInsideRows p alpha v hv ∨
        b ∈ subcriticalUpperNeighborIndices p v hv) := by
  have hsa := (mem_subcriticalMediumNeighborIndices p v hv s).mp hs
  obtain ⟨i, j, t, ho, rfl, hjt⟩ := hsa.1
  have hroot : v ∈ D.parts i j := by
    change v ∈ D.part ⟨i, j⟩
    rw [← ho]
    exact D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hi : i ∈ D.visibleComponentIndices theta := by
    have hvi := hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
    simpa only [ho, D.mem_visiblePartIndices] using hvi
  have hlo : alpha * (D.parts i t).card ≤ (degreeInFinset G v (D.parts i t) : ℝ) := by
    apply le_of_lt
    apply lt_of_not_ge
    intro hh
    have hh' := (h.tail_labels v hv ⟨i, t⟩ hsa.1).2.mpr hh
    rw [hsa.2] at hh'
    cases hh'
  have hhi : (degreeInFinset G v (D.parts i t) : ℝ) ≤ (1 - alpha) * (D.parts i t).card := by
    apply le_of_lt
    apply lt_of_not_ge
    intro hh
    have hh' := (h.tail_labels v hv ⟨i, t⟩ hsa.1).1.mpr hh
    rw [hsa.2] at hh'
    cases hh'
  by_contra hn
  apply subcriticalOppositeRow_impossible R hfree homega halpha htheta hdelta hscale
    i hi j t hjt v hroot (by
      change alpha * (D.part ⟨i, j⟩).card ≤
        (complementDegreeInFinset G v (D.part ⟨i, j⟩) : ℝ)
      rw [← ho]
      exact hown) hlo hhi
  intro u htu huj
  have hact : D.ActivePart (⟨i, t⟩ : D.PartIndex) ⟨i, u⟩ :=
    ⟨i, t, u, rfl, rfl, htu⟩
  have hnu : (⟨i, u⟩ : D.PartIndex) ∉ subcriticalUpperNeighborIndices p v hv :=
    fun hh ↦ hn ⟨⟨i, u⟩, hact, Or.inr hh⟩
  have hnh : (⟨i, u⟩ : D.PartIndex) ∉ subcriticalProfileHighInsideRows p alpha v hv :=
    fun hh ↦ hn ⟨⟨i, u⟩, hact, Or.inl hh⟩
  apply h.inside_not_high_complement_lower halpha.le halphaFifth hret v hv
    (a := ⟨i, u⟩) (by simp only [ho]) ?_
    (htrim ⟨i, u⟩ ((D.mem_visiblePartIndices theta ⟨i, u⟩).mpr hi)) hnu hnh
  intro he
  rw [ho] at he
  exact huj (by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he)

/-- With one possible upper target and no high inside row, every recorded
inside row and every medium active neighbor is adjacent to that target.
These are the exact incidence conditions used by the relocation bound. -/
theorem subcriticalUniqueUpper_noHigh_adjacencies
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hown : alpha * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ≤
      (complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ))
    (r : D.PartIndex)
    (hunique : ∀ b ∈ subcriticalUpperNeighborIndices p v hv, b = r)
    (hhigh : subcriticalProfileHighInsideRows p alpha v hv = ∅) :
    (∀ a ∈ subcriticalProfileInsideRows p v hv, D.ActivePart a r) ∧
      (∀ s ∈ subcriticalMediumNeighborIndices p v hv, D.ActivePart s r) := by
  have hnone (b : D.PartIndex) : b ∉ subcriticalProfileHighInsideRows p alpha v hv := by
    simp [hhigh]
  constructor
  · intro a ha
    obtain ⟨b, hab, hb⟩ := subcriticalInsideMedium_high_or_upper R hfree homega halpha
      halphaFifth htheta hdelta hscale hret h htrim v hv ha (hnone a)
    rcases hb with hb | hb
    · exact (hnone b hb).elim
    · simpa only [hunique b hb] using hab
  · intro s hs
    obtain ⟨b, hsb, hb⟩ := subcriticalMediumNeighbor_high_or_upper R hfree homega halpha
      halphaFifth htheta hdelta hscale hret h htrim v hv hown hs
    rcases hb with hb | hb
    · exact (hnone b hb).elim
    · simpa only [hunique b hb] using hsb

/-- The upper-empty high-negative branch: each medium active neighbor
has a genuine high inside companion. -/
theorem subcriticalMediumNeighbor_highInside_of_noUpper
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hown : alpha * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ≤
      (complementDegreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ))
    (hupper : subcriticalUpperNeighborIndices p v hv = ∅)
    {s : D.PartIndex} (hs : s ∈ subcriticalMediumNeighborIndices p v hv) :
    ∃ b ∈ subcriticalProfileHighInsideRows p alpha v hv, D.ActivePart s b := by
  obtain ⟨b, hsb, hb⟩ := subcriticalMediumNeighbor_high_or_upper R hfree homega halpha
    halphaFifth htheta hdelta hscale hret h htrim v hv hown hs
  rcases hb with hb | hb
  · exact ⟨b, hb, hsb⟩
  · simp only [hupper, Finset.notMem_empty] at hb

/-- The high-degree exceptional configuration has no inside row at all.
In particular a bad root with a nonempty recorded inside row is impossible
when both the upper-label and high-inside sets are empty. -/
theorem subcriticalInsideRows_empty_of_noUpper_noHigh
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaFifth : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta,
      2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hupper : subcriticalUpperNeighborIndices p v hv = ∅)
    (hhigh : subcriticalProfileHighInsideRows p alpha v hv = ∅) :
    subcriticalProfileInsideRows p v hv = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have han : a ∉ subcriticalProfileHighInsideRows p alpha v hv := by simp [hhigh]
  obtain ⟨b, _, hb⟩ := subcriticalInsideMedium_high_or_upper R hfree homega halpha
    halphaFifth htheta hdelta hscale hret h htrim v hv ha han
  simpa only [hupper, hhigh, Finset.notMem_empty, or_self] using hb

/-- A medium own row forces an upper active-neighbor label. The root is
in its own part and is not in any adjacent core part. -/
theorem subcriticalMediumOwn_upper_nonempty
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hdelta : delta ≤ subcriticalRowCountingTolerance k) (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hlower : alpha * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ≤
      (degreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ))
    (hupper : (degreeInFinset G v
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ) ≤
      (1 - alpha) * (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :
    (subcriticalUpperNeighborIndices p v hv).Nonempty := by
  let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hvis : a ∈ D.visiblePartIndices theta :=
    hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have hnot : v ∉ subcriticalCoreNeighborUnion D a.1 a.2 := by
    intro hh
    obtain ⟨j, hj, hvj⟩ := (mem_subcriticalCoreNeighborUnion D a.1 a.2 v).mp hh
    have he : (⟨a.1, j⟩ : D.PartIndex) = a :=
      D.mem_part_unique hvj (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
    have hja : j = a.2 := by
      have he' : (⟨a.1, j⟩ : D.PartIndex) = ⟨a.1, a.2⟩ := he
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using he'
    exact (D.core a.1).graph.ne_of_adj hj hja.symm
  obtain ⟨j, hj, hh⟩ := subcriticalMediumDegree_companion R hfree homega halpha htheta
    hdelta hscale a.1 ((D.mem_visiblePartIndices theta a).mp hvis) a.2 v hnot hlower hupper
  refine ⟨⟨a.1, j⟩, (h.upperNeighborIndices_iff v hv ⟨a.1, j⟩).mpr ⟨?_, hh⟩⟩
  exact ⟨a.1, a.2, j, rfl, rfl, hj⟩

end InducedStars
