import InducedStars.Structure.Subcritical.AlignmentWitness
import InducedStars.Structure.Subcritical.ComponentAlignment

/-!
# Alignment with an explicit candidate sequence

All reference cells are pulled back by one fixed permutation. The division
itself is never relabeled. The finite component construction uses signed
rectangles and retains actual graph isomorphisms.
-/

noncomputable section

open Finset
open scoped BigOperators Classical symmDiff

namespace InducedStars

open DenseGraph FiniteWeightedGraph

variable {k n : ℕ}

theorem subcriticalPaletteGap_le_one (k : ℕ) : subcriticalPaletteGap k ≤ 1 :=
  (min_le_left _ _).trans (pK_mem_Icc k).2

/-- The full reference covers every vertex either by one actual cell or by
an exactly zero row. This includes infinite candidate sequences. -/
theorem subcritical_aligned_reference_cell_or_zero
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (x : Fin n) :
    (∃ a, x ∈ subcriticalAlignedReferenceCellVertices L n pi a) ∨
      ∀ y, ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 := by
  by_cases h : ∃ a, x ∈ subcriticalAlignedReferenceCellVertices L n pi a
  · exact Or.inl h
  · right
    intro y
    apply subcriticalReference_weight_eq_zero_of_mem_realizedRemainder_left hk L pi
    rw [mem_subcriticalRealizedReferenceRemainder]
    exact fun a ha ↦ h ⟨a, ha⟩

/-- The converse cell alignment specialized to a part of a regular blow-up,
without removing the candidate's unused zero region. -/
theorem subcritical_large_part_has_reference_cell
    (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    (H : SimpleGraph (Fin n)) (hH : IsSubcriticalRegularBlowupFor D H)
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (a : D.PartIndex) {m : ℝ} (hm : 0 < m)
    (hsize : 2 * m ≤ (D.part a).card) (hdiag : 2 ≤ subcriticalPaletteGap k * m)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * m ^ 2) :
    ∃ c, ((D.part a \ subcriticalAlignedReferenceCellVertices L n pi c).card : ℝ) < m := by
  apply subcritical_large_clique_concentrates_in_cell H
    ((subcriticalReferenceWeightedGraph hk L n).permute pi)
    (subcriticalAlignedReferenceCellVertices L n pi) (D.part a)
    (subcriticalPaletteGap_pos hk) (subcriticalPaletteGap_le_one k) hm hsize hdiag
  · intro x hx y hy hxy
    exact hH.part_complete a hx hy hxy
  · exact subcritical_aligned_reference_cell_or_zero hk L pi
  · intro c x hx y hy
    exact subcriticalReference_weight_le_one_sub_paletteGap_of_mem_aligned_cell_of_notMem
      hk L pi c hx hy
  · simpa using hcut

/-- Matching all sufficiently large cells of one explicit candidate block
produces one entire canonical component, with two-sided cell error. -/
theorem subcritical_reference_component_has_match
    (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    (H : SimpleGraph (Fin n)) (hH : IsSubcriticalRegularBlowupFor D H)
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (j : ℕ) {m : ℝ} (hm : 0 < m)
    (hsize : ∀ v, 2 * (k - 1 : ℕ) * m ≤
      (subcriticalAlignedComponentCells L n pi j v).card)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * m ^ 2) :
    ∃ (i : Fin D.componentCount) (e : (L.core j).graph ≃g (D.core i).graph),
      ∀ v,
        m ≤ ((subcriticalAlignedComponentCells L n pi j v ∩ D.parts i (e v)).card : ℝ) ∧
        ((D.parts i (e v) \ subcriticalAlignedComponentCells L n pi j v).card : ℝ) < m ∧
        ((subcriticalAlignedComponentCells L n pi j v \ D.parts i (e v)).card : ℝ) ≤
          (((L.core j).order : ℝ) + 1) * m ∧
        ((D.parts i (e v) ∆ subcriticalAlignedComponentCells L n pi j v).card : ℝ) ≤
          (((L.core j).order : ℝ) + 2) * m := by
  apply subcritical_exists_component_cell_alignment hk D H hH
    ((subcriticalReferenceWeightedGraph hk L n).permute pi) (L.core j)
    (subcriticalAlignedComponentCells L n pi j)
  · intro u v huv
    apply subcriticalAlignedReferenceCellVertices_disjoint L pi
    exact fun h ↦ huv (by simpa using h)
  · exact subcriticalPaletteGap_pos hk
  · exact subcriticalPaletteGap_le_one k
  · exact hm
  · exact hsize
  · intro v x hx y hy
    exact subcriticalReference_weight_of_mem_same_aligned_cell hk L pi ⟨j, v⟩ hx hy
  · intro v x hx y hy
    exact subcriticalReference_weight_le_one_sub_paletteGap_of_mem_aligned_cell_of_notMem
      hk L pi ⟨j, v⟩ hx hy
  · intro u v huv x hx y hy
    rw [subcriticalReference_weight_of_mem_active_aligned_cells hk L pi j huv hx hy]
    exact min_le_left _ _
  · simpa using hcut

/-- A large part pins down its whole division component. Its matched core
has bounded order because one of its reference cells is large, not because
all cores in the candidate sequence have bounded order. -/
theorem subcritical_large_part_component_match
    (hk : 3 ≤ k) (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (H : SimpleGraph (Fin n)) (hH : IsSubcriticalRegularBlowupFor D H)
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (a : D.PartIndex) {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (hpart : t * n ≤ (D.part a).card)
    (hsmall : 2 * (k - 1 : ℕ) * m ≤ t * n / 4)
    (hround : 4 ≤ t * n / 4) (hdiag : 2 ≤ subcriticalPaletteGap k * m)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * m ^ 2) :
    ∃ (j : ℕ) (e : (D.core a.1).graph ≃g (L.core j).graph),
      ((L.core j).order : ℝ) ≤ 4 / t ∧
      ∀ u,
        t * n / 4 ≤ (subcriticalAlignedComponentCells L n pi j (e u)).card ∧
        m ≤ ((subcriticalAlignedComponentCells L n pi j (e u) ∩ D.parts a.1 u).card : ℝ) ∧
        ((D.parts a.1 u \ subcriticalAlignedComponentCells L n pi j (e u)).card : ℝ) < m ∧
        ((subcriticalAlignedComponentCells L n pi j (e u) \ D.parts a.1 u).card : ℝ) ≤
          (((L.core j).order : ℝ) + 1) * m ∧
        ((D.parts a.1 u ∆ subcriticalAlignedComponentCells L n pi j (e u)).card : ℝ) ≤
          (((L.core j).order : ℝ) + 2) * m := by
  have hr : (1 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k - 1)
  have hmSmall : 2 * m ≤ t * n / 4 := by nlinarith
  have hpart2 : 2 * m ≤ (D.part a).card := by linarith
  obtain ⟨⟨j, v⟩, hspill⟩ := subcritical_large_part_has_reference_cell
    hk D H hH L pi a hm hpart2 hdiag hcut
  let C := subcriticalAlignedComponentCells L n pi j
  have hcard : ((D.part a ∩ C v).card : ℝ) + (D.part a \ C v).card =
      (D.part a).card := by exact_mod_cast Finset.card_inter_add_card_sdiff (D.part a) (C v)
  have hinter : ((D.part a ∩ C v).card : ℝ) ≤ (C v).card := by
    exact_mod_cast Finset.card_le_card Finset.inter_subset_right
  have hlarge : t * n / 2 ≤ (C v).card := by
    change ((D.part a \ C v).card : ℝ) < m at hspill
    linarith
  have hsiblings (w : Fin (L.core j).order) : t * n / 4 ≤ (C w).card :=
    subcriticalAlignedReferenceCell_card_ge_quarter_of_card_ge_half
      hn L pi j v w hround hlarge
  have horder : ((L.core j).order : ℝ) ≤ 4 / t :=
    subcriticalReference_coreOrder_le_four_div_of_cell_card_ge_half
      hn L pi j v ht hround hlarge
  obtain ⟨i, e, he⟩ := subcritical_reference_component_has_match hk D H hH L pi j hm
    (fun w ↦ hsmall.trans (hsiblings w)) hcut
  have hi : i = a.1 := by
    by_contra hne
    have houtside := subcritical_cell_outside_component_lt D H hH
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) (C v) ⟨i, e v⟩
      (subcriticalPaletteGap_pos hk) (subcriticalPaletteGap_le_one k) hm (he v).1
      (fun x hx y hy ↦ subcriticalReference_weight_of_mem_same_aligned_cell
        hk L pi ⟨j, v⟩ hx hy) (by simpa using hcut)
    have hsub : D.part a ∩ C v ⊆ C v \ D.componentSupport i := by
      intro x hx
      obtain ⟨hxP, hxC⟩ := Finset.mem_inter.mp hx
      refine Finset.mem_sdiff.mpr ⟨hxC, ?_⟩
      intro hxi
      have hxa : x ∈ D.componentSupport a.1 :=
        SubcriticalDivision.mem_componentSupport.mpr ⟨a.2, hxP⟩
      exact Finset.disjoint_left.mp (D.componentSupport_disjoint hne) hxi hxa
    have hle : ((D.part a ∩ C v).card : ℝ) ≤ (C v \ D.componentSupport i).card := by
      exact_mod_cast Finset.card_le_card hsub
    change ((D.part a \ C v).card : ℝ) < m at hspill
    nlinarith
  subst i
  refine ⟨j, e.symm, horder, ?_⟩
  intro u
  refine ⟨hsiblings (e.symm u), ?_⟩
  simpa using he (e.symm u)

/-- Two division components with large overlaps in the cells of the same
reference block must be the same component. -/
theorem subcritical_component_unique_of_reference_matches
    (hk : 3 ≤ k) (D : SubcriticalDivision k (Fin n))
    (H : SimpleGraph (Fin n)) (hH : IsSubcriticalRegularBlowupFor D H)
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (i₁ i₂ : Fin D.componentCount) (j₁ j₂ : ℕ)
    (e₁ : (D.core i₁).graph ≃g (L.core j₁).graph)
    (e₂ : (D.core i₂).graph ≃g (L.core j₂).graph)
    {m : ℝ} (hm : 0 < m) (hj : j₁ = j₂)
    (h₁ : ∀ u, m ≤ ((subcriticalAlignedComponentCells L n pi j₁ (e₁ u) ∩
      D.parts i₁ u).card : ℝ))
    (h₂ : ∀ u, m ≤ ((subcriticalAlignedComponentCells L n pi j₂ (e₂ u) ∩
      D.parts i₂ u).card : ℝ))
    (hcut : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * m ^ 2) : i₁ = i₂ := by
  subst j₂
  by_contra hi
  let u : Fin (D.core i₁).order := ⟨0, (D.core i₁).order_pos⟩
  let v := e₂.symm (e₁ u)
  have hv : e₂ v = e₁ u := by simp [v]
  have hab : (⟨i₁, u⟩ : D.PartIndex) ≠ ⟨i₂, v⟩ :=
    fun h ↦ hi (congrArg Sigma.fst h)
  have ha := subcritical_activePart_of_matched_cell_edge D H hH
    ((subcriticalReferenceWeightedGraph hk L n).permute pi)
    (subcriticalAlignedComponentCells L n pi j₁ (e₁ u))
    (subcriticalAlignedComponentCells L n pi j₁ (e₁ u))
    ⟨i₁, u⟩ ⟨i₂, v⟩ (subcriticalPaletteGap_pos hk) hm hab (h₁ u)
    (by simpa only [hv, SubcriticalDivision.part] using h₂ v)
    (by
      intro x hx y hy
      rw [subcriticalReference_weight_of_mem_same_aligned_cell hk L pi ⟨j₁, e₁ u⟩ hx hy]
      exact subcriticalPaletteGap_le_one k)
    (by simpa using hcut)
  exact hi (SubcriticalDivision.activePart_same_component ha)

/-- The same canonical component cannot be matched to two distinct
reference blocks: one large overlap would lie wholly in the other match's
small spill. This uses actual labels, not representation independence. -/
theorem subcritical_reference_block_unique_of_part_matches
    (D : SubcriticalDivision k (Fin n)) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : Fin D.componentCount) (j₁ j₂ : ℕ)
    (e₁ : (D.core i).graph ≃g (L.core j₁).graph)
    (e₂ : (D.core i).graph ≃g (L.core j₂).graph)
    {m : ℝ}
    (h₁ : ∀ u, m ≤ ((subcriticalAlignedComponentCells L n pi j₁ (e₁ u) ∩
      D.parts i u).card : ℝ))
    (h₂ : ∀ u, ((D.parts i u \ subcriticalAlignedComponentCells L n pi j₂ (e₂ u)).card : ℝ) < m) :
    j₁ = j₂ := by
  by_contra hne
  let u : Fin (D.core i).order := ⟨0, (D.core i).order_pos⟩
  have hdisj := subcriticalAlignedReferenceCellVertices_disjoint L pi
    (show (⟨j₁, e₁ u⟩ : SubcriticalReferenceCellIndex L) ≠ ⟨j₂, e₂ u⟩ from
      fun h ↦ hne (congrArg Sigma.fst h))
  have hsub : subcriticalAlignedComponentCells L n pi j₁ (e₁ u) ∩ D.parts i u ⊆
      D.parts i u \ subcriticalAlignedComponentCells L n pi j₂ (e₂ u) := by
    intro x hx
    obtain ⟨hxC, hxP⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxP, fun hy ↦ Finset.disjoint_left.mp hdisj hxC hy⟩
  have hcard : ((subcriticalAlignedComponentCells L n pi j₁ (e₁ u) ∩ D.parts i u).card : ℝ) ≤
      (D.parts i u \ subcriticalAlignedComponentCells L n pi j₂ (e₂ u)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact (not_lt_of_ge ((h₁ u).trans hcard)) (h₂ u)

/-- A single injective matching for all visible components, including
coverage of every reference block whose cells exceed the stated threshold.
The assignment and the isomorphisms are constructed, not assumed. -/
theorem subcritical_exists_component_alignment
    (hk : 3 ≤ k) (hn : 0 < n) (D : SubcriticalDivision k (Fin n))
    (H : SimpleGraph (Fin n)) (hH : IsSubcriticalRegularBlowupFor D H)
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    {t m : ℝ} (ht : 0 < t) (hm : 0 < m)
    (B : ℕ) (hB : 4 / t ≤ (B : ℝ))
    (hsmall : 2 * (k - 1 : ℕ) * m ≤ t * n / 4)
    (hround : 4 ≤ t * n / 4) (hdiag : 2 ≤ subcriticalPaletteGap k * m)
    (herror : ((B : ℝ) + 2) * m ≤ t * n)
    (hcut : finiteLabeledCutDist (ofSimpleGraph H)
      ((subcriticalReferenceWeightedGraph hk L n).permute pi) * (n : ℝ) ^ 2 <
        subcriticalPaletteGap k * m ^ 2) :
    Nonempty (SubcriticalComponentAlignment D L pi t m B) := by
  classical
  let I := {i // i ∈ D.visibleComponentIndices t}
  have hlocal (i : I) : ∃ (j : ℕ) (e : (D.core i.val).graph ≃g (L.core j).graph),
      ((L.core j).order : ℝ) ≤ 4 / t ∧
      ∀ u,
        t * n / 4 ≤ (subcriticalAlignedComponentCells L n pi j (e u)).card ∧
        m ≤ ((subcriticalAlignedComponentCells L n pi j (e u) ∩ D.parts i.val u).card : ℝ) ∧
        ((D.parts i.val u \ subcriticalAlignedComponentCells L n pi j (e u)).card : ℝ) < m ∧
        ((subcriticalAlignedComponentCells L n pi j (e u) \ D.parts i.val u).card : ℝ) ≤
          (((L.core j).order : ℝ) + 1) * m ∧
        ((D.parts i.val u ∆ subcriticalAlignedComponentCells L n pi j (e u)).card : ℝ) ≤
          (((L.core j).order : ℝ) + 2) * m := by
    obtain ⟨u, hu⟩ := (D.mem_visibleComponentIndices t i.val).mp i.property
    exact subcritical_large_part_component_match hk hn D H hH L pi ⟨i.val, u⟩
      ht hm (by simpa [SubcriticalDivision.part] using hu) hsmall hround hdiag hcut
  choose f e horder hp using hlocal
  have hfactive (i : I) : blockIndexActive L.count (f i) := by
    let u : Fin (D.core i.val).order := ⟨0, (D.core i.val).order_pos⟩
    apply subcriticalReference_blockIndexActive_of_alignedCell_nonempty L pi (f i) (e i u)
    apply Finset.card_pos.mp
    have := (hp i u).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < t * n / 4) this)
  let f' : I → {j : ℕ // blockIndexActive L.count j} := fun i ↦ ⟨f i, hfactive i⟩
  have hf : Function.Injective f' := by
    intro i₁ i₂ hij
    apply Subtype.ext
    exact subcritical_component_unique_of_reference_matches hk D H hH L pi
      i₁.val i₂.val (f i₁) (f i₂) (e i₁) (e i₂) hm
      (congrArg Subtype.val hij) (fun u ↦ (hp i₁ u).2.1)
      (fun u ↦ (hp i₂ u).2.1) hcut
  refine ⟨{
    assignment := ⟨f', hf⟩
    coreIso := e
    order_le := fun i ↦ ?_
    cell_large := fun i u ↦ (hp i u).1
    overlap := fun i u ↦ (hp i u).2.1
    spill := fun i u ↦ (hp i u).2.2.1
    symmetric_difference := fun i u ↦ ?_
    covers_large_blocks := ?_ }⟩
  · exact_mod_cast (horder i).trans hB
  · exact (hp i u).2.2.2.2.trans
      (mul_le_mul_of_nonneg_right (by linarith [horder i]) hm.le)
  · intro j hj
    obtain ⟨i, ej, hej⟩ := subcritical_reference_component_has_match hk D H hH L pi j.val hm
      (fun v ↦ hsmall.trans (by linarith [hj v])) hcut
    let v : Fin (L.core j.val).order := ⟨0, (L.core j.val).order_pos⟩
    have hordj : ((L.core j.val).order : ℝ) ≤ B :=
      (subcriticalReference_coreOrder_le_four_div_of_cell_card_ge_half
        hn L pi j.val v ht hround (by linarith [hj v])).trans hB
    have hcard : ((subcriticalAlignedComponentCells L n pi j.val v ∩ D.parts i (ej v)).card : ℝ) +
        (subcriticalAlignedComponentCells L n pi j.val v \ D.parts i (ej v)).card =
        (subcriticalAlignedComponentCells L n pi j.val v).card := by
      exact_mod_cast Finset.card_inter_add_card_sdiff
        (subcriticalAlignedComponentCells L n pi j.val v) (D.parts i (ej v))
    have hinter : ((subcriticalAlignedComponentCells L n pi j.val v ∩
        D.parts i (ej v)).card : ℝ) ≤ (D.parts i (ej v)).card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_right
    have hrem : ((subcriticalAlignedComponentCells L n pi j.val v \ D.parts i (ej v)).card : ℝ) ≤
        ((B : ℝ) + 1) * m :=
      (hej v).2.2.1.trans (mul_le_mul_of_nonneg_right (by linarith) hm.le)
    have hvis : i ∈ D.visibleComponentIndices t := by
      apply (D.mem_visibleComponentIndices t i).mpr
      refine ⟨ej v, ?_⟩
      simp only [Fintype.card_fin]
      nlinarith [hj v]
    let ii : I := ⟨i, hvis⟩
    refine ⟨ii, Subtype.ext ?_⟩
    change f ii = j.val
    apply subcritical_reference_block_unique_of_part_matches D L pi i (f ii) j.val
      (e ii) ej.symm (fun u ↦ (hp ii u).2.1)
    intro u
    simpa using (hej (ej.symm u)).2.1

end InducedStars
