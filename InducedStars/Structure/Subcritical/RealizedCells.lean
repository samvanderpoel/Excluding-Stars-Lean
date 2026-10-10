import InducedStars.Structure.Subcritical.Reference

/-!
# Finitely realized cells of a sampled subcritical reference

An admissible candidate may have countably many component blocks, but a
reference sampled on `Fin n` realizes at most `n` of its literal core cells.
This file packages exactly those cells.  A single vertex permutation is kept
as an explicit parameter, so all later alignment arguments remain in the
original labels.
-/

noncomputable section

open Finset Set
open scoped Classical

namespace InducedStars

variable {k n : ℕ}

/-- A literal core-cell label of an admissible block sequence. -/
abbrev SubcriticalReferenceCellIndex (L : AdmissibleBlockSequence k) :=
  Σ i : ℕ, Fin (L.core i).order

/-- The unpermuted sampled vertices in one literal candidate cell. -/
abbrev subcriticalReferenceCellVerticesAt
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (a : SubcriticalReferenceCellIndex L) : Finset (Fin n) :=
  subcriticalReferenceCellVertices L n a.1 a.2

/-- Two distinct literal cell labels have disjoint sampled vertex sets. -/
theorem subcriticalReferenceCellVerticesAt_disjoint
    (L : AdmissibleBlockSequence k)
    {a b : SubcriticalReferenceCellIndex L} (hab : a ≠ b) :
    Disjoint (subcriticalReferenceCellVerticesAt L n a)
      (subcriticalReferenceCellVerticesAt L n b) := by
  rcases a with ⟨i, v⟩
  rcases b with ⟨j, w⟩
  by_cases hij : i = j
  · subst j
    apply subcriticalReferenceCellVertices_disjoint_of_ne L
    intro hvw
    apply hab
    cases hvw
    rfl
  · exact (subcriticalReferenceBlockVertices_disjoint L hij).mono
      (subcriticalReferenceCellVertices_subset_blockVertices L v)
      (subcriticalReferenceCellVertices_subset_blockVertices L w)

/-- A sampled vertex belongs to at most one literal candidate cell. -/
theorem subcriticalReferenceCellIndex_unique
    (L : AdmissibleBlockSequence k) {x : Fin n}
    {a b : SubcriticalReferenceCellIndex L}
    (ha : x ∈ subcriticalReferenceCellVerticesAt L n a)
    (hb : x ∈ subcriticalReferenceCellVerticesAt L n b) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp
    (subcriticalReferenceCellVerticesAt_disjoint L hab) ha hb

/-- Vertices that lie in some literal cell of the full sampled candidate. -/
def subcriticalReferenceCellCoveredVertices
    (L : AdmissibleBlockSequence k) (n : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun x ↦
    ∃ a : SubcriticalReferenceCellIndex L,
      x ∈ subcriticalReferenceCellVerticesAt L n a

@[simp] theorem mem_subcriticalReferenceCellCoveredVertices
    {L : AdmissibleBlockSequence k} {x : Fin n} :
    x ∈ subcriticalReferenceCellCoveredVertices L n ↔
      ∃ a : SubcriticalReferenceCellIndex L,
        x ∈ subcriticalReferenceCellVerticesAt L n a := by
  simp [subcriticalReferenceCellCoveredVertices]

/-- The unique literal cell label of a cell-covered sampled vertex. -/
def subcriticalReferenceCellIndexOfCovered
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (x : {x // x ∈ subcriticalReferenceCellCoveredVertices L n}) :
    SubcriticalReferenceCellIndex L :=
  Classical.choose (mem_subcriticalReferenceCellCoveredVertices.mp x.property)

theorem subcriticalReferenceCellIndexOfCovered_spec
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (x : {x // x ∈ subcriticalReferenceCellCoveredVertices L n}) :
    x.1 ∈ subcriticalReferenceCellVerticesAt L n
      (subcriticalReferenceCellIndexOfCovered L n x) :=
  Classical.choose_spec
    (mem_subcriticalReferenceCellCoveredVertices.mp x.property)

/-- The finite set of all literal cells which contain a sampled vertex. -/
def subcriticalRealizedReferenceCellIndices
    (L : AdmissibleBlockSequence k) (n : ℕ) :
    Finset (SubcriticalReferenceCellIndex L) := by
  classical
  exact (subcriticalReferenceCellCoveredVertices L n).attach.image
    (subcriticalReferenceCellIndexOfCovered L n)

theorem mem_subcriticalRealizedReferenceCellIndices
    (L : AdmissibleBlockSequence k)
    (a : SubcriticalReferenceCellIndex L) :
    a ∈ subcriticalRealizedReferenceCellIndices L n ↔
      (subcriticalReferenceCellVerticesAt L n a).Nonempty := by
  classical
  constructor
  · intro ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
    refine ⟨x.1, ?_⟩
    rw [← hxa]
    exact subcriticalReferenceCellIndexOfCovered_spec L n x
  · rintro ⟨x, hxa⟩
    have hxcovered : x ∈ subcriticalReferenceCellCoveredVertices L n :=
      mem_subcriticalReferenceCellCoveredVertices.mpr ⟨a, hxa⟩
    let x' : {x // x ∈ subcriticalReferenceCellCoveredVertices L n} :=
      ⟨x, hxcovered⟩
    apply Finset.mem_image.mpr
    refine ⟨x', by simp [x'], ?_⟩
    exact subcriticalReferenceCellIndex_unique L
      (subcriticalReferenceCellIndexOfCovered_spec L n x') hxa

/-- At most one realized cell can be charged to each sampled vertex. -/
theorem card_subcriticalRealizedReferenceCellIndices_le
    (L : AdmissibleBlockSequence k) (n : ℕ) :
    (subcriticalRealizedReferenceCellIndices L n).card ≤ n := by
  classical
  calc
    (subcriticalRealizedReferenceCellIndices L n).card ≤
        (subcriticalReferenceCellCoveredVertices L n).attach.card :=
      Finset.card_image_le
    _ = (subcriticalReferenceCellCoveredVertices L n).card := by simp
    _ ≤ n := by simpa using (Finset.card_le_card
      (Finset.subset_univ (subcriticalReferenceCellCoveredVertices L n)))

/-! ## One-permutation aligned cells and their remainder -/

/-- The inverse image of a literal reference cell under the one alignment
permutation used throughout the bridge. -/
def subcriticalAlignedReferenceCellVertices
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (pi : Equiv.Perm (Fin n)) (a : SubcriticalReferenceCellIndex L) :
    Finset (Fin n) :=
  (subcriticalReferenceCellVerticesAt L n a).map pi.symm.toEmbedding

@[simp] theorem mem_subcriticalAlignedReferenceCellVertices
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (a : SubcriticalReferenceCellIndex L) (x : Fin n) :
    x ∈ subcriticalAlignedReferenceCellVertices L n pi a ↔
      pi x ∈ subcriticalReferenceCellVerticesAt L n a := by
  classical
  simp [subcriticalAlignedReferenceCellVertices]

@[simp] theorem card_subcriticalAlignedReferenceCellVertices
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (a : SubcriticalReferenceCellIndex L) :
    (subcriticalAlignedReferenceCellVertices L n pi a).card =
      (subcriticalReferenceCellVerticesAt L n a).card := by
  simp [subcriticalAlignedReferenceCellVertices]

theorem subcriticalAlignedReferenceCellVertices_disjoint
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    {a b : SubcriticalReferenceCellIndex L} (hab : a ≠ b) :
    Disjoint (subcriticalAlignedReferenceCellVertices L n pi a)
      (subcriticalAlignedReferenceCellVertices L n pi b) := by
  exact (Finset.disjoint_map pi.symm.toEmbedding).mpr
    (subcriticalReferenceCellVerticesAt_disjoint L hab)

/-- The union of all cells actually realized at sample size `n`, transported
back to the original labels by `pi`. -/
def subcriticalRealizedReferenceSupport
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (pi : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  (subcriticalRealizedReferenceCellIndices L n).biUnion
    (subcriticalAlignedReferenceCellVertices L n pi)

@[simp] theorem mem_subcriticalRealizedReferenceSupport
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (x : Fin n) :
    x ∈ subcriticalRealizedReferenceSupport L n pi ↔
      ∃ a : SubcriticalReferenceCellIndex L,
        x ∈ subcriticalAlignedReferenceCellVertices L n pi a := by
  classical
  constructor
  · simp only [subcriticalRealizedReferenceSupport, Finset.mem_biUnion]
    rintro ⟨a, _ha, hxa⟩
    exact ⟨a, hxa⟩
  · rintro ⟨a, hxa⟩
    rw [subcriticalRealizedReferenceSupport, Finset.mem_biUnion]
    exact ⟨a, (mem_subcriticalRealizedReferenceCellIndices L a).mpr
      ⟨pi x, (mem_subcriticalAlignedReferenceCellVertices L pi a x).mp hxa⟩, hxa⟩

/-- Sampled vertices outside every literal candidate cell. -/
def subcriticalRealizedReferenceRemainder
    (L : AdmissibleBlockSequence k) (n : ℕ)
    (pi : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ \ subcriticalRealizedReferenceSupport L n pi

@[simp] theorem mem_subcriticalRealizedReferenceRemainder
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (x : Fin n) :
    x ∈ subcriticalRealizedReferenceRemainder L n pi ↔
      ∀ a : SubcriticalReferenceCellIndex L,
        x ∉ subcriticalAlignedReferenceCellVertices L n pi a := by
  simp only [subcriticalRealizedReferenceRemainder, Finset.mem_sdiff,
    Finset.mem_univ, true_and, mem_subcriticalRealizedReferenceSupport,
    not_exists]

/-- The aligned full reference is identically zero on every row based at the
realized-cell remainder. -/
theorem subcriticalReference_weight_eq_zero_of_mem_realizedRemainder_left
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) {x y : Fin n}
    (hx : x ∈ subcriticalRealizedReferenceRemainder L n pi) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 := by
  rw [DenseGraph.FiniteWeightedGraph.permute_weight]
  change L.profileKernel (pK k)
    (subcriticalReferenceSamplePoint (pi x),
      subcriticalReferenceSamplePoint (pi y)) = 0
  rw [AdmissibleBlockSequence.profileKernel,
    L.kernel_eq_zero_of_no_leftCell]
  · simp
  · intro i v hiv
    exact ((mem_subcriticalRealizedReferenceRemainder L pi x).mp hx ⟨i, v⟩)
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mpr
        (mem_subcriticalReferenceCellVertices.mpr hiv))

theorem subcriticalReference_weight_eq_zero_of_mem_realizedRemainder_right
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) {x y : Fin n}
    (hy : y ∈ subcriticalRealizedReferenceRemainder L n pi) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 := by
  rw [(subcriticalReferenceWeightedGraph hk L n).permute pi |>.symmetric]
  exact subcriticalReference_weight_eq_zero_of_mem_realizedRemainder_left
    hk L pi hy

/-! ## Exact aligned reference values -/

/-- The smallest positive distance from an entry of the candidate palette to
an endpoint of `[0,1]`. -/
def subcriticalPaletteGap (k : ℕ) : ℝ :=
  min (pK k) (1 - pK k)

theorem subcriticalPaletteGap_pos (hk : 3 ≤ k) :
    0 < subcriticalPaletteGap k := by
  rw [subcriticalPaletteGap, lt_min_iff]
  exact ⟨pK_pos (by omega), sub_pos.mpr (pK_lt_one (by omega))⟩

theorem pK_le_one_sub_subcriticalPaletteGap (k : ℕ) :
    pK k ≤ 1 - subcriticalPaletteGap k := by
  have h := min_le_right (pK k) (1 - pK k)
  simp only [subcriticalPaletteGap]
  linarith

theorem subcriticalReference_weight_of_mem_same_aligned_cell
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (a : SubcriticalReferenceCellIndex L)
    {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi a)
    (hy : y ∈ subcriticalAlignedReferenceCellVertices L n pi a) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 1 := by
  rcases a with ⟨i, v⟩
  rw [DenseGraph.FiniteWeightedGraph.permute_weight,
    subcriticalReferenceWeightedGraph_weight_of_mem_cells hk L v v
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mp hx)
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ y).mp hy),
    profileXiMatrix_apply_eq]

theorem subcriticalReference_weight_of_mem_active_aligned_cells
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ)
    {v w : Fin (L.core i).order} (hvw : (L.core i).graph.Adj v w)
    {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩)
    (hy : y ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = pK k := by
  rw [DenseGraph.FiniteWeightedGraph.permute_weight,
    subcriticalReferenceWeightedGraph_weight_of_mem_cells hk L v w
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mp hx)
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, w⟩ y).mp hy),
    profileXiMatrix_apply_of_adj (pK k) (L.core i) hvw]

theorem subcriticalReference_weight_of_mem_inactive_aligned_cells
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ)
    {v w : Fin (L.core i).order} (hvw : v ≠ w)
    (hnot : ¬ (L.core i).graph.Adj v w) {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩)
    (hy : y ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 := by
  rw [DenseGraph.FiniteWeightedGraph.permute_weight,
    subcriticalReferenceWeightedGraph_weight_of_mem_cells hk L v w
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mp hx)
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, w⟩ y).mp hy),
    profileXiMatrix_apply_of_ne_of_not_adj (pK k) (L.core i) hvw hnot]

theorem subcriticalReference_weight_of_mem_distinct_aligned_blocks
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) {i j : ℕ} (hij : i ≠ j)
    {v : Fin (L.core i).order} {w : Fin (L.core j).order} {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩)
    (hy : y ∈ subcriticalAlignedReferenceCellVertices L n pi ⟨j, w⟩) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y = 0 := by
  rw [DenseGraph.FiniteWeightedGraph.permute_weight]
  exact subcriticalReferenceWeightedGraph_weight_of_mem_distinct_blocks
    hk L hij
    (subcriticalReferenceCellVertices_subset_blockVertices L v
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mp hx))
    (subcriticalReferenceCellVertices_subset_blockVertices L w
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨j, w⟩ y).mp hy))

/-- Distinct aligned cells have reference weight at most `pK`, whether they
belong to one core or to different candidate components. -/
theorem subcriticalReference_weight_le_pK_of_mem_distinct_aligned_cells
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n))
    {a b : SubcriticalReferenceCellIndex L} (hab : a ≠ b) {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi a)
    (hy : y ∈ subcriticalAlignedReferenceCellVertices L n pi b) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y ≤ pK k := by
  rcases a with ⟨i, v⟩
  rcases b with ⟨j, w⟩
  by_cases hij : i = j
  · subst j
    have hvw : v ≠ w := by
      intro h
      apply hab
      cases h
      rfl
    by_cases hadj : (L.core i).graph.Adj v w
    · rw [subcriticalReference_weight_of_mem_active_aligned_cells
          hk L pi i hadj hx hy]
    · rw [subcriticalReference_weight_of_mem_inactive_aligned_cells
          hk L pi i hvw hadj hx hy]
      exact (pK_pos (by omega)).le
  · rw [subcriticalReference_weight_of_mem_distinct_aligned_blocks
        hk L pi hij hx hy]
    exact (pK_pos (by omega)).le

/-- Universal outside-cell bound.  The second vertex may lie in another
realized cell or in the unused zero region. -/
theorem subcriticalReference_weight_le_pK_of_mem_aligned_cell_of_notMem
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (a : SubcriticalReferenceCellIndex L)
    {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi a)
    (hy : y ∉ subcriticalAlignedReferenceCellVertices L n pi a) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y ≤ pK k := by
  by_cases hys : y ∈ subcriticalRealizedReferenceSupport L n pi
  · obtain ⟨b, hyb⟩ := (mem_subcriticalRealizedReferenceSupport L pi y).mp hys
    have hab : a ≠ b := by
      intro hab
      subst b
      exact hy hyb
    exact subcriticalReference_weight_le_pK_of_mem_distinct_aligned_cells
      hk L pi hab hx hyb
  · have hyr : y ∈ subcriticalRealizedReferenceRemainder L n pi := by
      simp [subcriticalRealizedReferenceRemainder, hys]
    rw [subcriticalReference_weight_eq_zero_of_mem_realizedRemainder_right
      hk L pi hyr]
    exact (pK_pos (by omega)).le

theorem subcriticalReference_weight_le_one_sub_paletteGap_of_mem_aligned_cell_of_notMem
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (a : SubcriticalReferenceCellIndex L)
    {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi a)
    (hy : y ∉ subcriticalAlignedReferenceCellVertices L n pi a) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y ≤
      1 - subcriticalPaletteGap k :=
  (subcriticalReference_weight_le_pK_of_mem_aligned_cell_of_notMem
    hk L pi a hx hy).trans (pK_le_one_sub_subcriticalPaletteGap k)

/-- A covered row is bounded by `1` on its own cell and by `1-gap`
everywhere else. -/
theorem subcriticalReference_weight_le_own_cell_indicator
    (hk : 3 ≤ k) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (a : SubcriticalReferenceCellIndex L)
    {x y : Fin n}
    (hx : x ∈ subcriticalAlignedReferenceCellVertices L n pi a) :
    ((subcriticalReferenceWeightedGraph hk L n).permute pi).weight x y ≤
      if y ∈ subcriticalAlignedReferenceCellVertices L n pi a then 1
      else 1 - subcriticalPaletteGap k := by
  split_ifs with hy
  · exact ((subcriticalReferenceWeightedGraph hk L n).permute pi).le_one x y
  · exact
      subcriticalReference_weight_le_one_sub_paletteGap_of_mem_aligned_cell_of_notMem
        hk L pi a hx hy

/-! ## Uniform finite cell-size estimates -/

theorem abs_card_subcriticalAlignedReferenceCellVertices_div_sub_le
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin (L.core i).order) :
    |((subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card : ℝ) / n -
        L.alpha i / (L.core i).order| ≤ 2 / (n : ℝ) := by
  simpa using abs_card_subcriticalReferenceCellVertices_div_sub_le hn L v

/-- All cells of one sampled candidate component differ in cardinality by
at most four; no global bound on core orders is used. -/
theorem abs_card_subcriticalAlignedReferenceCells_sub_le_four
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ)
    (v w : Fin (L.core i).order) :
    |((subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card : ℝ) -
        ((subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩).card : ℝ)| ≤
      (4 : ℝ) := by
  let av : ℝ :=
    (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card
  let aw : ℝ :=
    (subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩).card
  let t : ℝ := L.alpha i / (L.core i).order
  have hv := abs_card_subcriticalAlignedReferenceCellVertices_div_sub_le
    hn L pi i v
  have hw := abs_card_subcriticalAlignedReferenceCellVertices_div_sub_le
    hn L pi i w
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htri : |av / n - aw / n| ≤ |av / n - t| + |aw / n - t| := by
    calc
      |av / n - aw / n| = |(av / n - t) - (aw / n - t)| := by ring_nf
      _ ≤ |av / n - t| + |aw / n - t| := abs_sub _ _
  have hv' : |av / n - t| ≤ 2 / (n : ℝ) := by
    simpa only [av, t] using hv
  have hw' : |aw / n - t| ≤ 2 / (n : ℝ) := by
    simpa only [aw, t] using hw
  have hdiv : |av / n - aw / n| ≤ 4 / (n : ℝ) := by
    calc
      |av / n - aw / n| ≤ |av / n - t| + |aw / n - t| := htri
      _ ≤ 2 / (n : ℝ) + 2 / (n : ℝ) := add_le_add hv' hw'
      _ = 4 / (n : ℝ) := by ring
  have hmul := mul_le_mul_of_nonneg_right hdiv hnR.le
  have hleft : |av / n - aw / n| * n = |av - aw| := by
    have halg : (av / n - aw / n) * n = av - aw := by field_simp
    calc
      |av / n - aw / n| * n = |av / n - aw / n| * |(n : ℝ)| := by
        rw [abs_of_pos hnR]
      _ = |(av / n - aw / n) * n| := (abs_mul _ _).symm
      _ = |av - aw| := by rw [halg]
  have hright : 4 / (n : ℝ) * n = 4 := by field_simp
  rw [hleft, hright] at hmul
  simpa [av, aw] using hmul

/-- A cell occupying a positive normalized fraction forces its candidate
core to have bounded order.  The only rounding input is the literal `2/n`
cell-card estimate. -/
theorem subcriticalReference_coreOrder_le_two_div_of_large_aligned_cell
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin (L.core i).order)
    {zeta : ℝ} (hzeta : 0 < zeta)
    (hround : 4 ≤ zeta * (n : ℝ))
    (hlarge : zeta * (n : ℝ) ≤
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card) :
    ((L.core i).order : ℝ) ≤ 2 / zeta := by
  let c : ℝ :=
    (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card
  let q : ℝ := (L.core i).order
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (L.core i).order_pos
  have herr := abs_card_subcriticalAlignedReferenceCellVertices_div_sub_le
    hn L pi i v
  have herrUpper : c / n - L.alpha i / q ≤ 2 / (n : ℝ) := by
    exact (abs_le.mp herr).2
  have hlargeDiv : zeta ≤ c / n := by
    apply (le_div_iff₀ hnR).2
    simpa [c] using hlarge
  have halpha : L.alpha i / q ≤ 1 / q := by
    exact div_le_div_of_nonneg_right (L.alpha_le_one i) hq.le
  have hroundDiv : 2 / (n : ℝ) ≤ zeta / 2 := by
    apply (div_le_iff₀ hnR).2
    nlinarith
  have hhalf : zeta / 2 ≤ 1 / q := by linarith
  have hmul : q * zeta ≤ 2 := by
    have h := (le_div_iff₀ hq).mp hhalf
    nlinarith
  exact (le_div_iff₀ hzeta).2 hmul

/-- If one cell has size at least `theta*n/2` and the rounding allowance
`4` is at most `theta*n/4`, every sibling cell has size at least
`theta*n/4`. -/
theorem subcriticalAlignedReferenceCell_card_ge_quarter_of_card_ge_half
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ)
    (v w : Fin (L.core i).order) {theta : ℝ}
    (hround : 4 ≤ theta * (n : ℝ) / 4)
    (hlarge : theta * (n : ℝ) / 2 ≤
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card) :
    theta * (n : ℝ) / 4 ≤
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩).card := by
  have hdiff := abs_card_subcriticalAlignedReferenceCells_sub_le_four
    hn L pi i v w
  have hone := (abs_le.mp hdiff).2
  linarith

theorem subcriticalAlignedReferenceCell_nonempty_of_card_ge_half
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ)
    (v w : Fin (L.core i).order) {theta : ℝ}
    (hround : 4 ≤ theta * (n : ℝ) / 4)
    (hlarge : theta * (n : ℝ) / 2 ≤
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card) :
    (subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩).Nonempty := by
  apply Finset.card_pos.mp
  have hge := subcriticalAlignedReferenceCell_card_ge_quarter_of_card_ge_half
    hn L pi i v w hround hlarge
  have hpos : (0 : ℝ) <
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, w⟩).card :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < theta * n / 4) hge
  exact_mod_cast hpos

/-- A convenient specialized order bound at the half-cell threshold used by
the component-alignment argument. -/
theorem subcriticalReference_coreOrder_le_four_div_of_cell_card_ge_half
    (hn : 0 < n) (L : AdmissibleBlockSequence k)
    (pi : Equiv.Perm (Fin n)) (i : ℕ) (v : Fin (L.core i).order)
    {theta : ℝ} (htheta : 0 < theta)
    (hround : 4 ≤ theta * (n : ℝ) / 4)
    (hlarge : theta * (n : ℝ) / 2 ≤
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).card) :
    ((L.core i).order : ℝ) ≤ 4 / theta := by
  have hbase := subcriticalReference_coreOrder_le_two_div_of_large_aligned_cell
    hn L pi i v (show 0 < theta / 2 by positivity)
    (show 4 ≤ theta / 2 * (n : ℝ) by nlinarith) (by
      convert hlarge using 1 <;> ring)
  convert hbase using 1 <;> field_simp <;> ring

/-- A sampled aligned cell can be nonempty only when its candidate block has
positive mass.  This is proved from the literal half-open cell, rather than
from any finiteness assumption on the candidate sequence. -/
theorem subcriticalReference_alpha_pos_of_alignedCell_nonempty
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (i : ℕ) (v : Fin (L.core i).order)
    (hcell :
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).Nonempty) :
    0 < L.alpha i := by
  by_contra hnot
  have halpha : L.alpha i = 0 :=
    le_antisymm (le_of_not_gt hnot) (L.alpha_nonneg i)
  obtain ⟨x, hx⟩ := hcell
  have hxCell :
      subcriticalReferenceSamplePoint (pi x) ∈ L.blockCell i v :=
    mem_subcriticalReferenceCellVertices.mp
      ((mem_subcriticalAlignedReferenceCellVertices L pi ⟨i, v⟩ x).mp hx)
  have hlt : L.cellLeft i v < L.cellRight i v :=
    (show L.cellLeftUI i v ≤ subcriticalReferenceSamplePoint (pi x) from
      hxCell.1).trans_lt
      (show subcriticalReferenceSamplePoint (pi x) < L.cellRightUI i v from
        hxCell.2)
  simp [AdmissibleBlockSequence.cellLeft,
    AdmissibleBlockSequence.cellRight, halpha] at hlt

/-- Every nonempty aligned sampled cell comes from an active candidate-block
index. -/
theorem subcriticalReference_blockIndexActive_of_alignedCell_nonempty
    (L : AdmissibleBlockSequence k) (pi : Equiv.Perm (Fin n))
    (i : ℕ) (v : Fin (L.core i).order)
    (hcell :
      (subcriticalAlignedReferenceCellVertices L n pi ⟨i, v⟩).Nonempty) :
    blockIndexActive L.count i := by
  by_contra hinactive
  have halpha : L.alpha i = 0 := L.alpha_eq_zero_of_inactive i hinactive
  exact (subcriticalReference_alpha_pos_of_alignedCell_nonempty
    L pi i v hcell).ne' halpha

end InducedStars
