import InducedStars.Structure.Supercritical.Division
import InducedStars.Structure.Supercritical.Reference
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic

/-!
# Finite alignment of supercritical divisions

This file contains the overlap-matrix argument omitted from the informal
sentence in the proof of `lemma:SuperCloseStructureK1k`.  A vertex
permutation supplied by finite cut alignment pulls the balanced reference
blocks back to the original vertex labels.  Small labeled cut discrepancy
then forces every main part of a division to be concentrated in one pulled
back block.  A counting argument shows that the resulting map of parts is a
permutation.

The quantitative theorem uses integer error budgets.  This makes every
rounding convention explicit and is convenient for later instantiation with
floors or ceilings of real multiples of the vertex count.
-/

noncomputable section

open Finset Set
open scoped BigOperators symmDiff

namespace InducedStars

/-! ## Reference blocks in the aligned vertex labels -/

/-- Pull a canonical reference block back through the vertex permutation
used by the aligned finite reference matrix.  The orientation agrees with
`FiniteWeightedGraph.permute`: its weight at `(x,y)` is the unpermuted
reference weight at `(π x, π y)`. -/
def alignedSupercriticalReferencePart (k n : ℕ)
    (π : Equiv.Perm (Fin n)) (j : Fin (k - 1)) : Finset (Fin n) :=
  (supercriticalReferencePart k n j).map π.symm.toEmbedding

@[simp] theorem mem_alignedSupercriticalReferencePart
    {k n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin (k - 1)) (x : Fin n) :
    x ∈ alignedSupercriticalReferencePart k n π j ↔
      π x ∈ supercriticalReferencePart k n j := by
  simp [alignedSupercriticalReferencePart]

theorem alignedSupercriticalReferenceParts_pairwiseDisjoint
    (k n : ℕ) (π : Equiv.Perm (Fin n)) :
  Set.PairwiseDisjoint (Set.univ : Set (Fin (k - 1)))
      (alignedSupercriticalReferencePart k n π) := by
  intro i _ j _ hij
  change Disjoint (alignedSupercriticalReferencePart k n π i)
    (alignedSupercriticalReferencePart k n π j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  rw [mem_alignedSupercriticalReferencePart] at hxi hxj
  exact (Finset.disjoint_left.mp
    (supercriticalReferenceParts_pairwiseDisjoint k n
      (Set.mem_univ i) (Set.mem_univ j) hij)) hxi hxj

@[simp] theorem biUnion_alignedSupercriticalReferencePart
    {k n : ℕ} (hk : 3 ≤ k) (π : Equiv.Perm (Fin n)) :
    Finset.univ.biUnion (alignedSupercriticalReferencePart k n π) =
      (Finset.univ : Finset (Fin n)) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hxj⟩
    trivial
  · intro _
    have hx : π x ∈ Finset.univ.biUnion
        (supercriticalReferencePart k n) := by
      rw [biUnion_supercriticalReferencePart hk]
      exact Finset.mem_univ _
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    exact ⟨j, by simpa using hxj⟩

@[simp] theorem card_alignedSupercriticalReferencePart
    {k n : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin (k - 1)) :
    (alignedSupercriticalReferencePart k n π j).card =
      (supercriticalReferencePart k n j).card := by
  simp [alignedSupercriticalReferencePart]

theorem alignedSupercriticalReferencePart_card_ge_div
    {k n : ℕ} (hk : 3 ≤ k) (π : Equiv.Perm (Fin n))
    (j : Fin (k - 1)) :
    n / (k - 1) ≤ (alignedSupercriticalReferencePart k n π j).card := by
  rw [card_alignedSupercriticalReferencePart,
    card_supercriticalReferencePart hk]
  split <;> omega

theorem alignedSupercriticalReferencePart_card_le_div_add_one
    {k n : ℕ} (hk : 3 ≤ k) (π : Equiv.Perm (Fin n))
    (j : Fin (k - 1)) :
    (alignedSupercriticalReferencePart k n π j).card ≤
      n / (k - 1) + 1 := by
  rw [card_alignedSupercriticalReferencePart,
    card_supercriticalReferencePart hk]
  split <;> omega

theorem permutedReference_weight_of_mem_same_alignedPart
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (π : Equiv.Perm (Fin n))
    (j : Fin (k - 1)) {x y : Fin n}
    (hx : x ∈ alignedSupercriticalReferencePart k n π j)
    (hy : y ∈ alignedSupercriticalReferencePart k n π j) :
    ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π).weight x y = 1 := by
  exact supercriticalReferenceWeightedGraph_weight_of_mem_samePart hk hγ j
    (by simpa using hx) (by simpa using hy)

theorem permutedReference_weight_of_mem_distinct_alignedParts
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (π : Equiv.Perm (Fin n))
    {i j : Fin (k - 1)} (hij : i ≠ j) {x y : Fin n}
    (hx : x ∈ alignedSupercriticalReferencePart k n π i)
    (hy : y ∈ alignedSupercriticalReferencePart k n π j) :
    ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π).weight x y =
      supercriticalOffDiagonal k γ := by
  exact supercriticalReferenceWeightedGraph_weight_of_mem_distinct hk hγ hij
    (by simpa using hx) (by simpa using hy)

theorem supercriticalOffDiagonal_le_permutedReference_weight
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (π : Equiv.Perm (Fin n))
    (x y : Fin n) :
    supercriticalOffDiagonal k γ ≤
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π).weight x y := by
  exact supercriticalOffDiagonal_le_referenceWeight hk hγ (π x) (π y)

/-! ## Dominant overlap of a main part -/

/-- A reference block having maximum overlap with the indicated main part. -/
def dominantAlignedReferenceIndex {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (i : Fin (k - 1)) : Fin (k - 1) := by
  classical
  exact Classical.choose (Finset.exists_max_image Finset.univ
    (fun j : Fin (k - 1) ↦
      (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)

theorem overlap_le_dominantOverlap {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (i j : Fin (k - 1)) :
    (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card ≤
      (D.parts i ∩ alignedSupercriticalReferencePart k n π
        (dominantAlignedReferenceIndex hk D π i)).card := by
  classical
  exact (Classical.choose_spec (Finset.exists_max_image Finset.univ
    (fun j : Fin (k - 1) ↦
      (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card)
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩)).2 j (Finset.mem_univ _)

theorem sum_card_inter_alignedReferenceParts {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (i : Fin (k - 1)) :
    ∑ j : Fin (k - 1),
        (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card =
      (D.parts i).card := by
  classical
  let Q : Fin (k - 1) → Finset (Fin n) := fun j ↦
    D.parts i ∩ alignedSupercriticalReferencePart k n π j
  have hpair : (↑(Finset.univ : Finset (Fin (k - 1))) :
      Set (Fin (k - 1))).PairwiseDisjoint Q := by
    intro a _ b _ hab
    change Disjoint (Q a) (Q b)
    exact Finset.disjoint_of_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_right
        (alignedSupercriticalReferenceParts_pairwiseDisjoint k n π
          (Set.mem_univ a) (Set.mem_univ b) hab))
  have hunion : Finset.univ.biUnion Q = D.parts i := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Q,
      Finset.mem_inter]
    constructor
    · rintro ⟨j, hxP, -⟩
      exact hxP
    · intro hxP
      have hxU : x ∈ Finset.univ.biUnion
          (alignedSupercriticalReferencePart k n π) := by
        rw [biUnion_alignedSupercriticalReferencePart hk π]
        exact Finset.mem_univ _
      obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hxU
      exact ⟨j, hxP, hxj⟩
  calc
    ∑ j : Fin (k - 1),
        (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card =
        (Finset.univ.biUnion Q).card := by
          rw [Finset.card_biUnion hpair]
    _ = (D.parts i).card := congrArg Finset.card hunion

theorem mainPart_card_le_card_index_mul_dominantOverlap
    {k n : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (i : Fin (k - 1)) :
    (D.parts i).card ≤ (k - 1) *
      (D.parts i ∩ alignedSupercriticalReferencePart k n π
        (dominantAlignedReferenceIndex hk D π i)).card := by
  classical
  rw [← sum_card_inter_alignedReferenceParts hk D π i]
  calc
    ∑ j : Fin (k - 1),
        (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card ≤
        ∑ _j : Fin (k - 1),
          (D.parts i ∩ alignedSupercriticalReferencePart k n π
            (dominantAlignedReferenceIndex hk D π i)).card := by
      exact Finset.sum_le_sum fun j _ ↦ overlap_le_dominantOverlap hk D π i j
    _ = (k - 1) *
        (D.parts i ∩ alignedSupercriticalReferencePart k n π
          (dominantAlignedReferenceIndex hk D π i)).card := by
      simp [mul_comm]

/-! ## Rectangle estimates from labeled cut discrepancy -/

/-- The sparse-set rectangle estimate in `lemma:SuperCloseStructureK1k`: use
`D.sparse × univ`, on which the division model is identically zero and the
reference matrix is everywhere at least `ρ`. -/
theorem supercriticalOffDiagonal_mul_sparse_card_mul_n_le_labeledCut
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n)) :
    supercriticalOffDiagonal k γ * (D.sparse.card : ℝ) * n ≤
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
        (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
          (supercriticalDivisionModelGraph G D))
        ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) *
          (n : ℝ) ^ 2 := by
  classical
  let H := DenseGraph.FiniteWeightedGraph.ofSimpleGraph
    (supercriticalDivisionModelGraph G D)
  let R := (supercriticalReferenceWeightedGraph k hk γ hγ n).permute π
  have hsum : DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
      H R D.sparse Finset.univ ≤
      -(supercriticalOffDiagonal k γ * (D.sparse.card : ℝ) * n) := by
    unfold DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
    calc
      ∑ x ∈ D.sparse, ∑ y ∈ Finset.univ,
          (H.weight x y - R.weight x y) ≤
          ∑ _x ∈ D.sparse, ∑ _y ∈ (Finset.univ : Finset (Fin n)),
            (-supercriticalOffDiagonal k γ) := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y _hy
        have hH : H.weight x y = 0 := by
          change (if (supercriticalDivisionModelGraph G D).Adj x y then 1 else 0) = 0
          rw [if_neg (supercriticalDivisionModelGraph_not_adj_of_mem_sparse_left
            G D hx)]
        have hR : supercriticalOffDiagonal k γ ≤ R.weight x y := by
          exact supercriticalOffDiagonal_le_permutedReference_weight hk hγ π x y
        rw [hH]
        linarith
      _ = -(supercriticalOffDiagonal k γ * (D.sparse.card : ℝ) * n) := by
        simp [Fintype.card_fin]
        ring
  calc
    supercriticalOffDiagonal k γ * (D.sparse.card : ℝ) * n ≤
        -DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
          H R D.sparse Finset.univ := by linarith
    _ ≤ |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
          H R D.sparse Finset.univ| := neg_le_abs _
    _ ≤ DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist H R *
          (Fintype.card (Fin n) : ℝ) ^ 2 :=
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_rectangle_le
        H R D.sparse Finset.univ
    _ = DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) *
            (n : ℝ) ^ 2 := by simp [H, R]

/-- The exact discrepancy on the rectangle cut out by one main part and one
aligned reference block.  Every pair in this rectangle is off-diagonal,
the division model has weight one, and the reference has weight `ρ`. -/
theorem rectangleDiscrepancy_mainPart_inter_aligned_sdiff
    {k n : ℕ} (hk : 3 ≤ k) {γ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (i j : Fin (k - 1)) :
    DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π)
      (D.parts i ∩ alignedSupercriticalReferencePart k n π j)
      (D.parts i \ alignedSupercriticalReferencePart k n π j) =
    (1 - supercriticalOffDiagonal k γ) *
      ((D.parts i ∩ alignedSupercriticalReferencePart k n π j).card : ℝ) *
      ((D.parts i \ alignedSupercriticalReferencePart k n π j).card : ℝ) := by
  classical
  let A := D.parts i ∩ alignedSupercriticalReferencePart k n π j
  let C := D.parts i \ alignedSupercriticalReferencePart k n π j
  let H := DenseGraph.FiniteWeightedGraph.ofSimpleGraph
    (supercriticalDivisionModelGraph G D)
  let R := (supercriticalReferenceWeightedGraph k hk γ hγ n).permute π
  have hterm : ∀ x ∈ A, ∀ y ∈ C,
      H.weight x y - R.weight x y =
        1 - supercriticalOffDiagonal k γ := by
    intro x hx y hy
    have hxP : x ∈ D.parts i := (Finset.mem_inter.mp hx).1
    have hxB : x ∈ alignedSupercriticalReferencePart k n π j :=
      (Finset.mem_inter.mp hx).2
    have hyP : y ∈ D.parts i := (Finset.mem_sdiff.mp hy).1
    have hyB : y ∉ alignedSupercriticalReferencePart k n π j :=
      (Finset.mem_sdiff.mp hy).2
    have hxy : x ≠ y := by
      intro h
      exact hyB (h ▸ hxB)
    have hHAdj : (supercriticalDivisionModelGraph G D).Adj x y :=
      (supercriticalDivisionModelGraph_adj_of_mem_same_part G D i hxP hyP).2 hxy
    have hH : H.weight x y = 1 := by
      change (if (supercriticalDivisionModelGraph G D).Adj x y then 1 else 0) = 1
      rw [if_pos hHAdj]
    have hyU : y ∈ Finset.univ.biUnion
        (alignedSupercriticalReferencePart k n π) := by
      rw [biUnion_alignedSupercriticalReferencePart hk π]
      exact Finset.mem_univ _
    obtain ⟨l, _, hyl⟩ := Finset.mem_biUnion.mp hyU
    have hjl : j ≠ l := by
      intro h
      subst l
      exact hyB hyl
    have hR : R.weight x y = supercriticalOffDiagonal k γ := by
      exact permutedReference_weight_of_mem_distinct_alignedParts
        hk hγ π hjl hxB hyl
    rw [hH, hR]
  unfold DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy
  change (∑ x ∈ A, ∑ y ∈ C, (H.weight x y - R.weight x y)) = _
  calc
    ∑ x ∈ A, ∑ y ∈ C, (H.weight x y - R.weight x y) =
        ∑ _x ∈ A, ∑ _y ∈ C,
          (1 - supercriticalOffDiagonal k γ) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact hterm x hx y hy
    _ = (1 - supercriticalOffDiagonal k γ) * (A.card : ℝ) *
        (C.card : ℝ) := by simp; ring
    _ = _ := rfl

/-- Cut-distance upper bound for every dominant-overlap rectangle. -/
theorem one_sub_supercriticalOffDiagonal_mul_overlap_mul_sdiff_le_labeledCut
    {k n : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (G : SimpleGraph (Fin n))
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (i j : Fin (k - 1)) :
    (1 - supercriticalOffDiagonal k γ) *
        ((D.parts i ∩ alignedSupercriticalReferencePart k n π j).card : ℝ) *
        ((D.parts i \ alignedSupercriticalReferencePart k n π j).card : ℝ) ≤
      η * (n : ℝ) ^ 2 := by
  let H := DenseGraph.FiniteWeightedGraph.ofSimpleGraph
    (supercriticalDivisionModelGraph G D)
  let R := (supercriticalReferenceWeightedGraph k hk γ hγ n).permute π
  let A := D.parts i ∩ alignedSupercriticalReferencePart k n π j
  let C := D.parts i \ alignedSupercriticalReferencePart k n π j
  have hnonneg : 0 ≤ (1 - supercriticalOffDiagonal k γ) *
      (A.card : ℝ) * (C.card : ℝ) := by
    have hρ := supercriticalOffDiagonal_lt_one hk hγ.2
    positivity
  calc
    (1 - supercriticalOffDiagonal k γ) * (A.card : ℝ) * (C.card : ℝ) =
        |DenseGraph.FiniteWeightedGraph.rectangleDiscrepancy H R A C| := by
      rw [rectangleDiscrepancy_mainPart_inter_aligned_sdiff hk hγ G D π i j,
        abs_of_nonneg hnonneg]
    _ ≤ DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist H R *
          (Fintype.card (Fin n) : ℝ) ^ 2 :=
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist_rectangle_le H R A C
    _ ≤ η * (n : ℝ) ^ 2 := by
      simpa [H, R] using mul_le_mul_of_nonneg_right hcut (sq_nonneg (n : ℝ))

/-! ## Integer-budget consequences -/

/-- An integer sparse-set budget implied by the corrected `sparse × univ`
rectangle estimate. -/
theorem sparse_card_le_of_labeledCutDist_le
    {k n qSparse : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hSparseScale : η * (n : ℝ) ^ 2 <
      supercriticalOffDiagonal k γ * (qSparse + 1 : ℕ) * n) :
    D.sparse.card ≤ qSparse := by
  have hρ : 0 < supercriticalOffDiagonal k γ :=
    supercriticalOffDiagonal_pos hk hγ.1
  have hbase := supercriticalOffDiagonal_mul_sparse_card_mul_n_le_labeledCut
    hk hγ G D π
  have hupper :
      DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) *
            (n : ℝ) ^ 2 ≤ η * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_right hcut (sq_nonneg (n : ℝ))
  by_contra hnot
  have hq : qSparse + 1 ≤ D.sparse.card := by omega
  have hqR : ((qSparse + 1 : ℕ) : ℝ) ≤ (D.sparse.card : ℝ) := by
    exact_mod_cast hq
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlower : supercriticalOffDiagonal k γ * (qSparse + 1 : ℕ) * n ≤
      supercriticalOffDiagonal k γ * (D.sparse.card : ℝ) * n := by
    gcongr
  linarith

/-- Every main part is concentrated, within the integer budget `qMix`, in
its maximum-overlap aligned reference block. -/
theorem mainPart_sdiff_dominantAlignedReferencePart_card_le
    {k n qMix : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1)
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hMixScale : ((k - 1 : ℕ) : ℝ) * η * (n : ℝ) ^ 2 <
      (1 - supercriticalOffDiagonal k γ) * ((qMix + 1 : ℕ) : ℝ) ^ 2)
    (i : Fin (k - 1)) :
    (D.parts i \ alignedSupercriticalReferencePart k n π
      (dominantAlignedReferenceIndex hk D π i)).card ≤ qMix := by
  classical
  let j := dominantAlignedReferenceIndex hk D π i
  let a := (D.parts i ∩ alignedSupercriticalReferencePart k n π j).card
  let c := (D.parts i \ alignedSupercriticalReferencePart k n π j).card
  have hρ : supercriticalOffDiagonal k γ < 1 :=
    supercriticalOffDiagonal_lt_one hk hγ.2
  have hrect :=
    one_sub_supercriticalOffDiagonal_mul_overlap_mul_sdiff_le_labeledCut
      hk hγ G D π hcut i j
  change c ≤ qMix
  by_contra hnot
  have hqc : qMix + 1 ≤ c := by omega
  have hpcard : a + c = (D.parts i).card := by
    exact Finset.card_inter_add_card_sdiff (D.parts i)
      (alignedSupercriticalReferencePart k n π j)
  have hpdom : (D.parts i).card ≤ (k - 1) * a := by
    exact mainPart_card_le_card_index_mul_dominantOverlap hk D π i
  have hcpart : c ≤ (D.parts i).card := by omega
  have hprodNat : (qMix + 1) ^ 2 ≤ (k - 1) * a * c := by
    calc
      (qMix + 1) ^ 2 = (qMix + 1) * (qMix + 1) := by ring
      _ ≤ (D.parts i).card * c :=
        Nat.mul_le_mul (hqc.trans hcpart) hqc
      _ ≤ ((k - 1) * a) * c := Nat.mul_le_mul_right c hpdom
  have hprod : (((qMix + 1) ^ 2 : ℕ) : ℝ) ≤
      (((k - 1) * a * c : ℕ) : ℝ) := by exact_mod_cast hprodNat
  have hlower :
      (1 - supercriticalOffDiagonal k γ) * ((qMix + 1 : ℕ) : ℝ) ^ 2 ≤
        ((k - 1 : ℕ) : ℝ) *
          ((1 - supercriticalOffDiagonal k γ) * (a : ℝ) * (c : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hprod (by linarith :
      0 ≤ 1 - supercriticalOffDiagonal k γ)
    norm_num [Nat.cast_mul, Nat.cast_pow] at this ⊢
    nlinarith
  have hscaled : ((k - 1 : ℕ) : ℝ) *
      ((1 - supercriticalOffDiagonal k γ) * (a : ℝ) * (c : ℝ)) ≤
      ((k - 1 : ℕ) : ℝ) * (η * (n : ℝ) ^ 2) := by
    apply mul_le_mul_of_nonneg_left
    · simpa [a, c, j] using hrect
    · positivity
  linarith

/-! ## The overlap map is a permutation -/

private theorem alignedReferencePart_subset_sparse_union_partErrors
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n)) (f : Fin (k - 1) → Fin (k - 1))
    (j : Fin (k - 1)) (havoid : ∀ i, f i ≠ j) :
    alignedSupercriticalReferencePart k n π j ⊆
      D.sparse ∪ Finset.univ.biUnion (fun i ↦
        D.parts i \ alignedSupercriticalReferencePart k n π (f i)) := by
  classical
  intro x hxj
  rcases D.sparse_or_existsUnique_part x with hxs | ⟨i, hxi, _⟩
  · exact Finset.mem_union_left _ hxs
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hxi, ?_⟩⟩
    intro hxfi
    exact (Finset.disjoint_left.mp
      (alignedSupercriticalReferenceParts_pairwiseDisjoint k n π
        (Set.mem_univ (f i)) (Set.mem_univ j) (havoid i))) hxfi hxj

theorem dominantAlignedReferenceIndex_surjective
    {k n qSparse qMix : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) (π : Equiv.Perm (Fin n))
    (hsparse : D.sparse.card ≤ qSparse)
    (hmix : ∀ i,
      (D.parts i \ alignedSupercriticalReferencePart k n π
        (dominantAlignedReferenceIndex hk D π i)).card ≤ qMix)
    (hcover : qSparse + (k - 1) * qMix < n / (k - 1)) :
    Function.Surjective (dominantAlignedReferenceIndex hk D π) := by
  classical
  intro j
  by_contra hnot
  have havoid : ∀ i, dominantAlignedReferenceIndex hk D π i ≠ j := by
    intro i hij
    exact hnot ⟨i, hij⟩
  let E : Fin (k - 1) → Finset (Fin n) := fun i ↦
    D.parts i \ alignedSupercriticalReferencePart k n π
      (dominantAlignedReferenceIndex hk D π i)
  have hE : (Finset.univ.biUnion E).card ≤ (k - 1) * qMix := by
    have h := Finset.card_biUnion_le_card_mul Finset.univ E qMix
      (fun i _ ↦ hmix i)
    simpa [E] using h
  have hsubset := alignedReferencePart_subset_sparse_union_partErrors
    hk D π (dominantAlignedReferenceIndex hk D π) j havoid
  have hcard :
      (alignedSupercriticalReferencePart k n π j).card ≤
        qSparse + (k - 1) * qMix := by
    calc
      (alignedSupercriticalReferencePart k n π j).card ≤
          (D.sparse ∪ Finset.univ.biUnion E).card :=
        Finset.card_le_card (by simpa [E] using hsubset)
      _ ≤ D.sparse.card + (Finset.univ.biUnion E).card :=
        Finset.card_union_le _ _
      _ ≤ qSparse + (k - 1) * qMix := Nat.add_le_add hsparse hE
  have hlower := alignedSupercriticalReferencePart_card_ge_div hk π j
  omega

/-- Quantitative data produced by the finite overlap-matrix argument matching
the canonical division to the reference blocks in `lemma:SuperCloseStructureK1k`. -/
structure SupercriticalPartitionAlignment
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n)) (qSparse qMix : ℕ) where
  /-- The matching from division parts to pulled-back reference blocks. -/
  partPermutation : Equiv.Perm (Fin (k - 1))
  sparse_card_le : D.sparse.card ≤ qSparse
  main_sdiff_reference_le : ∀ i,
    (D.parts i \ alignedSupercriticalReferencePart k n π
      (partPermutation i)).card ≤ qMix
  reference_sdiff_main_le : ∀ i,
    (alignedSupercriticalReferencePart k n π (partPermutation i) \
      D.parts i).card ≤ qSparse + (k - 1) * qMix
  symmDiff_card_le : ∀ i,
    (D.parts i ∆ alignedSupercriticalReferencePart k n π
      (partPermutation i)).card ≤ qSparse + k * qMix
  part_card_lower : ∀ i,
    n / (k - 1) ≤ (D.parts i).card + qSparse + (k - 1) * qMix
  part_card_upper : ∀ i,
    (D.parts i).card ≤ n / (k - 1) + qMix + 1

/-- Full finite partition alignment.  The three strict scale conditions have
transparent meanings: the first detects one excess sparse vertex, the
second detects one excess mixed vertex in a main part, and the third rules
out an unmatched balanced reference block. -/
noncomputable def supercriticalPartitionAlignment_of_labeledCutDist_le
    {k n qSparse qMix : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hSparseScale : η * (n : ℝ) ^ 2 <
      supercriticalOffDiagonal k γ * (qSparse + 1 : ℕ) * n)
    (hMixScale : ((k - 1 : ℕ) : ℝ) * η * (n : ℝ) ^ 2 <
      (1 - supercriticalOffDiagonal k γ) * ((qMix + 1 : ℕ) : ℝ) ^ 2)
    (hcover : qSparse + (k - 1) * qMix < n / (k - 1)) :
    SupercriticalPartitionAlignment D π qSparse qMix := by
  classical
  have hsparse := sparse_card_le_of_labeledCutDist_le
    hk hγ hn G D π hcut hSparseScale
  have hmix : ∀ i,
      (D.parts i \ alignedSupercriticalReferencePart k n π
        (dominantAlignedReferenceIndex hk D π i)).card ≤ qMix :=
    fun i ↦ mainPart_sdiff_dominantAlignedReferencePart_card_le
      hk hγ G D π hcut hMixScale i
  have hsurj := dominantAlignedReferenceIndex_surjective
    hk D π hsparse hmix hcover
  have hbij : Function.Bijective (dominantAlignedReferenceIndex hk D π) :=
    Finite.surjective_iff_bijective.mp hsurj
  let τ : Equiv.Perm (Fin (k - 1)) :=
    Equiv.ofBijective (dominantAlignedReferenceIndex hk D π) hbij
  have hτ : ∀ i, τ i = dominantAlignedReferenceIndex hk D π i := fun _ ↦ rfl
  have hreverse : ∀ i,
      (alignedSupercriticalReferencePart k n π (τ i) \ D.parts i).card ≤
        qSparse + (k - 1) * qMix := by
    intro i
    let E : Fin (k - 1) → Finset (Fin n) := fun a ↦
      D.parts a \ alignedSupercriticalReferencePart k n π (τ a)
    have hsub : alignedSupercriticalReferencePart k n π (τ i) \ D.parts i ⊆
        D.sparse ∪ Finset.univ.biUnion E := by
      intro x hx
      have hxB := (Finset.mem_sdiff.mp hx).1
      have hxnot := (Finset.mem_sdiff.mp hx).2
      rcases D.sparse_or_existsUnique_part x with hxs | ⟨a, hxa, _⟩
      · exact Finset.mem_union_left _ hxs
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨a, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨hxa, ?_⟩⟩
        intro hxBa
        by_cases hai : a = i
        · subst a
          exact hxnot hxa
        · have hτne : τ a ≠ τ i := τ.injective.ne hai
          exact (Finset.disjoint_left.mp
            (alignedSupercriticalReferenceParts_pairwiseDisjoint k n π
              (Set.mem_univ (τ a)) (Set.mem_univ (τ i)) hτne)) hxBa hxB
    have hE : (Finset.univ.biUnion E).card ≤ (k - 1) * qMix := by
      have h := Finset.card_biUnion_le_card_mul Finset.univ E qMix
        (fun a _ ↦ by simpa [E, hτ] using hmix a)
      simpa [E] using h
    calc
      (alignedSupercriticalReferencePart k n π (τ i) \ D.parts i).card ≤
          (D.sparse ∪ Finset.univ.biUnion E).card := Finset.card_le_card hsub
      _ ≤ D.sparse.card + (Finset.univ.biUnion E).card :=
        Finset.card_union_le _ _
      _ ≤ qSparse + (k - 1) * qMix := Nat.add_le_add hsparse hE
  refine {
    partPermutation := τ
    sparse_card_le := hsparse
    main_sdiff_reference_le := fun i ↦ by simpa [hτ] using hmix i
    reference_sdiff_main_le := hreverse
    symmDiff_card_le := ?_
    part_card_lower := ?_
    part_card_upper := ?_ }
  · intro i
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
    have hforward :
        (D.parts i \ alignedSupercriticalReferencePart k n π (τ i)).card ≤
          qMix := by simpa [hτ] using hmix i
    have := Nat.add_le_add hforward (hreverse i)
    calc
      (D.parts i \ alignedSupercriticalReferencePart k n π (τ i)).card +
          (alignedSupercriticalReferencePart k n π (τ i) \ D.parts i).card ≤
          qMix + (qSparse + (k - 1) * qMix) := this
      _ = qSparse + k * qMix := by
        calc
          qMix + (qSparse + (k - 1) * qMix) =
              qSparse + ((k - 1) * qMix + qMix) := by omega
          _ = qSparse + k * qMix := by
            congr 1
            calc
              (k - 1) * qMix + qMix =
                  (k - 1) * qMix + 1 * qMix := by simp
              _ = ((k - 1) + 1) * qMix := by rw [Nat.add_mul]
              _ = k * qMix := by
                rw [Nat.sub_add_cancel (by omega : 1 ≤ k)]
  · intro i
    have hB := alignedSupercriticalReferencePart_card_ge_div hk π (τ i)
    have hcard : (alignedSupercriticalReferencePart k n π (τ i)).card ≤
        (alignedSupercriticalReferencePart k n π (τ i) \ D.parts i).card +
          (D.parts i).card := Finset.card_le_card_sdiff_add_card
    have := hreverse i
    omega
  · intro i
    have hB := alignedSupercriticalReferencePart_card_le_div_add_one hk π (τ i)
    have hcard : (D.parts i).card ≤
        (D.parts i \ alignedSupercriticalReferencePart k n π (τ i)).card +
          (alignedSupercriticalReferencePart k n π (τ i)).card :=
      Finset.card_le_card_sdiff_add_card
    have hf :
        (D.parts i \ alignedSupercriticalReferencePart k n π (τ i)).card ≤
          qMix := by simpa [hτ] using hmix i
    omega

/-- Proposition-valued form of
`supercriticalPartitionAlignment_of_labeledCutDist_le`, for theorem-facing
APIs and Blueprint proof-status tracking. -/
theorem exists_supercriticalPartitionAlignment_of_labeledCutDist_le
    {k n qSparse qMix : ℕ} (hk : 3 ≤ k) {γ η : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hSparseScale : η * (n : ℝ) ^ 2 <
      supercriticalOffDiagonal k γ * (qSparse + 1 : ℕ) * n)
    (hMixScale : ((k - 1 : ℕ) : ℝ) * η * (n : ℝ) ^ 2 <
      (1 - supercriticalOffDiagonal k γ) * ((qMix + 1 : ℕ) : ℝ) ^ 2)
    (hcover : qSparse + (k - 1) * qMix < n / (k - 1)) :
    Nonempty (SupercriticalPartitionAlignment D π qSparse qMix) := by
  exact ⟨supercriticalPartitionAlignment_of_labeledCutDist_le
    hk hγ hn G D π hcut hSparseScale hMixScale hcover⟩

/-! ## Real-tolerance wrapper -/

theorem abs_card_sub_card_le_card_symmDiff {V : Type*} [DecidableEq V]
    (A B : Finset V) :
    |(A.card : ℝ) - (B.card : ℝ)| ≤ (A ∆ B).card := by
  have hAB : A.card ≤ (A \ B).card + B.card :=
    Finset.card_le_card_sdiff_add_card
  have hBA : B.card ≤ (B \ A).card + A.card :=
    Finset.card_le_card_sdiff_add_card
  have hAsub : A \ B ⊆ A ∆ B := by
    intro x hx
    exact Finset.mem_symmDiff.mpr (Or.inl (Finset.mem_sdiff.mp hx))
  have hBsub : B \ A ⊆ A ∆ B := by
    intro x hx
    exact Finset.mem_symmDiff.mpr (Or.inr (Finset.mem_sdiff.mp hx))
  have hAc := Finset.card_mono hAsub
  have hBc := Finset.card_mono hBsub
  have hABR : (A.card : ℝ) ≤ (A \ B).card + B.card := by exact_mod_cast hAB
  have hBAR : (B.card : ℝ) ≤ (B \ A).card + A.card := by exact_mod_cast hBA
  have hAcR : ((A \ B).card : ℝ) ≤ (A ∆ B).card := by exact_mod_cast hAc
  have hBcR : ((B \ A).card : ℝ) ≤ (A ∆ B).card := by exact_mod_cast hBc
  rw [abs_le]
  constructor <;> linarith

/-- Every balanced reference block has size within one of the real average.
This includes the indivisible remainder explicitly rather than identifying
natural-number division with real division. -/
theorem abs_alignedReferencePart_card_sub_realAverage_le_one
    {k n : ℕ} (hk : 3 ≤ k) (π : Equiv.Perm (Fin n))
    (j : Fin (k - 1)) :
    |((alignedSupercriticalReferencePart k n π j).card : ℝ) -
        (n : ℝ) / (k - 1 : ℕ)| ≤ 1 := by
  let r := k - 1
  have hr : 0 < r := by omega
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmod : n % r < r := Nat.mod_lt n hr
  have hdecomp : n % r + r * (n / r) = n := Nat.mod_add_div n r
  have hdecompR : ((n % r : ℕ) : ℝ) + (r : ℝ) *
      ((n / r : ℕ) : ℝ) = n := by
    exact_mod_cast hdecomp
  have hfrac0 : 0 ≤ ((n % r : ℕ) : ℝ) / r := by positivity
  have hfrac1 : ((n % r : ℕ) : ℝ) / r < 1 := by
    exact (div_lt_one hrR).2 (by exact_mod_cast hmod)
  have havg : (n : ℝ) / r = ((n / r : ℕ) : ℝ) +
      ((n % r : ℕ) : ℝ) / r := by
    field_simp
    nlinarith
  rw [card_alignedSupercriticalReferencePart,
    card_supercriticalReferencePart hk]
  change |((n / r + if j.1 < n % r then 1 else 0 : ℕ) : ℝ) -
    (n : ℝ) / r| ≤ 1
  rw [havg]
  split_ifs
  · norm_num
    rw [abs_of_nonneg (by linarith)]
    linarith
  · norm_num
    rw [abs_of_nonneg hfrac0]
    linarith

/-- Natural-number division is less than one below the corresponding real
quotient.  This is the exact rounding estimate used in the eventual-size
wrapper below. -/
theorem realAverage_sub_one_lt_natDiv {n r : ℕ} (hr : 0 < r) :
    (n : ℝ) / r - 1 < ((n / r : ℕ) : ℝ) := by
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmod : n % r < r := Nat.mod_lt n hr
  have hdecomp : n % r + r * (n / r) = n := Nat.mod_add_div n r
  have hdecompR : ((n % r : ℕ) : ℝ) + (r : ℝ) *
      ((n / r : ℕ) : ℝ) = n := by
    exact_mod_cast hdecomp
  have hfrac : ((n % r : ℕ) : ℝ) / r < 1 :=
    (div_lt_one hrR).2 (by exact_mod_cast hmod)
  have havg : (n : ℝ) / r = ((n / r : ℕ) : ℝ) +
      ((n % r : ℕ) : ℝ) / r := by
    field_simp
    nlinarith
  rw [havg]
  linarith

/-- The real-tolerance form of finite partition alignment used by the
close-structure argument.  Besides balance and a small sparse class, it
retains both directed differences and the symmetric difference, so later
density estimates do not need to reconstruct overlap information. -/
structure SupercriticalRealPartitionAlignment
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n)) (ζ : ℝ) where
  partPermutation : Equiv.Perm (Fin (k - 1))
  sparse_card_le : (D.sparse.card : ℝ) ≤ ζ * n
  main_sdiff_reference_le : ∀ i,
    ((D.parts i \ alignedSupercriticalReferencePart k n π
      (partPermutation i)).card : ℝ) ≤ ζ * n
  reference_sdiff_main_le : ∀ i,
    ((alignedSupercriticalReferencePart k n π (partPermutation i) \
      D.parts i).card : ℝ) ≤ ζ * n
  symmDiff_card_le : ∀ i,
    ((D.parts i ∆ alignedSupercriticalReferencePart k n π
      (partPermutation i)).card : ℝ) ≤ ζ * n
  part_card_close : ∀ i,
    |((D.parts i).card : ℝ) - (n : ℝ) / (k - 1 : ℕ)| ≤ ζ * n

/-- Convert the exact integer alignment data to a single real tolerance.
The extra `1` is precisely the rounding loss between a balanced finite block
and the real average `n / (k - 1)`. -/
noncomputable def SupercriticalPartitionAlignment.toReal
    {k n qSparse qMix : ℕ} (hk : 3 ≤ k)
    {D : SupercriticalDivision k (Fin n)} {π : Equiv.Perm (Fin n)}
    (A : SupercriticalPartitionAlignment D π qSparse qMix)
    {ζ : ℝ}
    (hbudget : ((qSparse + k * qMix : ℕ) : ℝ) + 1 ≤ ζ * n) :
    SupercriticalRealPartitionAlignment D π ζ := by
  have hsparseBudget : (qSparse : ℝ) ≤ ζ * n := by
    have hnat : qSparse ≤ qSparse + k * qMix := by omega
    have hreal : (qSparse : ℝ) ≤ ((qSparse + k * qMix : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hmixBudget : (qMix : ℝ) ≤ ζ * n := by
    have hqmul : qMix ≤ k * qMix :=
      Nat.le_mul_of_pos_left qMix (by omega : 0 < k)
    have hnat : qMix ≤ qSparse + k * qMix :=
      hqmul.trans (Nat.le_add_left _ _)
    have hreal : (qMix : ℝ) ≤ ((qSparse + k * qMix : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hreverseBudget : ((qSparse + (k - 1) * qMix : ℕ) : ℝ) ≤
      ζ * n := by
    have hmul : (k - 1) * qMix ≤ k * qMix :=
      Nat.mul_le_mul_right qMix (Nat.sub_le k 1)
    have hnat : qSparse + (k - 1) * qMix ≤ qSparse + k * qMix :=
      Nat.add_le_add_left hmul qSparse
    have hreal : ((qSparse + (k - 1) * qMix : ℕ) : ℝ) ≤
        ((qSparse + k * qMix : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  refine {
    partPermutation := A.partPermutation
    sparse_card_le := ?_
    main_sdiff_reference_le := ?_
    reference_sdiff_main_le := ?_
    symmDiff_card_le := ?_
    part_card_close := ?_ }
  · exact (by exact_mod_cast A.sparse_card_le :
      (D.sparse.card : ℝ) ≤ qSparse) |>.trans hsparseBudget
  · intro i
    exact (by exact_mod_cast A.main_sdiff_reference_le i :
      ((D.parts i \ alignedSupercriticalReferencePart k n π
        (A.partPermutation i)).card : ℝ) ≤ qMix) |>.trans hmixBudget
  · intro i
    exact (by exact_mod_cast A.reference_sdiff_main_le i :
      ((alignedSupercriticalReferencePart k n π (A.partPermutation i) \
        D.parts i).card : ℝ) ≤
          ((qSparse + (k - 1) * qMix : ℕ) : ℝ)) |>.trans
          hreverseBudget
  · intro i
    have hA :
        ((D.parts i ∆ alignedSupercriticalReferencePart k n π
          (A.partPermutation i)).card : ℝ) ≤
            ((qSparse + k * qMix : ℕ) : ℝ) := by
      exact_mod_cast A.symmDiff_card_le i
    exact hA.trans (by linarith)
  · intro i
    let B := alignedSupercriticalReferencePart k n π (A.partPermutation i)
    have hPB : |((D.parts i).card : ℝ) - (B.card : ℝ)| ≤
        ((D.parts i ∆ B).card : ℝ) :=
      abs_card_sub_card_le_card_symmDiff (D.parts i) B
    have hBavg : |(B.card : ℝ) - (n : ℝ) / (k - 1 : ℕ)| ≤ 1 := by
      simpa [B] using abs_alignedReferencePart_card_sub_realAverage_le_one
        hk π (A.partPermutation i)
    have hsymm : ((D.parts i ∆ B).card : ℝ) ≤
        ((qSparse + k * qMix : ℕ) : ℝ) := by
      exact_mod_cast A.symmDiff_card_le i
    calc
      |((D.parts i).card : ℝ) - (n : ℝ) / (k - 1 : ℕ)| ≤
          |((D.parts i).card : ℝ) - (B.card : ℝ)| +
            |(B.card : ℝ) - (n : ℝ) / (k - 1 : ℕ)| :=
        abs_sub_le _ _ _
      _ ≤ ((D.parts i ∆ B).card : ℝ) + 1 := add_le_add hPB hBavg
      _ ≤ ((qSparse + k * qMix : ℕ) : ℝ) + 1 := by linarith
      _ ≤ ζ * n := hbudget

/-- A floor-free quantitative interface for real-tolerance alignment.  The
auxiliary rate `β` controls the integer budget `⌊β n⌋`; the two displayed
finite-size hypotheses account exactly for covering an indivisible balanced
partition and for its one-vertex rounding error. -/
theorem exists_supercriticalRealPartitionAlignment_of_labeledCutDist_le
    {k n : ℕ} (hk : 3 ≤ k) {γ η ζ β : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hn : 0 < n) (hβ : 0 < β)
    (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
    (π : Equiv.Perm (Fin n))
    (hcut : DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
      (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
        (supercriticalDivisionModelGraph G D))
      ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η)
    (hEtaSparse : η < supercriticalOffDiagonal k γ * β)
    (hEtaMix : ((k - 1 : ℕ) : ℝ) * η <
      (1 - supercriticalOffDiagonal k γ) * β ^ 2)
    (hCoverBudget : (k : ℝ) * β * (n : ℝ) + 1 ≤
      ((n / (k - 1) : ℕ) : ℝ))
    (hFinalBudget : ((k + 1 : ℕ) : ℝ) * β * (n : ℝ) + 1 ≤
      ζ * (n : ℝ)) :
    Nonempty (SupercriticalRealPartitionAlignment D π ζ) := by
  classical
  let q : ℕ := ⌊β * (n : ℝ)⌋₊
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hβn0 : 0 ≤ β * (n : ℝ) := by positivity
  have hqle : (q : ℝ) ≤ β * (n : ℝ) := by
    simpa [q] using (Nat.floor_le hβn0)
  have hqlt : β * (n : ℝ) < ((q + 1 : ℕ) : ℝ) := by
    simpa [q, Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (β * (n : ℝ)))
  have hρ : 0 < supercriticalOffDiagonal k γ :=
    supercriticalOffDiagonal_pos hk hγ.1
  have h1ρ : 0 < 1 - supercriticalOffDiagonal k γ := by
    linarith [supercriticalOffDiagonal_lt_one hk hγ.2]
  have hSparseScale : η * (n : ℝ) ^ 2 <
      supercriticalOffDiagonal k γ * ((q + 1 : ℕ) : ℝ) * n := by
    have h₁ := mul_lt_mul_of_pos_right hEtaSparse (sq_pos_of_pos hnR)
    have h₂ := mul_lt_mul_of_pos_left hqlt hρ
    have h₃ := mul_lt_mul_of_pos_right h₂ hnR
    nlinarith
  have hMixScale : ((k - 1 : ℕ) : ℝ) * η * (n : ℝ) ^ 2 <
      (1 - supercriticalOffDiagonal k γ) * ((q + 1 : ℕ) : ℝ) ^ 2 := by
    have h₁ := mul_lt_mul_of_pos_right hEtaMix (sq_pos_of_pos hnR)
    have hsq : (β * (n : ℝ)) ^ 2 < (((q + 1 : ℕ) : ℝ)) ^ 2 := by
      nlinarith
    have h₂ := mul_lt_mul_of_pos_left hsq h1ρ
    nlinarith
  have hcover : q + (k - 1) * q < n / (k - 1) := by
    have hcast : (((k * q + 1 : ℕ) : ℝ)) ≤
        ((n / (k - 1) : ℕ) : ℝ) := by
      calc
        (((k * q + 1 : ℕ) : ℝ)) = (k : ℝ) * (q : ℝ) + 1 := by norm_num
        _ ≤ (k : ℝ) * (β * (n : ℝ)) + 1 := by gcongr
        _ = (k : ℝ) * β * (n : ℝ) + 1 := by ring
        _ ≤ ((n / (k - 1) : ℕ) : ℝ) := hCoverBudget
    have hnat : k * q + 1 ≤ n / (k - 1) := by exact_mod_cast hcast
    calc
      q + (k - 1) * q = (1 + (k - 1)) * q := by
        rw [Nat.add_mul]
        simp
      _ = k * q := by
        congr 1
        omega
      _ < n / (k - 1) := by omega
  let A := supercriticalPartitionAlignment_of_labeledCutDist_le
    hk hγ hn G D π hcut hSparseScale hMixScale hcover
  have hqfinal : (((q + k * q : ℕ) : ℝ)) + 1 ≤ ζ * (n : ℝ) := by
    calc
      (((q + k * q : ℕ) : ℝ)) + 1 =
          ((k + 1 : ℕ) : ℝ) * (q : ℝ) + 1 := by
            push_cast
            ring
      _ ≤ ((k + 1 : ℕ) : ℝ) * (β * (n : ℝ)) + 1 := by gcongr
      _ = ((k + 1 : ℕ) : ℝ) * β * (n : ℝ) + 1 := by ring
      _ ≤ ζ * (n : ℝ) := hFinalBudget
  exact ⟨A.toReal hk hqfinal⟩

/-- Eventual real-tolerance partition alignment.  For every positive target
tolerance, one labeled-cut tolerance and one vertex threshold work uniformly
for every division and every aligning vertex permutation.  All finite
rounding and auxiliary-budget choices are hidden in this interface. -/
theorem eventually_supercriticalRealPartitionAlignment
    {k : ℕ} (hk : 3 ≤ k) {γ ζ : ℝ}
    (hγ : γ ∈ Set.Ico (gammaK k) 1) (hζ : 0 < ζ) :
    ∃ η > 0, ∃ n₀ : ℕ, ∀ {n : ℕ}, n₀ ≤ n →
      ∀ (G : SimpleGraph (Fin n)) (D : SupercriticalDivision k (Fin n))
        (π : Equiv.Perm (Fin n)),
        DenseGraph.FiniteWeightedGraph.finiteLabeledCutDist
          (DenseGraph.FiniteWeightedGraph.ofSimpleGraph
            (supercriticalDivisionModelGraph G D))
          ((supercriticalReferenceWeightedGraph k hk γ hγ n).permute π) ≤ η →
        Nonempty (SupercriticalRealPartitionAlignment D π ζ) := by
  let r : ℝ := (k - 1 : ℕ)
  let ρ : ℝ := supercriticalOffDiagonal k γ
  let β : ℝ := min (ζ / (2 * (k + 1 : ℕ)))
    (1 / (2 * (k : ℝ) * r))
  let η : ℝ := min (ρ * β / 2)
    ((1 - ρ) * β ^ 2 / (2 * (k : ℝ)))
  have hkR : 0 < (k : ℝ) := by positivity
  have hr : 0 < k - 1 := by omega
  have hrR : 0 < r := by
    dsimp [r]
    exact_mod_cast hr
  have hρ : 0 < ρ := by
    exact supercriticalOffDiagonal_pos hk hγ.1
  have h1ρ : 0 < 1 - ρ := by
    dsimp [ρ]
    linarith [supercriticalOffDiagonal_lt_one hk hγ.2]
  have hβleft : 0 < ζ / (2 * (k + 1 : ℕ)) := by positivity
  have hβright : 0 < 1 / (2 * (k : ℝ) * r) := by positivity
  have hβ : 0 < β := by
    exact lt_min hβleft hβright
  have hη : 0 < η := by
    exact lt_min (by positivity) (by positivity)
  have hEtaSparse : η < ρ * β := by
    have hprod : 0 < ρ * β := mul_pos hρ hβ
    have hhalf : ρ * β / 2 < ρ * β := by linarith
    exact (min_le_left _ _).trans_lt hhalf
  have hEtaMix : ((k - 1 : ℕ) : ℝ) * η <
      (1 - ρ) * β ^ 2 := by
    have hηright : η ≤
        (1 - ρ) * β ^ 2 / (2 * (k : ℝ)) := min_le_right _ _
    have hrk : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Nat.sub_le k 1)
    have hnonneg : 0 ≤ η := hη.le
    have hfirst : ((k - 1 : ℕ) : ℝ) * η ≤ (k : ℝ) * η :=
      mul_le_mul_of_nonneg_right hrk hnonneg
    have hsecond : (k : ℝ) * η ≤
        (1 - ρ) * β ^ 2 / 2 := by
      calc
        (k : ℝ) * η ≤ (k : ℝ) *
            ((1 - ρ) * β ^ 2 / (2 * (k : ℝ))) :=
          mul_le_mul_of_nonneg_left hηright hkR.le
        _ = (1 - ρ) * β ^ 2 / 2 := by
          field_simp
    have hhalf : (1 - ρ) * β ^ 2 / 2 <
        (1 - ρ) * β ^ 2 := by
      have hprod : 0 < (1 - ρ) * β ^ 2 := by positivity
      linarith
    exact hfirst.trans_lt (hsecond.trans_lt hhalf)
  have hβcover : (k : ℝ) * β < 1 / r := by
    have hmin : β ≤ 1 / (2 * (k : ℝ) * r) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_left hmin hkR.le
    have heq : (k : ℝ) * (1 / (2 * (k : ℝ) * r)) = 1 / (2 * r) := by
      field_simp
    have hhalf : 1 / (2 * r) < 1 / r := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 2 * r) hrR]
      nlinarith
    rw [heq] at hmul
    exact hmul.trans_lt hhalf
  have hβfinal : ((k + 1 : ℕ) : ℝ) * β < ζ := by
    have hmin : β ≤ ζ / (2 * (k + 1 : ℕ)) := min_le_left _ _
    have hk1R : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hmin hk1R.le
    have heq : ((k + 1 : ℕ) : ℝ) *
        (ζ / (2 * (k + 1 : ℕ))) = ζ / 2 := by
      field_simp
    rw [heq] at hmul
    have hhalf : ζ / 2 < ζ := by linarith
    exact hmul.trans_lt hhalf
  let cCover : ℝ := 1 / r - (k : ℝ) * β
  let cFinal : ℝ := ζ - ((k + 1 : ℕ) : ℝ) * β
  have hcCover : 0 < cCover := by
    dsimp [cCover]
    linarith
  have hcFinal : 0 < cFinal := by
    dsimp [cFinal]
    linarith
  obtain ⟨Ncover, hNcover⟩ := exists_nat_gt (2 / cCover)
  obtain ⟨Nfinal, hNfinal⟩ := exists_nat_gt (1 / cFinal)
  refine ⟨η, hη, max 1 (max Ncover Nfinal), ?_⟩
  intro n hn₀ G D π hcut
  have hn1 : 1 ≤ n := (Nat.le_max_left 1 (max Ncover Nfinal)).trans hn₀
  have hn : 0 < n := by omega
  have hnCover : Ncover ≤ n := by
    exact (Nat.le_max_left Ncover Nfinal).trans
      ((Nat.le_max_right 1 (max Ncover Nfinal)).trans hn₀)
  have hnFinal : Nfinal ≤ n := by
    exact (Nat.le_max_right Ncover Nfinal).trans
      ((Nat.le_max_right 1 (max Ncover Nfinal)).trans hn₀)
  have hcoverScale : 2 < cCover * (n : ℝ) := by
    have hnR : 2 / cCover < (n : ℝ) :=
      hNcover.trans_le (by exact_mod_cast hnCover)
    have := (div_lt_iff₀ hcCover).mp hnR
    nlinarith
  have hfinalScale : 1 < cFinal * (n : ℝ) := by
    have hnR : 1 / cFinal < (n : ℝ) :=
      hNfinal.trans_le (by exact_mod_cast hnFinal)
    have := (div_lt_iff₀ hcFinal).mp hnR
    nlinarith
  have hround := realAverage_sub_one_lt_natDiv (n := n) hr
  have hCoverBudget : (k : ℝ) * β * (n : ℝ) + 1 ≤
      ((n / (k - 1) : ℕ) : ℝ) := by
    have hreal : (k : ℝ) * β * (n : ℝ) + 2 < (n : ℝ) / r := by
      dsimp [cCover] at hcoverScale
      have heq : (1 / r - (k : ℝ) * β) * (n : ℝ) =
          (n : ℝ) / r - (k : ℝ) * β * (n : ℝ) := by ring
      rw [heq] at hcoverScale
      linarith
    have hround' : (n : ℝ) / r - 1 <
        ((n / (k - 1) : ℕ) : ℝ) := by
      simpa [r] using hround
    linarith
  have hFinalBudget : ((k + 1 : ℕ) : ℝ) * β * (n : ℝ) + 1 ≤
      ζ * (n : ℝ) := by
    dsimp [cFinal] at hfinalScale
    have heq : (ζ - ((k + 1 : ℕ) : ℝ) * β) * (n : ℝ) =
        ζ * (n : ℝ) - ((k + 1 : ℕ) : ℝ) * β * (n : ℝ) := by ring
    rw [heq] at hfinalScale
    linarith
  exact exists_supercriticalRealPartitionAlignment_of_labeledCutDist_le
    hk hγ hn hβ G D π hcut
      (by simpa [ρ] using hEtaSparse)
      (by simpa [ρ] using hEtaMix)
      hCoverBudget hFinalBudget

end InducedStars
