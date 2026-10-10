import DenseGraph.FiniteModels.MatrixCut
import InducedStars.Graphon.CellRelabeling
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite weighted graphs and labeled cut discrepancy

This file packages symmetric `[0,1]`-valued matrices on a finite vertex set
and the normalized labeled cut discrepancy between two such matrices.  The
discrepancy is a literal maximum over the finitely many pairs of vertex
subsets, rather than an abstract supremum.
-/

noncomputable section

open Finset
open scoped BigOperators

namespace DenseGraph

universe u

/-- A symmetric `[0,1]`-valued matrix on a finite vertex type. -/
structure FiniteWeightedGraph (V : Type u) where
  weight : Matrix V V ℝ
  symmetric : ∀ i j, weight i j = weight j i
  nonneg : ∀ i j, 0 ≤ weight i j
  le_one : ∀ i j, weight i j ≤ 1

namespace FiniteWeightedGraph

variable {V : Type u}

@[ext] theorem ext {A B : FiniteWeightedGraph V}
    (h : ∀ i j, A.weight i j = B.weight i j) : A = B := by
  cases A with
  | mk weightA symmetricA nonnegA leOneA =>
    cases B with
    | mk weightB symmetricB nonnegB leOneB =>
      have hw : weightA = weightB := funext fun i ↦ funext fun j ↦ h i j
      subst weightB
      rfl

theorem weight_isSymm (A : FiniteWeightedGraph V) :
    A.weight.IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  exact A.symmetric j i

/-- Regard a finite simple graph as its `0/1` adjacency weighted graph. -/
noncomputable def ofSimpleGraph (G : SimpleGraph V) : FiniteWeightedGraph V := by
  classical
  exact
    { weight := fun i j ↦ if G.Adj i j then 1 else 0
      symmetric := by
        intro i j
        rw [G.adj_comm]
      nonneg := by
        intro i j
        split <;> norm_num
      le_one := by
        intro i j
        split <;> norm_num }

@[simp] theorem ofSimpleGraph_weight (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : V) :
    (ofSimpleGraph G).weight i j = if G.Adj i j then 1 else 0 := by
  classical
  simp [ofSimpleGraph]

@[simp] theorem ofSimpleGraph_weight_self (G : SimpleGraph V) (i : V) :
    (ofSimpleGraph G).weight i i = 0 := by
  classical
  simp [ofSimpleGraph]

/-- Simultaneously reindex both coordinates by a vertex permutation. -/
def permute (A : FiniteWeightedGraph V) (e : Equiv.Perm V) :
    FiniteWeightedGraph V where
  weight i j := A.weight (e i) (e j)
  symmetric i j := A.symmetric (e i) (e j)
  nonneg i j := A.nonneg (e i) (e j)
  le_one i j := A.le_one (e i) (e j)

@[simp] theorem permute_weight (A : FiniteWeightedGraph V)
    (e : Equiv.Perm V) (i j : V) :
    (A.permute e).weight i j = A.weight (e i) (e j) := rfl

@[simp] theorem permute_refl (A : FiniteWeightedGraph V) :
    A.permute (Equiv.refl V) = A := by
  ext i j
  rfl

@[simp] theorem permute_symm_permute (A : FiniteWeightedGraph V)
    (e : Equiv.Perm V) :
    (A.permute e).permute e.symm = A := by
  ext i j
  simp

section Graphon

variable {n : ℕ}

private theorem matrixGraphon_congr {q : ℕ}
    {M N : Matrix (Fin q) (Fin q) ℝ}
    (hMN : M = N)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hN₀ : ∀ i j, 0 ≤ N i j)
    (hM₁ : ∀ i j, M i j ≤ 1) (hN₁ : ∀ i j, N i j ≤ 1) :
    InducedStars.matrixGraphon M hM hM₀ hM₁ =
      InducedStars.matrixGraphon N hN hN₀ hN₁ := by
  subst N
  rfl

/-- The equal-cell matrix graphon carried by a weighted graph on `Fin n`. -/
def toGraphon (A : FiniteWeightedGraph (Fin n)) : InducedStars.Graphon :=
  InducedStars.matrixGraphon A.weight A.weight_isSymm A.nonneg A.le_one

/-- The weighted graphon construction extends the existing adjacency-graphon
construction definitionally, up to proof irrelevance. -/
@[simp] theorem toGraphon_ofSimpleGraph (G : SimpleGraph (Fin n)) :
    (ofSimpleGraph G).toGraphon = InducedStars.graphGraphon G := by
  simp only [toGraphon, InducedStars.graphGraphon]
  congr 1

/-- Permuting a weighted matrix is the canonical equal-cell graphon
relabeling. -/
theorem toGraphon_permute_eq_relabel (A : FiniteWeightedGraph (Fin n))
    (e : Equiv.Perm (Fin n)) :
    (A.permute e).toGraphon =
      A.toGraphon.relabel (InducedStars.cellPermRelabeling e) := by
  have hweight : (A.permute e).weight =
      InducedStars.permuteMatrix e A.weight := by
    ext i j
    rfl
  calc
    (A.permute e).toGraphon =
        InducedStars.matrixGraphon (InducedStars.permuteMatrix e A.weight)
          (InducedStars.permuteMatrix_isSymm e A.weight_isSymm)
          (InducedStars.permuteMatrix_nonneg e A.nonneg)
          (InducedStars.permuteMatrix_le_one e A.le_one) :=
      matrixGraphon_congr hweight _ _ _ _ _ _
    _ = A.toGraphon.relabel (InducedStars.cellPermRelabeling e) := by
      exact InducedStars.matrixGraphon_permuteMatrix_eq_relabel e A.weight
        A.weight_isSymm A.nonneg A.le_one

/-- A simultaneous finite permutation changes a weighted graphon only by a
graphon relabeling. -/
@[simp] theorem cutDist_toGraphon_permute_self (A : FiniteWeightedGraph (Fin n))
    (e : Equiv.Perm (Fin n)) :
    InducedStars.cutDist (A.permute e).toGraphon A.toGraphon = 0 := by
  rw [toGraphon_permute_eq_relabel, InducedStars.cutDist_relabel_self]

end Graphon

section LabeledCut

variable [Fintype V] [DecidableEq V]

/-- The unnormalized signed rectangle discrepancy of two weighted graphs. -/
def rectangleDiscrepancy (A B : FiniteWeightedGraph V)
    (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, (A.weight i j - B.weight i j)

/-- All absolute rectangle discrepancies.  This finite set is nonempty since
it contains the value of the empty rectangle. -/
private def rectangleDiscrepancyValues (A B : FiniteWeightedGraph V) : Finset ℝ :=
  Finset.univ.image fun ST : Finset V × Finset V ↦
    |rectangleDiscrepancy A B ST.1 ST.2|

private theorem rectangleDiscrepancyValues_nonempty
    (A B : FiniteWeightedGraph V) :
    (rectangleDiscrepancyValues A B).Nonempty := by
  classical
  refine ⟨|rectangleDiscrepancy A B ∅ ∅|, ?_⟩
  simp [rectangleDiscrepancyValues]

/-- The largest unnormalized absolute rectangle discrepancy. -/
def finiteLabeledCutRaw (A B : FiniteWeightedGraph V) : ℝ :=
  (rectangleDiscrepancyValues A B).max'
    (rectangleDiscrepancyValues_nonempty A B)

/-- Normalized same-label cut discrepancy.  It is the attained maximum over
all pairs of vertex subsets, divided by the square of the vertex count. -/
def finiteLabeledCutDist (A B : FiniteWeightedGraph V) : ℝ :=
  finiteLabeledCutRaw A B / (Fintype.card V : ℝ) ^ 2

theorem abs_rectangleDiscrepancy_le_raw (A B : FiniteWeightedGraph V)
    (S T : Finset V) :
    |rectangleDiscrepancy A B S T| ≤ finiteLabeledCutRaw A B := by
  classical
  apply Finset.le_max'
  simp [rectangleDiscrepancyValues]

/-- The finite maximum in `finiteLabeledCutRaw` is attained. -/
theorem exists_rectangleDiscrepancy_eq_raw (A B : FiniteWeightedGraph V) :
    ∃ S T : Finset V,
      |rectangleDiscrepancy A B S T| = finiteLabeledCutRaw A B := by
  classical
  have hm := Finset.max'_mem (rectangleDiscrepancyValues A B)
    (rectangleDiscrepancyValues_nonempty A B)
  rcases Finset.mem_image.mp hm with ⟨ST, hST, hval⟩
  exact ⟨ST.1, ST.2, hval⟩

/-- The normalized labeled cut discrepancy is attained by a pair of vertex
subsets. -/
theorem exists_finiteLabeledCutDist_eq_rectangle
    (A B : FiniteWeightedGraph V) :
    ∃ S T : Finset V,
      finiteLabeledCutDist A B =
        |rectangleDiscrepancy A B S T| / (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨S, T, hST⟩ := exists_rectangleDiscrepancy_eq_raw A B
  refine ⟨S, T, ?_⟩
  rw [finiteLabeledCutDist, ← hST]

theorem finiteLabeledCutRaw_nonneg (A B : FiniteWeightedGraph V) :
    0 ≤ finiteLabeledCutRaw A B := by
  obtain ⟨S, T, hST⟩ := exists_rectangleDiscrepancy_eq_raw A B
  rw [← hST]
  exact abs_nonneg _

theorem finiteLabeledCutDist_nonneg (A B : FiniteWeightedGraph V) :
    0 ≤ finiteLabeledCutDist A B := by
  exact div_nonneg (finiteLabeledCutRaw_nonneg A B) (sq_nonneg _)

theorem finiteLabeledCutRaw_self (A : FiniteWeightedGraph V) :
    finiteLabeledCutRaw A A = 0 := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
    simp [rectangleDiscrepancy]
  · exact finiteLabeledCutRaw_nonneg A A

@[simp] theorem finiteLabeledCutDist_self (A : FiniteWeightedGraph V) :
    finiteLabeledCutDist A A = 0 := by
  simp [finiteLabeledCutDist, finiteLabeledCutRaw_self]

theorem rectangleDiscrepancy_comm (A B : FiniteWeightedGraph V)
    (S T : Finset V) :
    rectangleDiscrepancy B A S T = -rectangleDiscrepancy A B S T := by
  simp only [rectangleDiscrepancy]
  simp_rw [show ∀ i j, B.weight i j - A.weight i j =
      -(A.weight i j - B.weight i j) by intros; ring]
  simp

theorem finiteLabeledCutRaw_comm (A B : FiniteWeightedGraph V) :
    finiteLabeledCutRaw A B = finiteLabeledCutRaw B A := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
    rw [← abs_neg, ← rectangleDiscrepancy_comm]
    exact abs_rectangleDiscrepancy_le_raw B A ST.1 ST.2
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
    rw [rectangleDiscrepancy_comm, abs_neg]
    exact abs_rectangleDiscrepancy_le_raw A B ST.1 ST.2

theorem finiteLabeledCutDist_comm (A B : FiniteWeightedGraph V) :
    finiteLabeledCutDist A B = finiteLabeledCutDist B A := by
  rw [finiteLabeledCutDist, finiteLabeledCutDist, finiteLabeledCutRaw_comm]

private theorem rectangleDiscrepancy_add (A B C : FiniteWeightedGraph V)
    (S T : Finset V) :
    rectangleDiscrepancy A C S T =
      rectangleDiscrepancy A B S T + rectangleDiscrepancy B C S T := by
  simp only [rectangleDiscrepancy]
  simp_rw [show ∀ i j, A.weight i j - C.weight i j =
      (A.weight i j - B.weight i j) + (B.weight i j - C.weight i j) by
        intros; ring]
  simp only [Finset.sum_add_distrib]

theorem finiteLabeledCutRaw_triangle (A B C : FiniteWeightedGraph V) :
    finiteLabeledCutRaw A C ≤
      finiteLabeledCutRaw A B + finiteLabeledCutRaw B C := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
  rw [rectangleDiscrepancy_add]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_rectangleDiscrepancy_le_raw A B ST.1 ST.2)
    (abs_rectangleDiscrepancy_le_raw B C ST.1 ST.2))

theorem finiteLabeledCutDist_triangle (A B C : FiniteWeightedGraph V) :
    finiteLabeledCutDist A C ≤
      finiteLabeledCutDist A B + finiteLabeledCutDist B C := by
  simp only [finiteLabeledCutDist, ← add_div]
  exact div_le_div_of_nonneg_right (finiteLabeledCutRaw_triangle A B C)
    (sq_nonneg _)

/-- Every normalized rectangle sum is bounded by the labeled cut
discrepancy. -/
theorem abs_rectangleDiscrepancy_div_card_sq_le
    (A B : FiniteWeightedGraph V) (S T : Finset V) :
    |rectangleDiscrepancy A B S T| / (Fintype.card V : ℝ) ^ 2 ≤
      finiteLabeledCutDist A B := by
  exact div_le_div_of_nonneg_right (abs_rectangleDiscrepancy_le_raw A B S T)
    (sq_nonneg _)

/-- Unnormalized form of the rectangle inequality. -/
theorem abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq
    (A B : FiniteWeightedGraph V) (S T : Finset V) :
    |rectangleDiscrepancy A B S T| ≤
      finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 := by
  by_cases hV : Fintype.card V = 0
  · have hEmpty : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    letI : IsEmpty V := hEmpty
    have hS : S = ∅ := Subsingleton.elim _ _
    simp [rectangleDiscrepancy, hS]
  · calc
      |rectangleDiscrepancy A B S T| ≤ finiteLabeledCutRaw A B :=
        abs_rectangleDiscrepancy_le_raw A B S T
      _ = finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 := by
        rw [finiteLabeledCutDist]
        have hVℝ : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hV
        field_simp

/-- Named expanded form of the rectangle bound used by finite applications. -/
theorem finiteLabeledCutDist_rectangle_le
    (A B : FiniteWeightedGraph V) (S T : Finset V) :
    |∑ i ∈ S, ∑ j ∈ T, (A.weight i j - B.weight i j)| ≤
      finiteLabeledCutDist A B * (Fintype.card V : ℝ) ^ 2 := by
  exact abs_rectangleDiscrepancy_le_finiteLabeledCutDist_mul_card_sq A B S T

private theorem rectangleDiscrepancy_permute (A B : FiniteWeightedGraph V)
    (e : Equiv.Perm V) (S T : Finset V) :
    rectangleDiscrepancy (A.permute e) (B.permute e) S T =
      rectangleDiscrepancy A B (S.map e.toEmbedding) (T.map e.toEmbedding) := by
  classical
  simp [rectangleDiscrepancy]

/-- The same-label discrepancy is invariant under a simultaneous vertex
permutation. -/
theorem finiteLabeledCutRaw_permute (A B : FiniteWeightedGraph V)
    (e : Equiv.Perm V) :
    finiteLabeledCutRaw (A.permute e) (B.permute e) =
      finiteLabeledCutRaw A B := by
  apply le_antisymm
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
    rw [rectangleDiscrepancy_permute]
    exact abs_rectangleDiscrepancy_le_raw A B _ _
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨ST, hST, rfl⟩
    let S := ST.1.map e.symm.toEmbedding
    let T := ST.2.map e.symm.toEmbedding
    have hS : S.map e.toEmbedding = ST.1 := by
      ext i
      simp [S]
    have hT : T.map e.toEmbedding = ST.2 := by
      ext i
      simp [T]
    rw [← hS, ← hT, ← rectangleDiscrepancy_permute]
    exact abs_rectangleDiscrepancy_le_raw (A.permute e) (B.permute e) S T

theorem finiteLabeledCutDist_permute (A B : FiniteWeightedGraph V)
    (e : Equiv.Perm V) :
    finiteLabeledCutDist (A.permute e) (B.permute e) =
      finiteLabeledCutDist A B := by
  rw [finiteLabeledCutDist, finiteLabeledCutDist,
    finiteLabeledCutRaw_permute]

end LabeledCut

section GraphonCutBridge

variable {n : ℕ}

/-- The analytic cut norm between equal-cell weighted graphons is bounded by
the corresponding finite labeled cut discrepancy. -/
theorem cutNorm_toGraphon_sub_le_finiteLabeledCutDist
    (A B : FiniteWeightedGraph (Fin n)) :
    InducedStars.cutNorm (A.toGraphon.toL1 - B.toGraphon.toL1) ≤
      finiteLabeledCutDist A B := by
  by_cases hn : 0 < n
  · apply DenseGraph.cutNorm_matrixGraphon_sub_le_of_rect_sum hn
      A.weight B.weight A.weight_isSymm B.weight_isSymm
      A.nonneg A.le_one B.nonneg B.le_one
      (finiteLabeledCutDist_nonneg A B)
    intro S T
    have h := abs_rectangleDiscrepancy_le_raw A B S T
    calc
      |∑ i ∈ S, ∑ j ∈ T, (A.weight i j - B.weight i j)| ≤
          finiteLabeledCutRaw A B := h
      _ = finiteLabeledCutDist A B * (n : ℝ) ^ 2 := by
        rw [finiteLabeledCutDist, Fintype.card_fin]
        have hnℝ : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        field_simp
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hAB : A = B := by
      ext i
      exact Fin.elim0 i
    subst B
    simp

/-- The unlabeled graphon cut distance is bounded by the finite same-label
cut discrepancy. -/
theorem cutDist_toGraphon_le_finiteLabeledCutDist
    (A B : FiniteWeightedGraph (Fin n)) :
    InducedStars.cutDist A.toGraphon B.toGraphon ≤ finiteLabeledCutDist A B :=
  (InducedStars.cutDist_le_cutNorm _ _).trans
    (cutNorm_toGraphon_sub_le_finiteLabeledCutDist A B)

end GraphonCutBridge

end FiniteWeightedGraph

end DenseGraph
