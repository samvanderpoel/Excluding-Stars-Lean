import InducedStars.Graphon.Metric
import InducedStars.Graphon.Step
import DenseGraph.FiniteModels.MatrixCut
import InducedStars.Graphon.CellRelabeling
import InducedStars.Graphon.PartitionAlignment
import InducedStars.Graphon.PartitionCut
import InducedStars.Graphon.StepEstimates
import InducedStars.Regularity.Type
import Mathlib.Tactic

/-!
# Graphon approximation by types

This file defines the graphon carried by a paper regularity type.  Its matrix
contains the actual graph densities of the nonexceptional clusters; the
green/blue vertex decoration and the reduced-edge colors play no role in this
analytic object.
-/

noncomputable section

open Finset Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

open Regularity

universe u

section TypeGraphon

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {epsilon delta : ℝ} {ℓ : ℕ}

/-- The density matrix of a paper regularity type.

On the diagonal this deliberately uses `graphDensity G A A`.  Mathlib's
`interedges A A` consists of ordered adjacent pairs, so an undirected internal
edge is counted twice.  This is exactly the adjacency-matrix graphon
normalization and introduces no factor-of-two discrepancy. -/
def typeDensityMatrix (T : RegularityType G epsilon delta ℓ) :
    Matrix (Fin T.partition.clusterCount) (Fin T.partition.clusterCount) ℝ :=
  fun i j ↦ graphDensity G (T.partition.clusters i) (T.partition.clusters j)

theorem typeDensityMatrix_isSymm (T : RegularityType G epsilon delta ℓ) :
    (typeDensityMatrix T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact graphDensity_comm G _ _

theorem typeDensityMatrix_nonneg (T : RegularityType G epsilon delta ℓ)
    (i j : Fin T.partition.clusterCount) :
    0 ≤ typeDensityMatrix T i j :=
  graphDensity_nonneg G _ _

theorem typeDensityMatrix_le_one (T : RegularityType G epsilon delta ℓ)
    (i j : Fin T.partition.clusterCount) :
    typeDensityMatrix T i j ≤ 1 :=
  graphDensity_le_one G _ _

/-- The equal-cell graphon associated with a paper regularity type.

Only the nonexceptional clusters occur: the exceptional class has no cell.
The value on cell `(i,j)` is the actual graph density of those clusters, not
their color in the reduced colored graph. -/
def typeGraphon (T : RegularityType G epsilon delta ℓ) : Graphon :=
  matrixGraphon (typeDensityMatrix T) (typeDensityMatrix_isSymm T)
    (typeDensityMatrix_nonneg T) (typeDensityMatrix_le_one T)

/-- Cell formula for a type graphon. -/
theorem typeGraphon_ae_eq_on_cell (T : RegularityType G epsilon delta ℓ)
    (i j : Fin T.partition.clusterCount) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      typeGraphon T z =
        graphDensity G (T.partition.clusters i) (T.partition.clusters j) := by
  simpa [typeGraphon, typeDensityMatrix] using
    matrixGraphon_ae_eq_on_cell (typeDensityMatrix T) (typeDensityMatrix_isSymm T)
      (typeDensityMatrix_nonneg T) (typeDensityMatrix_le_one T) i j

/-- The type-matrix diagonal is the ordered adjacency density.  In
particular, each undirected internal edge contributes two ordered pairs. -/
theorem typeDensityMatrix_diag_eq_orderedEdgeCount
    (T : RegularityType G epsilon delta ℓ)
    (i : Fin T.partition.clusterCount) :
    typeDensityMatrix T i i =
      ((G.interedges (T.partition.clusters i) (T.partition.clusters i)).card : ℝ) /
        ((T.partition.clusters i).card : ℝ) ^ 2 := by
  rw [typeDensityMatrix, graphDensity_eq]
  ring_nf

end TypeGraphon

/-! ## Compatibility exports for the reusable finite matrix-cut layer -/

/-- Compatibility wrapper for the reusable finite-cube extremum lemma. -/
theorem abs_sum_mul_le_of_abs_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c a : ι → ℝ) (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1)
    {B : ℝ} (hB : ∀ s : Finset ι, |∑ i ∈ s, c i| ≤ B) :
    |∑ i, a i * c i| ≤ B :=
  DenseGraph.abs_sum_mul_le_of_abs_sum_le c a ha₀ ha₁ hB

/-- Compatibility wrapper for the reusable bilinear finite-cube lemma. -/
theorem abs_sum_mul_mul_le_of_abs_rect_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (D : ι → κ → ℝ) (a : ι → ℝ) (b : κ → ℝ)
    (ha₀ : ∀ i, 0 ≤ a i) (ha₁ : ∀ i, a i ≤ 1)
    (hb₀ : ∀ j, 0 ≤ b j) (hb₁ : ∀ j, b j ≤ 1)
    {B : ℝ}
    (hB : ∀ s : Finset ι, ∀ t : Finset κ,
      |∑ i ∈ s, ∑ j ∈ t, D i j| ≤ B) :
    |∑ i, ∑ j, a i * b j * D i j| ≤ B :=
  DenseGraph.abs_sum_mul_mul_le_of_abs_rect_sum_le
    D a b ha₀ ha₁ hb₀ hb₁ hB

/-- Compatibility name for the reusable equal-cell selection weight. -/
def cutCellWeight {q : ℕ} (S : Set UnitInterval) (i : Fin q) : ℝ :=
  DenseGraph.cutCellWeight S i

theorem cutCellWeight_nonneg {q : ℕ} (S : Set UnitInterval) (i : Fin q) :
    0 ≤ cutCellWeight S i := by
  simpa [cutCellWeight] using DenseGraph.cutCellWeight_nonneg S i

theorem cutCellWeight_le_one {q : ℕ} (hq : 0 < q)
    (S : Set UnitInterval) (i : Fin q) :
    cutCellWeight S i ≤ 1 := by
  simpa [cutCellWeight] using DenseGraph.cutCellWeight_le_one hq S i

/-- Compatibility wrapper for the exact reusable finite-cell cut formula. -/
theorem cutIntegral_matrixGraphon_sub_eq_sum {q : ℕ}
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1)
    (C : MeasurableCut) :
    cutIntegral
        ((matrixGraphon M hM hM₀ hM₁).toL1 -
          (matrixGraphon N hN hN₀ hN₁).toL1) C =
      ∑ i, ∑ j,
        (volume (C.left ∩ equalCell i)).toReal *
          (volume (C.right ∩ equalCell j)).toReal * (M i j - N i j) :=
  DenseGraph.cutIntegral_matrixGraphon_sub_eq_sum
    M N hM hN hM₀ hM₁ hN₀ hN₁ C

/-- Compatibility wrapper for the reusable finite rectangle-to-cut-norm
estimate. -/
theorem cutNorm_matrixGraphon_sub_le_of_rect_sum {q : ℕ} (hq : 0 < q)
    (M N : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm)
    (hM₀ : ∀ i j, 0 ≤ M i j) (hM₁ : ∀ i j, M i j ≤ 1)
    (hN₀ : ∀ i j, 0 ≤ N i j) (hN₁ : ∀ i j, N i j ≤ 1)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hrect : ∀ s t : Finset (Fin q),
      |∑ i ∈ s, ∑ j ∈ t, (M i j - N i j)| ≤ B * (q : ℝ) ^ 2) :
    cutNorm
        ((matrixGraphon M hM hM₀ hM₁).toL1 -
          (matrixGraphon N hN hN₀ hN₁).toL1) ≤ B :=
  DenseGraph.cutNorm_matrixGraphon_sub_le_of_rect_sum
    hq M N hM hN hM₀ hM₁ hN₀ hN₁ hB₀ hrect


section UniformRefinements

/-- The canonical `k × n` enumeration of `k*n` fine cells. -/
def typeFineCellEquiv (k n : ℕ) : Fin k × Fin n ≃ Fin (k * n) :=
  finProdFinEquiv

/-- The canonical `n × k` enumeration, transported to the same cardinal
`k*n` used by `typeFineCellEquiv`. -/
def graphFineCellEquiv (k n : ℕ) : Fin n × Fin k ≃ Fin (k * n) :=
  finProdFinEquiv |>.trans (finCongr (Nat.mul_comm n k))

/-- Fine-cell permutation induced by an alignment of graph vertex-copies
with type-cell copies.  Its direction is chosen so `permuteMatrix` turns a
type refinement into a matrix indexed in graph-copy order. -/
def alignedFineCellPerm {k n : ℕ}
    (e : Fin n × Fin k ≃ Fin k × Fin n) : Equiv.Perm (Fin (k * n)) :=
  (graphFineCellEquiv k n).symm |>.trans (e.trans (typeFineCellEquiv k n))

@[simp] theorem alignedFineCellPerm_graphFineCellEquiv {k n : ℕ}
    (e : Fin n × Fin k ≃ Fin k × Fin n) (p : Fin n × Fin k) :
    alignedFineCellPerm e (graphFineCellEquiv k n p) =
      typeFineCellEquiv k n (e p) := by
  simp [alignedFineCellPerm]

/-- Replicate a `k × k` matrix uniformly `n` times in each coordinate. -/
def typeUniformRefinementMatrix {k n : ℕ}
    (C : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin (k * n)) (Fin (k * n)) ℝ :=
  C.submatrix
    (fun x ↦ ((typeFineCellEquiv k n).symm x).1)
    (fun x ↦ ((typeFineCellEquiv k n).symm x).1)

/-- Replicate an `n × n` matrix uniformly `k` times in each coordinate,
using the common fine cardinal `k*n`. -/
def graphUniformRefinementMatrix {k n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (k * n)) (Fin (k * n)) ℝ :=
  M.submatrix
    (fun x ↦ ((graphFineCellEquiv k n).symm x).1)
    (fun x ↦ ((graphFineCellEquiv k n).symm x).1)

theorem typeUniformRefinementMatrix_isSymm {k n : ℕ}
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : C.IsSymm) :
    (typeUniformRefinementMatrix (n := n) C).IsSymm :=
  hC.submatrix _

theorem typeUniformRefinementMatrix_nonneg {k n : ℕ}
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : ∀ i j, 0 ≤ C i j) :
    ∀ x y, 0 ≤ typeUniformRefinementMatrix (n := n) C x y := by
  intro x y
  exact hC _ _

theorem typeUniformRefinementMatrix_le_one {k n : ℕ}
    {C : Matrix (Fin k) (Fin k) ℝ} (hC : ∀ i j, C i j ≤ 1) :
    ∀ x y, typeUniformRefinementMatrix (n := n) C x y ≤ 1 := by
  intro x y
  exact hC _ _

theorem graphUniformRefinementMatrix_isSymm {k n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsSymm) :
    (graphUniformRefinementMatrix (k := k) M).IsSymm :=
  hM.submatrix _

theorem graphUniformRefinementMatrix_nonneg {k n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, 0 ≤ M i j) :
    ∀ x y, 0 ≤ graphUniformRefinementMatrix (k := k) M x y := by
  intro x y
  exact hM _ _

theorem graphUniformRefinementMatrix_le_one {k n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : ∀ i j, M i j ≤ 1) :
    ∀ x y, graphUniformRefinementMatrix (k := k) M x y ≤ 1 := by
  intro x y
  exact hM _ _

@[simp] theorem permute_typeUniformRefinementMatrix_on_graphFineCells
    {k n : ℕ} (C : Matrix (Fin k) (Fin k) ℝ)
    (e : Fin n × Fin k ≃ Fin k × Fin n) (p q : Fin n × Fin k) :
    permuteMatrix (alignedFineCellPerm e)
        (typeUniformRefinementMatrix (n := n) C)
        (graphFineCellEquiv k n p) (graphFineCellEquiv k n q) =
      C (e p).1 (e q).1 := by
  simp [permuteMatrix, typeUniformRefinementMatrix]

@[simp] theorem graphUniformRefinementMatrix_on_graphFineCells
    {k n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (p q : Fin n × Fin k) :
    graphUniformRefinementMatrix (k := k) M
        (graphFineCellEquiv k n p) (graphFineCellEquiv k n q) =
      M p.1 q.1 := by
  simp [graphUniformRefinementMatrix]

theorem matrixGraphon_typeUniformRefinement_eq {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (C : Matrix (Fin k) (Fin k) ℝ)
    (hC : C.IsSymm) (hC₀ : ∀ i j, 0 ≤ C i j)
    (hC₁ : ∀ i j, C i j ≤ 1) :
    matrixGraphon (typeUniformRefinementMatrix (n := n) C)
        (typeUniformRefinementMatrix_isSymm (n := n) hC)
        (typeUniformRefinementMatrix_nonneg (n := n) hC₀)
        (typeUniformRefinementMatrix_le_one (n := n) hC₁) =
      matrixGraphon C hC hC₀ hC₁ := by
  apply matrixGraphon_uniformRefinement_eq (Nat.mul_pos hk hn)
    (dvd_mul_right k n)
  intro i j a b
  have hratio : k * n / k = n := by
    simpa [Nat.mul_comm] using Nat.mul_div_left n hk
  let a' : Fin n := finCongr hratio a
  let b' : Fin n := finCongr hratio b
  have ha : Graphon.refinementIndex (dvd_mul_right k n) i a =
      typeFineCellEquiv k n (i, a') := by
    apply Fin.ext
    simp [Graphon.refinementIndex, typeFineCellEquiv, finProdFinEquiv,
      a', hratio, Nat.add_comm, Nat.mul_comm]
  have hb : Graphon.refinementIndex (dvd_mul_right k n) j b =
      typeFineCellEquiv k n (j, b') := by
    apply Fin.ext
    simp [Graphon.refinementIndex, typeFineCellEquiv, finProdFinEquiv,
      b', hratio, Nat.add_comm, Nat.mul_comm]
  rw [ha, hb]
  simp [typeUniformRefinementMatrix]

theorem matrixGraphon_graphUniformRefinement_eq {k n : ℕ}
    (hk : 0 < k) (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hM₀ : ∀ i j, 0 ≤ M i j)
    (hM₁ : ∀ i j, M i j ≤ 1) :
    matrixGraphon (graphUniformRefinementMatrix (k := k) M)
        (graphUniformRefinementMatrix_isSymm (k := k) hM)
        (graphUniformRefinementMatrix_nonneg (k := k) hM₀)
        (graphUniformRefinementMatrix_le_one (k := k) hM₁) =
      matrixGraphon M hM hM₀ hM₁ := by
  apply matrixGraphon_uniformRefinement_eq (Nat.mul_pos hk hn)
    (dvd_mul_left n k)
  intro i j a b
  have hratio : k * n / n = k := by
    simpa [Nat.mul_comm] using Nat.mul_div_right k hn
  let a' : Fin k := finCongr hratio a
  let b' : Fin k := finCongr hratio b
  have ha : Graphon.refinementIndex (dvd_mul_left n k) i a =
      graphFineCellEquiv k n (i, a') := by
    apply Fin.ext
    simp [Graphon.refinementIndex, graphFineCellEquiv, finProdFinEquiv,
      a', finCongr, hratio, Nat.add_comm, Nat.mul_comm]
  have hb : Graphon.refinementIndex (dvd_mul_left n k) j b =
      graphFineCellEquiv k n (j, b') := by
    apply Fin.ext
    simp [Graphon.refinementIndex, graphFineCellEquiv, finProdFinEquiv,
      b', finCongr, hratio, Nat.add_comm, Nat.mul_comm]
  rw [ha, hb]
  simp [graphUniformRefinementMatrix]

end UniformRefinements

section AlignedPartition

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
  {epsilon delta : ℝ} {ℓ : ℕ}

/-- The uniformly refined type matrix after the finite partition alignment. -/
def alignedTypeFineMatrix (T : RegularityType G epsilon delta ℓ) :
    Matrix (Fin (T.partition.clusterCount * n))
      (Fin (T.partition.clusterCount * n)) ℝ :=
  permuteMatrix (alignedFineCellPerm T.partition.alignmentEquiv)
    (typeUniformRefinementMatrix (n := n) (typeDensityMatrix T))

/-- The adjacency matrix with `clusterCount` identical copies of each graph
vertex, on the same fine index type as `alignedTypeFineMatrix`. -/
def graphFineMatrix (T : RegularityType G epsilon delta ℓ) :
    Matrix (Fin (T.partition.clusterCount * n))
      (Fin (T.partition.clusterCount * n)) ℝ :=
  graphUniformRefinementMatrix (k := T.partition.clusterCount)
    (graphAdjacencyMatrix G)

theorem alignedTypeFineMatrix_isSymm
    (T : RegularityType G epsilon delta ℓ) :
    (alignedTypeFineMatrix G T).IsSymm :=
  permuteMatrix_isSymm _
    (typeUniformRefinementMatrix_isSymm (n := n) (typeDensityMatrix_isSymm T))

theorem alignedTypeFineMatrix_nonneg
    (T : RegularityType G epsilon delta ℓ) :
    ∀ x y, 0 ≤ alignedTypeFineMatrix G T x y :=
  permuteMatrix_nonneg _
    (typeUniformRefinementMatrix_nonneg (n := n) (typeDensityMatrix_nonneg T))

theorem alignedTypeFineMatrix_le_one
    (T : RegularityType G epsilon delta ℓ) :
    ∀ x y, alignedTypeFineMatrix G T x y ≤ 1 :=
  permuteMatrix_le_one _
    (typeUniformRefinementMatrix_le_one (n := n) (typeDensityMatrix_le_one T))

theorem graphFineMatrix_isSymm
    (T : RegularityType G epsilon delta ℓ) :
    (graphFineMatrix G T).IsSymm :=
  graphUniformRefinementMatrix_isSymm (k := T.partition.clusterCount)
    (graphAdjacencyMatrix_isSymm G)

theorem graphFineMatrix_nonneg
    (T : RegularityType G epsilon delta ℓ) :
    ∀ x y, 0 ≤ graphFineMatrix G T x y :=
  graphUniformRefinementMatrix_nonneg (k := T.partition.clusterCount)
    (graphAdjacencyMatrix_nonneg G)

theorem graphFineMatrix_le_one
    (T : RegularityType G epsilon delta ℓ) :
    ∀ x y, graphFineMatrix G T x y ≤ 1 :=
  graphUniformRefinementMatrix_le_one (k := T.partition.clusterCount)
    (graphAdjacencyMatrix_le_one G)

@[simp] theorem alignedTypeFineMatrix_on_graphFineCells
    (T : RegularityType G epsilon delta ℓ)
    (p q : Fin n × Fin T.partition.clusterCount) :
    alignedTypeFineMatrix G T
        (graphFineCellEquiv T.partition.clusterCount n p)
        (graphFineCellEquiv T.partition.clusterCount n q) =
      graphDensity G
        (T.partition.clusters (T.partition.alignmentLabel p))
        (T.partition.clusters (T.partition.alignmentLabel q)) := by
  rw [alignedTypeFineMatrix,
    permute_typeUniformRefinementMatrix_on_graphFineCells]
  rw [typeDensityMatrix, T.partition.alignmentEquiv_fst,
    T.partition.alignmentEquiv_fst]

@[simp] theorem graphFineMatrix_on_graphFineCells
    (T : RegularityType G epsilon delta ℓ)
    (p q : Fin n × Fin T.partition.clusterCount) :
    graphFineMatrix G T
        (graphFineCellEquiv T.partition.clusterCount n p)
        (graphFineCellEquiv T.partition.clusterCount n q) =
      if G.Adj p.1 q.1 then 1 else 0 := by
  rw [graphFineMatrix, graphUniformRefinementMatrix_on_graphFineCells,
    graphAdjacencyMatrix_apply]

/-- On the empty vertex type, both the finite adjacency graphon and every
type graphon are the zero kernel, even when the type has positive many empty
clusters. -/
theorem typeGraphon_fin_zero_eq_graphGraphon
    (G₀ : SimpleGraph (Fin 0)) [DecidableRel G₀.Adj]
    {epsilon₀ delta₀ : ℝ} {ℓ₀ : ℕ}
    (T₀ : RegularityType G₀ epsilon₀ delta₀ ℓ₀) :
    typeGraphon T₀ = graphGraphon G₀ := by
  rw [typeGraphon, graphGraphon]
  apply Graphon.ext
  filter_upwards [matrixGraphon_ae_eq_kernel (typeDensityMatrix T₀)
      (typeDensityMatrix_isSymm T₀) (typeDensityMatrix_nonneg T₀)
      (typeDensityMatrix_le_one T₀),
    matrixGraphon_ae_eq_kernel (graphAdjacencyMatrix G₀)
      (graphAdjacencyMatrix_isSymm G₀) (graphAdjacencyMatrix_nonneg G₀)
      (graphAdjacencyMatrix_le_one G₀)] with z hzT hzG
  rw [hzT, hzG]
  have hempty (A : Finset (Fin 0)) : A = ∅ := by
    ext v
    exact Fin.elim0 v
  simp only [matrixKernel]
  simp_rw [typeDensityMatrix, hempty, graphDensity_eq]
  simp

/-- A regularity type on a nonempty finite graph necessarily has at least one
nonexceptional cluster. -/
theorem RegularityType.clusterCount_pos_of_fin_pos
    (T : RegularityType G epsilon delta ℓ) (hn : 0 < n) :
    0 < T.partition.clusterCount := by
  by_contra hk
  have hk₀ : T.partition.clusterCount = 0 := Nat.eq_zero_of_not_pos hk
  have hcard := T.partition.exceptional_card_add_mul_clusterSize_eq
  rw [hk₀] at hcard
  simp only [zero_mul, Nat.add_zero] at hcard
  have hexception := T.partition.exceptional_card_le
  rw [hcard] at hexception
  simp only [Fintype.card_fin] at hexception
  have hnℝ : (0 : ℝ) < n := by exact_mod_cast hn
  have hepsilon : 1 ≤ epsilon := by
    nlinarith
  linarith [T.epsilon_lt_half]

/-- Analytic assembly lemma: a rectangle estimate on copied graph vertices
implies the same cut-distance estimate for the type and graph graphons. -/
theorem cutDist_typeGraphon_graphGraphon_le_of_host_rect_sum
    (T : RegularityType G epsilon delta ℓ)
    (hk : 0 < T.partition.clusterCount) (hn : 0 < n)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hrect : ∀ S U : Finset (Fin n × Fin T.partition.clusterCount),
      |∑ p ∈ S, ∑ q ∈ U,
        ((if G.Adj p.1 q.1 then (1 : ℝ) else 0) -
          graphDensity G
            (T.partition.clusters (T.partition.alignmentLabel p))
            (T.partition.clusters (T.partition.alignmentLabel q)))| ≤
        B * (T.partition.clusterCount * n : ℕ) ^ 2) :
    cutDist (typeGraphon T) (graphGraphon G) ≤ B := by
  classical
  let k := T.partition.clusterCount
  let qn := k * n
  let eG := graphFineCellEquiv k n
  let U := alignedTypeFineMatrix G T
  let W := graphFineMatrix G T
  have hfinite : ∀ s t : Finset (Fin qn),
      |∑ x ∈ s, ∑ y ∈ t, (U x y - W x y)| ≤ B * (qn : ℝ) ^ 2 := by
    intro s t
    let S : Finset (Fin n × Fin k) := s.map eG.symm.toEmbedding
    let R : Finset (Fin n × Fin k) := t.map eG.symm.toEmbedding
    have hsum :
        (∑ x ∈ s, ∑ y ∈ t, (U x y - W x y)) =
          ∑ p ∈ S, ∑ r ∈ R,
            (graphDensity G
                (T.partition.clusters (T.partition.alignmentLabel p))
                (T.partition.clusters (T.partition.alignmentLabel r)) -
              (if G.Adj p.1 r.1 then (1 : ℝ) else 0)) := by
      apply Finset.sum_equiv eG.symm
      · intro x
        simp [S]
      · intro x hx
        apply Finset.sum_equiv eG.symm
        · intro y
          simp [R]
        · intro y hy
          rw [show x = eG (eG.symm x) by simp,
            show y = eG (eG.symm y) by simp]
          change alignedTypeFineMatrix G T (eG (eG.symm x))
              (eG (eG.symm y)) -
            graphFineMatrix G T (eG (eG.symm x)) (eG (eG.symm y)) = _
          rw [alignedTypeFineMatrix_on_graphFineCells,
            graphFineMatrix_on_graphFineCells]
          simp
    rw [hsum]
    have hneg :
        (∑ p ∈ S, ∑ r ∈ R,
          (graphDensity G
              (T.partition.clusters (T.partition.alignmentLabel p))
              (T.partition.clusters (T.partition.alignmentLabel r)) -
            (if G.Adj p.1 r.1 then (1 : ℝ) else 0))) =
          -(∑ p ∈ S, ∑ r ∈ R,
            ((if G.Adj p.1 r.1 then (1 : ℝ) else 0) -
              graphDensity G
                (T.partition.clusters (T.partition.alignmentLabel p))
                (T.partition.clusters (T.partition.alignmentLabel r)))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hneg, abs_neg]
    simpa [k, qn] using hrect S R
  let U₀ := typeUniformRefinementMatrix (n := n) (typeDensityMatrix T)
  let hU₀symm := typeUniformRefinementMatrix_isSymm (n := n)
    (typeDensityMatrix_isSymm T)
  let hU₀nonneg := typeUniformRefinementMatrix_nonneg (n := n)
    (typeDensityMatrix_nonneg T)
  let hU₀le := typeUniformRefinementMatrix_le_one (n := n)
    (typeDensityMatrix_le_one T)
  let p := alignedFineCellPerm T.partition.alignmentEquiv
  let Ugraph := matrixGraphon U (alignedTypeFineMatrix_isSymm G T)
    (alignedTypeFineMatrix_nonneg G T) (alignedTypeFineMatrix_le_one G T)
  let Wgraph := matrixGraphon W (graphFineMatrix_isSymm G T)
    (graphFineMatrix_nonneg G T) (graphFineMatrix_le_one G T)
  have hcut : cutNorm (Ugraph.toL1 - Wgraph.toL1) ≤ B := by
    apply cutNorm_matrixGraphon_sub_le_of_rect_sum (Nat.mul_pos hk hn)
      U W (alignedTypeFineMatrix_isSymm G T) (graphFineMatrix_isSymm G T)
      (alignedTypeFineMatrix_nonneg G T) (alignedTypeFineMatrix_le_one G T)
      (graphFineMatrix_nonneg G T) (graphFineMatrix_le_one G T) hB₀
    simpa [qn, U, W] using hfinite
  have htype : matrixGraphon U₀ hU₀symm hU₀nonneg hU₀le = typeGraphon T := by
    simpa [U₀, hU₀symm, hU₀nonneg, hU₀le, typeGraphon] using
      matrixGraphon_typeUniformRefinement_eq hk hn (typeDensityMatrix T)
        (typeDensityMatrix_isSymm T) (typeDensityMatrix_nonneg T)
        (typeDensityMatrix_le_one T)
  have hgraph : Wgraph = graphGraphon G := by
    simpa [Wgraph, W, graphFineMatrix, graphGraphon] using
      matrixGraphon_graphUniformRefinement_eq hk hn (graphAdjacencyMatrix G)
        (graphAdjacencyMatrix_isSymm G) (graphAdjacencyMatrix_nonneg G)
        (graphAdjacencyMatrix_le_one G)
  have halign : Ugraph =
      (matrixGraphon U₀ hU₀symm hU₀nonneg hU₀le).relabel
        (cellPermRelabeling p) := by
    simpa [Ugraph, U, alignedTypeFineMatrix, U₀, p, hU₀symm,
      hU₀nonneg, hU₀le] using
      matrixGraphon_permuteMatrix_eq_relabel p U₀ hU₀symm hU₀nonneg hU₀le
  calc
    cutDist (typeGraphon T) (graphGraphon G) =
        cutDist (matrixGraphon U₀ hU₀symm hU₀nonneg hU₀le) Wgraph := by
          rw [htype, hgraph]
    _ = cutDist Ugraph Wgraph := by
      rw [halign, cutDist_relabel_left]
    _ ≤ cutNorm (Ugraph.toL1 - Wgraph.toL1) := cutDist_le_cutNorm _ _
    _ ≤ B := hcut

/-- A graphon built from an `epsilon`-regular partition is close in cut
distance to the adjacency graphon of its host graph.  The three finite error
sources are regular/irregular cluster pairs, diagonal cluster blocks, and the
exceptional class; the explicit coarse bound tends to zero when
`epsilon → 0` and the cluster count tends to infinity.

The diagonal term `1 / T.partition.clusterCount` is retained in the
finite estimate, as in the proof of `lemma:UFHatGraphonSeq`. -/
theorem cutDist_typeGraphon_graphGraphon_le
    (T : RegularityType G epsilon delta ℓ) :
    cutDist (typeGraphon T) (graphGraphon G) ≤
      5 * epsilon + 1 / (T.partition.clusterCount : ℝ) := by
  classical
  by_cases hn₀ : n = 0
  · subst n
    rw [typeGraphon_fin_zero_eq_graphGraphon G T]
    have hbound :
        0 ≤ 5 * epsilon + 1 / (T.partition.clusterCount : ℝ) := by
      have hinv : 0 ≤ 1 / (T.partition.clusterCount : ℝ) := by
        positivity
      nlinarith [T.epsilon_pos]
    simpa using hbound
  · have hn : 0 < n := Nat.pos_of_ne_zero hn₀
    have hk : 0 < T.partition.clusterCount :=
      RegularityType.clusterCount_pos_of_fin_pos G T hn
    have hkℝ : (0 : ℝ) < T.partition.clusterCount := by
      exact_mod_cast hk
    apply cutDist_typeGraphon_graphGraphon_le_of_host_rect_sum
      G T hk hn
    · have hinv : 0 < 1 / (T.partition.clusterCount : ℝ) := by
        positivity
      nlinarith [T.epsilon_pos]
    · intro S U
      exact T.partition.abs_centered_copy_sum_le G hk T.epsilon_pos.le
        T.partition.alignmentLabel
        (fun v hv b ↦ T.partition.alignmentLabel_of_mem_exceptional hv b)
        (fun i v hv b ↦ T.partition.alignmentLabel_of_mem_cluster i hv b)
        S U

end AlignedPartition

end InducedStars
