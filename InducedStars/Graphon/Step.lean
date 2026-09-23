import InducedStars.Graphon.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Equal-cell step graphons

This file constructs the graphon associated with a finite symmetric matrix and,
as a special case, the adjacency graphon of a finite simple graph.  We use the
half-open equal cells `[i/q,(i+1)/q)`; the point `1` is omitted from their union,
which changes no almost-everywhere statement.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal unitInterval

namespace InducedStars

/-- The left endpoint `i/q` of the `i`-th equal cell. -/
def equalCellLeft {q : ℕ} (i : Fin q) : UnitInterval :=
  ⟨(i : ℝ) / q, by positivity, by
    apply (div_le_one (by exact_mod_cast Nat.zero_lt_of_lt i.isLt)).2
    exact_mod_cast i.isLt.le⟩

/-- The right endpoint `(i+1)/q` of the `i`-th equal cell. -/
def equalCellRight {q : ℕ} (i : Fin q) : UnitInterval :=
  ⟨((i : ℕ) + 1 : ℝ) / q, by positivity, by
    apply (div_le_one (by exact_mod_cast Nat.zero_lt_of_lt i.isLt)).2
    exact_mod_cast i.isLt⟩

/-- The half-open equal cell `[i/q,(i+1)/q)` in the unit interval. -/
def equalCell {q : ℕ} (i : Fin q) : Set UnitInterval :=
  Ico (equalCellLeft i) (equalCellRight i)

@[measurability] theorem measurableSet_equalCell {q : ℕ} (i : Fin q) :
    MeasurableSet (equalCell i) :=
  measurableSet_Ico

/-- Each equal cell has normalized volume `1/q`. -/
theorem volume_equalCell {q : ℕ} (i : Fin q) :
    volume (equalCell i) = ENNReal.ofReal (1 / (q : ℝ)) := by
  rw [equalCell, unitInterval.volume_Ico]
  congr 1
  simp only [equalCellLeft, equalCellRight]
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt).ne'
  field_simp
  ring

/-- Equal cells with a common denominator are pairwise disjoint. -/
theorem equalCell_eq_of_mem {q : ℕ} {i j : Fin q} {x : UnitInterval}
    (hi : x ∈ equalCell i) (hj : x ∈ equalCell j) : i = j := by
  change (i : ℝ) / q ≤ (x : ℝ) ∧ (x : ℝ) < ((i : ℕ) + 1 : ℝ) / q at hi
  change (j : ℝ) / q ≤ (x : ℝ) ∧ (x : ℝ) < ((j : ℕ) + 1 : ℝ) / q at hj
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hs : ((i : ℕ) + 1 : ℝ) ≤ (j : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hd : (((i : ℕ) + 1 : ℝ) / q) ≤ (j : ℝ) / q :=
      div_le_div_of_nonneg_right hs hq
    exact (not_lt_of_ge hj.1) (hi.2.trans_le hd)
  · have hs : ((j : ℕ) + 1 : ℝ) ≤ (i : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hji)
    have hq : 0 ≤ (q : ℝ) := by positivity
    have hd : (((j : ℕ) + 1 : ℝ) / q) ≤ (i : ℝ) / q :=
      div_le_div_of_nonneg_right hs hq
    exact (not_lt_of_ge hi.1) (hj.2.trans_le hd)

/-- A product of two equal cells has volume `1/q²`. -/
theorem volume_equalCell_prod {q : ℕ} (i j : Fin q) :
    volume (equalCell i ×ˢ equalCell j) = ENNReal.ofReal (1 / (q : ℝ)) ^ 2 := by
  change ((volume : Measure UnitInterval).prod (volume : Measure UnitInterval))
      (equalCell i ×ˢ equalCell j) = _
  rw [Measure.prod_prod, volume_equalCell, volume_equalCell]
  ring

/-- The raw equal-cell step function associated with a square matrix. -/
def matrixKernel {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (z : UnitSquare) : ℝ :=
  ∑ i : Fin q, ∑ j : Fin q,
    (equalCell i ×ˢ equalCell j).indicator (fun _ ↦ M i j) z

@[fun_prop] theorem measurable_matrixKernel {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) :
    Measurable (matrixKernel M) := by
  unfold matrixKernel
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  refine Finset.measurable_sum Finset.univ ?_
  intro j hj
  exact measurable_const.indicator ((measurableSet_equalCell i).prod (measurableSet_equalCell j))

/-- On a specified cell rectangle, the raw step function has the matrix entry value. -/
theorem matrixKernel_of_mem {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (i j : Fin q) (z : UnitSquare) (hzi : z.1 ∈ equalCell i) (hzj : z.2 ∈ equalCell j) :
    matrixKernel M z = M i j := by
  classical
  have hxi (a : Fin q) : z.1 ∈ equalCell a ↔ a = i := by
    constructor
    · intro ha
      exact equalCell_eq_of_mem ha hzi
    · rintro rfl
      exact hzi
  have hyj (b : Fin q) : z.2 ∈ equalCell b ↔ b = j := by
    constructor
    · intro hb
      exact equalCell_eq_of_mem hb hzj
    · rintro rfl
      exact hzj
  unfold matrixKernel
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [hzi, hzj]
    · intro b hb hbj
      have hbnot : z ∉ equalCell i ×ˢ equalCell b := by
        intro h
        exact hbj ((hyj b).mp h.2)
      exact Set.indicator_of_notMem hbnot _
    · simp
  · intro a ha hai
    have hanot (b : Fin q) : z ∉ equalCell a ×ˢ equalCell b := by
      intro h
      exact hai ((hxi a).mp h.1)
    exact Finset.sum_eq_zero fun b hb ↦ Set.indicator_of_notMem (hanot b) _
  · simp

/-- The raw matrix step function is pointwise symmetric for a symmetric matrix. -/
theorem matrixKernel_symm {q : ℕ} {M : Matrix (Fin q) (Fin q) ℝ} (hM : M.IsSymm)
    (z : UnitSquare) : matrixKernel M (z.2, z.1) = matrixKernel M z := by
  classical
  simp only [matrixKernel, Set.indicator_apply, Set.mem_prod]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hM.apply]
  simp only [and_comm]

/-- If the entries lie in `[0,1]`, so does the raw step function. -/
theorem matrixKernel_mem_Icc {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) (z : UnitSquare) :
    matrixKernel M z ∈ Icc (0 : ℝ) 1 := by
  classical
  by_cases hx : ∃ i : Fin q, z.1 ∈ equalCell i
  · obtain ⟨i, hi⟩ := hx
    by_cases hy : ∃ j : Fin q, z.2 ∈ equalCell j
    · obtain ⟨j, hj⟩ := hy
      rw [matrixKernel_of_mem M i j z hi hj]
      exact ⟨h₀ i j, h₁ i j⟩
    · push Not at hy
      have hz : matrixKernel M z = 0 := by
        simp [matrixKernel, hy]
      rw [hz]
      exact ⟨le_rfl, zero_le_one⟩
  · push Not at hx
    have hz : matrixKernel M z = 0 := by
      simp [matrixKernel, hx]
    rw [hz]
    exact ⟨le_rfl, zero_le_one⟩

/-- The raw matrix step function is integrable. -/
theorem integrable_matrixKernel {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) :
    Integrable (matrixKernel M) unitSquareMeasure := by
  apply Integrable.of_bound (measurable_matrixKernel M).aestronglyMeasurable 1
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (matrixKernel_mem_Icc M h₀ h₁ z).1]
  exact (matrixKernel_mem_Icc M h₀ h₁ z).2

/-- The graphon associated with a symmetric `[0,1]`-valued finite matrix. -/
def matrixGraphon {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ) (hM : M.IsSymm)
    (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) : Graphon :=
  Graphon.ofFun (matrixKernel M) (integrable_matrixKernel M h₀ h₁)
    (ae_of_all _ fun z ↦ (matrixKernel_mem_Icc M h₀ h₁ z).1)
    (ae_of_all _ fun z ↦ (matrixKernel_mem_Icc M h₀ h₁ z).2)
    (matrixKernel_symm hM)

/-- A matrix graphon is represented a.e. by its raw step function. -/
theorem matrixGraphon_ae_eq_kernel {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1) :
    ∀ᵐ z ∂unitSquareMeasure, matrixGraphon M hM h₀ h₁ z = matrixKernel M z :=
  Graphon.coe_ofFun _ _ _ _ _

/-- The matrix graphon has value `M i j` a.e. on the `(i,j)` cell. -/
theorem matrixGraphon_ae_eq_on_cell {q : ℕ} (M : Matrix (Fin q) (Fin q) ℝ)
    (hM : M.IsSymm) (h₀ : ∀ i j, 0 ≤ M i j) (h₁ : ∀ i j, M i j ≤ 1)
    (i j : Fin q) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      matrixGraphon M hM h₀ h₁ z = M i j := by
  filter_upwards [matrixGraphon_ae_eq_kernel M hM h₀ h₁] with z hz hzij
  rw [hz, matrixKernel_of_mem M i j z hzij.1 hzij.2]

/-- The canonical real adjacency matrix, independent of a chosen decidability
instance for adjacency. -/
noncomputable def graphAdjacencyMatrix {n : ℕ}
    (G : SimpleGraph (Fin n)) : Matrix (Fin n) (Fin n) ℝ := by
  classical
  exact fun i j ↦ if G.Adj i j then 1 else 0

theorem graphAdjacencyMatrix_apply {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i j : Fin n) :
    graphAdjacencyMatrix G i j = if G.Adj i j then 1 else 0 := by
  classical
  simp [graphAdjacencyMatrix]

theorem graphAdjacencyMatrix_isSymm {n : ℕ} (G : SimpleGraph (Fin n)) :
    (graphAdjacencyMatrix G).IsSymm := by
  classical
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp only [graphAdjacencyMatrix]
  rw [G.adj_comm]

theorem graphAdjacencyMatrix_nonneg {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : 0 ≤ graphAdjacencyMatrix G i j := by
  classical
  simp only [graphAdjacencyMatrix]
  split <;> norm_num

theorem graphAdjacencyMatrix_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : graphAdjacencyMatrix G i j ≤ 1 := by
  classical
  simp only [graphAdjacencyMatrix]
  split <;> norm_num

/-- The finite adjacency graphon of `G`. -/
noncomputable def graphGraphon {n : ℕ} (G : SimpleGraph (Fin n)) : Graphon :=
  matrixGraphon (graphAdjacencyMatrix G) (graphAdjacencyMatrix_isSymm G)
    (graphAdjacencyMatrix_nonneg G) (graphAdjacencyMatrix_le_one G)

/-- Cell characterization of the finite adjacency graphon. -/
theorem graphGraphon_ae_eq_on_cell {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i j : Fin n) :
    ∀ᵐ z ∂unitSquareMeasure, z ∈ equalCell i ×ˢ equalCell j →
      graphGraphon G z = if G.Adj i j then 1 else 0 := by
  simpa only [graphGraphon, graphAdjacencyMatrix_apply] using
    matrixGraphon_ae_eq_on_cell (graphAdjacencyMatrix G)
      (graphAdjacencyMatrix_isSymm G) (graphAdjacencyMatrix_nonneg G)
      (graphAdjacencyMatrix_le_one G) i j

/-- The diagonal blocks of a finite simple-graph graphon have value zero a.e. -/
theorem graphGraphon_ae_eq_zero_on_diagonal_cell {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (i : Fin n) :
    ∀ᵐ z ∂unitSquareMeasure,
      z ∈ equalCell i ×ˢ equalCell i → graphGraphon G z = 0 := by
  filter_upwards [graphGraphon_ae_eq_on_cell G i i] with z hz hzi
  simpa using hz hzi

end InducedStars
