import InducedStars.Graphon.CleanTypeRow
import InducedStars.Graphon.TypeSequenceLimits
import Mathlib.Tactic

/-!
# Diagonal selection from clean Type-tower levels

For each level, choose one sufficiently late row index.  The chosen index is
simultaneously late enough for all entries of the fixed finite clean matrix
and large enough that the fixed cluster count is negligible compared with
the selected host size.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

/-- Quantitative diagonal choices from a family of completed clean Type
levels. -/
structure TypeTowerDiagonalSelection
    {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
    (eta : ℕ → ℝ) (delta : ℝ)
    (level : (m : ℕ) → CleanTypeSequenceLevel (f := f) G (eta m) delta) where
  /-- Row chosen at each tower level. -/
  rowIndex : ℕ → ℕ
  /-- The diagonal never selects before its own level number. -/
  stage_le : ∀ m, m ≤ rowIndex m
  /-- Every clean-density entry is uniformly close to its fixed-level limit. -/
  cleanMatrix_limitMatrix_close : ∀ m i j,
    |(level m).cleanMatrix (rowIndex m) i j - (level m).limitMatrix i j| ≤
      1 / (((m + 1 : ℕ) : ℝ))
  /-- The cluster-count/host-size ratio obeys the same diagonal schedule. -/
  clusterCount_div_hostSize_le : ∀ m,
    ((level m).clusterCount : ℝ) /
        ((level m).hostSize (rowIndex m) : ℝ) ≤
      1 / (((m + 1 : ℕ) : ℝ))

namespace TypeTowerDiagonalSelection

variable {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {eta : ℕ → ℝ} {delta : ℝ}
  {level : (m : ℕ) → CleanTypeSequenceLevel (f := f) G (eta m) delta}

/-- Every family of completed clean levels admits a quantitative diagonal
selection. -/
theorem nonempty : Nonempty (TypeTowerDiagonalSelection eta delta level) := by
  classical
  have hepsilon (m : ℕ) : 0 < 1 / (((m + 1 : ℕ) : ℝ)) := by
    positivity
  choose matrixThreshold hmatrixThreshold using fun m ↦
    Graphon.exists_threshold_matrix_entrywise_abs_sub_lt
      (level m).cleanMatrix (level m).limitMatrix
      (level m).cleanMatrix_tendsto (hepsilon m)
  let index : ℕ → ℕ := fun m ↦
    max m (max (matrixThreshold m) ((level m).clusterCount * (m + 1)))
  refine ⟨{
    rowIndex := index
    stage_le := ?_
    cleanMatrix_limitMatrix_close := ?_
    clusterCount_div_hostSize_le := ?_ }⟩
  · intro m
    exact le_max_left _ _
  · intro m i j
    apply (hmatrixThreshold m (index m) ?_ i j).le
    exact (le_max_left _ _).trans (le_max_right _ _)
  · intro m
    apply Graphon.natCast_div_natCast_le_one_div_natCast_of_mul_le
      ((level m).hostSize_pos (index m)) (Nat.succ_pos m)
    have hindex : (level m).clusterCount * (m + 1) ≤ index m :=
      (le_max_right _ _).trans (le_max_right _ _)
    have hextraction :
        index m ≤ (level m).row.extraction (index m) :=
      (level m).row.extraction_strictMono.id_le (index m)
    change (level m).clusterCount * (m + 1) ≤
      (level m).row.extraction (index m) + 1
    exact hindex.trans (hextraction.trans (Nat.le_succ _))

variable (D : TypeTowerDiagonalSelection eta delta level)

/-- The original sampling-graph index selected on the tower diagonal. -/
def originalIndex (m : ℕ) : ℕ :=
  (level m).row.extraction (D.rowIndex m)

/-- The selected original graph indices tend to infinity. -/
theorem originalIndex_tendsto_atTop : Tendsto D.originalIndex atTop atTop := by
  exact EquitablePartitionRow.tendsto_selected_extraction
    (fun m ↦ (level m).row) D.rowIndex D.stage_le

@[simp] theorem originalIndex_add_one (m : ℕ) :
    D.originalIndex m + 1 = (level m).hostSize (D.rowIndex m) :=
  rfl

end TypeTowerDiagonalSelection

end InducedStars
