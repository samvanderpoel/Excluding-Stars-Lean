import InducedStars.Graphon.CleanTypeRow
import InducedStars.Graphon.TypeTower
import Mathlib.Tactic

/-!
# Infinite clean Type towers

This module is the assumption-free assembly layer between the concrete
one-row extension construction and the Lovasz--Szegedy nested-matrix input.
It retains the actual clean Type levels while projecting their limiting
matrices and extraction rows to the small interfaces in `Graphon.TypeTower`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace InducedStars

/-- An infinite tower of clean Type-sequence levels.  Successive extraction
rows are nested, cluster counts at least double, and the limiting clean
matrices satisfy the exact consecutive block-average identity obtained after
passing the finite refinement estimates to the limit. -/
structure CleanTypeTowerSystem
    {f : ℕ} (G : (n : ℕ) → SimpleGraph (Fin (n + 1)))
    (eta : ℕ → ℝ) (delta : ℝ) where
  level : (m : ℕ) → CleanTypeSequenceLevel (f := f) G (eta m) delta
  factor : ℕ → ℕ → ℕ
  factor_strictMono : ∀ m, StrictMono (factor m)
  extraction_succ : ∀ m,
    (level (m + 1)).row.extraction =
      (level m).row.extraction ∘ factor m
  clusterCount_dvd_succ : ∀ m,
    (level m).clusterCount ∣ (level (m + 1)).clusterCount
  clusterCount_growth : ∀ m,
    2 * (level m).clusterCount ≤ (level (m + 1)).clusterCount
  limit_blockAverage_succ : ∀ m
      (i j : Fin (level m).clusterCount),
    (level m).limitMatrix i j =
      Graphon.matrixBlockAverage (clusterCount_dvd_succ m)
        (level (m + 1)).limitMatrix i j

namespace CleanTypeTowerSystem

variable {f : ℕ} {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {eta : ℕ → ℝ} {delta : ℝ}

variable (S : CleanTypeTowerSystem (f := f) G eta delta)

/-- The cluster-count sequence of the tower. -/
def clusterCount (m : ℕ) : ℕ :=
  (S.level m).clusterCount

theorem clusterCount_pos (m : ℕ) : 0 < S.clusterCount m :=
  (S.level m).clusterCount_pos

theorem clusterCount_zero_ge : 1 ≤ S.clusterCount 0 :=
  S.clusterCount_pos 0

theorem clusterCount_two_mul_le_succ (m : ℕ) :
    2 * S.clusterCount m ≤ S.clusterCount (m + 1) :=
  S.clusterCount_growth m

/-- The matrix-and-extraction projection of one concrete clean Type level. -/
def matrixLevel (m : ℕ) : Graphon.MatrixSubsequenceLevel where
  size := (S.level m).clusterCount
  size_pos := (S.level m).clusterCount_pos
  extraction := (S.level m).row.extraction
  extraction_strictMono := (S.level m).row.extraction_strictMono
  matrix := (S.level m).limitMatrix
  matrix_symmetric := (S.level m).limitMatrix_symmetric
  matrix_mem_Icc := (S.level m).limitMatrix_mem_Icc

/-- Projection of the concrete clean Type tower to its exact limiting-matrix
and subsequence tower. -/
def matrixTower : Graphon.MatrixSubsequenceTower where
  level := S.matrixLevel
  factor := S.factor
  factor_strictMono := S.factor_strictMono
  extraction_succ := S.extraction_succ
  size_dvd_succ := S.clusterCount_dvd_succ
  blockAverage_succ := S.limit_blockAverage_succ

/-- The nested extraction rows of the clean Type tower. -/
def subsequenceTower : Graphon.SubsequenceTower :=
  S.matrixTower.toSubsequenceTower

/-- The standard diagonal through the nested extraction rows. -/
def diagonal (m : ℕ) : ℕ :=
  S.subsequenceTower.diagonal m

theorem diagonal_strictMono : StrictMono S.diagonal :=
  S.subsequenceTower.diagonal_strictMono

/-- Successive limiting matrices, before deriving all-level compatibility. -/
def successiveDensityMatrices : Graphon.SuccessiveDensityMatrices :=
  S.matrixTower.toSuccessiveDensityMatrices

/-- The exact all-level nested density matrices supplied to the published
Lovasz--Szegedy limit interface. -/
def nestedDensityMatrices : Graphon.NestedDensityMatrices :=
  S.matrixTower.toNestedDensityMatrices

@[simp] theorem nestedDensityMatrices_size (m : ℕ) :
    S.nestedDensityMatrices.size m = S.clusterCount m :=
  rfl

@[simp] theorem nestedDensityMatrices_matrix (m : ℕ) :
    S.nestedDensityMatrices.matrix m = (S.level m).limitMatrix :=
  rfl

/-- The equal-cell graphon of the limiting matrix at one tower level. -/
def matrixLimitGraphon (m : ℕ) : Graphon :=
  matrixGraphon (S.level m).limitMatrix
    (S.level m).limitMatrix_symmetric
    (fun i j ↦ ((S.level m).limitMatrix_mem_Icc i j).1)
    (fun i j ↦ ((S.level m).limitMatrix_mem_Icc i j).2)

theorem clusterCount_tendsto_atTop :
    Tendsto S.clusterCount atTop atTop :=
  Graphon.tendsto_atTop_of_two_mul_le_succ S.clusterCount
    S.clusterCount_zero_ge S.clusterCount_two_mul_le_succ

theorem one_div_clusterCount_tendsto_zero :
    Tendsto (fun m ↦ 1 / (S.clusterCount m : ℝ)) atTop (nhds 0) :=
  Graphon.tendsto_one_div_natCast_of_two_mul_le_succ S.clusterCount
    S.clusterCount_zero_ge S.clusterCount_two_mul_le_succ

end CleanTypeTowerSystem

end InducedStars

