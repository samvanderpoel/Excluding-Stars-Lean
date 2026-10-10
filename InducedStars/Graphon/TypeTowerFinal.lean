import InducedStars.Graphon.TypeSequenceAssembly
import InducedStars.Graphon.TypeSequenceLimits
import InducedStars.Graphon.TypeTowerSelection
import InducedStars.Graphon.TypeTowerSystem
import Mathlib.Tactic

/-!
# Final diagonal assembly from a clean Type tower

The construction in this file is independent of the existence proof for the
tower.  Given an infinite exact tower, a quantitative diagonal selection,
the inherited sampling cut limit, and the common limiting-matrix graphon, it
packages the actual hosts and Types into `TypeSequenceAssemblyData`.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace InducedStars

open Regularity

namespace CleanTypeTowerSystem

variable {f : ℕ} {F : SimpleGraph (Fin f)}
  {G : (n : ℕ) → SimpleGraph (Fin (n + 1))}
  {eta : ℕ → ℝ} {delta : ℝ} {W : Graphon}

variable (S : CleanTypeTowerSystem (f := f) G eta delta)
  (D : TypeTowerDiagonalSelection eta delta S.level)

/-- The clean density matrix selected at each varying tower level. -/
def selectedCleanMatrix (m : ℕ) :
    Matrix (Fin (S.clusterCount m)) (Fin (S.clusterCount m)) ℝ :=
  (S.level m).cleanMatrix (D.rowIndex m)

/-- The limiting density matrix at each tower level. -/
def selectedLimitMatrix (m : ℕ) :
    Matrix (Fin (S.clusterCount m)) (Fin (S.clusterCount m)) ℝ :=
  (S.level m).limitMatrix

theorem selectedCleanMatrix_symmetric (m : ℕ) :
    (S.selectedCleanMatrix D m).IsSymm := by
  letI : DecidableRel
      (G ((S.level m).row.extraction (D.rowIndex m))).Adj :=
    (S.level m).hostAdjDecidable (D.rowIndex m)
  rw [selectedCleanMatrix, (S.level m).cleanMatrix_eq]
  exact cleanDensityMatrix_isSymm _ _

theorem selectedCleanMatrix_nonneg (m : ℕ)
    (i j : Fin (S.clusterCount m)) :
    0 ≤ S.selectedCleanMatrix D m i j := by
  letI : DecidableRel
      (G ((S.level m).row.extraction (D.rowIndex m))).Adj :=
    (S.level m).hostAdjDecidable (D.rowIndex m)
  rw [selectedCleanMatrix, (S.level m).cleanMatrix_eq]
  exact cleanDensityMatrix_nonneg _ _ _ _

theorem selectedCleanMatrix_le_one (m : ℕ)
    (i j : Fin (S.clusterCount m)) :
    S.selectedCleanMatrix D m i j ≤ 1 := by
  letI : DecidableRel
      (G ((S.level m).row.extraction (D.rowIndex m))).Adj :=
    (S.level m).hostAdjDecidable (D.rowIndex m)
  rw [selectedCleanMatrix, (S.level m).cleanMatrix_eq]
  exact cleanDensityMatrix_le_one _ _ _ _

theorem selectedLimitMatrix_symmetric (m : ℕ) :
    (S.selectedLimitMatrix m).IsSymm :=
  (S.level m).limitMatrix_symmetric

theorem selectedLimitMatrix_nonneg (m : ℕ)
    (i j : Fin (S.clusterCount m)) :
    0 ≤ S.selectedLimitMatrix m i j :=
  ((S.level m).limitMatrix_mem_Icc i j).1

theorem selectedLimitMatrix_le_one (m : ℕ)
    (i j : Fin (S.clusterCount m)) :
    S.selectedLimitMatrix m i j ≤ 1 :=
  ((S.level m).limitMatrix_mem_Icc i j).2

/-- The selected clean graphons approach their fixed-level limiting matrix
graphons in `L¹`. -/
theorem selected_clean_to_matrix_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist
        ((S.level m).cleanGraphon (D.rowIndex m))
        (S.matrixLimitGraphon m))
      atTop (nhds 0) := by
  have hmatrix :=
    Graphon.matrixGraphon_tendsto_graphonL1Dist_of_entrywise_one_div_add
      (S.selectedCleanMatrix D) S.selectedLimitMatrix
      (S.selectedCleanMatrix_symmetric D) S.selectedLimitMatrix_symmetric
      (S.selectedCleanMatrix_nonneg D) (S.selectedCleanMatrix_le_one D)
      S.selectedLimitMatrix_nonneg S.selectedLimitMatrix_le_one
      D.cleanMatrix_limitMatrix_close
  apply hmatrix.congr'
  filter_upwards [] with m
  simp [selectedCleanMatrix, selectedLimitMatrix, matrixLimitGraphon,
    (S.level m).cleanGraphon_eq, (S.level m).cleanMatrix_eq,
    cleanPartitionGraphon]
  congr

/-- The explicit Type-to-clean diagonal error vanishes. -/
theorem selected_type_to_clean_l1_tendsto
    (heta : Tendsto eta atTop (nhds 0)) :
    Tendsto
      (fun m ↦ graphonL1Dist
        ((S.level m).typeGraphon (D.rowIndex m))
        ((S.level m).cleanGraphon (D.rowIndex m)))
      atTop (nhds 0) := by
  let error : ℕ → ℝ := fun m ↦
    (S.level m).typeCleanError (D.rowIndex m)
  let hostSize : ℕ → ℕ := fun m ↦
    (S.level m).hostSize (D.rowIndex m)
  have herror : Tendsto error atTop (nhds 0) :=
    Graphon.tendsto_error_of_le_four_mul_eta_add_eight_mul_ratio_of_schedule
      error eta S.clusterCount hostSize
      (fun m ↦ (S.level m).typeCleanError_nonneg (D.rowIndex m))
      heta D.clusterCount_div_hostSize_le (by
        intro m
        exact le_of_eq ((S.level m).typeCleanError_eq (D.rowIndex m)))
  apply squeeze_zero
  · intro m
    exact graphonL1Dist_nonneg _ _
  · intro m
    exact (S.level m).type_to_clean_l1_le (D.rowIndex m)
  · exact herror

/-- The regularity cut error between the selected Type graphon and its host
adjacency graphon vanishes. The diagonal-block term tends to zero because
the cluster count tends to infinity. -/
theorem selected_type_to_host_cut_tendsto
    (heta : Tendsto eta atTop (nhds 0)) :
    Tendsto
      (fun m ↦ cutDist
        ((S.level m).typeGraphon (D.rowIndex m))
        (graphGraphon (G (D.originalIndex m))))
      atTop (nhds 0) := by
  have hbudget :=
    Graphon.tendsto_five_mul_eta_add_one_div_natCast_of_two_mul_le_succ
      eta S.clusterCount heta S.clusterCount_zero_ge
      S.clusterCount_two_mul_le_succ
  apply squeeze_zero
    (g := fun m ↦ 5 * eta m + 1 / (S.clusterCount m : ℝ))
  · intro m
    exact cutDist_nonneg _ _
  · intro m
    letI : DecidableRel (G (D.originalIndex m)).Adj :=
      (S.level m).hostAdjDecidable (D.rowIndex m)
    have hcut := cutDist_typeGraphon_graphGraphon_le
        (G (D.originalIndex m))
        ((S.level m).typeData (D.rowIndex m))
    rw [(S.level m).typeData_clusterCount] at hcut
    rw [(S.level m).typeGraphon_eq]
    exact hcut
  · exact hbudget

/-- Restrict the sampling cut convergence to the cofinal quantitative
diagonal selected from the tower. -/
theorem selected_host_to_target_cut_tendsto
    (hsampling : Tendsto
      (fun n ↦ cutDist (graphGraphon (G n)) W) atTop (nhds 0)) :
    Tendsto
      (fun m ↦ cutDist (graphGraphon (G (D.originalIndex m))) W)
      atTop (nhds 0) :=
  hsampling.comp D.originalIndex_tendsto_atTop

/-- Assemble all final metric and finite-Type data from an exact clean tower
and a chosen common `L¹` limit of its limiting matrix graphons. -/
def toTypeSequenceAssemblyData
    (heta_pos : ∀ m, 0 < eta m)
    (heta : Tendsto eta atTop (nhds 0))
    (hfree : ∀ n, ¬ InducedEmbeds F (G n))
    (hsampling : Tendsto
      (fun n ↦ cutDist (graphGraphon (G n)) W) atTop (nhds 0))
    (l1Limit : Graphon)
    (hmatrix : Tendsto
      (fun m ↦ graphonL1Dist (S.matrixLimitGraphon m) l1Limit)
      atTop (nhds 0)) :
    TypeSequenceAssemblyData F W delta where
  eta := eta
  eta_pos := heta_pos
  hostSize m := D.originalIndex m + 1
  hostSize_pos m := Nat.zero_lt_succ _
  host m := G (D.originalIndex m)
  hostAdjDecidable m := (S.level m).hostAdjDecidable (D.rowIndex m)
  typeData m := (S.level m).typeData (D.rowIndex m)
  host_inducedFree m := hfree (D.originalIndex m)
  cleanGraphon m := (S.level m).cleanGraphon (D.rowIndex m)
  matrixLimitGraphon := S.matrixLimitGraphon
  l1Limit := l1Limit
  type_to_clean_l1_tendsto := by
    apply (S.selected_type_to_clean_l1_tendsto D heta).congr'
    filter_upwards [] with m
    rw [(S.level m).typeGraphon_eq]
    rfl
  clean_to_matrix_l1_tendsto := S.selected_clean_to_matrix_l1_tendsto D
  matrix_to_limit_l1_tendsto := hmatrix
  type_to_host_cut_tendsto := by
    apply (S.selected_type_to_host_cut_tendsto D heta).congr'
    filter_upwards [] with m
    rw [(S.level m).typeGraphon_eq]
    rfl
  host_to_target_cut_tendsto := S.selected_host_to_target_cut_tendsto D hsampling
  eta_tendsto := heta
  clusterCount_tendsto := by
    apply S.clusterCount_tendsto_atTop.congr'
    filter_upwards [] with m
    exact ((S.level m).typeData_clusterCount (D.rowIndex m)).symm

end CleanTypeTowerSystem

end InducedStars
