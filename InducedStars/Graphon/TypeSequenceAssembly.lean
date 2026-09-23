import InducedStars.Graphon.TypeSequence
import Mathlib.Tactic

/-!
# Abstract assembly of a type-graphon sequence

This file isolates the final metric bookkeeping in the type-graphon sequence
argument.  Its input retains the actual finite hosts and regularity types, but
treats the intermediate clean and limiting-matrix graphons abstractly.  In
particular, it is independent of any specific clean-partition construction.
-/

noncomputable section

open Filter
open scoped Topology

namespace InducedStars

open Regularity

/-- Abstract data needed to assemble a `TypeGraphonSequenceResult` from the
three-stage `L¹` approximation and the two-stage cut approximation.

The stored `matrixLimitGraphon m` is the fixed-level limiting matrix graphon;
all such graphons approach the one common `l1Limit`. -/
structure TypeSequenceAssemblyData
    {f : ℕ} (F : SimpleGraph (Fin f)) (W : Graphon) (delta : ℝ) where
  eta : ℕ → ℝ
  eta_pos : ∀ m, 0 < eta m
  hostSize : ℕ → ℕ
  hostSize_pos : ∀ m, 0 < hostSize m
  host : (m : ℕ) → SimpleGraph (Fin (hostSize m))
  hostAdjDecidable : ∀ m, DecidableRel (host m).Adj
  typeData : (m : ℕ) →
    @RegularityType (Fin (hostSize m)) inferInstance inferInstance
      (host m) (hostAdjDecidable m) (eta m) delta f
  host_inducedFree : ∀ m, ¬ InducedEmbeds F (host m)
  cleanGraphon : ℕ → Graphon
  matrixLimitGraphon : ℕ → Graphon
  l1Limit : Graphon
  type_to_clean_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist
        (@typeGraphon _ inferInstance inferInstance
          (host m) (hostAdjDecidable m) (eta m) delta f (typeData m))
        (cleanGraphon m))
      atTop (nhds 0)
  clean_to_matrix_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist (cleanGraphon m) (matrixLimitGraphon m))
      atTop (nhds 0)
  matrix_to_limit_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist (matrixLimitGraphon m) l1Limit)
      atTop (nhds 0)
  type_to_host_cut_tendsto :
    Tendsto
      (fun m ↦ cutDist
        (@typeGraphon _ inferInstance inferInstance
          (host m) (hostAdjDecidable m) (eta m) delta f (typeData m))
        (graphGraphon (host m)))
      atTop (nhds 0)
  host_to_target_cut_tendsto :
    Tendsto (fun m ↦ cutDist (graphGraphon (host m)) W) atTop (nhds 0)
  eta_tendsto : Tendsto eta atTop (nhds 0)
  clusterCount_tendsto :
    Tendsto (fun m ↦ (typeData m).partition.clusterCount) atTop atTop

namespace TypeSequenceAssemblyData

variable {f : ℕ} {F : SimpleGraph (Fin f)} {W : Graphon} {delta : ℝ}

/-- The graphon sequence canonically carried by the retained regularity
types. -/
noncomputable def typeGraphonSeq (D : TypeSequenceAssemblyData F W delta) :
    ℕ → Graphon := fun m ↦
  @typeGraphon _ inferInstance inferInstance
    (D.host m) (D.hostAdjDecidable m) (D.eta m) delta f (D.typeData m)

/-- The three `L¹` approximation stages assemble to convergence of the type
graphons to the common limit. -/
theorem type_to_limit_l1_tendsto (D : TypeSequenceAssemblyData F W delta) :
    Tendsto (fun m ↦ graphonL1Dist (D.typeGraphonSeq m) D.l1Limit)
      atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun m ↦
          graphonL1Dist (D.typeGraphonSeq m) (D.cleanGraphon m) +
            (graphonL1Dist (D.cleanGraphon m) (D.matrixLimitGraphon m) +
              graphonL1Dist (D.matrixLimitGraphon m) D.l1Limit))
        atTop (nhds 0) := by
    simpa only [typeGraphonSeq, zero_add] using
      D.type_to_clean_l1_tendsto.add
        (D.clean_to_matrix_l1_tendsto.add D.matrix_to_limit_l1_tendsto)
  apply squeeze_zero
  · intro m
    exact graphonL1Dist_nonneg _ _
  · intro m
    exact (graphonL1Dist_triangle (D.typeGraphonSeq m) (D.cleanGraphon m)
      D.l1Limit).trans <| add_le_add le_rfl <|
        graphonL1Dist_triangle (D.cleanGraphon m) (D.matrixLimitGraphon m)
          D.l1Limit
  · exact hsum

/-- The two cut approximation stages assemble to convergence of the type
graphons to the target graphon. -/
theorem type_to_target_cut_tendsto (D : TypeSequenceAssemblyData F W delta) :
    Tendsto (fun m ↦ cutDist (D.typeGraphonSeq m) W) atTop (nhds 0) := by
  have hsum :
      Tendsto
        (fun m ↦ cutDist (D.typeGraphonSeq m) (graphGraphon (D.host m)) +
          cutDist (graphGraphon (D.host m)) W)
        atTop (nhds 0) := by
    simpa only [typeGraphonSeq, zero_add] using
      D.type_to_host_cut_tendsto.add D.host_to_target_cut_tendsto
  apply squeeze_zero
  · intro m
    exact cutDist_nonneg _ _
  · intro m
    exact cutDist_triangle (D.typeGraphonSeq m) (graphGraphon (D.host m)) W
  · exact hsum

/-- Forget the intermediate clean and limiting-matrix graphons after using
their convergence estimates to assemble the paper-facing result. -/
noncomputable def toTypeGraphonSequenceResult
    (D : TypeSequenceAssemblyData F W delta) :
    TypeGraphonSequenceResult F W delta where
  eta := D.eta
  eta_pos := D.eta_pos
  hostSize := D.hostSize
  hostSize_pos := D.hostSize_pos
  host := D.host
  hostAdjDecidable := D.hostAdjDecidable
  typeData := D.typeData
  host_inducedFree := D.host_inducedFree
  graphonSeq := D.typeGraphonSeq
  graphonSeq_eq := fun _ ↦ rfl
  l1Limit := D.l1Limit
  cut_tendsto := D.type_to_target_cut_tendsto
  l1_tendsto := D.type_to_limit_l1_tendsto
  eta_tendsto := D.eta_tendsto
  clusterCount_tendsto := D.clusterCount_tendsto

/-- The assembled common `L¹` limit is cut-equivalent to the original
target graphon. -/
theorem cutDist_l1Limit_target_eq_zero
    (D : TypeSequenceAssemblyData F W delta) :
    cutDist D.l1Limit W = 0 :=
  D.toTypeGraphonSequenceResult.cutDist_l1Limit_target_eq_zero

end TypeSequenceAssemblyData

end InducedStars
