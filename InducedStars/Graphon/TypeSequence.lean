import InducedStars.Graphon.Approximation
import InducedStars.Graphon.Densities
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Type graphon sequences

This file contains the paper-facing output type for Lemma
`lemma:UFHatGraphonSeq` and the elementary analytic facts used by its
construction.  The tower construction itself is developed in
`Graphon.TypeTower`.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology unitInterval

namespace InducedStars

open Regularity

/-- The zero-based error schedule used in the Type tower. -/
def typeSequenceEta (epsilonStar : ℝ) (m : ℕ) : ℝ :=
  min (epsilonStar / 2) (1 / ((m + 1 : ℕ) : ℝ))

theorem typeSequenceEta_pos {epsilonStar : ℝ} (h : 0 < epsilonStar) (m : ℕ) :
    0 < typeSequenceEta epsilonStar m := by
  exact lt_min (by positivity) (by positivity)

theorem typeSequenceEta_lt {epsilonStar : ℝ} (h : 0 < epsilonStar) (m : ℕ) :
    typeSequenceEta epsilonStar m < epsilonStar := by
  calc
    typeSequenceEta epsilonStar m ≤ epsilonStar / 2 := min_le_left _ _
    _ < epsilonStar := by linarith

theorem typeSequenceEta_tendsto_zero {epsilonStar : ℝ} (h : 0 < epsilonStar) :
    Tendsto (typeSequenceEta epsilonStar) atTop (𝓝 0) := by
  apply squeeze_zero
  · intro m
    exact (typeSequenceEta_pos h m).le
  · intro m
    exact min_le_right _ _
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The induced density of the unique graph on no vertices is one.

This is the empty-pattern branch needed by the paper-facing theorem; it
prevents adding an artificial nonemptiness assumption on the forbidden graph.
-/
theorem graphonInducedDensity_fin_zero (F : SimpleGraph (Fin 0)) (W : Graphon) :
    graphonInducedDensity F W = 1 := by
  have hF : F = ⊥ := by
    ext x
    exact Fin.elim0 x
  subst F
  have hEdges (G : SimpleGraph (Fin 0)) : finiteGraphEdges G = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    refine Sym2.inductionOn e ?_
    intro i _j
    exact Fin.elim0 i
  simp [graphonInducedDensity, graphonInducedIntegrand, hEdges]

/-- Complete reusable witness package for the Type Graphon Sequence Lemma.

The actual host graphs and actual `RegularityType` witnesses are retained.
The decidable adjacency field is explicit so subsequent definitions can use
the same witnesses without relying on a hidden choice of instances.
-/
structure TypeGraphonSequenceResult
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
  graphonSeq : ℕ → Graphon
  graphonSeq_eq : ∀ m,
    graphonSeq m = @typeGraphon _ inferInstance inferInstance
      (host m) (hostAdjDecidable m) (eta m) delta f (typeData m)
  l1Limit : Graphon
  cut_tendsto :
    Tendsto (fun m => cutDist (graphonSeq m) W) atTop (𝓝 0)
  l1_tendsto :
    Tendsto (fun m => graphonL1Dist (graphonSeq m) l1Limit) atTop (𝓝 0)
  eta_tendsto : Tendsto eta atTop (𝓝 0)
  clusterCount_tendsto :
    Tendsto (fun m => (typeData m).partition.clusterCount) atTop atTop

namespace TypeGraphonSequenceResult

variable {f : ℕ} {F : SimpleGraph (Fin f)} {W : Graphon} {delta : ℝ}

/-- The common `L¹` limit belongs to the cut-equivalence class of the
original target graphon. -/
theorem cutDist_l1Limit_target_eq_zero
    (R : TypeGraphonSequenceResult F W delta) :
    cutDist R.l1Limit W = 0 := by
  have hl1' : Tendsto
      (fun m => graphonL1Dist R.l1Limit (R.graphonSeq m)) atTop (𝓝 0) := by
    apply R.l1_tendsto.congr'
    filter_upwards [] with m
    exact graphonL1Dist_comm _ _
  have hsum : Tendsto
      (fun m => graphonL1Dist R.l1Limit (R.graphonSeq m) +
        cutDist (R.graphonSeq m) W) atTop (𝓝 0) := by
    simpa only [zero_add] using hl1'.add R.cut_tendsto
  apply le_antisymm
  · apply ge_of_tendsto' hsum
    intro m
    exact (cutDist_triangle R.l1Limit (R.graphonSeq m) W).trans
      (add_le_add (cutDist_le_graphonL1Dist _ _) le_rfl)
  · exact cutDist_nonneg _ _

end TypeGraphonSequenceResult

end InducedStars

