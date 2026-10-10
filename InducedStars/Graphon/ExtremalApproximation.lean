import InducedStars.Graphon.OptimizerProfile
import InducedStars.Graphon.TypeGraphonSequence
import InducedStars.Graphon.TypeProfileApproximation
import InducedStars.EdgeColoring.Stability
import Mathlib.Tactic

/-!
# Exact extremal-family approximations of graphon optimizers

This module formalizes the finite-stability-transfer portion of the proof of
paper Proposition `prop:graphon-char-fixed-gamma`.  It deliberately keeps all
finite colorings in the labels supplied by colored stability.  Decomposition
and rearrangement of their exact extremal witnesses belongs to the subsequent
classification layer.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace InducedStars

open Regularity

/-! ## Transport across cut-distance-zero equivalence -/

/-- Fixed-density optimizer status depends only on the cut-distance-zero
equivalence class. -/
theorem IsFixedDensityOptimizer.of_cutDist_eq_zero
    {k : ℕ} {γ : ℝ} {W U : Graphon}
    (hW : IsFixedDensityOptimizer k γ W)
    (hcut : cutDist U W = 0) :
    IsFixedDensityOptimizer k γ U := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [graphonInducedDensity_eq_of_cutDist_eq_zero
      (inducedStar k) U W hcut]
    exact hW.feasible.1
  · rw [graphonEdgeDensity_eq_of_cutDist_eq_zero U W hcut]
    exact hW.feasible.2
  · intro V hV
    calc
      graphonEntropy V ≤ graphonEntropy W := hW.entropy_le hV
      _ = graphonEntropy U :=
        (graphonEntropy_eq_of_cutDist_eq_zero U W hcut).symm

/-- Set-membership form of optimizer transport across cut distance zero. -/
theorem fixedDensityOptimizer_of_cutDist_eq_zero
    {k : ℕ} {γ : ℝ} {W U : Graphon}
    (hW : W ∈ fixedDensityOptimizers k γ)
    (hcut : cutDist U W = 0) :
    U ∈ fixedDensityOptimizers k γ :=
  hW.of_cutDist_eq_zero hcut

/-- Equality of value laws identifies the profile means chosen on two
cut-equivalent optimizer representatives. -/
theorem FixedDensityOptimizerProfile.randomMean_eq_of_cutDist_eq_zero
    {k : ℕ} {γ : ℝ} {W U : Graphon}
    (PW : FixedDensityOptimizerProfile k γ W)
    (PU : FixedDensityOptimizerProfile k γ U)
    (hcut : cutDist U W = 0) :
    PU.randomMean = PW.randomMean := by
  calc
    PU.randomMean =
        scalarRatio γ (graphonOneMass U) (graphonRandomMass U) :=
      PU.scalarRatio_eq_randomMean.symm
    _ = scalarRatio γ (graphonOneMass W) (graphonRandomMass W) := by
      rw [graphonOneMass_eq_of_cutDist_eq_zero U W hcut,
        graphonRandomMass_eq_of_cutDist_eq_zero U W hcut]
    _ = PW.randomMean := PW.scalarRatio_eq_randomMean

/-! ## A positive vanishing stability schedule -/

/-- The stage-dependent edit tolerance used in the colored-stability
diagonal extraction.  The mass cap later forces the retained exact coloring
to have a nonempty red core. -/
def optimizerStabilityError (U : Graphon) (m : ℕ) : ℝ :=
  min (1 / ((m + 1 : ℕ) : ℝ)) (graphonRandomMass U / 16)

theorem optimizerStabilityError_pos {U : Graphon}
    (hU : 0 < graphonRandomMass U) (m : ℕ) :
    0 < optimizerStabilityError U m := by
  exact lt_min (by positivity) (by
    positivity)

theorem optimizerStabilityError_nonneg (U : Graphon) (m : ℕ) :
    0 ≤ optimizerStabilityError U m := by
  unfold optimizerStabilityError
  exact le_min (by positivity)
    (div_nonneg (graphonRandomMass_nonneg U) (by norm_num))

theorem optimizerStabilityError_le_randomMass_div_sixteen
    (U : Graphon) (m : ℕ) :
    optimizerStabilityError U m ≤ graphonRandomMass U / 16 :=
  min_le_right _ _

theorem optimizerStabilityError_le_inv_succ (U : Graphon) (m : ℕ) :
    optimizerStabilityError U m ≤ 1 / ((m + 1 : ℕ) : ℝ) :=
  min_le_left _ _

theorem optimizerStabilityError_tendsto_zero (U : Graphon) :
    Tendsto (optimizerStabilityError U) atTop (nhds 0) := by
  apply squeeze_zero
  · exact optimizerStabilityError_nonneg U
  · exact optimizerStabilityError_le_inv_succ U
  · simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-! ## Nonempty exact cores -/

namespace ColoredGraph.ExtremalFamilyWitness

/-- An exact extremal-family witness with no cores has zero normalized red
area: its off-diagonal coloring is entirely green. -/
theorem normalizedRedArea_eq_zero_of_coreCount_eq_zero
    {k q : ℕ} {C : ColoredGraph (Fin q)}
    (E : ExtremalFamilyWitness k q C) (hcount : E.coreCount = 0) :
    C.normalizedRedArea = 0 := by
  have hred : C.edgeCount .red = 0 := by
    rw [edgeCount, Finset.card_eq_zero]
    apply Finset.eq_empty_of_forall_notMem
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        have hxy := (C.pair_mem_edgeFinset .red x y).1 he
        have hnone : ∀ i, ¬ (x ∈ E.coreVertices i ∧ y ∈ E.coreVertices i) := by
          intro i
          have hi : i.val < 0 := by simpa [hcount] using i.isLt
          omega
        have hgreen := E.offCoreGreen x y hxy.1 hnone
        rw [hxy.2] at hgreen
        cases hgreen
  simp [ColoredGraph.normalizedRedArea, hred]

/-- Positive red area forces at least one core in an exact extremal-family
witness. -/
theorem coreCount_pos_of_normalizedRedArea_pos
    {k q : ℕ} {C : ColoredGraph (Fin q)}
    (E : ExtremalFamilyWitness k q C)
    (hred : 0 < C.normalizedRedArea) :
    0 < E.coreCount := by
  by_contra hnot
  have hzero : E.coreCount = 0 := Nat.eq_zero_of_not_pos hnot
  rw [E.normalizedRedArea_eq_zero_of_coreCount_eq_zero hzero] at hred
  exact lt_irrefl 0 hred

end ColoredGraph.ExtremalFamilyWitness

/-! ## The retained labeled finite objects -/

/-- The actual selected Type.  This is definitionally the witness retained by
the Type graphon bridge, not a reconstructed reduced object. -/
noncomputable def optimizerSelectedType {k : ℕ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (m : ℕ) :
    @RegularityType (Fin (R.hostSize (σ m))) inferInstance inferInstance
      (R.host (σ m)) (R.hostAdjDecidable (σ m)) (R.eta (σ m)) θ (k + 1) :=
  R.typeData (σ m)

/-- Cluster count of the retained selected Type. -/
def optimizerSelectedClusterCount {k : ℕ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (m : ℕ) : ℕ := by
  letI : DecidableRel (R.host (σ m)).Adj := R.hostAdjDecidable (σ m)
  exact (R.typeData (σ m)).partition.clusterCount

/-- Selected cluster counts remain cofinal along a cofinal extraction. -/
theorem optimizerSelectedClusterCount_tendsto
    {k : ℕ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop) :
    Tendsto (optimizerSelectedClusterCount R σ) atTop atTop := by
  convert R.clusterCount_tendsto.comp hσ using 1
  funext m
  simp [optimizerSelectedClusterCount, Function.comp_def]

/-- Every retained Type has positive cluster count because its host is
nonempty. -/
theorem optimizerSelectedClusterCount_pos
    {k : ℕ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (m : ℕ) :
    0 < optimizerSelectedClusterCount R σ m := by
  letI : DecidableRel (R.host (σ m)).Adj := R.hostAdjDecidable (σ m)
  simpa [optimizerSelectedClusterCount] using
    RegularityType.clusterCount_pos_of_fin_pos (R.host (σ m))
      (R.typeData (σ m)) (R.hostSize_pos (σ m))

/-- The paper's coloring `φ_m`, along a specified extraction. -/
noncomputable def optimizerTypeColoring {k : ℕ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (m : ℕ) :
    ColoredGraph (Fin (optimizerSelectedClusterCount R σ m)) := by
  letI : DecidableRel (R.host (σ m)).Adj := R.hostAdjDecidable (σ m)
  change ColoredGraph (Fin (R.typeData (σ m)).partition.clusterCount)
  exact Regularity.typeCompleteColoring (R.typeData (σ m))

/-- Every selected complete Type coloring lies in the exact finite forbidden
class. -/
theorem optimizerTypeColoring_mem_Ck {k : ℕ} (hk : 3 ≤ k)
    {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (m : ℕ) :
    optimizerTypeColoring R σ m ∈
      ColoredGraph.Ck k (optimizerSelectedClusterCount R σ m) := by
  letI : DecidableRel (R.host (σ m)).Adj := R.hostAdjDecidable (σ m)
  change Regularity.typeCompleteColoring (R.typeData (σ m)) ∈
    ColoredGraph.Ck k (R.typeData (σ m)).partition.clusterCount
  exact Regularity.typeCompleteColoring_mem_Ck hk
    (R.typeData (σ m)) (R.host_inducedFree (σ m))

/-- The `{0,p,1}` profile graphon of the selected Type coloring. -/
noncomputable def optimizerTypeProfileGraphon
    {k : ℕ} {γ : ℝ} {W U : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    (σ : ℕ → ℕ) (P : FixedDensityOptimizerProfile k γ U) (m : ℕ) :
    Graphon :=
  profileColoringGraphon P.randomMean (optimizerTypeColoring R σ m)
    ⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩

/-- The `{0,p,1}` profile graphon of a retained exact extremal coloring. -/
noncomputable def optimizerExtremalProfileGraphon
    {k q : ℕ} {γ : ℝ} {U : Graphon}
    (P : FixedDensityOptimizerProfile k γ U)
    (C : ColoredGraph (Fin q)) : Graphon :=
  profileColoringGraphon P.randomMean C
    ⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩

/-! ## Convergence inherited from the Type bridge -/

/-- The finite Type-profile graphons converge in `L¹` to the bridge's common
limit along every cofinal extraction. -/
theorem optimizerTypeProfileGraphon_l1_tendsto
    {k : ℕ} {γ : ℝ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    (P : FixedDensityOptimizerProfile k γ R.l1Limit)
    (hsep₀ : 2 * θ < P.randomMean)
    (hsep₁ : 2 * θ < 1 - P.randomMean) :
    Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerTypeProfileGraphon R σ P m) R.l1Limit)
      atTop (nhds 0) := by
  let q : ℕ → ℕ := optimizerSelectedClusterCount R σ
  let err : ℕ → ℝ := fun m ↦
    (2 / θ) * graphonL1Dist (R.graphonSeq (σ m)) R.l1Limit +
      2 * R.eta (σ m) + 1 / (q m : ℝ)
  have hrecip : Tendsto (fun m ↦ 1 / (q m : ℝ)) atTop (nhds 0) := by
    apply (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    exact optimizerSelectedClusterCount_tendsto R hσ
  have hl1 : Tendsto
      (fun m ↦ (2 / θ) *
        graphonL1Dist (R.graphonSeq (σ m)) R.l1Limit)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := 2 / θ)).mul
      (R.l1_tendsto.comp hσ)
  have heta : Tendsto (fun m ↦ 2 * R.eta (σ m)) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul
      (R.eta_tendsto.comp hσ)
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err] using (hl1.add heta).add hrecip
  have hle : ∀ m,
      graphonL1Dist (optimizerTypeProfileGraphon R σ P m) R.l1Limit ≤
        err m := by
    intro m
    letI : DecidableRel (R.host (σ m)).Adj := R.hostAdjDecidable (σ m)
    have hbound := graphonL1Dist_typeProfileGraphon_le
      (R.typeData (σ m))
      (optimizerSelectedClusterCount_pos R σ m)
      P.randomMean_pos P.randomMean_lt_one hsep₀ hsep₁
      R.l1Limit P.ae_threeValued
    rw [← R.graphonSeq_eq (σ m)] at hbound
    simpa [optimizerTypeProfileGraphon, optimizerTypeColoring,
      optimizerSelectedClusterCount, q, err] using hbound
  exact squeeze_zero (fun m ↦ graphonL1Dist_nonneg _ _) hle herr

/-- The normalized red and blue-plus-diagonal areas of Type colorings
converge to the corresponding separated value-region masses. -/
theorem optimizerTypeColoring_areas_tendsto
    {k : ℕ} {γ : ℝ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    {σ : ℕ → ℕ}
    (P : FixedDensityOptimizerProfile k γ R.l1Limit)
    (hprofile : Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerTypeProfileGraphon R σ P m) R.l1Limit)
      atTop (nhds 0)) :
    Tendsto
        (fun m ↦ (optimizerTypeColoring R σ m).normalizedRedArea)
        atTop (nhds (graphonRandomMass R.l1Limit)) ∧
      Tendsto
        (fun m ↦
          (optimizerTypeColoring R σ m).normalizedBlueDiagonalArea)
        atTop (nhds (graphonOneMass R.l1Limit)) := by
  let sep : ℝ := min P.randomMean (1 - P.randomMean)
  have hsep : 0 < sep := by
    change 0 < min P.randomMean (1 - P.randomMean)
    rw [lt_min_iff]
    exact ⟨P.randomMean_pos, sub_pos.mpr P.randomMean_lt_one⟩
  let err : ℕ → ℝ := fun m ↦
    graphonL1Dist (optimizerTypeProfileGraphon R σ P m) R.l1Limit / sep
  have herr : Tendsto err atTop (nhds 0) := by
    simpa [err, div_eq_mul_inv] using
      hprofile.mul (tendsto_const_nhds (x := sep⁻¹))
  have hredBound : ∀ m,
      |(optimizerTypeColoring R σ m).normalizedRedArea -
          graphonRandomMass R.l1Limit| ≤ err m := by
    intro m
    let q := optimizerSelectedClusterCount R σ m
    let C := optimizerTypeColoring R σ m
    let A := optimizerTypeProfileGraphon R σ P m
    have hq : 0 < q := optimizerSelectedClusterCount_pos R σ m
    have hAthre := profileColoringGraphon_ae_threeValued hq P.randomMean C
      (⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩ :
        P.randomMean ∈ Icc (0 : ℝ) 1)
    change ∀ᵐ z ∂unitSquareMeasure,
      A.value z = 0 ∨ A.value z = P.randomMean ∨ A.value z = 1 at hAthre
    have hmass := graphonRandomMass_sub_abs_le_graphonL1Dist_div_min
      A R.l1Limit P.randomMean_pos P.randomMean_lt_one
      hAthre P.ae_threeValued
    change
      |graphonRandomMass
          (profileColoringGraphon P.randomMean C
            ⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩) -
          graphonRandomMass R.l1Limit| ≤ _ at hmass
    rw [graphonRandomMass_profileColoringGraphon hq
      ⟨P.randomMean_pos, P.randomMean_lt_one⟩ C] at hmass
    simpa [q, C, A, err, sep, optimizerTypeProfileGraphon] using hmass
  have hblueBound : ∀ m,
      |(optimizerTypeColoring R σ m).normalizedBlueDiagonalArea -
          graphonOneMass R.l1Limit| ≤ err m := by
    intro m
    let q := optimizerSelectedClusterCount R σ m
    let C := optimizerTypeColoring R σ m
    let A := optimizerTypeProfileGraphon R σ P m
    have hq : 0 < q := optimizerSelectedClusterCount_pos R σ m
    have hAthre := profileColoringGraphon_ae_threeValued hq P.randomMean C
      (⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩ :
        P.randomMean ∈ Icc (0 : ℝ) 1)
    change ∀ᵐ z ∂unitSquareMeasure,
      A.value z = 0 ∨ A.value z = P.randomMean ∨ A.value z = 1 at hAthre
    have hmass := graphonOneMass_sub_abs_le_graphonL1Dist_div_min
      A R.l1Limit P.randomMean_pos P.randomMean_lt_one
      hAthre P.ae_threeValued
    change
      |graphonOneMass
          (profileColoringGraphon P.randomMean C
            ⟨P.randomMean_pos.le, P.randomMean_lt_one.le⟩) -
          graphonOneMass R.l1Limit| ≤ _ at hmass
    rw [graphonOneMass_profileColoringGraphon hq
      ⟨P.randomMean_pos, P.randomMean_lt_one⟩ C] at hmass
    simpa [q, C, A, err, sep, optimizerTypeProfileGraphon] using hmass
  constructor
  · have hlower : Tendsto
        (fun m ↦ graphonRandomMass R.l1Limit - err m)
        atTop (nhds (graphonRandomMass R.l1Limit)) := by
      simpa using tendsto_const_nhds.sub herr
    have hupper : Tendsto
        (fun m ↦ graphonRandomMass R.l1Limit + err m)
        atTop (nhds (graphonRandomMass R.l1Limit)) := by
      simpa using tendsto_const_nhds.add herr
    exact Filter.Tendsto.squeeze hlower hupper
      (fun m ↦ by
        have hm := (abs_le.mp (hredBound m)).1
        linarith)
      (fun m ↦ by
        have hm := (abs_le.mp (hredBound m)).2
        linarith)
  · have hlower : Tendsto
        (fun m ↦ graphonOneMass R.l1Limit - err m)
        atTop (nhds (graphonOneMass R.l1Limit)) := by
      simpa using tendsto_const_nhds.sub herr
    have hupper : Tendsto
        (fun m ↦ graphonOneMass R.l1Limit + err m)
        atTop (nhds (graphonOneMass R.l1Limit)) := by
      simpa using tendsto_const_nhds.add herr
    exact Filter.Tendsto.squeeze hlower hupper
      (fun m ↦ by
        have hm := (abs_le.mp (hblueBound m)).1
        linarith)
      (fun m ↦ by
        have hm := (abs_le.mp (hblueBound m)).2
        linarith)

/-- Exact optimizer saturation turns convergence of the two finite color
areas into convergence of the normalized integer objective to zero. -/
theorem optimizerTypeColoring_normalizedObjective_tendsto
    {k : ℕ} {γ : ℝ} {W : Graphon} {θ : ℝ}
    (R : TypeGraphonSequenceResult (inducedStar k) W θ)
    {σ : ℕ → ℕ} (hσ : Tendsto σ atTop atTop)
    (P : FixedDensityOptimizerProfile k γ R.l1Limit)
    (hred : Tendsto
      (fun m ↦ (optimizerTypeColoring R σ m).normalizedRedArea)
      atTop (nhds (graphonRandomMass R.l1Limit)))
    (hblue : Tendsto
      (fun m ↦
        (optimizerTypeColoring R σ m).normalizedBlueDiagonalArea)
      atTop (nhds (graphonOneMass R.l1Limit))) :
    Tendsto
      (fun m ↦ normalizedObjective k (optimizerTypeColoring R σ m))
      atTop (nhds 0) := by
  have hrecip : Tendsto
      (fun m ↦ 1 / (optimizerSelectedClusterCount R σ m : ℝ))
      atTop (nhds 0) := by
    apply (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    exact optimizerSelectedClusterCount_tendsto R hσ
  have hexpr : Tendsto
      (fun m ↦
        (optimizerTypeColoring R σ m).normalizedRedArea -
          (delta k : ℝ) *
            (optimizerTypeColoring R σ m).normalizedBlueDiagonalArea +
          (delta k : ℝ) /
            (optimizerSelectedClusterCount R σ m : ℝ))
      atTop
      (nhds (graphonRandomMass R.l1Limit -
        (delta k : ℝ) * graphonOneMass R.l1Limit)) := by
    have hblue' := (tendsto_const_nhds (x := (delta k : ℝ))).mul hblue
    have hrecip' := (tendsto_const_nhds (x := (delta k : ℝ))).mul hrecip
    simpa [div_eq_mul_inv] using (hred.sub hblue').add hrecip'
  have hlimit : graphonRandomMass R.l1Limit -
      (delta k : ℝ) * graphonOneMass R.l1Limit = 0 := by
    simpa [delta] using
      sub_eq_zero.mpr P.randomMass_eq_delta_mul_oneMass
  rw [hlimit] at hexpr
  apply hexpr.congr'
  filter_upwards [] with m
  exact (normalizedObjective_eq k
    (optimizerSelectedClusterCount_pos R σ m)
    (optimizerTypeColoring R σ m)).symm

/-- Convergence of the normalized objective to zero supplies the unscaled
one-sided near-extremality hypothesis required by finite stability. -/
theorem eventually_objective_lower_bound_of_normalizedObjective_tendsto
    (k : ℕ) {q : ℕ → ℕ}
    (C : (m : ℕ) → ColoredGraph (Fin (q m)))
    (hq : ∀ m, 0 < q m)
    (hobj : Tendsto (fun m ↦ normalizedObjective k (C m))
      atTop (nhds 0))
    (inputDelta : ℝ) (hinputDelta : 0 < inputDelta) :
    ∀ᶠ m in atTop,
      -(inputDelta * (q m : ℝ) ^ 2) ≤
        (ColoredGraph.objective k (C m) : ℝ) := by
  have htail : ∀ᶠ m in atTop,
      -2 * inputDelta < normalizedObjective k (C m) :=
    (tendsto_order.1 hobj).1 (-2 * inputDelta) (by linarith)
  filter_upwards [htail] with m hm
  have hqReal : 0 < (q m : ℝ) := by exact_mod_cast hq m
  have hqSq : 0 < (q m : ℝ) ^ 2 := sq_pos_of_pos hqReal
  unfold normalizedObjective at hm
  rw [lt_div_iff₀ hqSq] at hm
  nlinarith

/-! ## Principal output package -/

/-- Labeled exact-extremal approximations of one fixed-density optimizer.

All Type colorings are definitionally obtained from the retained Type
witnesses.  All profile graphons are definitionally obtained from their
corresponding colorings.  In particular, none of these fields can be filled
by an unrelated auxiliary sequence. -/
structure OptimizerExtremalApproximationResult
    (k : ℕ) (γ : ℝ) (W : Graphon) where
  target : Graphon
  target_cut_eq_zero : cutDist target W = 0
  target_optimizer : IsFixedDensityOptimizer k γ target
  profile : FixedDensityOptimizerProfile k γ target
  threshold : ℝ
  threshold_pos : 0 < threshold
  threshold_lt_half : threshold < 1 / 2
  threshold_separates :
    2 * threshold < profile.randomMean ∧
      2 * threshold < 1 - profile.randomMean
  bridge : TypeGraphonSequenceResult (inducedStar k) W threshold
  target_eq_bridge_l1Limit : target = bridge.l1Limit
  extraction : ℕ → ℕ
  extraction_strictMono : StrictMono extraction
  selectedClusterCount_pos : ∀ m,
    0 < optimizerSelectedClusterCount bridge extraction m
  selectedClusterCount_tendsto :
    Tendsto (optimizerSelectedClusterCount bridge extraction) atTop atTop
  typeColoring_mem_Ck : ∀ m,
    optimizerTypeColoring bridge extraction m ∈
      ColoredGraph.Ck k (optimizerSelectedClusterCount bridge extraction m)
  typeProfile_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerTypeProfileGraphon bridge extraction profile m) target)
      atTop (nhds 0)
  typeRedArea_tendsto :
    Tendsto
      (fun m ↦ (optimizerTypeColoring bridge extraction m).normalizedRedArea)
      atTop (nhds (graphonRandomMass target))
  typeBlueArea_tendsto :
    Tendsto
      (fun m ↦
        (optimizerTypeColoring bridge extraction m).normalizedBlueDiagonalArea)
      atTop (nhds (graphonOneMass target))
  typeObjective_tendsto :
    Tendsto
      (fun m ↦ normalizedObjective k
        (optimizerTypeColoring bridge extraction m))
      atTop (nhds 0)
  extremalColoring : (m : ℕ) →
    ColoredGraph (Fin (optimizerSelectedClusterCount bridge extraction m))
  extremal_mem : ∀ m,
    extremalColoring m ∈ ColoredGraph.extremalFamily k
      (optimizerSelectedClusterCount bridge extraction m)
  extremalWitness : (m : ℕ) →
    ColoredGraph.ExtremalFamilyWitness k
      (optimizerSelectedClusterCount bridge extraction m) (extremalColoring m)
  extremal_coreCount_pos : ∀ m, 0 < (extremalWitness m).coreCount
  hamming_ratio_tendsto :
    Tendsto
      (fun m ↦
        (ColoredGraph.coloringHammingDistance
          (optimizerTypeColoring bridge extraction m) (extremalColoring m) : ℝ) /
            (optimizerSelectedClusterCount bridge extraction m : ℝ) ^ 2)
      atTop (nhds 0)
  extremalProfile_l1_tendsto :
    Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerExtremalProfileGraphon profile (extremalColoring m)) target)
      atTop (nhds 0)
  extremalRedArea_tendsto :
    Tendsto (fun m ↦ (extremalColoring m).normalizedRedArea)
      atTop (nhds (graphonRandomMass target))
  extremalBlueArea_tendsto :
    Tendsto (fun m ↦ (extremalColoring m).normalizedBlueDiagonalArea)
      atTop (nhds (graphonOneMass target))
  extremalObjective_tendsto :
    Tendsto (fun m ↦ normalizedObjective k (extremalColoring m))
      atTop (nhds 0)

namespace OptimizerExtremalApproximationResult

variable {k : ℕ} {γ : ℝ} {W : Graphon}

/-- The actual Type selected at stage `m`. -/
abbrev selectedType (R : OptimizerExtremalApproximationResult k γ W) (m : ℕ) :=
  optimizerSelectedType R.bridge R.extraction m

/-- The selected Type order `q_m`. -/
abbrev selectedClusterCount
    (R : OptimizerExtremalApproximationResult k γ W) (m : ℕ) :=
  optimizerSelectedClusterCount R.bridge R.extraction m

/-- The retained Type complete coloring `φ_m`. -/
abbrev typeColoring
    (R : OptimizerExtremalApproximationResult k γ W) (m : ℕ) :=
  optimizerTypeColoring R.bridge R.extraction m

/-- The Type-profile graphon `A_m`. -/
abbrev typeProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (m : ℕ) :=
  optimizerTypeProfileGraphon R.bridge R.extraction R.profile m

/-- The exact-extremal profile graphon `B_m` (the paper's `H_m`), kept in
the labels in which stability compares it with `φ_m`. -/
abbrev extremalProfileGraphon
    (R : OptimizerExtremalApproximationResult k γ W) (m : ℕ) :=
  optimizerExtremalProfileGraphon R.profile (R.extremalColoring m)

end OptimizerExtremalApproximationResult

/-! ## Assembly by finite stability and a cofinal diagonal -/

/-- Preparation and finite-stability transfer in the proof of paper
Proposition `prop:graphon-char-fixed-gamma`.

The result stops with labeled exact-extremal witnesses whose profile graphons
converge in `L¹` to a fixed representative cut-equivalent to the input
optimizer. The original coordinates are retained in this comparison.  Component equalization and the reverse classification are
left to the next layer. -/
theorem existsOptimizerExtremalApproximation
    (k : ℕ) (hk : 3 ≤ k)
    (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1)
    (W : Graphon) (hW : W ∈ fixedDensityOptimizers k γ) :
    Nonempty (OptimizerExtremalApproximationResult k γ W) := by
  classical
  have hWopt : IsFixedDensityOptimizer k γ W := hW
  let PW : FixedDensityOptimizerProfile k γ W := hWopt.profile hk hγ
  let θ : ℝ := optimizerTypeThreshold PW
  have hθpos : 0 < θ := optimizerTypeThreshold_pos PW
  have hθhalf : θ < 1 / 2 := optimizerTypeThreshold_lt_half PW
  obtain ⟨bridge⟩ := typeGraphonSequence (inducedStar k) W θ
    hθpos hθhalf hWopt.feasible.1
  let U : Graphon := bridge.l1Limit
  have hcut : cutDist U W = 0 := bridge.cutDist_l1Limit_target_eq_zero
  have hUopt : IsFixedDensityOptimizer k γ U :=
    hWopt.of_cutDist_eq_zero hcut
  let PU : FixedDensityOptimizerProfile k γ U := hUopt.profile hk hγ
  have hpEq : PU.randomMean = PW.randomMean :=
    FixedDensityOptimizerProfile.randomMean_eq_of_cutDist_eq_zero PW PU hcut
  have hsep₀ : 2 * θ < PU.randomMean := by
    rw [hpEq]
    exact two_mul_optimizerTypeThreshold_lt_randomMean PW
  have hsep₁ : 2 * θ < 1 - PU.randomMean := by
    rw [hpEq]
    exact two_mul_optimizerTypeThreshold_lt_one_sub_randomMean PW

  -- First obtain all convergence statements on the unextracted bridge.
  have hId : Tendsto (id : ℕ → ℕ) atTop atTop := tendsto_id
  have hProfileRaw : Tendsto
      (fun n ↦ graphonL1Dist
        (optimizerTypeProfileGraphon bridge id PU n) U)
      atTop (nhds 0) :=
    optimizerTypeProfileGraphon_l1_tendsto bridge hId PU hsep₀ hsep₁
  have hAreasRaw := optimizerTypeColoring_areas_tendsto bridge PU hProfileRaw
  have hRedRaw := hAreasRaw.1
  have hBlueRaw := hAreasRaw.2
  have hObjectiveRaw :=
    optimizerTypeColoring_normalizedObjective_tendsto
      bridge hId PU hRedRaw hBlueRaw

  let q : ℕ → ℕ := optimizerSelectedClusterCount bridge id
  let φ : (n : ℕ) → ColoredGraph (Fin (q n)) :=
    optimizerTypeColoring bridge id
  let A : ℕ → Graphon := optimizerTypeProfileGraphon bridge id PU
  have hqpos : ∀ n, 0 < q n := by
    intro n
    exact optimizerSelectedClusterCount_pos bridge id n
  have hqTop : Tendsto q atTop atTop :=
    optimizerSelectedClusterCount_tendsto bridge hId
  have hφCk : ∀ n, φ n ∈ ColoredGraph.Ck k (q n) := by
    intro n
    exact optimizerTypeColoring_mem_Ck hk bridge id n

  let ε : ℕ → ℝ := optimizerStabilityError U
  have hεpos : ∀ m, 0 < ε m :=
    optimizerStabilityError_pos PU.randomMass_pos
  have hεzero : Tendsto ε atTop (nhds 0) :=
    optimizerStabilityError_tendsto_zero U
  have hstability : ∀ m, ∃ inputDelta : ℝ, 0 < inputDelta ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n),
        C ∈ ColoredGraph.Ck k n →
        -(inputDelta * (n : ℝ) ^ 2) ≤
            (ColoredGraph.objective k C : ℝ) →
        ∃ Cstar : ColoredGraph (Fin n),
          Cstar ∈ ColoredGraph.extremalFamily k n ∧
          (C.coloringHammingDistance Cstar : ℝ) ≤ ε m * (n : ℝ) ^ 2 :=
    fun m ↦ ColoredGraph.kthOrderStability k hk (ε m) (hεpos m)
  choose inputDelta hinputDelta n₀ hstability using hstability

  have hNear : ∀ m, ∀ᶠ n in atTop,
      -(inputDelta m * (q n : ℝ) ^ 2) ≤
        (ColoredGraph.objective k (φ n) : ℝ) := by
    intro m
    exact eventually_objective_lower_bound_of_normalizedObjective_tendsto
      k φ hqpos hObjectiveRaw (inputDelta m) (hinputDelta m)
  let Good : ℕ → ℕ → Prop := fun m n ↦
    n₀ m ≤ q n ∧
      -(inputDelta m * (q n : ℝ) ^ 2) ≤
        (ColoredGraph.objective k (φ n) : ℝ) ∧
      graphonL1Dist (A n) U ≤ ε m ∧
      graphonRandomMass U / 2 ≤ (φ n).normalizedRedArea
  have hGood : ∀ m, ∀ᶠ n in atTop, Good m n := by
    intro m
    have hlarge : ∀ᶠ n in atTop, n₀ m ≤ q n :=
      hqTop.eventually (eventually_ge_atTop (n₀ m))
    have hclose' : ∀ᶠ n in atTop,
        graphonL1Dist (A n) U < ε m :=
      (tendsto_order.1 hProfileRaw).2 (ε m) (hεpos m)
    have hred' : ∀ᶠ n in atTop,
        graphonRandomMass U / 2 < (φ n).normalizedRedArea :=
      (tendsto_order.1 hRedRaw).1 (graphonRandomMass U / 2)
        (by linarith [PU.randomMass_pos])
    filter_upwards [hlarge, hNear m, hclose', hred'] with n hn hnear hclose hred
    exact ⟨hn, hnear, hclose.le, hred.le⟩
  obtain ⟨σ, hσ, hσTop, hσGood⟩ :=
    Graphon.exists_strictMono_selection_of_eventually hGood

  have hApply : ∀ m, ∃ Cstar : ColoredGraph
      (Fin (optimizerSelectedClusterCount bridge σ m)),
      Cstar ∈ ColoredGraph.extremalFamily k
          (optimizerSelectedClusterCount bridge σ m) ∧
        ((optimizerTypeColoring bridge σ m).coloringHammingDistance Cstar : ℝ) ≤
          ε m * (optimizerSelectedClusterCount bridge σ m : ℝ) ^ 2 := by
    intro m
    apply hstability m
    · simpa [q, optimizerSelectedClusterCount] using (hσGood m).1
    · exact optimizerTypeColoring_mem_Ck hk bridge σ m
    · change -(inputDelta m * (q (σ m) : ℝ) ^ 2) ≤
        (ColoredGraph.objective k (φ (σ m)) : ℝ)
      exact (hσGood m).2.1
  choose ψ hψmem hψdist using hApply
  let E : (m : ℕ) → ColoredGraph.ExtremalFamilyWitness k
      (optimizerSelectedClusterCount bridge σ m) (ψ m) := fun m ↦
    Classical.choice (show Nonempty
      (ColoredGraph.ExtremalFamilyWitness k
        (optimizerSelectedClusterCount bridge σ m) (ψ m)) from hψmem m)

  have hProfileSelected :=
    optimizerTypeProfileGraphon_l1_tendsto bridge hσTop PU hsep₀ hsep₁
  have hAreasSelected :=
    optimizerTypeColoring_areas_tendsto bridge PU hProfileSelected
  have hRedSelected := hAreasSelected.1
  have hBlueSelected := hAreasSelected.2
  have hObjectiveSelected :=
    optimizerTypeColoring_normalizedObjective_tendsto
      bridge hσTop PU hRedSelected hBlueSelected

  let ratio : ℕ → ℝ := fun m ↦
    ((optimizerTypeColoring bridge σ m).coloringHammingDistance (ψ m) : ℝ) /
      (optimizerSelectedClusterCount bridge σ m : ℝ) ^ 2
  have hratio_nonneg : ∀ m, 0 ≤ ratio m := by
    intro m
    exact div_nonneg (Nat.cast_nonneg _)
      (sq_nonneg (optimizerSelectedClusterCount bridge σ m : ℝ))
  have hratio_le : ∀ m, ratio m ≤ ε m := by
    intro m
    have hqReal : 0 < (optimizerSelectedClusterCount bridge σ m : ℝ) := by
      exact_mod_cast optimizerSelectedClusterCount_pos bridge σ m
    have hqSq : 0 <
        (optimizerSelectedClusterCount bridge σ m : ℝ) ^ 2 :=
      sq_pos_of_pos hqReal
    change
      ((optimizerTypeColoring bridge σ m).coloringHammingDistance (ψ m) : ℝ) /
          (optimizerSelectedClusterCount bridge σ m : ℝ) ^ 2 ≤ ε m
    rw [div_le_iff₀ hqSq]
    exact hψdist m
  have hratio : Tendsto ratio atTop (nhds 0) :=
    squeeze_zero hratio_nonneg hratio_le hεzero

  have hprofileEdit : Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerTypeProfileGraphon bridge σ PU m)
        (optimizerExtremalProfileGraphon PU (ψ m)))
      atTop (nhds 0) := by
    have hupper : Tendsto (fun m ↦ 2 * ratio m) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hratio
    have hle : ∀ m,
        graphonL1Dist
            (optimizerTypeProfileGraphon bridge σ PU m)
            (optimizerExtremalProfileGraphon PU (ψ m)) ≤
          2 * ratio m := by
      intro m
      have hm := graphonL1Dist_profileColoringGraphon_le
        (optimizerSelectedClusterCount_pos bridge σ m)
        PU.randomMean (optimizerTypeColoring bridge σ m) (ψ m)
        ⟨PU.randomMean_pos.le, PU.randomMean_lt_one.le⟩
      rw [mul_div_assoc] at hm
      simpa [optimizerTypeProfileGraphon, optimizerExtremalProfileGraphon,
        ratio] using hm
    exact squeeze_zero (fun m ↦ graphonL1Dist_nonneg _ _) hle hupper
  have hExtremalProfile : Tendsto
      (fun m ↦ graphonL1Dist
        (optimizerExtremalProfileGraphon PU (ψ m)) U)
      atTop (nhds 0) := by
    have hupper : Tendsto
        (fun m ↦
          graphonL1Dist
              (optimizerExtremalProfileGraphon PU (ψ m))
              (optimizerTypeProfileGraphon bridge σ PU m) +
            graphonL1Dist (optimizerTypeProfileGraphon bridge σ PU m) U)
        atTop (nhds 0) := by
      have hedge : Tendsto
          (fun m ↦ graphonL1Dist
            (optimizerExtremalProfileGraphon PU (ψ m))
            (optimizerTypeProfileGraphon bridge σ PU m))
          atTop (nhds 0) := by
        apply hprofileEdit.congr'
        filter_upwards [] with m
        exact graphonL1Dist_comm _ _
      simpa using hedge.add hProfileSelected
    exact squeeze_zero (fun m ↦ graphonL1Dist_nonneg _ _)
      (fun m ↦ graphonL1Dist_triangle _ _ _) hupper

  have hredDiff : Tendsto
      (fun m ↦
        (optimizerTypeColoring bridge σ m).normalizedRedArea -
          (ψ m).normalizedRedArea)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun m ↦ 2 * ratio m) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hratio
    have hlower : Tendsto (fun m ↦ -(2 * ratio m)) atTop (nhds 0) := by
      simpa using hupper.neg
    apply Filter.Tendsto.squeeze hlower hupper
    · intro m
      have hm := ColoredGraph.abs_normalizedRedArea_sub_le_hamming
        (optimizerSelectedClusterCount_pos bridge σ m)
        (optimizerTypeColoring bridge σ m) (ψ m)
      rw [mul_div_assoc] at hm
      exact (abs_le.mp (by simpa [ratio] using hm)).1
    · intro m
      have hm := ColoredGraph.abs_normalizedRedArea_sub_le_hamming
        (optimizerSelectedClusterCount_pos bridge σ m)
        (optimizerTypeColoring bridge σ m) (ψ m)
      rw [mul_div_assoc] at hm
      exact (abs_le.mp (by simpa [ratio] using hm)).2
  have hblueDiff : Tendsto
      (fun m ↦
        (optimizerTypeColoring bridge σ m).normalizedBlueDiagonalArea -
          (ψ m).normalizedBlueDiagonalArea)
      atTop (nhds 0) := by
    have hupper : Tendsto (fun m ↦ 2 * ratio m) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (2 : ℝ))).mul hratio
    have hlower : Tendsto (fun m ↦ -(2 * ratio m)) atTop (nhds 0) := by
      simpa using hupper.neg
    apply Filter.Tendsto.squeeze hlower hupper
    · intro m
      have hm := ColoredGraph.abs_normalizedBlueDiagonalArea_sub_le_hamming
        (optimizerSelectedClusterCount_pos bridge σ m)
        (optimizerTypeColoring bridge σ m) (ψ m)
      rw [mul_div_assoc] at hm
      exact (abs_le.mp (by simpa [ratio] using hm)).1
    · intro m
      have hm := ColoredGraph.abs_normalizedBlueDiagonalArea_sub_le_hamming
        (optimizerSelectedClusterCount_pos bridge σ m)
        (optimizerTypeColoring bridge σ m) (ψ m)
      rw [mul_div_assoc] at hm
      exact (abs_le.mp (by simpa [ratio] using hm)).2
  have hExtremalRed : Tendsto (fun m ↦ (ψ m).normalizedRedArea)
      atTop (nhds (graphonRandomMass U)) := by
    have h := hRedSelected.sub hredDiff
    simpa [U] using h
  have hExtremalBlue : Tendsto
      (fun m ↦ (ψ m).normalizedBlueDiagonalArea)
      atTop (nhds (graphonOneMass U)) := by
    have h := hBlueSelected.sub hblueDiff
    simpa [U] using h

  have hExtremalObjective : Tendsto
      (fun m ↦ normalizedObjective k (ψ m)) atTop (nhds 0) := by
    have hrecip : Tendsto
        (fun m ↦ 1 / (optimizerSelectedClusterCount bridge σ m : ℝ))
        atTop (nhds 0) := by
      apply (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      exact optimizerSelectedClusterCount_tendsto bridge hσTop
    have hexpr :=
      (hExtremalRed.sub
        ((tendsto_const_nhds (x := (delta k : ℝ))).mul hExtremalBlue)).add
        ((tendsto_const_nhds (x := (delta k : ℝ))).mul hrecip)
    have hlimit : graphonRandomMass U -
        (delta k : ℝ) * graphonOneMass U = 0 := by
      simpa [delta] using sub_eq_zero.mpr PU.randomMass_eq_delta_mul_oneMass
    simp only [mul_zero, sub_zero, add_zero] at hexpr
    rw [hlimit] at hexpr
    apply hexpr.congr'
    filter_upwards [] with m
    simpa [div_eq_mul_inv] using
      (normalizedObjective_eq k
        (optimizerSelectedClusterCount_pos bridge σ m) (ψ m)).symm

  have hCorePos : ∀ m, 0 < (E m).coreCount := by
    intro m
    have harea := ColoredGraph.abs_normalizedRedArea_sub_le_hamming
      (optimizerSelectedClusterCount_pos bridge σ m)
      (optimizerTypeColoring bridge σ m) (ψ m)
    rw [mul_div_assoc] at harea
    have harea' :
        (optimizerTypeColoring bridge σ m).normalizedRedArea -
            (ψ m).normalizedRedArea ≤ 2 * ε m := by
      calc
        _ ≤ 2 * ratio m := (abs_le.mp (by simpa [ratio] using harea)).2
        _ ≤ 2 * ε m := by gcongr; exact hratio_le m
    have hredSelected : graphonRandomMass U / 2 ≤
        (optimizerTypeColoring bridge σ m).normalizedRedArea := by
      convert (hσGood m).2.2.2 using 1 <;>
        simp [q, φ, optimizerSelectedClusterCount, optimizerTypeColoring]
    have hεcap : ε m ≤ graphonRandomMass U / 16 :=
      optimizerStabilityError_le_randomMass_div_sixteen U m
    have hredψ : 0 < (ψ m).normalizedRedArea := by
      nlinarith [PU.randomMass_pos]
    exact (E m).coreCount_pos_of_normalizedRedArea_pos hredψ

  refine ⟨{
    target := U
    target_cut_eq_zero := hcut
    target_optimizer := hUopt
    profile := PU
    threshold := θ
    threshold_pos := hθpos
    threshold_lt_half := hθhalf
    threshold_separates := ⟨hsep₀, hsep₁⟩
    bridge := bridge
    target_eq_bridge_l1Limit := rfl
    extraction := σ
    extraction_strictMono := hσ
    selectedClusterCount_pos := optimizerSelectedClusterCount_pos bridge σ
    selectedClusterCount_tendsto :=
      optimizerSelectedClusterCount_tendsto bridge hσTop
    typeColoring_mem_Ck := optimizerTypeColoring_mem_Ck hk bridge σ
    typeProfile_l1_tendsto := hProfileSelected
    typeRedArea_tendsto := hRedSelected
    typeBlueArea_tendsto := hBlueSelected
    typeObjective_tendsto := hObjectiveSelected
    extremalColoring := ψ
    extremal_mem := hψmem
    extremalWitness := E
    extremal_coreCount_pos := hCorePos
    hamming_ratio_tendsto := hratio
    extremalProfile_l1_tendsto := hExtremalProfile
    extremalRedArea_tendsto := hExtremalRed
    extremalBlueArea_tendsto := hExtremalBlue
    extremalObjective_tendsto := hExtremalObjective }⟩

end InducedStars
