import InducedStars.FiniteModels.GraphonLimits
import InducedStars.FiniteModels.WRandom
import InducedStars.Graphon.Equivalence
import InducedStars.Graphon.FlexibleBand
import InducedStars.PriorLiterature
import Mathlib.MeasureTheory.Constructions.SimpleGraph
import Mathlib.Tactic

/-!
# Abundance of flexible pairs in graphon samples

This file packages the finite probabilistic bridge used by the exact-edge
repair.  A closed positive-mass band of a graphon determines a deterministic
graph on the sampled latent points.  Sampling the corresponding {0,1}-valued
band graphon produces that graph almost surely.  The BCLSV sampled-graph
cut-convergence theorem then gives both abundance of band pairs and the
usual concentration of the exactly normalized sampled edge count.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Classical

namespace InducedStars

/-! ## The deterministic graph of flexible latent pairs -/

/-- The simple graph whose edges are the latent pairs on which `W` takes a
value in the closed band `[L,U]`. -/
noncomputable def flexiblePairGraph {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ L ≤ W.value (x i, x j) ∧ W.value (x i, x j) ≤ U
  symm.symm i j hij := by
    refine ⟨hij.1.symm, ?_⟩
    rw [← W.value_symm (x i) (x j)]
    exact hij.2
  loopless.irrefl i hi := hi.1 rfl

@[simp]
theorem flexiblePairGraph_adj {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) (i j : Fin n) :
    (flexiblePairGraph W L U x).Adj i j ↔
      i ≠ j ∧ L ≤ W.value (x i, x j) ∧ W.value (x i, x j) ≤ U :=
  Iff.rfl

/-- The finite set of unordered flexible latent pairs. -/
noncomputable def flexiblePairFinset {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) : Finset (Sym2 (Fin n)) :=
  finiteGraphEdges (flexiblePairGraph W L U x)

/-- The number of unordered flexible latent pairs. -/
noncomputable def flexiblePairCount {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) : ℕ :=
  (flexiblePairFinset W L U x).card

@[simp]
theorem mk_mem_flexiblePairFinset {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) (i j : Fin n) :
    s(i, j) ∈ flexiblePairFinset W L U x ↔
      i ≠ j ∧ L ≤ W.value (x i, x j) ∧ W.value (x i, x j) ≤ U := by
  simp [flexiblePairFinset]

@[simp]
theorem finiteGraphEdges_flexiblePairGraph {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) :
    finiteGraphEdges (flexiblePairGraph W L U x) =
      flexiblePairFinset W L U x :=
  rfl

@[simp]
theorem edgeCount_flexiblePairGraph {n : ℕ} (W : Graphon) (L U : ℝ)
    (x : Fin n → UnitInterval) :
    (finiteGraphEdges (flexiblePairGraph W L U x)).card =
      flexiblePairCount W L U x :=
  rfl

/-- Ordered-square normalization of the flexible-pair count. -/
noncomputable def normalizedFlexiblePairCount {n : ℕ} (W : Graphon)
    (L U : ℝ) (x : Fin n → UnitInterval) : ℝ :=
  2 * (flexiblePairCount W L U x : ℝ) / (n : ℝ) ^ 2

@[measurability, fun_prop]
theorem measurable_flexiblePairGraph {n : ℕ} (W : Graphon) (L U : ℝ) :
    Measurable (flexiblePairGraph W L U :
      (Fin n → UnitInterval) → SimpleGraph (Fin n)) := by
  rw [SimpleGraph.measurable_iff_adj]
  intro i j
  by_cases hij : i = j
  · subst j
    simp
  · simp only [flexiblePairGraph_adj, hij, true_and]
    fun_prop

@[measurability, fun_prop]
theorem measurable_flexiblePairFinset {n : ℕ} (W : Graphon) (L U : ℝ) :
    Measurable (flexiblePairFinset W L U :
      (Fin n → UnitInterval) → Finset (Sym2 (Fin n))) := by
  rw [measurable_finset_iff]
  intro e
  induction e using Sym2.inductionOn with
  | _ i j =>
      by_cases hij : i = j
      · subst j
        simp
      · simp only [mk_mem_flexiblePairFinset, hij, true_and]
        fun_prop

@[measurability, fun_prop]
theorem measurable_flexiblePairCount {n : ℕ} (W : Graphon) (L U : ℝ) :
    Measurable (flexiblePairCount W L U : (Fin n → UnitInterval) → ℕ) := by
  exact (measurable_of_countable
    (fun s : Finset (Sym2 (Fin n)) ↦ s.card)).comp
      (measurable_flexiblePairFinset W L U)

@[measurability, fun_prop]
theorem measurable_normalizedFlexiblePairCount {n : ℕ}
    (W : Graphon) (L U : ℝ) :
    Measurable (normalizedFlexiblePairCount W L U :
      (Fin n → UnitInterval) → ℝ) := by
  unfold normalizedFlexiblePairCount
  fun_prop

/-! ## The band graphon samples the flexible-pair graph -/

private theorem flexibleBandGraphon_pairValue_ae_eq_indicator {n : ℕ}
    (W : Graphon) (L U : ℝ) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    ∀ᵐ x : Fin n → UnitInterval ∂volume,
      graphonPairValue (flexibleBandGraphon W L U) x e =
        if e ∈ flexiblePairFinset W L U x then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ i j =>
      have hij : i ≠ j := by
        simpa only [Sym2.mk_isDiag_iff] using he
      have hpull :=
        (measurePreserving_pairProjection hij).quasiMeasurePreserving.ae
          (flexibleBandGraphon_value_ae_eq_ite W L U)
      filter_upwards [hpull] with x hx
      simpa [hij] using hx

/-- Conditional on almost every latent sample, the band graphon assigns
probability one to the corresponding flexible-pair graph. -/
theorem wRandomConditionalWeight_flexibleBandGraphon_eq_one_ae {n : ℕ}
    (W : Graphon) (L U : ℝ) :
    ∀ᵐ x : Fin n → UnitInterval ∂volume,
      wRandomConditionalWeight (flexibleBandGraphon W L U) x
        (flexiblePairGraph W L U x) = 1 := by
  classical
  have hall : ∀ᵐ x : Fin n → UnitInterval ∂volume,
      ∀ e : Sym2 (Fin n), ¬ e.IsDiag →
        graphonPairValue (flexibleBandGraphon W L U) x e =
          if e ∈ flexiblePairFinset W L U x then 1 else 0 := by
    apply Filter.eventually_all.2
    intro e
    by_cases he : ¬ e.IsDiag
    · exact (flexibleBandGraphon_pairValue_ae_eq_indicator W L U e he).mono
        fun _ hx _ ↦ hx
    · exact ae_of_all _ fun _ he' ↦ (he he').elim
  filter_upwards [hall] with x hx
  unfold wRandomConditionalWeight graphonInducedIntegrand
  rw [show (∏ e ∈ finiteGraphEdges (flexiblePairGraph W L U x),
      graphonPairValue (flexibleBandGraphon W L U) x e) = 1 by
        apply Finset.prod_eq_one
        intro e he
        have heSet : e ∈ (flexiblePairGraph W L U x).edgeSet :=
          (mem_finiteGraphEdges (flexiblePairGraph W L U x) e).mp he
        have hne :=
          (flexiblePairGraph W L U x).not_isDiag_of_mem_edgeSet heSet
        have hmem : e ∈ flexiblePairFinset W L U x := by
          simpa only [finiteGraphEdges_flexiblePairGraph] using he
        rw [hx e hne, if_pos hmem],
      show (∏ e ∈ finiteGraphEdges (flexiblePairGraph W L U x)ᶜ,
        (1 - graphonPairValue (flexibleBandGraphon W L U) x e)) = 1 by
        apply Finset.prod_eq_one
        intro e he
        have heSet : e ∈ (flexiblePairGraph W L U x)ᶜ.edgeSet :=
          (mem_finiteGraphEdges (flexiblePairGraph W L U x)ᶜ e).mp he
        have hne :=
          (flexiblePairGraph W L U x)ᶜ.not_isDiag_of_mem_edgeSet heSet
        have hnot : e ∉ flexiblePairFinset W L U x := by
          induction e using Sym2.inductionOn with
          | _ i j =>
              have heAdj :
                  (flexiblePairGraph W L U x)ᶜ.Adj i j := by
                simpa only [SimpleGraph.mem_edgeSet] using heSet
              intro hflex
              have hAdj : (flexiblePairGraph W L U x).Adj i j := by
                change i ≠ j ∧ L ≤ W.value (x i, x j) ∧
                  W.value (x i, x j) ≤ U
                exact (mk_mem_flexiblePairFinset W L U x i j).mp hflex
              exact ((SimpleGraph.compl_adj _ _ _).mp heAdj).2 hAdj
        rw [hx e hne, if_neg hnot]
        norm_num]
  norm_num

/-- The full almost-everywhere deterministic sampling law for the band
graphon, stated as a conditional-mass indicator. -/
theorem wRandomConditionalWeight_flexibleBandGraphon_ae_eq_indicator {n : ℕ}
    (W : Graphon) (L U : ℝ) (G : SimpleGraph (Fin n)) :
    ∀ᵐ x : Fin n → UnitInterval ∂volume,
      wRandomConditionalWeight (flexibleBandGraphon W L U) x G =
        if G = flexiblePairGraph W L U x then 1 else 0 := by
  classical
  filter_upwards [wRandomConditionalWeight_flexibleBandGraphon_eq_one_ae
    (n := n) W L U] with x hdet
  by_cases hG : G = flexiblePairGraph W L U x
  · subst G
    simp only [hdet, ite_true]
  · rw [if_neg hG]
    let D := flexiblePairGraph W L U x
    let p : SimpleGraph (Fin n) → ℝ :=
      fun H ↦ wRandomConditionalWeight (flexibleBandGraphon W L U) x H
    have hsum : ∑ H : SimpleGraph (Fin n), p H = 1 :=
      sum_wRandomConditionalWeight (flexibleBandGraphon W L U) x
    have hD : p D = 1 := by
      simpa only [p, D] using hdet
    have herase := Finset.sum_erase_add Finset.univ p (Finset.mem_univ D)
    have hsumErase : ∑ H ∈ Finset.univ.erase D, p H = 0 := by
      rw [hsum, hD] at herase
      linarith
    have hGmem : G ∈ Finset.univ.erase D := by
      exact Finset.mem_erase.mpr ⟨by simpa only [D] using hG, Finset.mem_univ G⟩
    have hle : p G ≤ ∑ H ∈ Finset.univ.erase D, p H :=
      Finset.single_le_sum
        (fun H _ ↦ wRandomConditionalWeight_nonneg
          (flexibleBandGraphon W L U) x H) hGmem
    have hpzero : p G = 0 := le_antisymm (hle.trans_eq hsumErase)
      (wRandomConditionalWeight_nonneg (flexibleBandGraphon W L U) x G)
    simpa only [p] using hpzero

/-- Every set of labeled simple graphs on a finite vertex type is measurable
for Mathlib's adjacency-generated measurable structure. -/
theorem measurableSet_simpleGraph_fin {n : ℕ}
    (A : Set (SimpleGraph (Fin n))) : MeasurableSet A := by
  have hImage :
      MeasurableSet (SimpleGraph.edgeSet '' A : Set (Set (Sym2 (Fin n)))) :=
    (Set.to_countable _).measurableSet
  have hPreimage := SimpleGraph.measurable_edgeSet hImage
  simpa only [Set.preimage_image_eq A SimpleGraph.edgeSet_injective]
    using hPreimage

/-- Under the band graphon, every graph-only event is exactly the pullback
of that event along the deterministic flexible-pair graph. -/
theorem wRandomGraphEventProbability_flexibleBandGraphon {n : ℕ}
    (W : Graphon) (L U : ℝ) (A : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability (flexibleBandGraphon W L U) A =
      wRandomLatentEventProbability
        {x : Fin n → UnitInterval | flexiblePairGraph W L U x ∈ A} := by
  classical
  let B : Set (Fin n → UnitInterval) :=
    {x | flexiblePairGraph W L U x ∈ A}
  have hB : MeasurableSet B :=
    (measurable_flexiblePairGraph W L U)
      (measurableSet_simpleGraph_fin A)
  calc
    wRandomGraphEventProbability (flexibleBandGraphon W L U) A =
        wRandomJointEventProbability (flexibleBandGraphon W L U)
          (WRandomJointEvent.ofGraphSet A) :=
      (wRandomJointEventProbability_ofGraphSet
        (flexibleBandGraphon W L U) A).symm
    _ = wRandomJointEventProbability (flexibleBandGraphon W L U)
          (WRandomJointEvent.ofLatentSet B hB) := by
      unfold wRandomJointEventProbability
      apply integral_congr_ae
      have hall : ∀ᵐ x : Fin n → UnitInterval ∂volume,
          ∀ G : SimpleGraph (Fin n),
            wRandomConditionalWeight (flexibleBandGraphon W L U) x G =
              if G = flexiblePairGraph W L U x then 1 else 0 := by
        exact Filter.eventually_all.2 fun G ↦
          wRandomConditionalWeight_flexibleBandGraphon_ae_eq_indicator
            W L U G
      filter_upwards [hall] with x hx
      unfold wRandomJointEventIntegrand WRandomJointEvent.ofGraphSet
        WRandomJointEvent.ofLatentSet
      simp_rw [hx]
      let D := flexiblePairGraph W L U x
      have hRight :
          (∑ G : SimpleGraph (Fin n),
            if x ∈ B then
              (if G = flexiblePairGraph W L U x then (1 : ℝ) else 0)
            else 0) = if D ∈ A then 1 else 0 := by
        by_cases hD : D ∈ A
        · simp [B, D, hD]
        · simp [B, D, hD]
      rw [hRight]
      change (∑ G : SimpleGraph (Fin n),
        if G ∈ A then (if G = D then 1 else 0) else 0) =
          if D ∈ A then 1 else 0
      by_cases hD : D ∈ A
      · rw [if_pos hD]
        rw [Finset.sum_eq_single D]
        · simp [hD]
        · intro G _hG hGD
          simp [hGD]
        · simp
      · rw [if_neg hD]
        apply Finset.sum_eq_zero
        intro G _hG
        by_cases hGA : G ∈ A
        · have hGD : G ≠ D := by
            intro hEq
            exact hD (hEq ▸ hGA)
          simp [hGA, hGD]
        · simp [hGA]
    _ = wRandomLatentEventProbability B :=
      wRandomJointEventProbability_ofLatentSet
        (flexibleBandGraphon W L U) B hB
    _ = wRandomLatentEventProbability
          {x : Fin n → UnitInterval | flexiblePairGraph W L U x ∈ A} := rfl

/-! ## Edge density is controlled by cut distance -/

/-- The full unit-square cut. -/
private def fullMeasurableCut : MeasurableCut where
  left := Set.univ
  right := Set.univ
  measurable_left := MeasurableSet.univ
  measurable_right := MeasurableSet.univ

/-- The full-cut integral of a graphon difference is its edge-density
difference. -/
private theorem cutIntegral_graphon_sub_full (U W : Graphon) :
    cutIntegral (U.toL1 - W.toL1) fullMeasurableCut =
      graphonEdgeDensity U - graphonEdgeDensity W := by
  rw [cutIntegral]
  simp only [fullMeasurableCut, MeasurableCut.rectangle,
    Set.univ_prod_univ, Measure.restrict_univ]
  calc
    (∫ z : UnitSquare, (U.toL1 - W.toL1) z ∂unitSquareMeasure) =
        ∫ z : UnitSquare, (U z - W z) ∂unitSquareMeasure := by
      exact integral_congr_ae (Lp.coeFn_sub U.toL1 W.toL1)
    _ = (∫ z : UnitSquare, U z ∂unitSquareMeasure) -
          ∫ z : UnitSquare, W z ∂unitSquareMeasure := by
      exact integral_sub (L1.integrable_coeFn U.toL1)
        (L1.integrable_coeFn W.toL1)
    _ = graphonEdgeDensity U - graphonEdgeDensity W := by
      rw [← graphonEdgeDensity_eq_integral,
        ← graphonEdgeDensity_eq_integral]

/-- The difference of two graphon edge densities is bounded by the cut norm
of their representative difference. -/
theorem abs_graphonEdgeDensity_sub_le_cutNorm (U W : Graphon) :
    |graphonEdgeDensity U - graphonEdgeDensity W| ≤
      cutNorm (U.toL1 - W.toL1) := by
  rw [← cutIntegral_graphon_sub_full]
  exact abs_cutIntegral_le_cutNorm _ _

/-- Edge density is 1-Lipschitz for graphon cut distance. -/
theorem abs_graphonEdgeDensity_sub_le_cutDist (U W : Graphon) :
    |graphonEdgeDensity U - graphonEdgeDensity W| ≤ cutDist U W := by
  let a : NNReal :=
    ⟨|graphonEdgeDensity U - graphonEdgeDensity W|, abs_nonneg _⟩
  have ha : a ≤ cutDistNN U W := by
    unfold cutDistNN
    apply le_ciInf
    intro e
    apply NNReal.coe_le_coe.mp
    change |graphonEdgeDensity U - graphonEdgeDensity W| ≤
      cutNorm (relabelKernel U.toL1 e - W.toL1)
    have h := abs_graphonEdgeDensity_sub_le_cutNorm (U.relabel e) W
    rw [Graphon.relabel_toL1] at h
    have hDensity : graphonEdgeDensity (U.relabel e) =
        graphonEdgeDensity U :=
      graphonEdgeDensity_eq_of_cutDist_eq_zero (U.relabel e) U
        (cutDist_relabel_self U e)
    simpa only [hDensity] using h
  exact_mod_cast ha

/-! ## Sampled edge-count concentration -/

/-- BCLSV cut convergence implies convergence in probability of sampled
graphon edge density. -/
theorem wRandomGraphEdgeDensity_convergenceInProbability
    (W : Graphon) (ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          ε ≤ |graphonEdgeDensity (graphGraphon G) -
            graphonEdgeDensity W|})
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro n
    exact wRandomGraphEventProbability_nonneg W _
  · intro n
    apply wRandomGraphEventProbability_mono W
    intro G hG
    exact hG.trans (abs_graphonEdgeDensity_sub_le_cutDist
      (graphGraphon G) W)
  · exact PriorLiterature.bclsvWRandomGraphCutConvergenceInProbability
      W ε hε

/-- Exact finite normalization of sampled edge-count concentration: the
quantity converging to `γ` is `2 |E(G)| / n²`, exactly the edge density of
`graphGraphon G`. -/
theorem wRandomGraphNormalizedEdgeCount_convergenceInProbability
    (W : Graphon) (γ ε : ℝ) (hDensity : graphonEdgeDensity W = γ)
    (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          ε ≤ |2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 - γ|})
      atTop (nhds 0) := by
  have hEdge := wRandomGraphEdgeDensity_convergenceInProbability W ε hε
  apply hEdge.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  apply congrArg (wRandomGraphEventProbability W)
  ext G
  simp only [Set.mem_setOf_eq]
  rw [graphonEdgeDensity_graphGraphon hn, hDensity]

/-! ## Flexible-pair abundance -/

/-- The normalized number of latent pairs in a closed band converges in
probability to the measure of that band. -/
theorem normalizedFlexiblePairCount_convergenceInProbability
    (W : Graphon) (L U ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomLatentEventProbability
        {x : Fin n → UnitInterval |
          ε ≤ |normalizedFlexiblePairCount W L U x -
            graphonClosedBandMass W L U|})
      atTop (nhds 0) := by
  have hGraph :=
    wRandomGraphNormalizedEdgeCount_convergenceInProbability
      (flexibleBandGraphon W L U) (graphonClosedBandMass W L U) ε
      (graphonEdgeDensity_flexibleBandGraphon W L U) hε
  apply hGraph.congr'
  filter_upwards [] with n
  rw [wRandomGraphEventProbability_flexibleBandGraphon]
  apply congrArg wRandomLatentEventProbability
  ext x
  simp only [Set.mem_setOf_eq, normalizedFlexiblePairCount,
    edgeCount_flexiblePairGraph]

/-- Product-volume probability of a measurable latent-event complement. -/
theorem wRandomLatentEventProbability_compl {n : ℕ}
    (A : Set (Fin n → UnitInterval)) (hA : MeasurableSet A) :
    wRandomLatentEventProbability Aᶜ =
      1 - wRandomLatentEventProbability A := by
  unfold wRandomLatentEventProbability
  rw [measureReal_compl hA]
  simp

/-- Equivalent high-probability form of normalized flexible-pair
convergence: every fixed open error window has probability tending to one. -/
theorem normalizedFlexiblePairCount_close_probability_tendsto_one
    (W : Graphon) (L U ε : ℝ) (hε : 0 < ε) :
    Tendsto
      (fun n ↦ wRandomLatentEventProbability
        {x : Fin n → UnitInterval |
          |normalizedFlexiblePairCount W L U x -
            graphonClosedBandMass W L U| < ε})
      atTop (nhds 1) := by
  let bad : (n : ℕ) → Set (Fin n → UnitInterval) := fun n ↦
    {x | ε ≤ |normalizedFlexiblePairCount W L U x -
      graphonClosedBandMass W L U|}
  have hTail : Tendsto
      (fun n ↦ wRandomLatentEventProbability (bad n))
      atTop (nhds 0) := by
    simpa only [bad] using
      normalizedFlexiblePairCount_convergenceInProbability W L U ε hε
  have hOneMinus : Tendsto
      (fun n ↦ 1 - wRandomLatentEventProbability (bad n))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hTail
  apply hOneMinus.congr'
  filter_upwards [] with n
  have hBad : MeasurableSet (bad n) := by
    dsimp only [bad]
    measurability
  have hSet :
      {x : Fin n → UnitInterval |
        |normalizedFlexiblePairCount W L U x -
          graphonClosedBandMass W L U| < ε} = (bad n)ᶜ := by
    ext x
    simp only [bad, Set.mem_setOf_eq, Set.mem_compl_iff, not_le]
  rw [hSet, wRandomLatentEventProbability_compl (bad n) hBad]

/-- A positive-mass closed band contains a positive normalized fraction of
the sampled latent pairs with probability tending to one.  The threshold is
half of the limiting band mass. -/
theorem flexiblePairAbundance_probability_tendsto_one
    (W : Graphon) (L U : ℝ)
    (hMass : 0 < graphonClosedBandMass W L U) :
    Tendsto
      (fun n ↦ wRandomLatentEventProbability
        {x : Fin n → UnitInterval |
          graphonClosedBandMass W L U / 2 <
            normalizedFlexiblePairCount W L U x})
      atTop (nhds 1) := by
  have hClose :=
    normalizedFlexiblePairCount_close_probability_tendsto_one W L U
      (graphonClosedBandMass W L U / 2) (half_pos hMass)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hClose tendsto_const_nhds
  · filter_upwards [] with n
    unfold wRandomLatentEventProbability
    refine measureReal_mono ?_ (by finiteness)
    intro x hx
    change |normalizedFlexiblePairCount W L U x -
      graphonClosedBandMass W L U| <
        graphonClosedBandMass W L U / 2 at hx
    change graphonClosedBandMass W L U / 2 <
      normalizedFlexiblePairCount W L U x
    have hLower := (abs_lt.mp hx).1
    linarith
  · filter_upwards [] with n
    unfold wRandomLatentEventProbability
    exact measureReal_le_one

/-- Eventual positive-probability version of flexible-pair abundance, with
the explicit uniform probability lower bound `1/2`. -/
theorem eventually_flexiblePairAbundance_positiveFraction
    (W : Graphon) (L U : ℝ)
    (hMass : 0 < graphonClosedBandMass W L U) :
    ∀ᶠ n in atTop,
      (1 : ℝ) / 2 < wRandomLatentEventProbability
        {x : Fin n → UnitInterval |
          graphonClosedBandMass W L U / 2 <
            normalizedFlexiblePairCount W L U x} := by
  exact (flexiblePairAbundance_probability_tendsto_one W L U hMass).eventually
    (Ioi_mem_nhds (by norm_num))

end InducedStars
