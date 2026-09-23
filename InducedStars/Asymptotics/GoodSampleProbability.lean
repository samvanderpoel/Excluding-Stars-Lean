import InducedStars.Asymptotics.GoodSupportedGraphs
import InducedStars.Asymptotics.SampledEdgeCount
import InducedStars.FiniteModels.ConditionalConcentration
import InducedStars.FiniteModels.WRandomEvents
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# High-probability good samples for exact-edge repair

This file combines the independent probabilistic inputs in the fixed-density
transfer.  Flexible-pair abundance and the two conditional Chebyshev bounds
supply repair capacity, sampled edge-count concentration supplies the edit
radius, and BCLSV cut convergence supplies graphon proximity.  The
induced-free support condition is imposed only almost everywhere when the
joint event is projected to its finite graph marginal.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal

namespace InducedStars

/-! ## Deterministic scale conversion -/

/-- The number of unordered pairs is at most half the ordered square. -/
theorem completeEdgeCount_cast_le_half_square (n : ℕ) :
    (completeEdgeCount n : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
  rw [completeEdgeCount, Nat.cast_choose_two]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- On an abundant latent configuration, the canonical abundance radius and
every sufficiently smaller edit radius fit separately inside the present and
absent flexible-pair capacities. -/
theorem flexiblePairCapacity_of_abundant
    {n : ℕ} (hn : 0 < n) (W : Graphon) (L U η : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) (hη : 0 ≤ η)
    (hηPresent : η ≤ L * graphonClosedBandMass W L U / 4)
    (hηAbsent : η ≤
      (1 - U) * graphonClosedBandMass W L U / 4)
    (x : Fin n → UnitInterval) (G : SimpleGraph (Fin n))
    (hAbundant : x ∈ flexiblePairAbundantSet n W L U)
    (hPresent : L / 2 * (flexiblePairCount W L U x : ℝ) ≤
      ((presentFlexibleEdgeFinset W x L U G).card : ℝ))
    (hAbsent : (1 - U) / 2 * (flexiblePairCount W L U x : ℝ) ≤
      ((absentFlexibleEdgeFinset W x L U G).card : ℝ)) :
    fractionalEditRadius (graphonClosedBandMass W L U / 4)
        (completeEdgeCount n) ≤ flexiblePairCount W L U x ∧
      fractionalEditRadius η (completeEdgeCount n) ≤
        (presentFlexibleEdgeFinset W x L U G).card ∧
      fractionalEditRadius η (completeEdgeCount n) ≤
        (absentFlexibleEdgeFinset W x L U G).card := by
  let M : ℝ := graphonClosedBandMass W L U
  let F : ℝ := flexiblePairCount W L U x
  let N : ℝ := completeEdgeCount n
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnSq : 0 < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  have hAbundant' : M / 2 < 2 * F / (n : ℝ) ^ 2 := by
    change graphonClosedBandMass W L U / 2 <
      normalizedFlexiblePairCount W L U x at hAbundant
    simpa only [M, F, normalizedFlexiblePairCount] using hAbundant
  have hFBase : M * (n : ℝ) ^ 2 / 4 < F := by
    have hmul := (lt_div_iff₀ hnSq).mp hAbundant'
    nlinarith
  have hN : N ≤ (n : ℝ) ^ 2 / 2 := by
    simpa only [N] using completeEdgeCount_cast_le_half_square n
  have hM : 0 < M := by simpa only [M] using hMass
  have hqCast :
      (fractionalEditRadius (M / 4) (completeEdgeCount n) : ℝ) ≤
        M / 4 * N := by
    exact Nat.floor_le (mul_nonneg (div_nonneg hM.le (by norm_num))
      (Nat.cast_nonneg _))
  have hqReal :
      (fractionalEditRadius (M / 4) (completeEdgeCount n) : ℝ) < F := by
    calc
      (fractionalEditRadius (M / 4) (completeEdgeCount n) : ℝ) ≤
          M / 4 * N := hqCast
      _ ≤ M / 4 * ((n : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hN (div_nonneg hM.le (by norm_num))
      _ < F := by nlinarith
  have hq : fractionalEditRadius (M / 4) (completeEdgeCount n) ≤
      flexiblePairCount W L U x := by
    dsimp only [F] at hqReal
    exact_mod_cast hqReal.le
  have hηCast :
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) ≤ η * N := by
    exact Nat.floor_le (mul_nonneg hη (Nat.cast_nonneg _))
  have hPresentCore :
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) <
        L / 2 * F := by
    have hLF : L * M * (n : ℝ) ^ 2 / 8 < L / 2 * F := by
      have hmul := mul_lt_mul_of_pos_left hFBase (half_pos hL)
      nlinarith
    calc
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) ≤ η * N :=
        hηCast
      _ ≤ (L * M / 4) * N :=
        mul_le_mul_of_nonneg_right (by simpa only [M] using hηPresent)
          (by positivity)
      _ ≤ (L * M / 4) * ((n : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ < L / 2 * F := by
        convert hLF using 1 <;> ring
  have hAbsentCore :
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) <
        (1 - U) / 2 * F := by
    have hc : 0 < 1 - U := sub_pos.mpr hU
    have hcF : (1 - U) * M * (n : ℝ) ^ 2 / 8 <
        (1 - U) / 2 * F := by
      have hmul := mul_lt_mul_of_pos_left hFBase (half_pos hc)
      nlinarith
    calc
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) ≤ η * N :=
        hηCast
      _ ≤ ((1 - U) * M / 4) * N :=
        mul_le_mul_of_nonneg_right (by simpa only [M] using hηAbsent)
          (by positivity)
      _ ≤ ((1 - U) * M / 4) * ((n : ℝ) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ < (1 - U) / 2 * F := by
        convert hcF using 1 <;> ring
  have hPresentNat : fractionalEditRadius η (completeEdgeCount n) ≤
      (presentFlexibleEdgeFinset W x L U G).card := by
    exact_mod_cast hPresentCore.le.trans hPresent
  have hAbsentNat : fractionalEditRadius η (completeEdgeCount n) ≤
      (absentFlexibleEdgeFinset W x L U G).card := by
    exact_mod_cast hAbsentCore.le.trans hAbsent
  simpa only [M] using ⟨hq, hPresentNat, hAbsentNat⟩

/-! ## The combined failure event -/

/-- Failure of at least one property needed from a graphon sample: flexible
repair capacity, the prescribed edge-count window, or cut proximity. -/
def goodSampleFailureJointEvent (n : ℕ) (W : Graphon) (L U : ℝ)
    (m : ℕ) (η ξ : ℝ) : WRandomJointEvent n :=
  (flexibleRepairCapacityFailureJointEvent n W L U).union
    ((WRandomJointEvent.ofGraphSet
      {G : SimpleGraph (Fin n) |
        fractionalEditRadius η (completeEdgeCount n) <
          Nat.dist (finiteGraphEdges G).card m}).union
      (WRandomJointEvent.ofGraphSet
        {G : SimpleGraph (Fin n) | ξ ≤ cutDist (graphGraphon G) W}))

/-- The combined failure event has probability tending to zero. -/
theorem goodSampleFailure_probability_tendsto_zero
    (W : Graphon) (L U : ℝ) (m : ℕ → ℕ) (γ η ξ : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hDensity : graphonEdgeDensity W = γ)
    (hη : 0 < η) (hξ : 0 < ξ) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (goodSampleFailureJointEvent n W L U (m n) η ξ))
      atTop (nhds 0) := by
  have hCapacity := flexibleRepairCapacityFailure_probability_tendsto_zero
    W L U hL hU hMass
  have hEdgeGraph :=
    wRandomGraphEdgeCount_outsideFractionalRadius_probability_tendsto_zero
      W m γ η hm hDensity hη
  have hEdge : Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (WRandomJointEvent.ofGraphSet
          {G : SimpleGraph (Fin n) |
            fractionalEditRadius η (completeEdgeCount n) <
              Nat.dist (finiteGraphEdges G).card (m n)}))
      atTop (nhds 0) := by
    apply hEdgeGraph.congr'
    filter_upwards [] with n
    exact (wRandomJointEventProbability_ofGraphSet W _).symm
  have hCutGraph :=
    PriorLiterature.bclsvWRandomGraphCutConvergenceInProbability W ξ hξ
  have hCut : Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (WRandomJointEvent.ofGraphSet
          {G : SimpleGraph (Fin n) | ξ ≤ cutDist (graphGraphon G) W}))
      atTop (nhds 0) := by
    apply hCutGraph.congr'
    filter_upwards [] with n
    exact (wRandomJointEventProbability_ofGraphSet W _).symm
  apply squeeze_zero
  · intro n
    exact wRandomJointEventProbability_nonneg W _
  · intro n
    calc
      wRandomJointEventProbability W
          (goodSampleFailureJointEvent n W L U (m n) η ξ) ≤
          wRandomJointEventProbability W
              (flexibleRepairCapacityFailureJointEvent n W L U) +
            wRandomJointEventProbability W
              ((WRandomJointEvent.ofGraphSet
                {G : SimpleGraph (Fin n) |
                  fractionalEditRadius η (completeEdgeCount n) <
                    Nat.dist (finiteGraphEdges G).card (m n)}).union
                (WRandomJointEvent.ofGraphSet
                  {G : SimpleGraph (Fin n) |
                    ξ ≤ cutDist (graphGraphon G) W})) :=
        wRandomJointEventProbability_union_le W _ _
      _ ≤ wRandomJointEventProbability W
              (flexibleRepairCapacityFailureJointEvent n W L U) +
            (wRandomJointEventProbability W
                (WRandomJointEvent.ofGraphSet
                  {G : SimpleGraph (Fin n) |
                    fractionalEditRadius η (completeEdgeCount n) <
                      Nat.dist (finiteGraphEdges G).card (m n)}) +
              wRandomJointEventProbability W
                (WRandomJointEvent.ofGraphSet
                  {G : SimpleGraph (Fin n) |
                    ξ ≤ cutDist (graphGraphon G) W})) :=
        by
          gcongr
          exact wRandomJointEventProbability_union_le W _ _
  · simpa only [zero_add, add_zero] using hCapacity.add (hEdge.add hCut)

/-- The complement of the combined failure event has probability tending to
one. -/
theorem goodSampleReady_probability_tendsto_one
    (W : Graphon) (L U : ℝ) (m : ℕ → ℕ) (γ η ξ : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hDensity : graphonEdgeDensity W = γ)
    (hη : 0 < η) (hξ : 0 < ξ) :
    Tendsto
      (fun n ↦ wRandomJointEventProbability W
        (goodSampleFailureJointEvent n W L U (m n) η ξ).compl)
      atTop (nhds 1) := by
  have hFailure := goodSampleFailure_probability_tendsto_zero
    W L U m γ η ξ hL hU hMass hm hDensity hη hξ
  have hSub : Tendsto
      (fun n ↦ (1 : ℝ) - wRandomJointEventProbability W
        (goodSampleFailureJointEvent n W L U (m n) η ξ))
      atTop (nhds (1 - 0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ))
      atTop (nhds 1)).sub hFailure
  have hSub' : Tendsto
      (fun n ↦ (1 : ℝ) - wRandomJointEventProbability W
        (goodSampleFailureJointEvent n W L U (m n) η ξ))
      atTop (nhds 1) := by simpa using hSub
  apply hSub'.congr'
  filter_upwards [] with n
  exact (wRandomJointEventProbability_compl W _).symm

/-! ## Projection to the finite good-graph family -/

/-- At every nontrivial order, the ready joint event projects into the
finite family of good supported graphs.  The support theorem is used only
almost everywhere, exactly where its measure-theoretic statement applies. -/
theorem goodSampleReady_probability_le_goodSupportedGraphs
    {h n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin h)) (W : Graphon)
    (L U : ℝ) (m : ℕ) (η ξ : ℝ)
    (hfree : graphonInducedDensity H W = 0)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U)
    (hη : 0 ≤ η)
    (hηPresent : η ≤ L * graphonClosedBandMass W L U / 4)
    (hηAbsent : η ≤
      (1 - U) * graphonClosedBandMass W L U / 4) :
    wRandomJointEventProbability W
        (goodSampleFailureJointEvent n W L U m η ξ).compl ≤
      wRandomGraphEventProbability W
        {G : SimpleGraph (Fin n) |
          G ∈ goodSupportedGraphs H W L U m
            (fractionalEditRadius η (completeEdgeCount n))
            (fractionalEditRadius
              (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
            ξ n} := by
  rw [← wRandomJointEventProbability_ofGraphSet]
  unfold wRandomJointEventProbability
  apply integral_mono_ae
    (integrable_wRandomJointEventIntegrand W
      (goodSampleFailureJointEvent n W L U m η ξ).compl)
    (integrable_wRandomJointEventIntegrand W
      (WRandomJointEvent.ofGraphSet
        {G : SimpleGraph (Fin n) |
          G ∈ goodSupportedGraphs H W L U m
            (fractionalEditRadius η (completeEdgeCount n))
            (fractionalEditRadius
              (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
            ξ n}))
  filter_upwards [ae_conditionalSupport_inducedFree H W hfree] with x hSupport
  classical
  unfold wRandomJointEventIntegrand
  apply Finset.sum_le_sum
  intro G _hG
  by_cases hReady :
      (goodSampleFailureJointEvent n W L U m η ξ).compl.Holds x G
  · by_cases hWeight : 0 < wRandomConditionalWeight W x G
    · have hNotFailure :
          ¬ (goodSampleFailureJointEvent n W L U m η ξ).Holds x G :=
        hReady
      have hCapacity :
          ¬ (flexibleRepairCapacityFailureJointEvent n W L U).Holds x G := by
        intro h
        exact hNotFailure (Or.inl h)
      have hEdge : Nat.dist (finiteGraphEdges G).card m ≤
          fractionalEditRadius η (completeEdgeCount n) := by
        apply Nat.le_of_not_gt
        intro hedge
        exact hNotFailure (Or.inr (Or.inl hedge))
      have hCut : cutDist (graphGraphon G) W < ξ := by
        apply lt_of_not_ge
        intro hcut
        exact hNotFailure (Or.inr (Or.inr hcut))
      have hAbundant : x ∈ flexiblePairAbundantSet n W L U := by
        by_contra hx
        exact hCapacity (Or.inl hx)
      have hPresent : L / 2 * (flexiblePairCount W L U x : ℝ) ≤
          ((presentFlexibleEdgeFinset W x L U G).card : ℝ) := by
        apply le_of_not_gt
        intro hp
        exact hCapacity (Or.inr (Or.inl hp))
      have hAbsent : (1 - U) / 2 *
            (flexiblePairCount W L U x : ℝ) ≤
          ((absentFlexibleEdgeFinset W x L U G).card : ℝ) := by
        apply le_of_not_gt
        intro ha
        exact hCapacity (Or.inr (Or.inr ha))
      obtain ⟨hq, hp, ha⟩ := flexiblePairCapacity_of_abundant
        (by omega : 0 < n) W L U η hL hU hMass hη
        hηPresent hηAbsent x G hAbundant hPresent hAbsent
      have hEnoughPresent : (finiteGraphEdges G).card - m ≤
          (presentFlexibleEdgeFinset W x L U G).card := by
        unfold Nat.dist at hEdge
        omega
      have hEnoughAbsent : m - (finiteGraphEdges G).card ≤
          (absentFlexibleEdgeFinset W x L U G).card := by
        unfold Nat.dist at hEdge
        omega
      have hGood : G ∈ goodSupportedGraphs H W L U m
          (fractionalEditRadius η (completeEdgeCount n))
          (fractionalEditRadius
            (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
          ξ n := by
        rw [mem_goodSupportedGraphs]
        exact ⟨{
          latent := x
          support_inducedFree := hSupport
          weight_pos := hWeight
          flexiblePairCount_lower := hq
          enoughPresent := hEnoughPresent
          enoughAbsent := hEnoughAbsent
          edgeDistance_le := hEdge
          cutDist_lt := hCut }⟩
      rw [if_pos hReady]
      have hGoodEvent :
          (WRandomJointEvent.ofGraphSet
            {G : SimpleGraph (Fin n) |
              G ∈ goodSupportedGraphs H W L U m
                (fractionalEditRadius η (completeEdgeCount n))
                (fractionalEditRadius
                  (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
                ξ n}).Holds x G := hGood
      rw [if_pos hGoodEvent]
    · have hZero : wRandomConditionalWeight W x G = 0 :=
        le_antisymm (not_lt.mp hWeight)
          (wRandomConditionalWeight_nonneg W x G)
      simp [hReady, hZero]
  · rw [if_neg hReady]
    split_ifs
    · exact wRandomConditionalWeight_nonneg W x G
    · exact le_rfl

/-- The marginal finite event of good supported graphs has probability
tending to one.  This is the high-probability input used by the entropy and
exact-edge repair transfer. -/
theorem goodSupportedGraphs_probability_tendsto_one
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (L U : ℝ) (m : ℕ → ℕ) (γ η ξ : ℝ)
    (hfree : graphonInducedDensity H W = 0)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hDensity : graphonEdgeDensity W = γ)
    (hη : 0 < η)
    (hηPresent : η ≤ L * graphonClosedBandMass W L U / 4)
    (hηAbsent : η ≤
      (1 - U) * graphonClosedBandMass W L U / 4)
    (hξ : 0 < ξ) :
    Tendsto
      (fun n ↦ finiteEventMass
        (goodSupportedGraphs H W L U (m n)
          (fractionalEditRadius η (completeEdgeCount n))
          (fractionalEditRadius
            (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
          ξ n)
        (wRandomGraphMass W))
      atTop (nhds 1) := by
  have hReady := goodSampleReady_probability_tendsto_one
    W L U m γ η ξ hL hU hMass hm hDensity hη hξ
  have hLower : ∀ᶠ n in atTop,
      wRandomJointEventProbability W
          (goodSampleFailureJointEvent n W L U (m n) η ξ).compl ≤
        finiteEventMass
          (goodSupportedGraphs H W L U (m n)
            (fractionalEditRadius η (completeEdgeCount n))
            (fractionalEditRadius
              (graphonClosedBandMass W L U / 4) (completeEdgeCount n))
            ξ n)
          (wRandomGraphMass W) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [finiteEventMass_wRandomGraphMass_eq_eventProbability]
    exact goodSampleReady_probability_le_goodSupportedGraphs hn H W L U
      (m n) η ξ hfree hL hU hMass hη.le hηPresent hηAbsent
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hReady tendsto_const_nhds
  · exact hLower
  · exact Eventually.of_forall fun n ↦
      finiteEventMass_le_one
        (fun G ↦ wRandomGraphMass_nonneg W G) (wRandomGraphMass_sum W)

end InducedStars
