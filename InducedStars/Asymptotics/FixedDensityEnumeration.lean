import InducedStars.Asymptotics.EntropyTransfer
import InducedStars.Asymptotics.FixedDensityTransfer
import InducedStars.Asymptotics.GoodSampleProbability
import InducedStars.Asymptotics.RepairScale
import InducedStars.Graphon.Counting
import Mathlib.Tactic

/-!
# Fixed-density induced-free enumeration

This module completes the local proof of the fixed-density transfer.  The
unpublished claw-free manuscript is used only as a proof blueprint.  The
actual argument below combines the locally proved flexible-band repair and
entropy estimates with the three narrow published interfaces recorded in
`PriorLiterature`.
-/

noncomputable section

open Filter MeasureTheory Set Topology

namespace InducedStars

/-! ## A band-dependent edit cap -/

/-- The largest convenient edit fraction simultaneously supported by the
present and absent halves of a positive graphon band. -/
noncomputable def flexibleRepairEtaMax (W : Graphon) (L U : ℝ) : ℝ :=
  min (L * graphonClosedBandMass W L U / 4)
    ((1 - U) * graphonClosedBandMass W L U / 4)

theorem flexibleRepairEtaMax_pos (W : Graphon) (L U : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (hMass : 0 < graphonClosedBandMass W L U) :
    0 < flexibleRepairEtaMax W L U := by
  unfold flexibleRepairEtaMax
  apply lt_min
  · positivity
  · positivity

theorem flexibleRepairEtaMax_le_present (W : Graphon) (L U : ℝ) :
    flexibleRepairEtaMax W L U ≤
      L * graphonClosedBandMass W L U / 4 :=
  min_le_left _ _

theorem flexibleRepairEtaMax_le_absent (W : Graphon) (L U : ℝ) :
    flexibleRepairEtaMax W L U ≤
      (1 - U) * graphonClosedBandMass W L U / 4 :=
  min_le_right _ _

/-! ## Entropy lower bound -/

/-- Every positive-random feasible graphon gives the expected epsilon-
eventual lower bound for exact-edge induced-free graph counts.  This is the
liminf half of the fixed-density transfer. -/
theorem fixedDensityCount_liminf_ge_graphonEntropy
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon) (γ : ℝ)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m γ)
    (hW : W ∈ positiveRandomFixedDensityGraphons H γ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - ε <
        normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) := by
  obtain ⟨L, U, hL, _hLU, hU, hMass⟩ :=
    exists_graphonClosedBandMass_pos W hW.2.2
  let etaMax := flexibleRepairEtaMax W L U
  let q : ℕ → ℕ := fun n ↦
    fractionalEditRadius (graphonClosedBandMass W L U / 4)
      (completeEdgeCount n)
  let A : ℝ → (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun eta n ↦
    goodSupportedGraphs H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) 1 n
  apply eventually_normalizedLogGraphCount_gt_entropy_of_smallRepairsBelow
    H W A m etaMax
      (flexibleRepairEtaMax_pos W L U hL hU hMass) ?_
      (PriorLiterature.jansonWRandomGraphEntropyAsymptotic W) ?_ ε hε
  · intro eta heta
    have hetaMax : eta ≤ flexibleRepairEtaMax W L U :=
      heta.2.le.trans (min_le_left _ _)
    have hPresent : eta ≤ L * graphonClosedBandMass W L U / 4 :=
      hetaMax.trans (flexibleRepairEtaMax_le_present W L U)
    have hAbsent : eta ≤
        (1 - U) * graphonClosedBandMass W L U / 4 :=
      hetaMax.trans (flexibleRepairEtaMax_le_absent W L U)
    simpa only [A, q] using
      goodSupportedGraphs_probability_tendsto_one H W L U m γ eta 1
        hW.2.1 hL hU hMass hm hW.1 heta.1 hPresent hAbsent
        (by norm_num)
  · intro eta heta n
    dsimp only [A, q]
    exact goodSupportedGraphs_card_le_exactFamily_mul_hammingBall
      H W L U (m n) (fractionalEditRadius eta (completeEdgeCount n))
        (fractionalEditRadius (graphonClosedBandMass W L U / 4)
          (completeEdgeCount n)) 1 hL hU

/-! ## Exact-edge limit-set inclusion -/

/-- Every positive-random fixed-density graphon is an actual cut limit of
exact-edge induced-free graphs.  The proof retains the repaired graph
sequence; it does not infer limit-set membership from a counting bound. -/
theorem positiveRandomFixedDensityGraphons_subset_exactEdgeInducedFreeLimitSet
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ) :
    positiveRandomFixedDensityGraphons H γ ⊆
      exactEdgeInducedFreeLimitSet H γ m := by
  intro W hW
  obtain ⟨L, U, hL, _hLU, hU, hMass⟩ :=
    exists_graphonClosedBandMass_pos W hW.2.2
  apply mem_labeledGraphFamilyLimitSet_of_eventually_exists_cutDist_lt
  intro ε hε
  let etaMax := flexibleRepairEtaMax W L U
  let eta : ℝ := min (etaMax / 2) (ε / 4)
  let xi : ℝ := ε / 4
  let q : ℕ → ℕ := fun n ↦
    fractionalEditRadius (graphonClosedBandMass W L U / 4)
      (completeEdgeCount n)
  let A : (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun n ↦
    goodSupportedGraphs H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi n
  have hetaMaxPos : 0 < etaMax :=
    flexibleRepairEtaMax_pos W L U hL hU hMass
  have hetaPos : 0 < eta := by
    dsimp only [eta]
    exact lt_min (half_pos hetaMaxPos) (by positivity)
  have hxiPos : 0 < xi := by
    dsimp only [xi]
    positivity
  have hetaLeMax : eta ≤ etaMax := by
    exact (min_le_left _ _).trans (by linarith)
  have hetaPresent : eta ≤
      L * graphonClosedBandMass W L U / 4 :=
    hetaLeMax.trans (flexibleRepairEtaMax_le_present W L U)
  have hetaAbsent : eta ≤
      (1 - U) * graphonClosedBandMass W L U / 4 :=
    hetaLeMax.trans (flexibleRepairEtaMax_le_absent W L U)
  have hgood : Tendsto
      (fun n ↦ finiteEventMass (A n) (wRandomGraphMass W))
      atTop (nhds 1) := by
    simpa only [A, q] using
      goodSupportedGraphs_probability_tendsto_one H W L U m γ eta xi
        hW.2.1 hL hU hMass hm hW.1 hetaPos hetaPresent hetaAbsent hxiPos
  have hnonempty : ∀ᶠ n in atTop, (A n).Nonempty :=
    eventually_nonempty_of_finiteEventMass_tendsto_one W A hgood
  have hetaEps : eta < 3 * ε / 4 := by
    have hle : eta ≤ ε / 4 := min_le_right _ _
    linarith
  have hpenalty : ∀ᶠ n in atTop,
      2 * (fractionalEditRadius eta (completeEdgeCount n) : ℝ) /
          (n : ℝ) ^ 2 < 3 * ε / 4 :=
    eventually_fractionalEditRadius_orderedSquare_lt hetaPos.le hetaEps
  filter_upwards [hnonempty, hpenalty, eventually_ge_atTop 2]
    with n hAn hpenaltyN hn
  obtain ⟨G, hG⟩ := hAn
  let K := repairGoodSupportedGraph H W L U (m n)
    (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi G
  have hKmem : K ∈ inducedFreeGraphFinsetWithEdges H n (m n) := by
    dsimp only [K]
    exact repairGoodSupportedGraph_mem_exactFamily H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi G hG hL hU
  refine ⟨K, hKmem, ?_⟩
  have hcut := cutDist_repairGoodSupportedGraph_lt_add
    (by omega : 0 < n) H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi G hG
  dsimp only [K]
  dsimp only [xi] at hcut
  linarith

/-- A nonempty positive-random domain supplies exact-edge induced-free
graphs at every sufficiently large order. -/
theorem eventually_inducedFreeGraphFinsetWithEdges_nonempty
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty) :
    ∀ᶠ n in atTop,
      (inducedFreeGraphFinsetWithEdges H n (m n)).Nonempty := by
  obtain ⟨W, hW⟩ := hdomain
  obtain ⟨L, U, hL, _hLU, hU, hMass⟩ :=
    exists_graphonClosedBandMass_pos W hW.2.2
  let etaMax := flexibleRepairEtaMax W L U
  let eta : ℝ := etaMax / 2
  let q : ℕ → ℕ := fun n ↦
    fractionalEditRadius (graphonClosedBandMass W L U / 4)
      (completeEdgeCount n)
  let A : (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun n ↦
    goodSupportedGraphs H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) 1 n
  have hetaMaxPos : 0 < etaMax :=
    flexibleRepairEtaMax_pos W L U hL hU hMass
  have hetaPos : 0 < eta := half_pos hetaMaxPos
  have hetaLeMax : eta ≤ etaMax := by
    dsimp only [eta]
    linarith
  have hgood : Tendsto
      (fun n ↦ finiteEventMass (A n) (wRandomGraphMass W))
      atTop (nhds 1) := by
    simpa only [A, q] using
      goodSupportedGraphs_probability_tendsto_one H W L U m γ eta 1
        hW.2.1 hL hU hMass hm hW.1 hetaPos
        (hetaLeMax.trans (flexibleRepairEtaMax_le_present W L U))
        (hetaLeMax.trans (flexibleRepairEtaMax_le_absent W L U))
        (by norm_num)
  have hnonempty : ∀ᶠ n in atTop, (A n).Nonempty :=
    eventually_nonempty_of_finiteEventMass_tendsto_one W A hgood
  filter_upwards [hnonempty] with n hAn
  obtain ⟨G, hG⟩ := hAn
  refine ⟨repairGoodSupportedGraph H W L U (m n)
    (fractionalEditRadius eta (completeEdgeCount n)) (q n) 1 G, ?_⟩
  exact repairGoodSupportedGraph_mem_exactFamily H W L U (m n)
    (fractionalEditRadius eta (completeEdgeCount n)) (q n) 1 G hG hL hU

/-! ## Feasibility, the upper bound, and the full transfer -/

/-- Every limit of exact-edge induced-`H`-free graphs satisfies both closed
graphon constraints. -/
theorem exactEdgeInducedFreeLimitSet_feasible
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ) (U : Graphon)
    (hU : U ∈ exactEdgeInducedFreeLimitSet H γ m) :
    graphonEdgeDensity U = γ ∧ graphonInducedDensity H U = 0 := by
  exact ⟨graphonEdgeDensity_eq_of_mem_exactEdgeInducedFreeLimitSet hm hU,
    graphonInducedDensity_eq_zero_of_mem_exactEdgeInducedFreeLimitSet hU⟩

/-- The exact-edge limit-set entropy supremum is exactly the
positive-random fixed-density value. -/
theorem graphonEntropy_sSup_exactEdgeInducedFreeLimitSet_eq_positiveRandom
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty) :
    sSup (graphonEntropy '' exactEdgeInducedFreeLimitSet H γ m) =
      positiveRandomFixedDensityEntropyValue H γ := by
  exact graphonEntropy_sSup_limitSet_eq_positiveRandom H γ
    (exactEdgeInducedFreeLimitSet H γ m) hdomain
    (positiveRandomFixedDensityGraphons_subset_exactEdgeInducedFreeLimitSet
      H γ m hm)
    (exactEdgeInducedFreeLimitSet_feasible H γ m hm)

/-- The HJS graph-class bound, with all local exact-edge hypotheses
discharged by the repair and feasibility theorems. -/
theorem eventually_fixedDensityCount_le_positiveRandomEntropyValue_of_asymptoticDensity
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) ≤
        positiveRandomFixedDensityEntropyValue H γ + ε := by
  exact eventually_fixedDensityCount_le_positiveRandomEntropyValue
    H γ m hdomain
    (eventually_inducedFreeGraphFinsetWithEdges_nonempty H γ m hm hdomain)
    (positiveRandomFixedDensityGraphons_subset_exactEdgeInducedFreeLimitSet
      H γ m hm)
    (exactEdgeInducedFreeLimitSet_feasible H γ m hm) ε hε

/-- Local formalization of Proposition 2.11 from
“The typical structure of dense claw-free graphs.”
This theorem is proved in Lean from published external inputs;
it is not an axiom. -/
theorem inducedFreeFixedDensityEnumeration
    {h : ℕ} (H : SimpleGraph (Fin h)) (γ : ℝ)
    (_hγ : γ ∈ Ioo (0 : ℝ) 1) (m : ℕ → ℕ)
    (hm : HasAsymptoticEdgeDensity m γ)
    (hne : (positiveRandomFixedDensityGraphons H γ).Nonempty) :
    Tendsto
      (fun n ↦ normalizedLogGraphCount n
        (inducedFreeGraphCountWithEdges H n (m n)))
      atTop (nhds (positiveRandomFixedDensityEntropyValue H γ)) := by
  exact tendsto_fixedDensityCount_of_eventual_entropy_bounds H γ m hne
    (fun W hW ε hε ↦
      fixedDensityCount_liminf_ge_graphonEntropy H W γ m hm hW ε hε)
    (fun ε hε ↦
      eventually_fixedDensityCount_le_positiveRandomEntropyValue_of_asymptoticDensity
        H γ m hm hne ε hε)

end InducedStars
