import InducedStars.Asymptotics.GoodSupportedGraphs
import Mathlib.Tactic

/-!
# Entropy transfer through exact-edge repair

This file contains the finite counting bridge in the fixed-density argument.
A high-probability family of sampled graphs retains the graphon entropy.  If
that family can be repaired into an exact-edge induced-free family with a
uniform Hamming radius, bounded repair fibers cost at most the logarithm of
one graph Hamming ball.
-/

noncomputable section

open Filter Finset Set Topology

namespace InducedStars

/-- Taking base-two logarithms in a bounded-fiber cardinality comparison.
The nonemptiness assumption is needed because `log2` is totalized at zero. -/
theorem normalizedLogCard_sub_hammingBall_le_of_card_le
    {n r : ℕ} {A B : Finset (SimpleGraph (Fin n))}
    (hn : 2 ≤ n) (hA : A.Nonempty)
    (hcard : A.card ≤
      B.card * hammingBallVolume (completeEdgeCount n) r) :
    log2 (A.card : ℝ) / (completeEdgeCount n : ℝ) -
        log2 (hammingBallVolume (completeEdgeCount n) r : ℝ) /
          (completeEdgeCount n : ℝ) ≤
      log2 (B.card : ℝ) / (completeEdgeCount n : ℝ) := by
  have hAcard : 0 < A.card := Finset.card_pos.mpr hA
  have hvol : 0 < hammingBallVolume (completeEdgeCount n) r :=
    hammingBallVolume_pos _ _
  have hBcard : 0 < B.card := by
    by_contra hB
    have hBzero : B.card = 0 := Nat.eq_zero_of_not_pos hB
    rw [hBzero, zero_mul] at hcard
    omega
  have hlog : log2 (A.card : ℝ) ≤
      log2 ((B.card : ℝ) *
        (hammingBallVolume (completeEdgeCount n) r : ℝ)) := by
    unfold log2
    apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
    apply Real.strictMonoOn_log.monotoneOn
    · show (A.card : ℝ) ∈ Set.Ioi 0
      change (0 : ℝ) < (A.card : ℝ)
      exact_mod_cast hAcard
    · show (B.card : ℝ) *
          (hammingBallVolume (completeEdgeCount n) r : ℝ) ∈ Set.Ioi 0
      change (0 : ℝ) < (B.card : ℝ) *
        (hammingBallVolume (completeEdgeCount n) r : ℝ)
      exact mul_pos (by exact_mod_cast hBcard) (by exact_mod_cast hvol)
    · exact_mod_cast hcard
  rw [log2_mul (by exact_mod_cast hBcard.ne')
    (by exact_mod_cast hvol.ne')] at hlog
  have hN : (0 : ℝ) < completeEdgeCount n := by
    exact_mod_cast Nat.choose_pos hn
  calc
    log2 (A.card : ℝ) / (completeEdgeCount n : ℝ) -
        log2 (hammingBallVolume (completeEdgeCount n) r : ℝ) /
          (completeEdgeCount n : ℝ) =
      (log2 (A.card : ℝ) -
        log2 (hammingBallVolume (completeEdgeCount n) r : ℝ)) /
          (completeEdgeCount n : ℝ) := by ring
    _ ≤ log2 (B.card : ℝ) / (completeEdgeCount n : ℝ) :=
      (div_le_div_iff_of_pos_right hN).2 (by linarith)

/-- Pointwise entropy-counting bridge for an arbitrary graph event whose
members have a radius-`r` repair into the exact-edge induced-free family. -/
theorem normalizedLogCard_sub_hammingBall_le_exactCount
    {h n m r : ℕ} (H : SimpleGraph (Fin h))
    (A : Finset (SimpleGraph (Fin n)))
    (hn : 2 ≤ n) (hA : A.Nonempty)
    (hrepair : A.card ≤
      (inducedFreeGraphFinsetWithEdges H n m).card *
        hammingBallVolume (completeEdgeCount n) r) :
    log2 (A.card : ℝ) / (completeEdgeCount n : ℝ) -
        log2 (hammingBallVolume (completeEdgeCount n) r : ℝ) /
          (completeEdgeCount n : ℝ) ≤
      normalizedLogGraphCount n
        (inducedFreeGraphCountWithEdges H n m) := by
  simpa [normalizedLogGraphCount] using
    normalizedLogCard_sub_hammingBall_le_of_card_le hn hA hrepair

/-- Epsilon-eventual entropy lower bound after a fractional-radius repair.

The hypotheses expose the two independent ingredients: the graph event has
`W`-random probability tending to one, and every event family satisfies the
bounded-fiber cardinality comparison into the exact-edge target.  The sampled
entropy convergence is kept explicit so that the only published input needed
by an application is Janson's entropy theorem. -/
theorem eventually_normalizedLogGraphCount_gt_entropy_sub_binaryEntropy
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (A : (n : ℕ) → Finset (SimpleGraph (Fin n))) (m : ℕ → ℕ)
    (eta : ℝ) (heta : eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hprob : Tendsto
      (fun n ↦ finiteEventMass (A n) (wRandomGraphMass W))
      atTop (nhds 1))
    (hentropy : Tendsto
      (fun n ↦ wRandomGraphEntropy W n /
        (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W)))
    (hrepair : ∀ n, (A n).card ≤
      (inducedFreeGraphFinsetWithEdges H n (m n)).card *
        hammingBallVolume (completeEdgeCount n)
          (fractionalEditRadius eta (completeEdgeCount n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - binaryEntropy eta - ε <
        normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) := by
  have hEvent :=
    eventually_normalizedLogCard_ge_of_eventProbability_tendsto_one
      W A hprob hentropy (ε / 2) (by positivity)
  have hBall := eventually_normalizedLog_hammingBallVolume_le_add
    eta heta (ε / 2) (by positivity)
  have hprobPos : ∀ᶠ n in atTop,
      0 < finiteEventMass (A n) (wRandomGraphMass W) :=
    (tendsto_order.1 hprob).1 0 (by norm_num)
  have hnLarge : ∀ᶠ n in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [hEvent, hBall, hprobPos, hnLarge] with n hEventN hBallN hprobN hn
  have hA : (A n).Nonempty := by
    by_contra hne
    have hempty : A n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, finiteEventMass] at hprobN
  have hBridge := normalizedLogCard_sub_hammingBall_le_exactCount
    H (A n) hn hA (hrepair n)
  exact (by linarith :
      graphonEntropy W - binaryEntropy eta - ε <
        log2 ((A n).card : ℝ) / (completeEdgeCount n : ℝ) -
          log2 (hammingBallVolume (completeEdgeCount n)
            (fractionalEditRadius eta (completeEdgeCount n)) : ℝ) /
              (completeEdgeCount n : ℝ)).trans_le hBridge

/-- Binary entropy can be made arbitrarily small inside any prescribed
positive upper interval. -/
theorem exists_pos_lt_binaryEntropy_lt
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    ∃ eta ∈ Ioo (0 : ℝ) b, binaryEntropy eta < c := by
  let S : Set ℝ := {x | binaryEntropy x < c}
  have hSopen : IsOpen S :=
    isOpen_lt binaryEntropy_continuous continuous_const
  have hzero : (0 : ℝ) ∈ S := by
    simp [S, hc]
  obtain ⟨delta, hdelta, hball⟩ :=
    Metric.isOpen_iff.mp hSopen 0 hzero
  let eta : ℝ := min (delta / 2) (b / 2)
  have hetaPos : 0 < eta := by
    dsimp [eta]
    exact lt_min (by positivity) (by positivity)
  have hetaB : eta < b := by
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨eta, ⟨hetaPos, hetaB⟩, hball ?_⟩
  change dist eta 0 < delta
  rw [Real.dist_eq, sub_zero, abs_of_pos hetaPos]
  exact lt_of_le_of_lt (min_le_left _ _) (by linarith)

/-- Binary entropy can be made arbitrarily small while retaining a positive
repair fraction strictly below one half. -/
theorem exists_pos_lt_half_binaryEntropy_lt
    {c : ℝ} (hc : 0 < c) :
    ∃ eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ), binaryEntropy eta < c :=
  exists_pos_lt_binaryEntropy_lt (by norm_num) hc

/-- Arbitrarily small repairs below a fixed positive cap lose no entropy
density.  The cap accommodates applications where the supply of flexible
present and absent edges is only guaranteed below a band-dependent constant. -/
theorem eventually_normalizedLogGraphCount_gt_entropy_of_smallRepairsBelow
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (A : ℝ → (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ) (etaMax : ℝ) (hetaMax : 0 < etaMax)
    (hprob : ∀ eta ∈ Ioo (0 : ℝ) (min etaMax (1 / 2 : ℝ)), Tendsto
      (fun n ↦ finiteEventMass (A eta n) (wRandomGraphMass W))
      atTop (nhds 1))
    (hentropy : Tendsto
      (fun n ↦ wRandomGraphEntropy W n /
        (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W)))
    (hrepair : ∀ eta ∈ Ioo (0 : ℝ) (min etaMax (1 / 2 : ℝ)), ∀ n,
      (A eta n).card ≤
        (inducedFreeGraphFinsetWithEdges H n (m n)).card *
          hammingBallVolume (completeEdgeCount n)
            (fractionalEditRadius eta (completeEdgeCount n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - ε <
        normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) := by
  have hcap : 0 < min etaMax (1 / 2 : ℝ) :=
    lt_min hetaMax (by norm_num)
  obtain ⟨eta, hetaCap, hEtaEntropy⟩ :=
    exists_pos_lt_binaryEntropy_lt (c := ε / 2) hcap (by positivity)
  have hetaHalf : eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ) :=
    ⟨hetaCap.1, hetaCap.2.trans_le (min_le_right _ _)⟩
  have hLower :=
    eventually_normalizedLogGraphCount_gt_entropy_sub_binaryEntropy
      H W (A eta) m eta hetaHalf (hprob eta hetaCap) hentropy
        (hrepair eta hetaCap) (ε / 2) (by positivity)
  filter_upwards [hLower] with n hn
  linarith

/-- Arbitrarily small fractional-radius repair loses no entropy density.

This is the quantifier package used for a liminf-style lower bound: for each
positive repair fraction an event family may be chosen independently. -/
theorem eventually_normalizedLogGraphCount_gt_entropy_of_arbitrarilySmallRepairs
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (A : ℝ → (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (m : ℕ → ℕ)
    (hprob : ∀ eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ), Tendsto
      (fun n ↦ finiteEventMass (A eta n) (wRandomGraphMass W))
      atTop (nhds 1))
    (hentropy : Tendsto
      (fun n ↦ wRandomGraphEntropy W n /
        (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W)))
    (hrepair : ∀ eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ), ∀ n,
      (A eta n).card ≤
        (inducedFreeGraphFinsetWithEdges H n (m n)).card *
          hammingBallVolume (completeEdgeCount n)
            (fractionalEditRadius eta (completeEdgeCount n)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - ε <
        normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) := by
  obtain ⟨eta, heta, hEtaEntropy⟩ :=
    exists_pos_lt_half_binaryEntropy_lt (c := ε / 2) (by positivity)
  have hLower :=
    eventually_normalizedLogGraphCount_gt_entropy_sub_binaryEntropy
      H W (A eta) m eta heta (hprob eta heta) hentropy
        (hrepair eta heta) (ε / 2) (by positivity)
  filter_upwards [hLower] with n hn
  linarith

/-! ## Specialization to selected good supported witnesses -/

/-- The exact counting loss for the deterministic selected-witness repair of
`goodSupportedGraphs`. -/
theorem normalizedLog_goodSupportedGraphs_sub_hammingBall_le_exactCount
    {h n : ℕ} (hn : 2 ≤ n) (H : SimpleGraph (Fin h)) (W : Graphon)
    (L U : ℝ) (m r q : ℕ) (xi : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (hgood : (goodSupportedGraphs H W L U m r q xi n).Nonempty) :
    log2 ((goodSupportedGraphs H W L U m r q xi n).card : ℝ) /
          (completeEdgeCount n : ℝ) -
        log2 (hammingBallVolume (completeEdgeCount n) r : ℝ) /
          (completeEdgeCount n : ℝ) ≤
      normalizedLogGraphCount n
        (inducedFreeGraphCountWithEdges H n m) := by
  apply normalizedLogCard_sub_hammingBall_le_exactCount H
    (goodSupportedGraphs H W L U m r q xi n) hn hgood
  exact goodSupportedGraphs_card_le_exactFamily_mul_hammingBall
    H W L U m r q xi hL hU

/-- Direct fractional-radius specialization for good supported sampled
graphs.  This is the form used by the fixed-density transfer theorem; the
remaining analytic step may choose `eta` arbitrarily close to zero. -/
theorem eventually_exactCount_gt_entropy_sub_binaryEntropy_of_goodSupported
    {h : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (L U : ℝ) (m q : ℕ → ℕ) (xi eta : ℝ)
    (hL : 0 < L) (hU : U < 1)
    (heta : eta ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (hprob : Tendsto
      (fun n ↦ finiteEventMass
        (goodSupportedGraphs H W L U (m n)
          (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi n)
        (wRandomGraphMass W))
      atTop (nhds 1))
    (hentropy : Tendsto
      (fun n ↦ wRandomGraphEntropy W n /
        (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - binaryEntropy eta - ε <
        normalizedLogGraphCount n
          (inducedFreeGraphCountWithEdges H n (m n)) := by
  let A : (n : ℕ) → Finset (SimpleGraph (Fin n)) := fun n ↦
    goodSupportedGraphs H W L U (m n)
      (fractionalEditRadius eta (completeEdgeCount n)) (q n) xi n
  refine eventually_normalizedLogGraphCount_gt_entropy_sub_binaryEntropy
    H W A m eta heta hprob hentropy ?_ ε hε
  intro n
  exact goodSupportedGraphs_card_le_exactFamily_mul_hammingBall
    H W L U (m n) (fractionalEditRadius eta (completeEdgeCount n))
      (q n) xi hL hU

end InducedStars
