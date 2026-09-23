import InducedStars.Asymptotics.FixedDensityEnumeration
import InducedStars.Asymptotics.GnpDensity
import InducedStars.Asymptotics.GnpSlices
import InducedStars.Asymptotics.WeightedEntropyUpper
import InducedStars.Graphon.GnpDomains
import InducedStars.Graphon.TwoBlockPerturbation
import Mathlib.Tactic

/-!
# Large-deviation transfer for induced-free `G(n,p)` events

This module converts the fixed-density labeled enumeration theorem into the
lower bound for the unconditioned binomial random-graph event, combines it
with the weighted HJS upper bound, and uses the local two-block approximation
to identify the full and positive-random graphon rate domains.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A positive comparison of two masses passes to their normalized base-two
logarithms.  The hypothesis `2 ≤ n` makes the edge normalization strictly
positive. -/
theorem normalizedLogProbability_mono {n : ℕ} (hn : 2 ≤ n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    normalizedLogProbability n x ≤ normalizedLogProbability n y := by
  have hN : 0 < (completeEdgeCount n : ℝ) := by
    exact_mod_cast Nat.choose_pos hn
  unfold normalizedLogProbability normalizedLogAtGraphOrder log2
  apply div_le_div_of_nonneg_right _ hN.le
  exact div_le_div_of_nonneg_right (Real.log_le_log hx hxy)
    realLogTwo_pos.le

/-- The negative graphon relative entropy in the exact log-odds form used by
the binomial slice exponent. -/
theorem neg_graphonRelativeEntropy_eq_entropy_add_edgeLogOdds
    {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (W : Graphon) :
    -graphonRelativeEntropy p W =
      graphonEntropy W +
        graphonEdgeDensity W * log2 (p / (1 - p)) +
          log2 (1 - p) := by
  rw [graphonRelativeEntropy_eq_negEntropy_add_edge hp W,
    log2_div (sub_pos.mpr hp.2).ne' hp.1.ne',
    log2_div hp.1.ne' (sub_pos.mpr hp.2).ne']
  ring

/-- Every positive-random induced-`H`-free graphon gives the expected
epsilon-eventual lower bound for the full labeled `G(n,p)` event.

The proof uses the floor exact-edge sequence at the graphon's edge density,
the fixed-density enumeration lower bound, the exact slice exponent, and
the inclusion of that slice in the full induced-free event. -/
theorem eventually_normalizedLogGnpInducedFreeProbability_gt_neg_relativeEntropy
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (W : Graphon)
    (hW : W ∈ positiveRandomInducedFreeGraphons H)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      -graphonRelativeEntropy p W - ε <
        normalizedLogGnpInducedFreeProbability H n p := by
  let γ := graphonEdgeDensity W
  let m : ℕ → ℕ := floorEdgeCountSequence γ
  have hγ : γ ∈ Set.Ioo (0 : ℝ) 1 := by
    exact graphonEdgeDensity_mem_Ioo_of_randomMass_pos W hW.2
  have hm : HasAsymptoticEdgeDensity m γ := by
    exact floorEdgeCountSequence_hasAsymptoticEdgeDensity
      ⟨hγ.1.le, hγ.2.le⟩
  have hWfixed : W ∈ positiveRandomFixedDensityGraphons H γ := by
    exact ⟨rfl, hW.1, hW.2⟩
  have hdomain : (positiveRandomFixedDensityGraphons H γ).Nonempty :=
    ⟨W, hWfixed⟩
  have hcountLower :=
    fixedDensityCount_liminf_ge_graphonEntropy H W γ m hm hWfixed
      (ε / 2) (half_pos hε)
  have hnonempty :=
    eventually_inducedFreeGraphFinsetWithEdges_nonempty H γ m hm hdomain
  have hedgeTendsto : Tendsto
      (fun n ↦ (m n : ℝ) / (completeEdgeCount n : ℝ) *
          log2 (p / (1 - p)) + log2 (1 - p))
      Filter.atTop
      (nhds (γ * log2 (p / (1 - p)) + log2 (1 - p))) :=
    (hm.mul_const (log2 (p / (1 - p)))).add_const (log2 (1 - p))
  have hedgeLower : ∀ᶠ n in Filter.atTop,
      γ * log2 (p / (1 - p)) + log2 (1 - p) - ε / 2 <
        (m n : ℝ) / (completeEdgeCount n : ℝ) *
          log2 (p / (1 - p)) + log2 (1 - p) :=
    (tendsto_order.mp hedgeTendsto).1 _ (by linarith)
  filter_upwards [hcountLower, hnonempty, hedgeLower,
      eventually_ge_atTop 2] with n hcount hne hedge hn
  have hmn : m n ≤ completeEdgeCount n := by
    exact floorEdgeCountSequence_le_completeEdgeCount
      ⟨hγ.1.le, hγ.2.le⟩ n
  have hcountPos : 0 < inducedFreeGraphCountWithEdges H n (m n) := by
    rw [inducedFreeGraphCountWithEdges_eq_card]
    exact Finset.card_pos.mpr hne
  have hslicePos : 0 < gnpInducedFreeSliceWeight H n (m n) p :=
    (gnpInducedFreeSliceWeight_pos_iff_count_pos H n (m n) hp).2 hcountPos
  have hsliceLe : gnpInducedFreeSliceWeight H n (m n) p ≤
      gnpInducedFreeProbability H n p :=
    (gnpInducedFreeSliceWeight_le_maximal H n p hmn).trans
      (maximalInducedFreeSliceWeight_le_probability H n
        ⟨hp.1.le, hp.2.le⟩)
  have hlogLe := normalizedLogProbability_mono hn hslicePos hsliceLe
  have hexact := normalizedLogGnpInducedFreeSliceWeight_eq_odds
    H n (m n) p hp hmn hcountPos hn
  have hlowerSlice : -graphonRelativeEntropy p W - ε <
      normalizedLogProbability n
        (gnpInducedFreeSliceWeight H n (m n) p) := by
    rw [hexact,
      neg_graphonRelativeEntropy_eq_entropy_add_edgeLogOdds hp W]
    dsimp only [γ] at hedge ⊢
    linarith
  exact hlowerSlice.trans_le hlogLe

/-- Epsilon-eventual lower bound by the infimum over the positive-random
induced-free domain.  The proof takes an approximate minimizer; it does not
assume that the infimum is attained. -/
theorem eventually_normalizedLogGnpInducedFreeProbability_gt_neg_positiveRandomRate
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      -positiveRandomInducedFreeRateValue H p - ε <
        normalizedLogGnpInducedFreeProbability H n p := by
  have hlt : positiveRandomInducedFreeRateValue H p <
      positiveRandomInducedFreeRateValue H p + ε / 2 := by
    linarith
  obtain ⟨z, hz, hzlt⟩ := exists_lt_of_csInf_lt
    (positiveRandomInducedFreeRateValues_nonempty H p hne)
    (by simpa only [positiveRandomInducedFreeRateValue] using hlt)
  obtain ⟨W, hW, rfl⟩ := hz
  have hWlower :=
    eventually_normalizedLogGnpInducedFreeProbability_gt_neg_relativeEntropy
      H p hp W hW (ε / 2) (half_pos hε)
  filter_upwards [hWlower] with n hn
  dsimp only [positiveRandomInducedFreeRateValue] at hzlt ⊢
  linarith

/-! ## Squeezing the lower and upper transfers -/

/-- General induced-free `G(n,p)` large-deviation transfer once the
positive-random and full graphon rate values have been identified.

The lower bound is the locally proved fixed-density enumeration transfer;
the upper bound is the compactness/HJS weighted-family argument.  Both use
the exact normalization `log₂ probability / n.choose 2`. -/
theorem inducedFreeGnpLargeDeviation_of_rateValue_eq
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty)
    (hrate : positiveRandomInducedFreeRateValue H p =
      inducedFreeGraphonRateValue H p) :
    Tendsto
      (fun n ↦ normalizedLogGnpInducedFreeProbability H n p)
      Filter.atTop (nhds (-inducedFreeGraphonRateValue H p)) := by
  have hfull : (inducedFreeGraphons H).Nonempty := by
    obtain ⟨W, hW⟩ := hne
    exact ⟨W, positiveRandomInducedFreeGraphons_subset H hW⟩
  rw [tendsto_order]
  constructor
  · intro a ha
    let ε := (-inducedFreeGraphonRateValue H p - a) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hlower :=
      eventually_normalizedLogGnpInducedFreeProbability_gt_neg_positiveRandomRate
        H p hp hne ε hε
    filter_upwards [hlower] with n hn
    rw [hrate] at hn
    dsimp [ε] at hn
    linarith
  · intro b hb
    let ε := (b - (-inducedFreeGraphonRateValue H p)) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hupper := inducedFreeGnp_limsup_le_fullRate
      H p hp hfull ε hε
    filter_upwards [hupper] with n hn
    dsimp [ε] at hn
    linarith

/-- Local formalization of Proposition 2.10 from
“The typical structure of dense claw-free graphs.”
The manuscript supplies only a proof blueprint; this theorem is Lean-proved.

Paper: Lemma `lemma:LDPforGNPkl`
-/
theorem inducedFreeGnpLargeDeviation
    {h : ℕ} (H : SimpleGraph (Fin h)) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hne : (positiveRandomInducedFreeGraphons H).Nonempty) :
    Tendsto
      (fun n ↦ normalizedLogProbability n
        (gnpInducedFreeProbability H n p))
      Filter.atTop
      (nhds (-positiveRandomInducedFreeRateValue H p)) := by
  have hrate := positiveRandomInducedFreeRateValue_eq_full H p hp hne
  simpa only [normalizedLogGnpInducedFreeProbability, hrate] using
    inducedFreeGnpLargeDeviation_of_rateValue_eq H p hp hne hrate

end InducedStars
