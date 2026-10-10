import InducedStars.FiniteModels.GraphonLimits
import InducedStars.FiniteModels.Shannon
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Entropy costs of graph events and edit balls

The estimates here are fully finite.  They provide the quantitative bridge
from the entropy of the `W`-random graph to a high-probability set of labeled
graphs and the subexponential cost of an edit ball.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace InducedStars

/-- Number of subsets of an `N`-element set having size at most `r`. -/
def hammingBallVolume (N r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (r + 1), N.choose j

theorem graphHammingBall_card_le_hammingBallVolume {n r : ℕ}
    (G : SimpleGraph (Fin n)) :
    (graphHammingBall G r).card ≤ hammingBallVolume (completeEdgeCount n) r := by
  exact graphHammingBall_card_le G

theorem graphEditDistance_le_completeEdgeCount {n : ℕ}
    (G K : SimpleGraph (Fin n)) :
    graphEditDistance G K ≤ completeEdgeCount n := by
  rw [graphEditDistance, ← completeEdgeFinset_card n]
  exact Finset.card_le_card (graphEditFinset_subset_completeEdgeFinset G K)

@[simp] theorem graphHammingBall_completeEdgeCount {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    graphHammingBall G (completeEdgeCount n) = Finset.univ := by
  ext K
  simp [graphEditDistance_le_completeEdgeCount]

theorem card_simpleGraph_le_two_pow_completeEdgeCount (n : ℕ) :
    Fintype.card (SimpleGraph (Fin n)) ≤ 2 ^ completeEdgeCount n := by
  have hball := graphHammingBall_card_le
    (G := (⊥ : SimpleGraph (Fin n))) (r := completeEdgeCount n)
  rw [graphHammingBall_completeEdgeCount, Finset.card_univ,
    Nat.sum_range_choose] at hball
  exact hball

theorem log2_card_simpleGraph_le_completeEdgeCount (n : ℕ) :
    log2 (Fintype.card (SimpleGraph (Fin n)) : ℝ) ≤
      (completeEdgeCount n : ℝ) := by
  have hcard := card_simpleGraph_le_two_pow_completeEdgeCount n
  calc
    log2 (Fintype.card (SimpleGraph (Fin n)) : ℝ) ≤
        log2 ((2 : ℝ) ^ completeEdgeCount n) := by
      unfold log2
      apply div_le_div_of_nonneg_right _ realLogTwo_pos.le
      apply Real.strictMonoOn_log.monotoneOn
      · show 0 < (Fintype.card (SimpleGraph (Fin n)) : ℝ)
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (SimpleGraph (Fin n)))
      · show 0 < (2 : ℝ) ^ completeEdgeCount n
        positivity
      · exact_mod_cast hcard
    _ = (completeEdgeCount n : ℝ) := by
      rw [log2_pow, log2_two, mul_one]

theorem tendsto_completeEdgeCount_atTop :
    Tendsto completeEdgeCount atTop atTop := by
  apply (Nat.choose_mono 2).tendsto_atTop_atTop
  intro b
  refine ⟨b + 2, ?_⟩
  rw [Nat.choose]
  simp only [Nat.choose_one_right]
  omega

theorem tendsto_completeEdgeCount_cast_atTop :
    Tendsto (fun n ↦ (completeEdgeCount n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp tendsto_completeEdgeCount_atTop

/-- Event entropy bound specialized to labeled graphs; the ambient entropy
cost is exactly at most one bit per possible unordered edge. -/
theorem wRandomGraphEntropy_le_event {n : ℕ} (W : Graphon)
    (A : Finset (SimpleGraph (Fin n))) :
    wRandomGraphEntropy W n ≤
      1 + finiteEventMass A (wRandomGraphMass W) * log2 (A.card : ℝ) +
        (1 - finiteEventMass A (wRandomGraphMass W)) *
          (completeEdgeCount n : ℝ) := by
  classical
  have hbase := finiteShannonEntropy_le_event A
    (fun G ↦ wRandomGraphMass_nonneg W G) (wRandomGraphMass_sum W)
  unfold wRandomGraphEntropy
  refine hbase.trans ?_
  have hpnonneg : 0 ≤ 1 - finiteEventMass A (wRandomGraphMass W) := by
    linarith [finiteEventMass_le_one (s := A)
      (fun G ↦ wRandomGraphMass_nonneg W G) (wRandomGraphMass_sum W)]
  have hambient := log2_card_simpleGraph_le_completeEdgeCount n
  nlinarith [mul_le_mul_of_nonneg_left hambient hpnonneg]

/-- The explicit lower expression for the logarithmic size of a graph event
obtained by rearranging the event entropy inequality. -/
noncomputable def entropyEventLowerBound (W : Graphon)
    (A : (n : ℕ) → Finset (SimpleGraph (Fin n))) (n : ℕ) : ℝ :=
  wRandomGraphEntropy W n / (completeEdgeCount n : ℝ) -
    1 / (completeEdgeCount n : ℝ) -
    (1 - finiteEventMass (A n) (wRandomGraphMass W))

/-- A nonempty graph event has normalized logarithmic cardinality at least
the rearranged entropy lower expression. -/
theorem entropyEventLowerBound_le_normalizedLogCard
    (W : Graphon) (A : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    {n : ℕ} (hn : 2 ≤ n) (hA : (A n).Nonempty) :
    entropyEventLowerBound W A n ≤
      log2 ((A n).card : ℝ) / (completeEdgeCount n : ℝ) := by
  let p := finiteEventMass (A n) (wRandomGraphMass W)
  let L := log2 ((A n).card : ℝ)
  let N : ℝ := completeEdgeCount n
  have hNnat : 0 < completeEdgeCount n := Nat.choose_pos hn
  have hN : 0 < N := by
    change (0 : ℝ) < (completeEdgeCount n : ℝ)
    exact_mod_cast hNnat
  have hp0 : 0 ≤ p := finiteEventMass_nonneg
    (fun G ↦ wRandomGraphMass_nonneg W G)
  have hp1 : p ≤ 1 := finiteEventMass_le_one
    (fun G ↦ wRandomGraphMass_nonneg W G) (wRandomGraphMass_sum W)
  have hL : 0 ≤ L := by
    apply log2_nonneg
    exact_mod_cast Finset.one_le_card.mpr hA
  have hpL : p * L ≤ L := by nlinarith
  have hentropy := wRandomGraphEntropy_le_event W (A n)
  have hentropy' : wRandomGraphEntropy W n ≤
      1 + L + (1 - p) * N := by
    dsimp [p, L, N] at hentropy ⊢
    linarith
  dsimp [entropyEventLowerBound, p, L, N]
  apply (le_div_iff₀ hN).2
  dsimp [N]
  field_simp [hN.ne']
  dsimp [p, L, N] at hentropy'
  linarith

/-- A graph event whose probability tends to one retains the full sampled
entropy density.  The statement is epsilon-eventual and therefore avoids any
informal `o(n²)` notation. -/
theorem eventually_normalizedLogCard_ge_of_eventProbability_tendsto_one
    (W : Graphon) (A : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (hprob : Tendsto
      (fun n ↦ finiteEventMass (A n) (wRandomGraphMass W))
      atTop (nhds 1))
    (hentropy : Tendsto
      (fun n ↦ wRandomGraphEntropy W n /
        (completeEdgeCount n : ℝ))
      atTop (nhds (graphonEntropy W)))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      graphonEntropy W - ε <
        log2 ((A n).card : ℝ) / (completeEdgeCount n : ℝ) := by
  have hinv : Tendsto
      (fun n ↦ (completeEdgeCount n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_completeEdgeCount_cast_atTop
  have hlower : Tendsto (entropyEventLowerBound W A) atTop
      (nhds (graphonEntropy W)) := by
    have hcompl : Tendsto
        (fun n ↦ 1 - finiteEventMass (A n) (wRandomGraphMass W))
        atTop (nhds 0) := by
      simpa using hprob.const_sub 1
    change Tendsto
      (fun n ↦ wRandomGraphEntropy W n / (completeEdgeCount n : ℝ) -
        1 / (completeEdgeCount n : ℝ) -
        (1 - finiteEventMass (A n) (wRandomGraphMass W)))
      atTop (nhds (graphonEntropy W))
    simpa only [one_div, sub_zero] using (hentropy.sub hinv).sub hcompl
  have hlowerEventually : ∀ᶠ n in atTop,
      graphonEntropy W - ε < entropyEventLowerBound W A n :=
    (tendsto_order.1 hlower).1 _ (by linarith)
  have hpPos : ∀ᶠ n in atTop,
      0 < finiteEventMass (A n) (wRandomGraphMass W) :=
    (tendsto_order.1 hprob).1 0 (by norm_num)
  have horders : ∀ᶠ n in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [hlowerEventually, hpPos, horders] with n hlowerN hpN hn
  have hA : (A n).Nonempty := by
    by_contra hne
    have hempty : A n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty, finiteEventMass] at hpN
  exact hlowerN.trans_le
    (entropyEventLowerBound_le_normalizedLogCard W A hn hA)

/-! ## A finite binomial-ball estimate -/

private theorem hamming_term_lower {N r j : ℕ}
    (hr : 0 < r) (hhalf : 2 * r ≤ N) (hj : j ≤ r) :
    r ^ r * (N - r) ^ (N - r) ≤
      r ^ j * (N - r) ^ (N - j) := by
  have hrN : r ≤ N := by omega
  have hjN : j ≤ N := hj.trans hrN
  have hpow : r ^ (r - j) ≤ (N - r) ^ (r - j) := by
    exact Nat.pow_le_pow_left (by omega) _
  calc
    r ^ r * (N - r) ^ (N - r) =
        (r ^ j * r ^ (r - j)) * (N - r) ^ (N - r) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    _ ≤ (r ^ j * (N - r) ^ (r - j)) *
        (N - r) ^ (N - r) := by gcongr
    _ = r ^ j * (N - r) ^ (N - j) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega

/-- The binomial-ball volume times the least binomial weight below the
halfway point is at most the full binomial expansion. -/
theorem hammingBallVolume_mul_weight_le (N r : ℕ)
    (hr : 0 < r) (hhalf : 2 * r ≤ N) :
    hammingBallVolume N r * (r ^ r * (N - r) ^ (N - r)) ≤ N ^ N := by
  have hsub : Finset.range (r + 1) ⊆ Finset.range (N + 1) := by
    intro j hj
    rw [Finset.mem_range] at hj ⊢
    omega
  calc
    hammingBallVolume N r * (r ^ r * (N - r) ^ (N - r)) =
        ∑ j ∈ Finset.range (r + 1),
          N.choose j * (r ^ r * (N - r) ^ (N - r)) := by
      rw [hammingBallVolume, Finset.sum_mul]
    _ ≤ ∑ j ∈ Finset.range (r + 1),
          N.choose j * (r ^ j * (N - r) ^ (N - j)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.mul_le_mul_left _
        (hamming_term_lower hr hhalf
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          N.choose j * (r ^ j * (N - r) ^ (N - j)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro j _ _
      positivity
    _ = N ^ N := by
      calc
        (∑ j ∈ Finset.range (N + 1),
            N.choose j * (r ^ j * (N - r) ^ (N - j))) =
            ∑ j ∈ Finset.range (N + 1),
              r ^ j * (N - r) ^ (N - j) * N.choose j := by
          apply Finset.sum_congr rfl
          intro j _
          ac_rfl
        _ = (r + (N - r)) ^ N := (add_pow r (N - r) N).symm
        _ = N ^ N := by rw [Nat.add_sub_of_le (by omega : r ≤ N)]

theorem hammingBallVolume_pos (N r : ℕ) :
    0 < hammingBallVolume N r := by
  have hzero : 0 ∈ Finset.range (r + 1) := by simp
  have hone : N.choose 0 ≤ hammingBallVolume N r := by
    unfold hammingBallVolume
    exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hzero
  simpa using lt_of_lt_of_le (by simp : 0 < N.choose 0) hone

private theorem nat_mul_binaryEntropy_div_eq {N r : ℕ}
    (hr : 0 < r) (hrN : r < N) :
    (N : ℝ) * binaryEntropy ((r : ℝ) / (N : ℝ)) =
      (N : ℝ) * log2 (N : ℝ) -
        (r : ℝ) * log2 (r : ℝ) -
        ((N - r : ℕ) : ℝ) * log2 ((N - r : ℕ) : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hr.trans hrN))
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsub0 : ((N - r : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt hrN))
  have hcastSub : ((N - r : ℕ) : ℝ) = (N : ℝ) - (r : ℝ) := by
    exact Nat.cast_sub (Nat.le_of_lt hrN)
  have hsumCast : (N : ℝ) = (r : ℝ) + ((N - r : ℕ) : ℝ) := by
    rw [hcastSub]
    ring
  rw [binaryEntropy_eq_formula,
    show 1 - (r : ℝ) / (N : ℝ) =
        ((N - r : ℕ) : ℝ) / (N : ℝ) by
      rw [hcastSub]
      field_simp,
    log2_div hr0 hN0, log2_div hsub0 hN0]
  field_simp [hN0]
  rw [hsumCast]
  ring

/-- Sharp binary-entropy upper bound for the lower half of a Hamming ball. -/
theorem log2_hammingBallVolume_le (N r : ℕ)
    (hr : 0 < r) (hhalf : 2 * r ≤ N) :
    log2 (hammingBallVolume N r : ℝ) ≤
      (N : ℝ) * binaryEntropy ((r : ℝ) / (N : ℝ)) := by
  have hrN : r < N := by omega
  have hN : 0 < N := hr.trans hrN
  have hNr : 0 < N - r := Nat.sub_pos_of_lt hrN
  have hcast := hammingBallVolume_mul_weight_le N r hr hhalf
  have hcastR :
      (hammingBallVolume N r : ℝ) *
          ((r : ℝ) ^ r * ((N - r : ℕ) : ℝ) ^ (N - r)) ≤
        (N : ℝ) ^ N := by
    exact_mod_cast hcast
  have hvolPos : 0 < (hammingBallVolume N r : ℝ) := by
    exact_mod_cast hammingBallVolume_pos N r
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hNrPos : 0 < ((N - r : ℕ) : ℝ) := by exact_mod_cast hNr
  have hleftPos : 0 <
      (hammingBallVolume N r : ℝ) *
        ((r : ℝ) ^ r * ((N - r : ℕ) : ℝ) ^ (N - r)) := by
    exact mul_pos hvolPos (mul_pos (pow_pos hrPos _) (pow_pos hNrPos _))
  have hrightPos : 0 < (N : ℝ) ^ N := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hleftPos hrightPos hcastR
  rw [Real.log_mul hvolPos.ne' (mul_pos (pow_pos hrPos _)
      (pow_pos hNrPos _)).ne',
    Real.log_mul (pow_pos hrPos _).ne' (pow_pos hNrPos _).ne',
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  rw [nat_mul_binaryEntropy_div_eq hr hrN, log2]
  have hnum :
      Real.log (hammingBallVolume N r : ℝ) ≤
        (N : ℝ) * Real.log (N : ℝ) -
          (r : ℝ) * Real.log (r : ℝ) -
          ((N - r : ℕ) : ℝ) * Real.log ((N - r : ℕ) : ℝ) := by
    linarith
  calc
    Real.log (hammingBallVolume N r : ℝ) / Real.log 2 ≤
        ((N : ℝ) * Real.log (N : ℝ) -
          (r : ℝ) * Real.log (r : ℝ) -
          ((N - r : ℕ) : ℝ) * Real.log ((N - r : ℕ) : ℝ)) /
            Real.log 2 := div_le_div_of_nonneg_right hnum realLogTwo_pos.le
    _ = (N : ℝ) * (Real.log (N : ℝ) / Real.log 2) -
        (r : ℝ) * (Real.log (r : ℝ) / Real.log 2) -
        ((N - r : ℕ) : ℝ) *
          (Real.log ((N - r : ℕ) : ℝ) / Real.log 2) := by ring

@[simp] theorem log2_hammingBallVolume_zero (N : ℕ) :
    log2 (hammingBallVolume N 0 : ℝ) = 0 := by
  simp [hammingBallVolume]

/-! ## Vanishing-rate edit radii -/

/-- Integer edit radius obtained by flooring a real fraction of all possible
edges. -/
def fractionalEditRadius (η : ℝ) (N : ℕ) : ℕ :=
  ⌊η * (N : ℝ)⌋₊

/-- The floored edit-radius fraction converges to its prescribed real
fraction. -/
theorem fractionalEditRadius_ratio_tendsto (η : ℝ) (hη : 0 ≤ η) :
    Tendsto
      (fun n ↦ (fractionalEditRadius η (completeEdgeCount n) : ℝ) /
        (completeEdgeCount n : ℝ))
      atTop (nhds η) := by
  exact (tendsto_nat_floor_mul_div_atTop hη).comp
    tendsto_completeEdgeCount_cast_atTop

theorem fractionalEditRadius_entropy_tendsto (η : ℝ) (hη : 0 ≤ η) :
    Tendsto
      (fun n ↦ binaryEntropy
        ((fractionalEditRadius η (completeEdgeCount n) : ℝ) /
          (completeEdgeCount n : ℝ)))
      atTop (nhds (binaryEntropy η)) :=
  binaryEntropy_continuous.tendsto η |>.comp
    (fractionalEditRadius_ratio_tendsto η hη)

/-- Eventually, the normalized logarithm of a fractional edit ball is
bounded by the binary entropy of its actual floored radius fraction. -/
theorem eventually_normalizedLog_hammingBallVolume_le
    (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) (1 / 2 : ℝ)) :
    ∀ᶠ n in atTop,
      log2 (hammingBallVolume (completeEdgeCount n)
          (fractionalEditRadius η (completeEdgeCount n)) : ℝ) /
          (completeEdgeCount n : ℝ) ≤
        binaryEntropy
          ((fractionalEditRadius η (completeEdgeCount n) : ℝ) /
            (completeEdgeCount n : ℝ)) := by
  have hratio := fractionalEditRadius_ratio_tendsto η hη.1.le
  have hpos : ∀ᶠ n in atTop,
      0 < (fractionalEditRadius η (completeEdgeCount n) : ℝ) /
        (completeEdgeCount n : ℝ) :=
    (tendsto_order.1 hratio).1 0 hη.1
  have hhalf : ∀ᶠ n in atTop,
      (fractionalEditRadius η (completeEdgeCount n) : ℝ) /
        (completeEdgeCount n : ℝ) < 1 / 2 :=
    (tendsto_order.1 hratio).2 (1 / 2) hη.2
  have hNpos : ∀ᶠ n in atTop, 0 < completeEdgeCount n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact Nat.choose_pos hn
  filter_upwards [hpos, hhalf, hNpos] with n hposN hhalfN hN
  let N := completeEdgeCount n
  let r := fractionalEditRadius η N
  change 0 < (r : ℝ) / (N : ℝ) at hposN
  change (r : ℝ) / (N : ℝ) < 1 / 2 at hhalfN
  change 0 < N at hN
  have hr : 0 < r := by
    by_contra hr0
    have : r = 0 := Nat.eq_zero_of_not_pos hr0
    rw [this] at hposN
    norm_num at hposN
  have htwo : 2 * r ≤ N := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    have : (2 : ℝ) * r < N := by
      rw [div_lt_iff₀ hNR] at hhalfN
      linarith
    exact_mod_cast this.le
  have hbound := log2_hammingBallVolume_le N r hr htwo
  have hNR : (0 : ℝ) ≤ N := by positivity
  exact div_le_iff₀ (by exact_mod_cast hN) |>.2 (by
    simpa only [mul_comm] using hbound)

/-- Epsilon-eventual form of the edit-ball entropy estimate. -/
theorem eventually_normalizedLog_hammingBallVolume_le_add
    (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) (1 / 2 : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      log2 (hammingBallVolume (completeEdgeCount n)
          (fractionalEditRadius η (completeEdgeCount n)) : ℝ) /
          (completeEdgeCount n : ℝ) <
        binaryEntropy η + ε := by
  have hentropy := fractionalEditRadius_entropy_tendsto η hη.1.le
  have heventually : ∀ᶠ n in atTop,
      binaryEntropy
          ((fractionalEditRadius η (completeEdgeCount n) : ℝ) /
            (completeEdgeCount n : ℝ)) <
        binaryEntropy η + ε :=
    (tendsto_order.1 hentropy).2 _ (by linarith)
  filter_upwards [eventually_normalizedLog_hammingBallVolume_le η hη,
    heventually] with n hle hlt
  exact hle.trans_lt hlt

end InducedStars
