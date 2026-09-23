import DenseGraph.Combinatorics.BinomialEntropy
import InducedStars.Analysis.RateMinimization
import InducedStars.Structure.Critical.BinomialExpansion
import Mathlib.Tactic

/-!
# Entropy of balanced retained-support reference slices

This file gives the uniform entropy lower bound used when a sparse vertex set
is prescribed.  The remaining vertices are divided as evenly as possible;
the assertion is uniform both in a sufficiently small sparse-set size and in
the graph chosen on that sparse set.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- Cross-coordinate capacity of an exactly balanced ordered partition of
the `n-s` retained vertices. -/
def criticalRetainedSupportCapacity (k n s : ℕ) : ℕ :=
  DenseGraph.balancedMultipartiteCrossCapacity (k - 1) (n - s)

/-- Selected cross coordinates after forcing the balanced retained parts to
be cliques and prescribing `t` edges on the sparse set.  Natural subtraction
makes the declaration total outside the eventual feasible range. -/
def criticalRetainedSupportSelectedCount (k n s t : ℕ) : ℕ :=
  criticalEdgeCount k n -
    (t + DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s))

/-- The retained-support selected count before prescribing the `t` sparse
edges, expressed relative to the balanced full reference count. -/
def criticalRetainedSupportPreSelectedCount (k n s : ℕ) : ℕ :=
  criticalTargetSelectedCount k n + criticalSelectedIncrease k n s


/-- The limiting retained-support capacity in `n²` normalization. -/
noncomputable def criticalReferenceCapacitySquareDensity (k : ℕ) : ℝ :=
  ((k - 2 : ℕ) : ℝ) / (2 * ((k - 1 : ℕ) : ℝ))

/-- The limiting retained-support selected count in `n²` normalization. -/
noncomputable def criticalReferenceSelectedSquareDensity (k : ℕ) : ℝ :=
  (gammaK k - 1 / ((k - 1 : ℕ) : ℝ)) / 2

theorem criticalReferenceCapacitySquareDensity_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalReferenceCapacitySquareDensity k := by
  unfold criticalReferenceCapacitySquareDensity
  exact div_pos (by exact_mod_cast (show 0 < k - 2 by omega))
    (mul_pos (by norm_num) (by
      exact_mod_cast (show 0 < k - 1 by omega)))

theorem criticalReferenceSelectedSquareDensity_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalReferenceSelectedSquareDensity k := by
  have hgap := one_div_parts_lt_gammaK hk
  unfold criticalReferenceSelectedSquareDensity
  positivity

theorem criticalReferenceSelectedSquareDensity_lt_capacity
    {k : ℕ} (hk : 3 ≤ k) :
    criticalReferenceSelectedSquareDensity k <
      criticalReferenceCapacitySquareDensity k := by
  have hp := pK_lt_one (show 2 ≤ k by omega)
  have hb := criticalReferenceCapacitySquareDensity_pos hk
  have hratio :
      criticalReferenceSelectedSquareDensity k =
        criticalReferenceCapacitySquareDensity k * pK k := by
    unfold criticalReferenceSelectedSquareDensity
    unfold criticalReferenceCapacitySquareDensity
    have hmain := gammaK_mul_sub_one_div k hk
    have hr : (0 : ℝ) < (k - 1 : ℕ) := by
      exact_mod_cast (show 0 < k - 1 by omega)
    have hs : (0 : ℝ) < (k - 2 : ℕ) := by
      exact_mod_cast (show 0 < k - 2 by omega)
    field_simp [hr.ne', hs.ne'] at hmain ⊢
    nlinarith
  rw [hratio]
  nlinarith [mul_pos hb (pK_pos (show 2 ≤ k by omega))]

/-- The natural-log entropy exponent of the limiting critical reference
slice equals the paper's base-two entropy density after conversion to nats. -/
theorem criticalReferenceEntropyExponent_eq
    {k : ℕ} (hk : 3 ≤ k) :
    criticalReferenceCapacitySquareDensity k * Real.binEntropy (pK k) =
      entropyDensity k (gammaK k) * Real.log 2 / 2 := by
  rw [entropyDensity_of_ge hk le_rfl, entropyDensityUpper]
  have harg :
      (((k - 1 : ℕ) : ℝ) * gammaK k - 1) / (k - 2 : ℕ) = pK k := by
    rw [mul_comm]
    exact gammaK_mul_sub_one_div k hk
  rw [harg]
  unfold criticalReferenceCapacitySquareDensity binaryEntropy
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  field_simp [hr.ne', realLogTwo_ne_zero]
  norm_num [Nat.cast_sub (show 2 ≤ k by omega),
    Nat.cast_sub (show 1 ≤ k by omega)]
  ring

/-- The two-coordinate entropy perspective used to pass from normalized
capacity and selected count to a binomial exponent. -/
noncomputable def criticalNormalizedBinomialEntropy (x y : ℝ) : ℝ :=
  x * Real.binEntropy (y / x)

theorem criticalNormalizedBinomialEntropy_continuousAt
    {x y : ℝ} (hx : x ≠ 0) :
    ContinuousAt (fun z : ℝ × ℝ ↦
      criticalNormalizedBinomialEntropy z.1 z.2) (x, y) := by
  unfold criticalNormalizedBinomialEntropy
  fun_prop

theorem criticalNormalizedBinomialEntropy_at_reference
    {k : ℕ} (hk : 3 ≤ k) :
    criticalNormalizedBinomialEntropy
        (criticalReferenceCapacitySquareDensity k)
        (criticalReferenceSelectedSquareDensity k) =
      entropyDensity k (gammaK k) * Real.log 2 / 2 := by
  have hb := criticalReferenceCapacitySquareDensity_pos hk
  have hratio :
      criticalReferenceSelectedSquareDensity k /
          criticalReferenceCapacitySquareDensity k = pK k := by
    have hmain :
        criticalReferenceSelectedSquareDensity k =
          criticalReferenceCapacitySquareDensity k * pK k := by
      unfold criticalReferenceSelectedSquareDensity
      unfold criticalReferenceCapacitySquareDensity
      have hgamma := gammaK_mul_sub_one_div k hk
      have hr : (0 : ℝ) < (k - 1 : ℕ) := by
        exact_mod_cast (show 0 < k - 1 by omega)
      have hs : (0 : ℝ) < (k - 2 : ℕ) := by
        exact_mod_cast (show 0 < k - 2 by omega)
      field_simp [hr.ne', hs.ne'] at hgamma ⊢
      nlinarith
    rw [hmain]
    field_simp [hb.ne']
  rw [criticalNormalizedBinomialEntropy, hratio,
    criticalReferenceEntropyExponent_eq hk]

theorem criticalTargetCapacity_squareDensity_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦ (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (criticalReferenceCapacitySquareDensity k)) := by
  have h := (criticalTargetCapacity_orderedSquare_tendsto k hk).const_mul
    (1 / 2 : ℝ)
  convert h using 1
  · funext n
    ring
  · unfold criticalReferenceCapacitySquareDensity
    ring

theorem criticalTargetSelectedCount_squareDensity_tendsto
    (k : ℕ) (hk : 3 ≤ k) :
    Tendsto
      (fun n : ℕ ↦
        (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2)
      atTop (nhds (criticalReferenceSelectedSquareDensity k)) := by
  have h := (criticalTargetSelectedCount_orderedSquare_tendsto k hk).const_mul
    (1 / 2 : ℝ)
  convert h using 1
  · funext n
    ring
  · unfold criticalReferenceSelectedSquareDensity
    ring

/-! ## Exact retained-support bookkeeping -/

theorem criticalTargetCapacity_eq_loss_add_retained
    {k n s : ℕ}
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n) :
    criticalTargetCapacity k n =
      criticalCapacityLoss k n s + criticalRetainedSupportCapacity k n s +
        Nat.choose s 2 := by
  calc
    criticalTargetCapacity k n =
        (criticalTargetCapacity k n - criticalMaximumCombinedCapacity k n s) +
          criticalMaximumCombinedCapacity k n s :=
      (Nat.sub_add_cancel hcapacity).symm
    _ = criticalCapacityLoss k n s +
          criticalRetainedSupportCapacity k n s + Nat.choose s 2 := by
      simp [criticalCapacityLoss, criticalMaximumCombinedCapacity,
        criticalRetainedSupportCapacity, Nat.add_assoc]

theorem criticalRetainedSupportSelectedCount_eq_pre_sub
    {k n s t : ℕ}
    (hreference :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n ≤
        criticalEdgeCount k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n)
    (_ht : t ≤ criticalRetainedSupportPreSelectedCount k n s) :
    criticalRetainedSupportSelectedCount k n s t =
      criticalRetainedSupportPreSelectedCount k n s - t := by
  unfold criticalRetainedSupportSelectedCount
  unfold criticalRetainedSupportPreSelectedCount criticalTargetSelectedCount
  unfold criticalSelectedIncrease
  omega

/-- Positivity of the totalized selected count is exactly the finite guard
that the forced retained-support and sparse edges fit below the critical edge
count. -/
theorem criticalRetainedSupport_forcedEdges_lt_edgeCount_of_selected_pos
    {k n s t : ℕ}
    (hpos : 0 < criticalRetainedSupportSelectedCount k n s t) :
    t + DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) <
      criticalEdgeCount k n := by
  unfold criticalRetainedSupportSelectedCount at hpos
  omega

/-- Weak form of the retained-support forced-edge feasibility guard. -/
theorem criticalRetainedSupport_forcedEdges_le_edgeCount_of_selected_pos
    {k n s t : ℕ}
    (hpos : 0 < criticalRetainedSupportSelectedCount k n s t) :
    t + DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
      criticalEdgeCount k n :=
  (criticalRetainedSupport_forcedEdges_lt_edgeCount_of_selected_pos hpos).le

theorem criticalRetainedSupportPreSelectedCount_sub_target_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    criticalRetainedSupportPreSelectedCount k n s -
        criticalTargetSelectedCount k n ≤ s * (n - s) := by
  have hsum := criticalCapacityLoss_add_selectedIncrease
    (k := k) (n := n) (s := s) hk hs hcapacity hinternal
  unfold criticalRetainedSupportPreSelectedCount
  omega

theorem criticalTargetCapacity_sub_retained_le
    {k n s : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hcapacity : criticalMaximumCombinedCapacity k n s ≤
      criticalTargetCapacity k n)
    (hinternal :
      DenseGraph.balancedMultipartiteInternalCapacity (k - 1) (n - s) ≤
        DenseGraph.balancedMultipartiteInternalCapacity (k - 1) n) :
    criticalTargetCapacity k n - criticalRetainedSupportCapacity k n s ≤
      s * (n - s) + Nat.choose s 2 := by
  have hsum := criticalCapacityLoss_add_selectedIncrease
    (k := k) (n := n) (s := s) hk hs hcapacity hinternal
  have hcap := criticalTargetCapacity_eq_loss_add_retained hcapacity
  omega

/-! ## Uniform normalized retained slices -/

-- This uniform finite perturbation calculation needs a larger local
-- elaboration budget than Lean's default.
set_option maxHeartbeats 800000 in
/-- If the allowed sparse fraction is sufficiently small, the retained
capacity and selected count stay uniformly close to their full-reference
limits.  The conclusion includes all finite feasibility guards. -/
theorem eventually_criticalRetainedSupport_normalized_close
    (k : ℕ) (hk : 3 ≤ k) {zeta : ℝ} (hzeta : 0 < zeta)
    (hzetaSelected : 4 * zeta < criticalReferenceSelectedSquareDensity k)
    (hzetaGap : 4 * zeta <
      criticalReferenceCapacitySquareDensity k -
        criticalReferenceSelectedSquareDensity k) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
        (s : ℝ) ≤ delta * (n : ℝ) →
        ∀ t : ℕ, t ≤ Nat.choose s 2 →
          0 < criticalRetainedSupportSelectedCount k n s t ∧
          criticalRetainedSupportSelectedCount k n s t ≤
            criticalRetainedSupportCapacity k n s ∧
          |(criticalRetainedSupportCapacity k n s : ℝ) / (n : ℝ) ^ 2 -
              criticalReferenceCapacitySquareDensity k| < zeta ∧
          |(criticalRetainedSupportSelectedCount k n s t : ℝ) /
                (n : ℝ) ^ 2 -
              criticalReferenceSelectedSquareDensity k| < zeta := by
  let delta : ℝ := min (1 / 32) (zeta / 16)
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta32 : delta ≤ 1 / 32 := min_le_left _ _
  have hdeltaZeta : delta ≤ zeta / 16 := min_le_right _ _
  have hdeltaOne : delta ≤ 1 := by linarith
  have hNclose : ∀ᶠ n : ℕ in atTop,
      |(criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2 -
          criticalReferenceCapacitySquareDensity k| < zeta / 4 := by
    have hlim := criticalTargetCapacity_squareDensity_tendsto k hk
    have hevent := hlim.eventually
      (Metric.ball_mem_nhds _ (div_pos hzeta (by norm_num : (0 : ℝ) < 4)))
    filter_upwards [hevent] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  have hMclose : ∀ᶠ n : ℕ in atTop,
      |(criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2 -
          criticalReferenceSelectedSquareDensity k| < zeta / 4 := by
    have hlim := criticalTargetSelectedCount_squareDensity_tendsto k hk
    have hevent := hlim.eventually
      (Metric.ball_mem_nhds _ (div_pos hzeta (by norm_num : (0 : ℝ) < 4)))
    filter_upwards [hevent] with n hn
    simpa only [Metric.mem_ball, Real.dist_eq] using hn
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hNclose, hMclose,
    eventually_balancedInternalCapacity_le_criticalEdgeCount k hk,
    eventually_criticalTargetSelectedCount_mem_Ioo k hk,
    eventually_ge_atTop (4 * (k - 1) ^ 2),
    eventually_ge_atTop 2] with n hNclose hMclose hreference hselectedFull hnLarge hnTwo
  intro s hs hsSmall t ht
  have hnPos : 0 < n := by omega
  have hnSqPos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  by_cases hsZero : s = 0
  · subst s
    have htZero : t = 0 := by simpa using ht
    subst t
    exact ⟨by
        simpa [criticalRetainedSupportSelectedCount,
          criticalTargetSelectedCount] using hselectedFull.1,
      by
        simpa [criticalRetainedSupportCapacity,
          criticalRetainedSupportSelectedCount,
          criticalTargetCapacity, criticalTargetSelectedCount] using
            hselectedFull.2.le,
      by
        have h := lt_trans hNclose (by nlinarith : zeta / 4 < zeta)
        simpa [criticalRetainedSupportCapacity,
          criticalTargetCapacity] using h,
      by
        have h := lt_trans hMclose (by nlinarith : zeta / 4 < zeta)
        simpa [criticalRetainedSupportSelectedCount,
          criticalTargetSelectedCount] using h⟩
  · have hsOne : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hsZero
    have hsmallReal : (16 : ℝ) * (s : ℝ) ≤ (n : ℝ) := by
      calc
        (16 : ℝ) * (s : ℝ) ≤ 16 * (delta * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hsSmall (by norm_num)
        _ ≤ (n : ℝ) := by
          have hn0 : (0 : ℝ) ≤ n := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hdelta32 hn0]
    have hsmall : 16 * s ≤ n := by exact_mod_cast hsmallReal
    have hcapacity := criticalMaximumCombinedCapacity_le_target
      hk hsOne hsmall hnLarge
    have hinternal := criticalBalancedInternalCapacity_mono_sparse
      hk hsOne hsmall hnLarge
    have hNle : criticalRetainedSupportCapacity k n s ≤
        criticalTargetCapacity k n := by
      have hcapEq := criticalTargetCapacity_eq_loss_add_retained hcapacity
      omega
    have hNdiffNat :
        criticalTargetCapacity k n - criticalRetainedSupportCapacity k n s ≤
          s * (n - s) + Nat.choose s 2 :=
      criticalTargetCapacity_sub_retained_le hk hs hcapacity hinternal
    have hchoose : Nat.choose s 2 ≤ s ^ 2 := Nat.choose_le_pow s 2
    have hsn : s * (n - s) ≤ s * n :=
      Nat.mul_le_mul_left s (Nat.sub_le n s)
    have hperturbReal :
        ((criticalTargetCapacity k n -
          criticalRetainedSupportCapacity k n s : ℕ) : ℝ) ≤
            2 * delta * (n : ℝ) ^ 2 := by
      have hsR : (0 : ℝ) ≤ s := by positivity
      have hnR : (0 : ℝ) ≤ n := by positivity
      have hsSq : (s : ℝ) ^ 2 ≤ delta * (n : ℝ) ^ 2 := by
        have hsSq' : (s : ℝ) ^ 2 ≤
            delta ^ 2 * (n : ℝ) ^ 2 := by nlinarith
        have hdSq : delta ^ 2 ≤ delta := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hdSq (sq_nonneg (n : ℝ))]
      have hsnR : ((s * (n - s) : ℕ) : ℝ) ≤
          delta * (n : ℝ) ^ 2 := by
        push_cast
        rw [Nat.cast_sub hs]
        calc
          (s : ℝ) * ((n : ℝ) - (s : ℝ)) ≤
              (s : ℝ) * (n : ℝ) := by nlinarith
          _ ≤ (delta * (n : ℝ)) * (n : ℝ) := by
            exact mul_le_mul_of_nonneg_right hsSmall hnR
          _ = delta * (n : ℝ) ^ 2 := by ring
      have hnatR :
          ((criticalTargetCapacity k n -
              criticalRetainedSupportCapacity k n s : ℕ) : ℝ) ≤
            ((s * (n - s) + Nat.choose s 2 : ℕ) : ℝ) := by
        exact_mod_cast hNdiffNat
      have hchooseR : (Nat.choose s 2 : ℝ) ≤ (s : ℝ) ^ 2 := by
        exact_mod_cast hchoose
      push_cast at hnatR
      calc
        ((criticalTargetCapacity k n -
            criticalRetainedSupportCapacity k n s : ℕ) : ℝ) ≤
            (s : ℝ) * (n - s : ℕ) + (Nat.choose s 2 : ℝ) := hnatR
        _ ≤ delta * (n : ℝ) ^ 2 + (s : ℝ) ^ 2 :=
          add_le_add (by simpa only [Nat.cast_mul] using hsnR) hchooseR
        _ ≤ delta * (n : ℝ) ^ 2 + delta * (n : ℝ) ^ 2 :=
          add_le_add (le_refl _) hsSq
        _ = 2 * delta * (n : ℝ) ^ 2 := by ring
    have hNperturb :
        |(criticalRetainedSupportCapacity k n s : ℝ) / (n : ℝ) ^ 2 -
          (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2| ≤
            2 * delta := by
      rw [← sub_div]
      rw [abs_div, abs_of_nonneg hnSqPos.le]
      apply (div_le_iff₀ hnSqPos).2
      have hNleR :
          (criticalRetainedSupportCapacity k n s : ℝ) ≤
            (criticalTargetCapacity k n : ℝ) := by
        exact_mod_cast hNle
      rw [abs_of_nonpos (sub_nonpos.mpr hNleR), neg_sub,
        ← Nat.cast_sub hNle]
      exact hperturbReal
    have hNretClose :
        |(criticalRetainedSupportCapacity k n s : ℝ) / (n : ℝ) ^ 2 -
            criticalReferenceCapacitySquareDensity k| < zeta := by
      calc
        |_ - _| ≤
            |(criticalRetainedSupportCapacity k n s : ℝ) / (n : ℝ) ^ 2 -
              (criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2| +
            |(criticalTargetCapacity k n : ℝ) / (n : ℝ) ^ 2 -
              criticalReferenceCapacitySquareDensity k| := abs_sub_le _ _ _
        _ < 2 * delta + zeta / 4 := add_lt_add_of_le_of_lt hNperturb hNclose
        _ < zeta := by nlinarith
    have hpreDiff :
        criticalRetainedSupportPreSelectedCount k n s -
            criticalTargetSelectedCount k n ≤ s * (n - s) :=
      criticalRetainedSupportPreSelectedCount_sub_target_le
        hk hs hcapacity hinternal
    have htargetLePre : criticalTargetSelectedCount k n ≤
        criticalRetainedSupportPreSelectedCount k n s := by
      simp [criticalRetainedSupportPreSelectedCount]
    have htLeSq : t ≤ s ^ 2 := ht.trans hchoose
    have htTarget : t < criticalTargetSelectedCount k n := by
      have hMlower :
          (criticalReferenceSelectedSquareDensity k - zeta / 4) *
              (n : ℝ) ^ 2 < (criticalTargetSelectedCount k n : ℝ) := by
        have hlower :
            criticalReferenceSelectedSquareDensity k - zeta / 4 <
              (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2 := by
          rw [abs_lt] at hMclose
          linarith
        exact (lt_div_iff₀ hnSqPos).mp hlower
      have htR : (t : ℝ) ≤ delta * (n : ℝ) ^ 2 := by
        have hsSq : (s : ℝ) ^ 2 ≤ delta * (n : ℝ) ^ 2 := by
          have hsSq' : (s : ℝ) ^ 2 ≤
              delta ^ 2 * (n : ℝ) ^ 2 := by nlinarith
          have hdSq : delta ^ 2 ≤ delta := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hdSq (sq_nonneg (n : ℝ))]
        exact (by exact_mod_cast htLeSq : (t : ℝ) ≤ (s : ℝ) ^ 2) |>.trans hsSq
      have hcoef : delta <
          criticalReferenceSelectedSquareDensity k - zeta / 4 := by
        nlinarith
      have hcoefPos : 0 <
          criticalReferenceSelectedSquareDensity k - zeta / 4 :=
        lt_trans hdelta hcoef
      have htReal : (t : ℝ) < criticalTargetSelectedCount k n := by
        nlinarith [mul_pos hcoefPos hnSqPos]
      exact (by exact_mod_cast htReal)
    have htPre : t ≤ criticalRetainedSupportPreSelectedCount k n s :=
      htTarget.le.trans htargetLePre
    have hselectedEq := criticalRetainedSupportSelectedCount_eq_pre_sub
      hreference hinternal htPre
    have hMpositive : 0 < criticalRetainedSupportSelectedCount k n s t := by
      rw [hselectedEq]
      omega
    have hMperturbReal :
        |(criticalRetainedSupportSelectedCount k n s t : ℝ) /
              (n : ℝ) ^ 2 -
            (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2| ≤
          2 * delta := by
      rw [← sub_div, abs_div, abs_of_nonneg hnSqPos.le]
      apply (div_le_iff₀ hnSqPos).2
      have hsnR : ((s * (n - s) : ℕ) : ℝ) ≤
          delta * (n : ℝ) ^ 2 := by
        push_cast
        rw [Nat.cast_sub hs]
        nlinarith
      have htR : (t : ℝ) ≤ delta * (n : ℝ) ^ 2 := by
        have hsSq : (s : ℝ) ^ 2 ≤ delta * (n : ℝ) ^ 2 := by
          have hsSq' : (s : ℝ) ^ 2 ≤
              delta ^ 2 * (n : ℝ) ^ 2 := by nlinarith
          have hdSq : delta ^ 2 ≤ delta := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hdSq (sq_nonneg (n : ℝ))]
        exact (by exact_mod_cast htLeSq : (t : ℝ) ≤ (s : ℝ) ^ 2) |>.trans hsSq
      have hpreDiffR :
          (criticalRetainedSupportPreSelectedCount k n s : ℝ) -
              (criticalTargetSelectedCount k n : ℝ) ≤
            delta * (n : ℝ) ^ 2 := by
        have hpreDiffCast :
            ((criticalRetainedSupportPreSelectedCount k n s -
                criticalTargetSelectedCount k n : ℕ) : ℝ) ≤
              ((s * (n - s) : ℕ) : ℝ) := by
          exact_mod_cast hpreDiff
        rw [Nat.cast_sub htargetLePre] at hpreDiffCast
        exact hpreDiffCast.trans hsnR
      have htargetLePreR :
          (criticalTargetSelectedCount k n : ℝ) ≤
            (criticalRetainedSupportPreSelectedCount k n s : ℝ) := by
        exact_mod_cast htargetLePre
      have hselectedCast :
          (criticalRetainedSupportSelectedCount k n s t : ℝ) =
            (criticalRetainedSupportPreSelectedCount k n s : ℝ) - (t : ℝ) := by
        rw [hselectedEq, Nat.cast_sub htPre]
      rw [hselectedCast]
      calc
        |(criticalRetainedSupportPreSelectedCount k n s : ℝ) - (t : ℝ) -
            (criticalTargetSelectedCount k n : ℝ)| ≤
            ((criticalRetainedSupportPreSelectedCount k n s : ℝ) -
              (criticalTargetSelectedCount k n : ℝ)) + (t : ℝ) := by
          rw [show (criticalRetainedSupportPreSelectedCount k n s : ℝ) - (t : ℝ) -
              (criticalTargetSelectedCount k n : ℝ) =
              ((criticalRetainedSupportPreSelectedCount k n s : ℝ) -
                (criticalTargetSelectedCount k n : ℝ)) - (t : ℝ) by ring]
          rw [abs_le]
          constructor <;> nlinarith
        _ ≤ delta * (n : ℝ) ^ 2 + delta * (n : ℝ) ^ 2 :=
          add_le_add hpreDiffR htR
        _ = 2 * delta * (n : ℝ) ^ 2 := by ring
    have hMretClose :
        |(criticalRetainedSupportSelectedCount k n s t : ℝ) /
                (n : ℝ) ^ 2 -
            criticalReferenceSelectedSquareDensity k| < zeta := by
      calc
        |_ - _| ≤
            |(criticalRetainedSupportSelectedCount k n s t : ℝ) /
                (n : ℝ) ^ 2 -
              (criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2| +
            |(criticalTargetSelectedCount k n : ℝ) / (n : ℝ) ^ 2 -
              criticalReferenceSelectedSquareDensity k| := abs_sub_le _ _ _
        _ < 2 * delta + zeta / 4 := add_lt_add_of_le_of_lt hMperturbReal hMclose
        _ < zeta := by nlinarith
    have hMNreal :
        (criticalRetainedSupportSelectedCount k n s t : ℝ) <
          (criticalRetainedSupportCapacity k n s : ℝ) := by
      have hNlower := neg_lt_of_abs_lt hNretClose
      have hMupper := lt_of_abs_lt hMretClose
      apply (div_lt_div_iff_of_pos_right hnSqPos).mp
      nlinarith
    have hMN : criticalRetainedSupportSelectedCount k n s t ≤
        criticalRetainedSupportCapacity k n s := by
      exact_mod_cast hMNreal.le
    exact ⟨hMpositive, hMN, hNretClose, hMretClose⟩

end InducedStars
