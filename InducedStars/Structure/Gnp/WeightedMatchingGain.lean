import InducedStars.Structure.Gnp.WeightedMatching
import InducedStars.Structure.Gnp.WeightedPartition
import DenseGraph.Combinatorics.MatchingCoefficientGrowth
import DenseGraph.Combinatorics.LogarithmicGain

/-!
# Uniform weighted matching gain on a positive retained support

Paper: `eqn:critical-matching-transfer-K1k` and the conclusion of
`lemma:critical-gnp-comparison-K1k` in `paper/gnp.tex`.
A fixed positive fraction of available vertices supplies an `exp(c n log n)`
gain, after any fixed exponential cost and the matching activity. Thresholds
are chosen before the retained key, not separately for each key.
-/

noncomputable section
open Filter Finset Set
open scoped Topology BigOperators

namespace InducedStars

/-- Fixed positive activity costs only exponentially in `n`; a linear-size
matching still gives a uniform positive `n log n` gain. -/
theorem eventually_matchingCoefficient_activity_gain
    (a : ℝ) (ha : 0 < a) (z : ℝ) (hz : 0 < z) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ q : ℕ,
      a * n ≤ q → q ≤ n →
        Real.exp (C * n + (a / 16) * n * Real.log n) ≤
          (DenseGraph.labeledMatchingCoefficient (2 * q) q : ℝ) * z^q := by
  filter_upwards [DenseGraph.eventually_matchingCoefficient_exponential_gain a ha,
    DenseGraph.eventually_linear_sub_mul_log_le (by positivity : 0 < a / 16)
      (C + |Real.log z|) 0] with n hmatching hbudget
  intro q hql hqu
  have hM : Real.exp ((a / 8) * n * Real.log n) ≤
      (DenseGraph.labeledMatchingCoefficient (2 * q) q : ℝ) := by
    have hfour : (1 : ℝ) ≤ 4^q := one_le_pow₀ (by norm_num)
    exact (le_mul_of_one_le_left (Real.exp_nonneg _) hfour).trans
      (hmatching q (2 * q) hql le_rfl)
  have hzpow : Real.exp (-|Real.log z| * n) ≤ z^q := by
    have heq : z^q = Real.exp ((q : ℝ) * Real.log z) := by
      rw [Real.exp_nat_mul, Real.exp_log hz]
    rw [heq]
    apply Real.exp_le_exp.mpr
    have hqn : (q : ℝ) ≤ n := by exact_mod_cast hqu
    have h1 := mul_le_mul_of_nonneg_left (neg_abs_le (Real.log z))
      (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    have h2 := mul_le_mul_of_nonpos_left hqn (neg_nonpos.mpr (abs_nonneg (Real.log z)))
    nlinarith
  calc
    _ ≤ Real.exp ((a / 8) * n * Real.log n) * Real.exp (-|Real.log z| * n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith
    _ ≤ _ := mul_le_mul hM hzpow (Real.exp_nonneg _) (Nat.cast_nonneg _)

/-- The actual sparse-side weighted sum of every key with retained support
at least `a*n` is suppressed by a fixed positive `n log n` exponent, even
after any fixed linear exponential cost. The smallness reserve leaves room
both for the sparse edges and for the inserted matching. -/
theorem eventually_retainedKeyWeightedSparseSum_matching_gain
    (k : ℕ) (hk : 3 ≤ k) (eta a ω : ℝ)
    (heta : 0 < eta) (ha : 0 < a) (ha1 : a ≤ 1)
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hreserve : subcriticalSparseSideConstant k * eta ≤ ω / 4)
    (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ K : SubcriticalRetainedKey k (Fin n),
      a * n ≤ K.support.card →
        Real.exp (C * n + (a / 128) * n * Real.log n) *
          retainedKeyWeightedSparseSum K eta (pK k) ≤
            gnpInducedStarCutBallMass k n (pK k) zeroGraphon ω := by
  have hp := pK_mem_Ioo (show 2 ≤ k by omega)
  let z : ℝ := pK k / (1 - pK k)
  have hz : 0 < z := div_pos hp.1 (sub_pos.mpr hp.2)
  have hscale : Tendsto (fun n : ℕ ↦ (a / 8) * n) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).const_mul_atTop
      (by positivity)
  have hscaleω : Tendsto (fun n : ℕ ↦ ω * n) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).const_mul_atTop hω
  filter_upwards [eventually_ge_atTop (3 : ℕ),
    hscale.eventually (eventually_ge_atTop (1 : ℝ)),
    hscaleω.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_matchingCoefficient_activity_gain (a / 8) (by positivity) z hz C]
    with n hn hlarge hωlarge hgain
  intro K hsupport
  let q : ℕ := Nat.floor (a * n / 4)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hqu : (q : ℝ) ≤ a * n / 4 := Nat.floor_le (by positivity)
  have hql : a / 8 * n ≤ q := by
    have hfloor := Nat.sub_one_lt_floor (a * (n : ℝ) / 4)
    change a * (n : ℝ) / 4 - 1 < (q : ℝ) at hfloor
    nlinarith
  have hqn4 : (q : ℝ) ≤ (n : ℝ) / 4 := by
    have hmul := mul_le_mul_of_nonneg_right ha1 hnpos.le
    nlinarith
  have hqn : q ≤ n := by exact_mod_cast (show (q : ℝ) ≤ n by linarith)
  have hqSupport : 2 * q ≤ K.support.card := by
    have : 2 * (q : ℝ) ≤ K.support.card := by nlinarith [mul_pos ha hnpos]
    exact_mod_cast this
  have hpartition : K.remainder.card + K.support.card = n := by
    simpa only [SubcriticalRetainedKey.remainder, Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (K.support.subset_univ)
  have hs : K.remainder.card + 2 * q ≤ n := by omega
  let B := Finset.range (Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) + 1)
  have hb (b : ℕ) (hb : b ∈ B) : (b : ℝ) ≤ ω / 4 * (n : ℝ)^2 := by
    have hnat : b ≤ Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) :=
      Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hfloor := Nat.floor_le
      (show 0 ≤ subcriticalSparseSideConstant k * eta * (n : ℝ)^2 from
        mul_nonneg (mul_nonneg (subcriticalSparseSideConstant_pos hk).le heta.le) (sq_nonneg _))
    have hcastFloor : (b : ℝ) ≤
        (Nat.floor (subcriticalSparseSideConstant k * eta * (n : ℝ)^2) : ℝ) := by
      exact_mod_cast hnat
    have hcast : (b : ℝ) ≤ subcriticalSparseSideConstant k * eta * (n : ℝ)^2 :=
      hcastFloor.trans hfloor
    exact hcast.trans (mul_le_mul_of_nonneg_right hreserve (sq_nonneg _))
  have hfeasible : ∀ b ∈ B, b + q ≤ completeEdgeCount n := by
    intro b hbB
    have hbound := hb b hbB
    have hωsq := mul_le_mul_of_nonneg_right hω1 (sq_nonneg (n : ℝ))
    have hN : (completeEdgeCount n : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      rw [completeEdgeCount, Nat.cast_choose_two]
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpoly := mul_nonneg (show 0 ≤ (n : ℝ) - 3 by linarith) hnpos.le
    have : (b : ℝ) + q ≤ (completeEdgeCount n : ℝ) := by rw [hN]; nlinarith
    exact_mod_cast this
  have hsmall : ∀ b ∈ B, 2 * ((b + q : ℕ) : ℝ) / (n : ℝ)^2 < ω := by
    intro b hbB
    apply (div_lt_iff₀ (sq_pos_of_pos hnpos)).mpr
    have hbound := hb b hbB
    have hωn := mul_le_mul_of_nonneg_right hωlarge hnpos.le
    push_cast
    nlinarith [mul_pos hω (sq_pos_of_pos hnpos)]
  have htransfer := gnpSparseMatchingTransfer_zeroCutBall hk (by omega) hs hp B hfeasible hsmall
  have hcoef : Real.exp (C * n + (a / 128) * n * Real.log n) ≤
      (((2 * q).factorial / (2^q * q.factorial) : ℕ) : ℝ) * z^q := by
    have h := hgain q hql hqn
    simpa only [DenseGraph.labeledMatchingCoefficient, Nat.sub_self, Nat.factorial_zero,
      mul_one, div_div, show (8 : ℝ) * 16 = 128 by norm_num] using h
  have hS : 0 ≤ retainedKeyWeightedSparseSum K eta (pK k) := by
    unfold retainedKeyWeightedSparseSum
    apply mul_nonneg (pow_nonneg (sub_pos.mpr hp.2).le _)
    exact Finset.sum_nonneg fun b _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.le _)
  exact (mul_le_mul_of_nonneg_right hcoef hS).trans
    (by simpa only [retainedKeyWeightedSparseSum, B, z, mul_assoc] using htransfer)

end InducedStars
