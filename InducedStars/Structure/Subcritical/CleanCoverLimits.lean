import InducedStars.Structure.Subcritical.CleanCoverProbability

/-!
# A uniform positive fraction of identifiable fixed-profile covers

The constants and thresholds depend on the number of parts and a strict
upper density bound only, not on the separate fixed counts in the cells.
-/

noncomputable section
open Finset Filter Topology
open scoped BigOperators Classical
namespace InducedStars

private theorem eventually_cleanCoverNearSum_le (r : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (∑ t ∈ Finset.Icc 1 n, ((r.factorial * n.choose t * r^t : ℕ) : ℝ) *
        Real.exp (-(c * t * n))) ≤ Real.exp (-(c / 8 * n)) := by
  filter_upwards [DenseGraph.eventually_natCast_mul_le_exp_mul (r + 1) (half_pos hc),
    DenseGraph.eventually_sum_mul_choose_mul_exp_neg_le r.factorial (half_pos hc),
    eventually_ge_atTop 1] with n hn hsum hn1
  have hr : (r : ℝ) ≤ Real.exp (c / 2 * n) := by
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    calc
      (r : ℝ) ≤ ((r + 1 : ℕ) : ℝ) * n := by push_cast; nlinarith
      _ ≤ _ := hn
  calc
    _ ≤ ∑ t ∈ Finset.Icc 1 n, ((r.factorial * n.choose t : ℕ) : ℝ) *
        Real.exp (-(c / 2 * t * n)) := by
      apply Finset.sum_le_sum
      intro t ht
      have hp := pow_le_pow_left₀ (Nat.cast_nonneg r) hr t
      calc
        _ ≤ ((r.factorial * n.choose t : ℕ) : ℝ) *
            (Real.exp (c / 2 * n))^t * Real.exp (-(c * t * n)) := by
          push_cast
          gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ ≤ Real.exp (-((c / 2) / 4 * n)) := hsum
    _ = _ := by congr 1; ring

/-- The deterministic near/far union-bound expression tends to zero. -/
theorem cleanCoverUnionBound_tendsto_zero {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      (∑ t ∈ Finset.Icc 1 n,
        (((k - 1).factorial * n.choose t * (k - 1)^t : ℕ) : ℝ) *
          Real.exp (-(c / (4 * (k - 1 : ℕ)) * t * n))) +
      (k : ℝ)^n * Real.exp (-(c / (16 * (k - 1 : ℕ)^8) * (n:ℝ)^2)))
      atTop (𝓝 0) := by
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hn : 0 < c / (4 * (k - 1 : ℕ)) := by positivity
  have hf : 0 < c / (16 * (k - 1 : ℕ)^8) := by positivity
  have hlin := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (show 0 < c / (4 * (k - 1 : ℕ)) / 8 by positivity))
  have hsquare : Tendsto (fun n : ℕ ↦ (n : ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hquad := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (hsquare.const_mul_atTop (show 0 < c / (16 * (k - 1 : ℕ)^8) / 2 by positivity))
  apply squeeze_zero' (Eventually.of_forall (fun n ↦ by positivity))
    (g := fun n : ℕ ↦ Real.exp (-(c / (4 * (k - 1 : ℕ)) / 8 * n)) +
      Real.exp (-(c / (16 * (k - 1 : ℕ)^8) / 2 * (n : ℝ)^2)))
  · filter_upwards [eventually_cleanCoverNearSum_le (k - 1) hn,
      DenseGraph.eventually_pow_mul_exp_neg_sq_le k hf] with n hn hf
    exact add_le_add hn (by simpa only [Nat.cast_pow] using hf)
  · simpa only [Function.comp_apply, zero_add] using hlin.add hquad

/-- Uniformity includes every feasible cell quota; there is no profile-
dependent threshold. -/
theorem eventually_fixedProfileNonuniqueCover_probability_le
    {k : ℕ} (hk : 3 ≤ k) {c eps : ℝ} (hc : 0 < c) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : SupercriticalDivision k (Fin n))
      (p : SupercriticalEdgeProfile D) (a : ℕ),
      D.IsFull → (∀ i, a ≤ (D.parts i).card) → n ≤ 2 * (k - 1) * a →
      (∀ e, profileDensity p e ≤ Real.exp (-c)) →
      (supercriticalFixedProfileBlockModel D p).eventProbability
        (fixedProfileNonuniqueCoverEvent D p) ≤ eps := by
  filter_upwards [(cleanCoverUnionBound_tendsto_zero hk hc).eventually
    (gt_mem_nhds heps)] with n hn D p a hD hpart hscale hdensity
  exact (fixedProfileNonuniqueCover_probability_le_near_far
    hk D p hD hpart hscale hc.le hdensity).trans hn.le

def fixedProfileUniqueCoverEvent {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (p : SupercriticalEdgeProfile D) : Finset (supercriticalFixedProfileBlockModel D p).Sample :=
  Finset.univ \ fixedProfileNonuniqueCoverEvent D p

@[simp] theorem mem_fixedProfileUniqueCoverEvent {k n : ℕ}
    (D : SupercriticalDivision k (Fin n)) (p : SupercriticalEdgeProfile D)
    (S : (supercriticalFixedProfileBlockModel D p).Sample) :
    S ∈ fixedProfileUniqueCoverEvent D p ↔
      HasUniqueCoMultipartiteCover k (fixedProfileCleanGraph D p S) := by
  simp [fixedProfileUniqueCoverEvent, fixedProfileNonuniqueCoverEvent]

/-- At least half the actual independent fixed-cell samples have a unique
unordered clique cover, uniformly over all the feasible cell profiles. -/
theorem eventually_fixedProfile_uniqueCover_half
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : SupercriticalDivision k (Fin n))
      (p : SupercriticalEdgeProfile D) (a : ℕ),
      D.IsFull → (∀ i, a ≤ (D.parts i).card) → n ≤ 2 * (k - 1) * a →
      (∀ e, profileDensity p e ≤ Real.exp (-c)) →
      supercriticalProfileMultiplicity p ≤ 2 * (fixedProfileUniqueCoverEvent D p).card := by
  filter_upwards [eventually_fixedProfileNonuniqueCover_probability_le hk hc
    (by norm_num : (0 : ℝ) < 1 / 2)] with n hn D p a hD hpart hscale hdensity
  have hp := hn D p a hD hpart hscale hdensity
  rw [DenseGraph.FixedCardinalityBlockModel.eventProbability_eq_card_div] at hp
  have hpos : (0 : ℝ) < (supercriticalFixedProfileBlockModel D p).sampleSpaceCard := by
    exact_mod_cast (supercriticalFixedProfileBlockModel D p).sampleSpaceCard_pos
  have hb := (div_le_iff₀ hpos).mp hp
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (fixedProfileNonuniqueCoverEvent D p))
  rw [Finset.card_univ, supercriticalFixedProfileBlockModel_card_sample] at hcard
  rw [supercriticalFixedProfileBlockModel_sampleSpaceCard_eq] at hb
  change (fixedProfileUniqueCoverEvent D p).card +
    (fixedProfileNonuniqueCoverEvent D p).card = supercriticalProfileMultiplicity p at hcard
  have hbad : 2 * (fixedProfileNonuniqueCoverEvent D p).card ≤ supercriticalProfileMultiplicity p := by
    exact_mod_cast (show (2 : ℝ) * (fixedProfileNonuniqueCoverEvent D p).card ≤
      supercriticalProfileMultiplicity p by linarith)
  omega

end InducedStars
