import InducedStars.Structure.Subcritical.DistinguishedReferenceFiber

/-!
# Uniform finite headroom for distinguished references

All thresholds depend only on a positive lower support fraction, the core
order, and the chosen density window. They are uniform over the finite
target/remainder edge counts in a compact density band.
-/

noncomputable section
open Filter Finset Set Topology
open scoped Classical BigOperators
namespace InducedStars

theorem subcriticalReference_support_lower {k n m b : ℕ} (hk : 3 ≤ k)
    {a : ℝ} (ha : 0 < a)
    (hmu : a ≤ subcriticalReferenceMass k n m b)
    (hscale : (4 : ℝ) * (k - 1 : ℕ) ≤ a * n) :
    2 * (k - 1) ≤ subcriticalReferenceSupportSize k n m b ∧
      a * n ≤ 2 * (subcriticalReferenceSupportSize k n m b : ℝ) := by
  have hr : (2 : ℝ) ≤ (k - 1 : ℕ) := by exact_mod_cast (show 2 ≤ k - 1 by omega)
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hm := mul_le_mul_of_nonneg_right hmu hn0
  have hf := (subcriticalReferenceSupportSize_floor_bounds k n m b).2
  constructor
  · exact_mod_cast (show (2 : ℝ) * (k - 1 : ℕ) ≤
      (subcriticalReferenceSupportSize k n m b : ℝ) by linarith)
  · linarith

theorem subcriticalReference_headroom_of_scale {k n m b : ℕ} (hk : 3 ≤ k)
    (hn : 2 ≤ n)
    (hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k))
    {a delta : ℝ} (ha : 0 < a) (hd : 0 ≤ delta)
    (hmu : a ≤ subcriticalReferenceMass k n m b)
    (hscale : (4 : ℝ) * (k - 1 : ℕ) ≤ a * n)
    (hmean : (128 : ℝ) * k ≤ delta * a^2 * n)
    (hpair : (16 : ℝ) * ((k - 1 : ℕ) : ℝ)^2 ≤ delta * a^2 * (n : ℝ)^2) :
    ∃ hrq : k - 1 ≤ subcriticalReferenceSupportSize k n m b,
      ∃ hqn : subcriticalReferenceSupportSize k n m b ≤ n,
        (4 : ℝ) * k * n ≤ delta * retainedActiveTotalCapacity
          (balancedRetainedDivision hk hrq hqn) 0 n ∧
        (∀ e : RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n,
          1 / (retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e : ℝ) ≤ delta) ∧
        a^2 * (n : ℝ)^2 ≤ 32 * retainedActiveTotalCapacity
          (balancedRetainedDivision hk hrq hqn) 0 n ∧
        ∀ e : RetainedActivePair (balancedRetainedDivision hk hrq hqn) 0 n,
          a^2 * (n : ℝ)^2 ≤ 16 * ((k - 1 : ℕ) : ℝ)^2 *
            retainedActiveCapacity (balancedRetainedDivision hk hrq hqn) 0 n e := by
  have hs := subcriticalReference_support_lower hk ha hmu hscale
  have hrq : k - 1 ≤ subcriticalReferenceSupportSize k n m b := by omega
  have hqn := subcriticalReferenceSupportSize_le (subcriticalReferenceMass_mem_Ioo hk hgamma).2.le
  let D := balancedRetainedDivision hk hrq hqn
  have hsq : a^2 * (n : ℝ)^2 ≤
      4 * (subcriticalReferenceSupportSize k n m b : ℝ)^2 := by
    nlinarith [sq_nonneg (a * n - 2 * (subcriticalReferenceSupportSize k n m b : ℝ)),
      mul_nonneg (show 0 ≤ a * n by positivity)
        (show 0 ≤ 2 * (subcriticalReferenceSupportSize k n m b : ℝ) - a * n by linarith [hs.2])]
  have hA : a^2 * (n : ℝ)^2 ≤ 32 * retainedActiveTotalCapacity D 0 n := by
    have h := balancedRetainedDivision_total_capacity_lower hk hrq hqn hs.1
    change (subcriticalReferenceSupportSize k n m b : ℝ)^2 / 8 ≤
      retainedActiveTotalCapacity D 0 n at h
    linarith
  have hN (e : RetainedActivePair D 0 n) :
      a^2 * (n : ℝ)^2 ≤ 16 * ((k - 1 : ℕ) : ℝ)^2 * retainedActiveCapacity D 0 n e := by
    have h := balancedRetainedDivision_pair_capacity_lower hk hrq hqn hs.1 e
    linarith
  refine ⟨hrq, hqn, ?_, ?_, hA, hN⟩
  · have h1 := mul_le_mul_of_nonneg_right hmean (show (0 : ℝ) ≤ n by positivity)
    have h2 := mul_le_mul_of_nonneg_left hA hd
    nlinarith [h1, h2]
  · intro e
    have hcap : (0 : ℝ) < retainedActiveCapacity D 0 n e := by
      exact_mod_cast retainedActiveCapacity_pos D 0 n e
    apply (div_le_iff₀ hcap).2
    have hh := mul_le_mul_of_nonneg_left (hN e) hd
    have h : (16 : ℝ) * ((k - 1 : ℕ) : ℝ)^2 ≤
        (16 : ℝ) * ((k - 1 : ℕ) : ℝ)^2 *
          (delta * retainedActiveCapacity D 0 n e) := by
      nlinarith [hpair, hh]
    have hr0 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
    have hrpos : (0 : ℝ) < 16 * ((k - 1 : ℕ) : ℝ)^2 := by positivity
    apply (mul_le_mul_iff_right₀ hrpos).mp
    nlinarith [h]

private theorem eventually_real_nat_ge (c : ℝ) : ∀ᶠ n : ℕ in atTop, c ≤ (n : ℝ) := by
  filter_upwards [eventually_ge_atTop (Nat.ceil c)] with n hn
  exact (Nat.le_ceil c).trans (by exact_mod_cast hn)

/-- The elementary finite reserves hold uniformly for every sufficiently
large graph order; no graph, division, profile, or finite edge level enters
the threshold. -/
theorem eventually_subcriticalReference_scale {k : ℕ} {a delta : ℝ}
    (ha : 0 < a) (hd : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      (4 : ℝ) * (k - 1 : ℕ) ≤ a * n ∧
      (128 : ℝ) * k ≤ delta * a^2 * n ∧
      (16 : ℝ) * ((k - 1 : ℕ) : ℝ)^2 ≤ delta * a^2 * (n : ℝ)^2 := by
  have hp : 0 < delta * a^2 := by positivity
  filter_upwards [eventually_ge_atTop 2,
    eventually_real_nat_ge (4 * (k - 1 : ℕ) / a),
    eventually_real_nat_ge (128 * (k : ℝ) / (delta * a^2)),
    eventually_real_nat_ge (16 * ((k - 1 : ℕ) : ℝ)^2 / (delta * a^2))]
    with n hn h1 h2 h3
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨hn, ?_, ?_, ?_⟩
  · simpa only [mul_comm] using (div_le_iff₀ ha).mp h1
  · simpa only [mul_comm] using (div_le_iff₀ hp).mp h2
  · have h := (div_le_iff₀ hp).mp h3
    nlinarith [mul_nonneg hp.le (show 0 ≤ (n : ℝ)^2 - n by nlinarith)]

end InducedStars
