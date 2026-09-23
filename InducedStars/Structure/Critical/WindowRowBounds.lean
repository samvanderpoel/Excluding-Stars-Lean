import InducedStars.Structure.Critical.WindowCounting
import InducedStars.Structure.Critical.WindowRowRates

/-!
# Actual assembly rows relative to the equitable reference mass
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

def criticalWindowReferenceMass (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  (criticalWindowBalancedMultinomial (k - 1) n : ℝ) *
    criticalWindowCompletionCount k a n 0 0

theorem eventually_criticalWindowReferenceMass_pos
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < criticalWindowReferenceMass k a n := by
  have hs : Tendsto (fun n : ℕ ↦ ((0 : ℕ) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by simp
  filter_upwards [eventually_criticalWindowEmptyCompletion_pos hk a hs] with n hn
  exact mul_pos (by exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n)
    (by exact_mod_cast hn)

theorem criticalWindowAssemblyEnvelope_pos
    {k n s : ℕ} (hk : 3 ≤ k) (a : ℝ) (hs : s ≤ n) :
    0 < criticalWindowAssemblyEnvelope k a n s := by
  unfold criticalWindowAssemblyEnvelope
  have hc : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hs
  have hM : (0 : ℝ) < criticalWindowBalancedMultinomial (k - 1) (n - s) := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) (n - s)
  have hN : (0 : ℝ) < criticalWindowBalancedMultinomial (k - 1) n := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n
  exact mul_pos (mul_pos (mul_pos hc (div_pos hM hN))
    (criticalRemainderPartitionFunction_pos hk s)) (Real.exp_pos _)

theorem criticalWindowReferenceMass_mul_envelope
    (k n s : ℕ) (a : ℝ) :
    criticalWindowReferenceMass k a n * criticalWindowAssemblyEnvelope k a n s =
      (n.choose s : ℝ) * (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        criticalWindowCompletionCount k a n 0 0 *
          Real.exp (criticalWindowCompletionExponent k a n s 0) * criticalRemainderPartitionFunction k s := by
  have hM : (criticalWindowBalancedMultinomial (k - 1) n : ℝ) ≠ 0 := by
    exact_mod_cast (criticalWindowBalancedMultinomial_pos (k - 1) n).ne'
  unfold criticalWindowReferenceMass criticalWindowAssemblyEnvelope
  field_simp <;> ring

theorem criticalWindowReferenceMass_mul_emptyRatio
    {k n s : ℕ} {a : ℝ} (hB : criticalWindowCompletionCount k a n 0 0 ≠ 0) :
    criticalWindowReferenceMass k a n * criticalWindowEmptyAssemblyRatio k a n s =
      (n.choose s : ℝ) * (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
        criticalWindowCompletionCount k a n s 0 / ((s + (k - 1)).choose (k - 1) : ℝ) := by
  have hM : (criticalWindowBalancedMultinomial (k - 1) n : ℝ) ≠ 0 := by
    exact_mod_cast (criticalWindowBalancedMultinomial_pos (k - 1) n).ne'
  have hB' : (criticalWindowCompletionCount k a n 0 0 : ℝ) ≠ 0 := by exact_mod_cast hB
  unfold criticalWindowReferenceMass criticalWindowEmptyAssemblyRatio
  field_simp <;> ring

theorem eventually_criticalWindowAssemblyEnvelope_le_exp
    {k : ℕ} (hk : 3 ≤ k) (a L : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n → (s : ℝ) / Real.log (n : ℝ) ≤ L →
      criticalWindowAssemblyEnvelope k a n s ≤
        Real.exp ((criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)) + epsilon) *
          Real.log (n : ℝ) ^ 2) := by
  have hu := DenseGraph.eventually_uniform_of_normalizedSequences_tendsto_zero
    criticalWindowLog_nat_tendsto_atTop criticalWindowLog_nat_tendsto_atTop
    (F := fun n s _t ↦ Real.log (criticalWindowAssemblyEnvelope k a n s) / Real.log (n : ℝ) ^ 2 -
      criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)))
    (fun s _t x _y _hx _hy hs _ht ↦ by
      have hpoly := (hs.const_mul (1 - a / criticalWindowThreshold k)).sub
        ((hs.pow 2).const_mul (gammaK k / criticalWindowThreshold k))
      have h := (criticalWindowAssemblyEnvelope_log_scale_tendsto hk a hs).sub hpoly
      simpa only [criticalWindowRate, sub_self] using h) L 0 hepsilon
  filter_upwards [hu,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with n hn hl
  intro s hsn hs
  have hh := (abs_le.mp (hn s 0 hs (by simp))).2
  have hle : Real.log (criticalWindowAssemblyEnvelope k a n s) ≤
      (criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)) + epsilon) * Real.log (n : ℝ) ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hl)).mp
    linarith
  have h := Real.exp_le_exp.mpr hle
  rw [Real.exp_log (criticalWindowAssemblyEnvelope_pos hk a hsn)] at h
  exact h

/-- Actual assembly rows satisfy the sharp upper rate uniformly over each
bounded logarithmic range. -/
theorem exists_criticalWindowAssembly_upper_rate_uniform
    {k : ℕ} (hk : 3 ≤ k) (a L : ℝ) (hL : 0 ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ s : ℕ,
      s ≤ n → (s : ℝ) / Real.log (n : ℝ) ≤ L →
      ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) s).card : ℝ) ≤
        C * criticalWindowReferenceMass k a n *
          Real.exp ((criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)) + epsilon) *
            Real.log (n : ℝ) ^ 2) := by
  obtain ⟨C, hC, hrow⟩ := exists_criticalWindowAssembly_row_bounds_uniform hk a L hL (half_pos hepsilon)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrow, eventually_criticalWindowAssemblyEnvelope_le_exp hk a L (half_pos hepsilon),
    eventually_criticalWindowReferenceMass_pos hk a] with n hr he hbase
  intro s hsn hs
  have hupper := (hr s hs).2
  have hid : C * (n.choose s : ℝ) *
      (criticalWindowBalancedMultinomial (k - 1) (n - s) : ℝ) *
      (criticalWindowCompletionCount k a n 0 0 : ℝ) *
      Real.exp (criticalWindowCompletionExponent k a n s 0 + epsilon / 2 * Real.log (n : ℝ) ^ 2) *
      criticalRemainderPartitionFunction k s =
      C * criticalWindowReferenceMass k a n * criticalWindowAssemblyEnvelope k a n s *
        Real.exp (epsilon / 2 * Real.log (n : ℝ) ^ 2) := by
    rw [Real.exp_add]
    rw [show C * criticalWindowReferenceMass k a n * criticalWindowAssemblyEnvelope k a n s =
      C * (criticalWindowReferenceMass k a n * criticalWindowAssemblyEnvelope k a n s) by ring,
      criticalWindowReferenceMass_mul_envelope]
    ring
  rw [hid] at hupper
  calc
    _ ≤ C * criticalWindowReferenceMass k a n * criticalWindowAssemblyEnvelope k a n s *
        Real.exp (epsilon / 2 * Real.log (n : ℝ) ^ 2) := hupper
    _ ≤ C * criticalWindowReferenceMass k a n *
        Real.exp ((criticalWindowRate k a ((s : ℝ) / Real.log (n : ℝ)) + epsilon / 2) *
          Real.log (n : ℝ) ^ 2) * Real.exp (epsilon / 2 * Real.log (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (he s hsn hs) (mul_pos hC hbase).le)
        (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem eventually_criticalWindowEmptyAssemblyRatio_ge_exp
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s : ℕ → ℕ} {x epsilon : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp ((criticalWindowRate k a x - epsilon) * Real.log (n : ℝ) ^ 2) ≤
        criticalWindowEmptyAssemblyRatio k a n (s n) := by
  have h := (criticalWindowEmptyAssemblyRatio_log_scale_tendsto hk a hs).eventually
    (Ioi_mem_nhds (sub_lt_self _ hepsilon))
  have hs0 : Tendsto (fun n : ℕ ↦ ((0 : ℕ) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by simp
  filter_upwards [h, eventually_criticalWindowLogarithmicSize_le_order hs,
    eventually_criticalWindowEmptyCompletion_pos hk a hs,
    eventually_criticalWindowEmptyCompletion_pos hk a hs0,
    criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn hsn hBs hB0 hl
  have hratio : 0 < criticalWindowEmptyAssemblyRatio k a n (s n) := by
    unfold criticalWindowEmptyAssemblyRatio
    have hc : (0 : ℝ) < n.choose (s n) := by exact_mod_cast Nat.choose_pos hsn
    have hMs : (0 : ℝ) < criticalWindowBalancedMultinomial (k - 1) (n - s n) := by
      exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) (n - s n)
    have hM : (0 : ℝ) < criticalWindowBalancedMultinomial (k - 1) n := by
      exact_mod_cast criticalWindowBalancedMultinomial_pos (k - 1) n
    have hBs' : (0 : ℝ) < criticalWindowCompletionCount k a n (s n) 0 := by exact_mod_cast hBs
    have hB0' : (0 : ℝ) < criticalWindowCompletionCount k a n 0 0 := by exact_mod_cast hB0
    have hd : (0 : ℝ) < (s n + (k - 1)).choose (k - 1) := by
      exact_mod_cast Nat.choose_pos (Nat.le_add_left (k - 1) (s n))
    positivity
  have hle := (lt_div_iff₀ (sq_pos_of_pos hl)).mp hn
  have he := Real.exp_le_exp.mpr hle.le
  rw [Real.exp_log hratio] at he
  exact he

/-- A single moving empty-remainder assembly gives the sharp lower rate
for the whole conditioning family. -/
theorem exists_criticalWindowTotal_lower_rate
    {k : ℕ} (hk : 3 ≤ k) (a : ℝ) {s : ℕ → ℕ} {x epsilon : ℝ}
    (hx : 0 ≤ x)
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      C⁻¹ * criticalWindowReferenceMass k a n *
          Real.exp ((criticalWindowRate k a x - epsilon) * Real.log (n : ℝ) ^ 2) ≤
        ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) := by
  classical
  obtain ⟨C, hC, hrow⟩ := exists_criticalWindowAssembly_row_bounds_uniform hk a (x + 1)
    (by linarith) (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrow, hs.eventually (Iio_mem_nhds (by linarith : x < x + 1)),
    eventually_criticalWindowEmptyAssemblyRatio_ge_exp hk a hs hepsilon,
    eventually_criticalWindowReferenceMass_pos hk a] with n hr hsn he hbase
  have hB : criticalWindowCompletionCount k a n 0 0 ≠ 0 := by
    intro hz
    simp [criticalWindowReferenceMass, hz] at hbase
  have hid : C⁻¹ * (n.choose (s n) : ℝ) *
      (criticalWindowBalancedMultinomial (k - 1) (n - s n) : ℝ) *
      criticalWindowCompletionCount k a n (s n) 0 /
        ((s n + (k - 1)).choose (k - 1) : ℝ) =
      C⁻¹ * criticalWindowReferenceMass k a n * criticalWindowEmptyAssemblyRatio k a n (s n) := by
    rw [show C⁻¹ * criticalWindowReferenceMass k a n * criticalWindowEmptyAssemblyRatio k a n (s n) =
      C⁻¹ * (criticalWindowReferenceMass k a n * criticalWindowEmptyAssemblyRatio k a n (s n)) by ring,
      criticalWindowReferenceMass_mul_emptyRatio hB]
    ring
  have hrow' := (hr (s n) hsn.le).1
  rw [hid] at hrow'
  have hsub : ((exactCriticalAssemblyFinset k n (criticalWindowEdgeCount k a n) (s n)).card : ℝ) ≤
      ((criticalWindowInducedStarFreeGraphFinset k n a).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset (HasExactCriticalStructure k (s n))
      (inducedStarFreeGraphFinsetWithEdges k n (criticalWindowEdgeCount k a n))))
  exact (mul_le_mul_of_nonneg_left he (mul_pos (inv_pos.mpr hC) hbase).le).trans
    (hrow'.trans hsub)

end InducedStars
