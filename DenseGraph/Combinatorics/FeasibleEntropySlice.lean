import DenseGraph.Combinatorics.BinomialEntropy
import DenseGraph.Analysis

/-!
# Feasible entropy slices with forced and variable coordinates

The entropy value requires a proof of feasibility. Zero variable capacity
is feasible only when the target equals the forced count. Integer counting
separately guards subtraction of forced edges before taking a binomial.
-/

noncomputable section
namespace DenseGraph
attribute [local instance] Classical.propDecidable

/-- Feasible real counts: forced mass plus a choice among variable mass. -/
structure EntropySliceFeasible (R B target : ℝ) : Prop where
  capacity_nonneg : 0 ≤ R
  lower : B ≤ target
  upper : target ≤ B + R

namespace EntropySliceFeasible

theorem target_eq_of_capacity_zero {R B target : ℝ}
    (h : EntropySliceFeasible R B target) (hR : R = 0) : target = B := by
  have := h.upper
  rw [hR, add_zero] at this
  exact le_antisymm this h.lower

theorem density_mem_Icc {R B target : ℝ}
    (h : EntropySliceFeasible R B target) (hR : 0 < R) :
    (target - B) / R ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (sub_nonneg.mpr h.lower) hR.le,
    (div_le_one hR).mpr (by linarith [h.upper])⟩

/-- Entropy in bits, defined only on the feasible domain. The zero-capacity
case is explicit rather than justified by totalized division. -/
def value {R B target : ℝ} (_h : EntropySliceFeasible R B target) : ℝ :=
  if R = 0 then 0 else R * binaryEntropy ((target - B) / R)

theorem value_eq {R B target : ℝ} (h : EntropySliceFeasible R B target) :
    h.value = R * binaryEntropy ((target - B) / R) := by
  by_cases hR : R = 0 <;> simp [value, hR]

theorem value_zero {B target : ℝ} (h : EntropySliceFeasible 0 B target) :
    h.value = 0 ∧ target = B := by
  exact ⟨by simp [value], h.target_eq_of_capacity_zero rfl⟩

theorem value_nonneg {R B target : ℝ} (h : EntropySliceFeasible R B target) :
    0 ≤ h.value := by
  by_cases hR : R = 0
  · simp [value, hR]
  · have hq := h.density_mem_Icc (lt_of_le_of_ne h.capacity_nonneg (Ne.symm hR))
    rw [value_eq]
    exact mul_nonneg h.capacity_nonneg (binaryEntropy_nonneg hq.1 hq.2)

theorem value_le_capacity {R B target : ℝ} (h : EntropySliceFeasible R B target) :
    h.value ≤ R := by
  have hH : binaryEntropy ((target - B) / R) ≤ 1 := by
    rw [binaryEntropy]
    exact (div_le_one realLogTwo_pos).mpr Real.binEntropy_le_log_two
  rw [value_eq]
  simpa using mul_le_mul_of_nonneg_left hH h.capacity_nonneg

end EntropySliceFeasible

/-- Exact selection count with natural subtraction guarded first. -/
def guardedEntropySliceCount (R B m : ℕ) : ℕ :=
  if B ≤ m then R.choose (m - B) else 0

theorem guardedEntropySliceCount_eq_zero_of_lt {R B m : ℕ} (hm : m < B) :
    guardedEntropySliceCount R B m = 0 := by
  simp [guardedEntropySliceCount, Nat.not_le.mpr hm]

theorem guardedEntropySliceCount_pos_iff (R B m : ℕ) :
    0 < guardedEntropySliceCount R B m ↔ B ≤ m ∧ m ≤ B + R := by
  by_cases hB : B ≤ m
  · rw [guardedEntropySliceCount, if_pos hB]
    constructor
    · intro h
      have : m - B ≤ R := by
        by_contra hnot
        rw [Nat.choose_eq_zero_of_lt (by omega)] at h
        omega
      omega
    · intro h
      exact Nat.choose_pos (by omega)
  · simp [guardedEntropySliceCount, hB]

theorem entropySliceFeasible_nat {R B m : ℕ} (hB : B ≤ m) (hm : m ≤ B + R) :
    EntropySliceFeasible R B m := by
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast hB, by exact_mod_cast hm⟩

/-- Binary-unit upper entropy bound for the actual guarded count. -/
theorem log2_guardedEntropySliceCount_le {R B m : ℕ}
    (hB : B ≤ m) (hm : m ≤ B + R) :
    log2 (guardedEntropySliceCount R B m) ≤ (entropySliceFeasible_nat hB hm).value := by
  rw [guardedEntropySliceCount, if_pos hB, EntropySliceFeasible.value_eq]
  have h := log_choose_upper_binEntropy (show m - B ≤ R by omega)
  have hh := div_le_div_of_nonneg_right h realLogTwo_pos.le
  simpa [log2, binaryEntropy, binomialEntropyPerspective, Nat.cast_sub hB,
    mul_div_assoc] using hh

/-- Binary-unit lower bound, with its logarithmic finite-size error. -/
theorem entropySliceValue_sub_log_le_log2_count {R B m : ℕ}
    (hB : B ≤ m) (hm : m ≤ B + R) :
    (entropySliceFeasible_nat hB hm).value - log2 ((R : ℝ) + 1) ≤
      log2 (guardedEntropySliceCount R B m) := by
  rw [guardedEntropySliceCount, if_pos hB, EntropySliceFeasible.value_eq]
  have h := log_choose_lower_binEntropy (show m - B ≤ R by omega)
  have hh := div_le_div_of_nonneg_right h realLogTwo_pos.le
  simpa [log2, binaryEntropy, binomialEntropyPerspective, Nat.cast_sub hB,
    sub_div, mul_div_assoc] using hh

end DenseGraph
