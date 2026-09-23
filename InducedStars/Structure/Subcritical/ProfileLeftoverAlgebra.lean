import InducedStars.Structure.Subcritical.ProfileLeftover
import InducedStars.Structure.Subcritical.SparseSide
import InducedStars.Analysis.Entropy

/-!
# Explicit absorption into the profile error budget

Finite scalar bookkeeping for the fixed-remainder leftover count.
Binary entropy and binary logarithms are converted explicitly before natural
exponentiation. No tail, local-entropy, or probability exponent is introduced.
-/

noncomputable section

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Binary entropy dominates its argument on the lower half interval. -/
theorem binaryEntropy_ge_self_of_le_half {t : ℝ} (ht : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    t ≤ binaryEntropy t := by
  rcases eq_or_lt_of_le ht with hzero | htpos
  · rw [← hzero, binaryEntropy_zero]
  have hlog : Real.log t ≤ -Real.log 2 := by
    calc
      Real.log t ≤ Real.log (1 / 2 : ℝ) := Real.log_le_log htpos htHalf
      _ = -Real.log 2 := by simp
  have hbits : log2 t ≤ -1 := by
    apply (div_le_iff₀ realLogTwo_pos).mpr
    linarith
  have hq : log2 (1 - t) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ realLogTwo_pos.le
    exact Real.log_nonpos (by linarith) (by linarith)
  rw [binaryEntropy_eq_formula]
  have hp := mul_le_mul_of_nonneg_left hbits ht
  have hneg := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 1 - t) hq
  nlinarith

private theorem errorConstant_bounds (k R₀ : ℕ) :
    1 ≤ subcriticalProfileErrorConstant k R₀ ∧
      ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k ≤
        subcriticalProfileErrorConstant k R₀ ∧
      2 * ((k - 1 : ℕ) : ℝ) ≤ subcriticalProfileErrorConstant k R₀ ∧
      subcriticalSparseSideConstant k ≤ subcriticalProfileErrorConstant k R₀ := by
  let X : ℝ := k + 1
  have hX1 : 1 ≤ X := by
    dsimp [X]
    linarith [show (0 : ℝ) ≤ k by positivity]
  have hKX : (k : ℝ) ≤ X := by dsimp [X]; linarith
  have hrX : ((k - 1 : ℕ) : ℝ) ≤ X :=
    (by exact_mod_cast Nat.sub_le k 1 : ((k - 1 : ℕ) : ℝ) ≤ k).trans hKX
  have hX14 : X ≤ X^4 := by simpa using pow_le_pow_right₀ hX1 (by omega : 1 ≤ 4)
  have hX24 : X^2 ≤ X^4 := pow_le_pow_right₀ hX1 (by omega)
  have hX34 : X^3 ≤ X^4 := pow_le_pow_right₀ hX1 (by omega)
  have hC : 1000 * X^4 ≤ subcriticalProfileErrorConstant k R₀ := by
    unfold subcriticalProfileErrorConstant
    have hR : (1 : ℝ) ≤ (R₀ + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le R₀)
    have hmul := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1000 * X^4)
    simpa only [mul_one, X, Nat.cast_add, Nat.cast_one] using hmul
  have hprod : ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k ≤ 100 * X^3 := by
    unfold subcriticalSparseSideConstant
    calc
      ((k - 1 : ℕ) : ℝ) * (100 * (k : ℝ)^2) ≤ X * (100 * X^2) := by gcongr
      _ = 100 * X^3 := by ring
  have hk2 : subcriticalSparseSideConstant k ≤ 100 * X^2 := by
    unfold subcriticalSparseSideConstant
    gcongr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

private theorem one_le_log2_order_succ (hn : 2 ≤ Fintype.card V) :
    1 ≤ log2 (Fintype.card V + 1) := by
  have hN : (2 : ℝ) ≤ Fintype.card V + 1 := by exact_mod_cast (by omega : 2 ≤ Fintype.card V + 1)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN
  exact (le_div_iff₀ realLogTwo_pos).mpr (by simpa using hlog)

private theorem log_order_succ_le_log2 (hn : 2 ≤ Fintype.card V) :
    Real.log (Fintype.card V + 1) ≤ log2 (Fintype.card V + 1) := by
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hb := one_le_log2_order_succ (V := V) hn
  have hid : Real.log (Fintype.card V + 1) = log2 (Fintype.card V + 1) * Real.log 2 := by
    unfold log2
    field_simp
  rw [hid]
  exact mul_le_of_le_one_right (by linarith) hl2

private theorem rootFraction_nonneg {alpha theta epsilon : ℝ}
    (ha : 0 ≤ alpha) (ht : 0 ≤ theta) (he : 0 ≤ epsilon) :
    0 ≤ subcriticalProfileRootFraction alpha theta epsilon := by
  unfold subcriticalProfileRootFraction
  positivity

/-- The polynomial coefficient in `Err` simultaneously dominates the
visible, fixed-small-side, root-root, and witness-selection costs. -/
theorem subcriticalLeftoverRowCodeExponent_le_errorBudget
    {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2)
    (ht : 0 ≤ theta) (hd : 0 ≤ delta) (he : 0 ≤ epsilon) :
    (p.roots.card : ℝ) *
      (binaryEntropy (5 * alpha) * Fintype.card V +
        ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k * theta * Fintype.card V +
        2 * ((k - 1 : ℕ) : ℝ) * log2 (Fintype.card V + 1) +
        subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V) ≤
      subcriticalProfileErrorBudget alpha delta epsilon p := by
  obtain ⟨hC1, hCr, hClog, _⟩ := errorConstant_bounds k R₀
  have hEnt : 0 ≤ binaryEntropy (5 * alpha) := binaryEntropy_nonneg (by positivity) (by linarith)
  have hLog : 0 ≤ log2 (Fintype.card V + 1) := log2_nonneg (by norm_num)
  have hRho := rootFraction_nonneg ha ht he
  have h1 := mul_le_mul_of_nonneg_right hC1
    (mul_nonneg hEnt (Nat.cast_nonneg (Fintype.card V)))
  have h2 := mul_le_mul_of_nonneg_right hCr
    (mul_nonneg ht (Nat.cast_nonneg (Fintype.card V)))
  have h3 := mul_le_mul_of_nonneg_right hClog hLog
  have h4 := mul_le_mul_of_nonneg_right hC1
    (mul_nonneg hRho (Nat.cast_nonneg (Fintype.card V)))
  have h5 : 0 ≤ subcriticalProfileErrorConstant k R₀ * (delta * Fintype.card V) := by positivity
  have hrow : binaryEntropy (5 * alpha) * Fintype.card V +
      ((k - 1 : ℕ) : ℝ) * subcriticalSparseSideConstant k * theta * Fintype.card V +
      2 * ((k - 1 : ℕ) : ℝ) * log2 (Fintype.card V + 1) +
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V ≤
      subcriticalProfileErrorConstant k R₀ *
        (binaryEntropy (5 * alpha) * Fintype.card V + theta * Fintype.card V +
          delta * Fintype.card V +
          subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V +
          log2 (Fintype.card V + 1)) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg p.roots.card)
  simpa only [subcriticalProfileErrorBudget, mul_left_comm, mul_assoc] using hmul

/-- The exact finite rootwise edge bound is absorbed by the profile error
budget. This bound does not fix a remainder graph and is valid separately
from the fixed-remainder cardinality repair. -/
theorem subcriticalLeftoverEdgeBudget_le_errorBudget
    {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2)
    (ht : 0 ≤ theta) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hB : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V) :
    (p.roots.card : ℝ) *
      (5 * alpha * Fintype.card V +
        subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card) ≤
      subcriticalProfileErrorBudget alpha delta epsilon p := by
  obtain ⟨hC1, _, _, hCk⟩ := errorConstant_bounds k R₀
  have hEnt : 0 ≤ binaryEntropy (5 * alpha) := binaryEntropy_nonneg (by positivity) (by linarith)
  have hEntLower := binaryEntropy_ge_self_of_le_half (by positivity : 0 ≤ 5 * alpha) haHalf
  have hLog : 0 ≤ log2 (Fintype.card V + 1) := log2_nonneg (by norm_num)
  have hRho := rootFraction_nonneg ha ht he
  have h1 := mul_le_mul_of_nonneg_right hEntLower (Nat.cast_nonneg (Fintype.card V))
  have h2 := mul_le_mul_of_nonneg_right hC1
    (mul_nonneg hEnt (Nat.cast_nonneg (Fintype.card V)))
  have h3 := mul_le_mul_of_nonneg_right hCk
    (mul_nonneg ht (Nat.cast_nonneg (Fintype.card V)))
  have h4 := mul_le_mul_of_nonneg_right hC1
    (mul_nonneg hRho (Nat.cast_nonneg (Fintype.card V)))
  have h5 : 0 ≤ subcriticalProfileErrorConstant k R₀ *
      (delta * Fintype.card V + log2 (Fintype.card V + 1)) := by positivity
  have hrow : 5 * alpha * Fintype.card V +
      subcriticalSparseSideConstant k * theta * Fintype.card V + p.roots.card ≤
      subcriticalProfileErrorConstant k R₀ *
        (binaryEntropy (5 * alpha) * Fintype.card V + theta * Fintype.card V +
          delta * Fintype.card V +
          subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V +
          log2 (Fintype.card V + 1)) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg p.roots.card)
  simpa only [subcriticalProfileErrorBudget, mul_left_comm, mul_assoc] using hmul

/-- Absorb the exact fixed-remainder row-code cardinality into `exp Err`.
The visible-row input is already converted from binary entropy to natural
exponential units by its explicit `Real.log 2` multiplier. The small-side
degree cutoff is the exact natural floor, not an additional assumption. -/
theorem subcriticalLeftoverRawCount_le_exp_errorBudget
    {D : SubcriticalDivision k V} {eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}
    (p : SubcriticalProfile D eta R₀ theta)
    (hk : 3 ≤ k) (hn : 2 ≤ Fintype.card V)
    (ha : 0 ≤ alpha) (haHalf : 5 * alpha ≤ 1 / 2)
    (ht : 0 ≤ theta) (hd : 0 ≤ delta) (he : 0 ≤ epsilon)
    (hB : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * Fintype.card V)
    (aVis : ℝ) (haVis : 0 ≤ aVis)
    (haVisBound : aVis ≤ Real.exp (Real.log 2 * binaryEntropy (5 * alpha) * Fintype.card V)) :
    (aVis * ((Fintype.card V + 1 : ℝ)^(k - 1) *
        (2 : ℝ)^((k - 1) * (⌊subcriticalSparseSideConstant k * theta * Fintype.card V⌋₊ + 1))) *
      (2 : ℝ)^p.roots.card)^p.roots.card ≤
      Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) := by
  let N := Fintype.card V
  let B := p.roots.card
  let r := k - 1
  let d := ⌊subcriticalSparseSideConstant k * theta * N⌋₊
  have hEnt : 0 ≤ binaryEntropy (5 * alpha) := binaryEntropy_nonneg (by positivity) (by linarith)
  have hCk := (subcriticalSparseSideConstant_pos hk).le
  have hdBound : (d : ℝ) ≤ subcriticalSparseSideConstant k * theta * N :=
    Nat.floor_le (by positivity)
  have hLog := one_le_log2_order_succ (V := V) hn
  have hLogNat := log_order_succ_le_log2 (V := V) hn
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hrow : Real.log 2 * binaryEntropy (5 * alpha) * N +
      (r : ℝ) * Real.log (N + 1) + ((r * (d + 1) : ℕ) : ℝ) * Real.log 2 +
      (B : ℝ) * Real.log 2 ≤
      binaryEntropy (5 * alpha) * N +
        (r : ℝ) * subcriticalSparseSideConstant k * theta * N +
        2 * (r : ℝ) * log2 (N + 1) +
        subcriticalProfileRootFraction alpha theta epsilon * N := by
    have h1 := mul_le_mul_of_nonneg_right hl2 (mul_nonneg hEnt (Nat.cast_nonneg N))
    have h2 := mul_le_mul_of_nonneg_left hLogNat (Nat.cast_nonneg r)
    have h3 := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (r * (d + 1)))
    have h4 := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg B)
    have h5 := mul_le_mul_of_nonneg_left hdBound (Nat.cast_nonneg r)
    have h6 := mul_le_mul_of_nonneg_left hLog (Nat.cast_nonneg r)
    push_cast at h3 ⊢
    dsimp [N, B] at *
    nlinarith
  have hpowN : (N + 1 : ℝ)^r = Real.exp ((r : ℝ) * Real.log (N + 1)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hpow2 (s : ℕ) : (2 : ℝ)^s = Real.exp ((s : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    _ ≤ (Real.exp (Real.log 2 * binaryEntropy (5 * alpha) * N) *
        ((N + 1 : ℝ)^r * (2 : ℝ)^(r * (d + 1))) * (2 : ℝ)^B)^B := by
      change (aVis * _ * _)^B ≤ _
      gcongr
    _ = Real.exp ((B : ℝ) *
        (Real.log 2 * binaryEntropy (5 * alpha) * N +
          (r : ℝ) * Real.log (N + 1) + ((r * (d + 1) : ℕ) : ℝ) * Real.log 2 +
          (B : ℝ) * Real.log 2)) := by
      rw [hpowN, hpow2, hpow2]
      simp only [← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ Real.exp (subcriticalProfileErrorBudget alpha delta epsilon p) := by
      apply Real.exp_le_exp.mpr
      exact (mul_le_mul_of_nonneg_left hrow (Nat.cast_nonneg B)).trans
        (subcriticalLeftoverRowCodeExponent_le_errorBudget p ha haHalf ht hd he)

end InducedStars
