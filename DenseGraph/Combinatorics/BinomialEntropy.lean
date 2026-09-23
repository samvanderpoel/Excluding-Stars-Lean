import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Tactic
import DenseGraph.FiniteModels.FixedCardinalityBlocks

/-!
# Entropy bounds for binomial coefficients

This file proves the standard natural-logarithm entropy sandwich for a
binomial coefficient.  The lower bound is obtained from the exact finite
binomial-mode estimate in `FixedCardinalityBlocks`; no Stirling approximation
is used.
-/

noncomputable section

namespace DenseGraph

/-- The natural-logarithm binary-entropy exponent attached to an exact
binomial slice.  Mathlib's `Real.binEntropy` is measured in nats. -/
def binomialEntropyPerspective (N m : ℕ) : ℝ :=
  (N : ℝ) * Real.binEntropy ((m : ℝ) / (N : ℝ))

private theorem binomialPointMass_quota_eq_choose_mul_exp_neg_entropy
    {N m : ℕ} (hm : m ≤ N) :
    FixedCardinalityBlockModel.binomialPointMass N m
        (FixedCardinalityBlockModel.quotaParameter N m) =
      (Nat.choose N m : ℝ) * Real.exp (-binomialEntropyPerspective N m) := by
  by_cases hN : N = 0
  · have hm0 : m = 0 := by omega
    subst N
    subst m
    simp [FixedCardinalityBlockModel.binomialPointMass,
      FixedCardinalityBlockModel.quotaParameter, binomialEntropyPerspective]
  by_cases hm0 : m = 0
  · subst m
    simp [FixedCardinalityBlockModel.binomialPointMass,
      FixedCardinalityBlockModel.quotaParameter, binomialEntropyPerspective]
  by_cases hmN : m = N
  · subst m
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    simp [FixedCardinalityBlockModel.binomialPointMass,
      FixedCardinalityBlockModel.quotaParameter, binomialEntropyPerspective, hNR]
  let q : ℝ := (m : ℝ) / (N : ℝ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hmLtN : m < N := lt_of_le_of_ne hm hmN
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqone : q < 1 := by
    dsimp [q]
    exact (div_lt_one hNpos).2 (by exact_mod_cast hmLtN)
  have honeqpos : 0 < 1 - q := sub_pos.mpr hqone
  have hNq : (N : ℝ) * q = (m : ℝ) := by
    dsimp [q]
    field_simp
  have hNsubq : (N : ℝ) * (1 - q) = ((N - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]
    nlinarith
  have hexponent :
      -binomialEntropyPerspective N m =
        (m : ℝ) * Real.log q +
          ((N - m : ℕ) : ℝ) * Real.log (1 - q) := by
    rw [binomialEntropyPerspective]
    rw [show (m : ℝ) / (N : ℝ) = q by rfl]
    rw [Real.binEntropy, Real.log_inv, Real.log_inv]
    rw [← hNq, ← hNsubq]
    ring
  have hqpow :
      Real.exp ((m : ℝ) * Real.log q) = q ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log hqpos]
  have honeqpow :
      Real.exp (((N - m : ℕ) : ℝ) * Real.log (1 - q)) =
        (1 - q) ^ (N - m) := by
    rw [Real.exp_nat_mul, Real.exp_log honeqpos]
  rw [show FixedCardinalityBlockModel.quotaParameter N m = q by
    rfl, FixedCardinalityBlockModel.binomialPointMass, hexponent,
    Real.exp_add, hqpow, honeqpow]
  ring

/-- Multiplicative form of the upper entropy bound. -/
theorem choose_le_exp_binomialEntropyPerspective
    {N m : ℕ} (hm : m ≤ N) :
    (Nat.choose N m : ℝ) ≤ Real.exp (binomialEntropyPerspective N m) := by
  have hq :
      FixedCardinalityBlockModel.quotaParameter N m ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · by_cases hN : N = 0
      · have hm0 : m = 0 := by omega
        simp [FixedCardinalityBlockModel.quotaParameter, hN, hm0]
      · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).2
        exact_mod_cast hm
  have hmass := FixedCardinalityBlockModel.binomialPointMass_le_one hq hm
  rw [binomialPointMass_quota_eq_choose_mul_exp_neg_entropy hm] at hmass
  calc
    (Nat.choose N m : ℝ) =
        ((Nat.choose N m : ℝ) *
            Real.exp (-binomialEntropyPerspective N m)) *
          Real.exp (binomialEntropyPerspective N m) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ 1 * Real.exp (binomialEntropyPerspective N m) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_pos _).le
    _ = Real.exp (binomialEntropyPerspective N m) := one_mul _

/-- Multiplicative form of the lower entropy bound.  The factor `N + 1` is
the exact maximum-at-least-average loss from the finite binomial law. -/
theorem exp_binomialEntropyPerspective_div_succ_le_choose
    {N m : ℕ} (hm : m ≤ N) :
    Real.exp (binomialEntropyPerspective N m) / ((N + 1 : ℕ) : ℝ) ≤
      (Nat.choose N m : ℝ) := by
  have hmass :=
    FixedCardinalityBlockModel.binomialModePointMass_ge_inv_succ hm
  rw [binomialPointMass_quota_eq_choose_mul_exp_neg_entropy hm] at hmass
  have hE : 0 ≤ Real.exp (binomialEntropyPerspective N m) := (Real.exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_right hmass hE
  calc
    Real.exp (binomialEntropyPerspective N m) / ((N + 1 : ℕ) : ℝ) =
        (1 / ((N + 1 : ℕ) : ℝ)) *
          Real.exp (binomialEntropyPerspective N m) := by ring
    _ ≤ ((Nat.choose N m : ℝ) *
          Real.exp (-binomialEntropyPerspective N m)) *
            Real.exp (binomialEntropyPerspective N m) := hscaled
    _ = (Nat.choose N m : ℝ) := by
      rw [mul_assoc, ← Real.exp_add]
      simp

/-- Lower natural-log entropy bound for a binomial coefficient. -/
theorem log_choose_lower_binEntropy
    {N m : ℕ} (hm : m ≤ N) :
    binomialEntropyPerspective N m - Real.log ((N + 1 : ℕ) : ℝ) ≤
      Real.log (Nat.choose N m : ℝ) := by
  have hchoose : (0 : ℝ) < Nat.choose N m := by
    exact_mod_cast Nat.choose_pos hm
  rw [Real.le_log_iff_exp_le hchoose]
  rw [Real.exp_sub, Real.exp_log (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))]
  exact exp_binomialEntropyPerspective_div_succ_le_choose hm

/-- Upper natural-log entropy bound for a binomial coefficient. -/
theorem log_choose_upper_binEntropy
    {N m : ℕ} (hm : m ≤ N) :
    Real.log (Nat.choose N m : ℝ) ≤ binomialEntropyPerspective N m := by
  have hchoose : (0 : ℝ) < Nat.choose N m := by
    exact_mod_cast Nat.choose_pos hm
  exact (Real.log_le_iff_le_exp hchoose).2
    (choose_le_exp_binomialEntropyPerspective hm)

/-- The two-sided natural-log entropy sandwich in a single declaration. -/
theorem log_choose_binEntropy_sandwich
    {N m : ℕ} (hm : m ≤ N) :
    binomialEntropyPerspective N m - Real.log ((N + 1 : ℕ) : ℝ) ≤
        Real.log (Nat.choose N m : ℝ) ∧
      Real.log (Nat.choose N m : ℝ) ≤ binomialEntropyPerspective N m :=
  ⟨log_choose_lower_binEntropy hm, log_choose_upper_binEntropy hm⟩

end DenseGraph
