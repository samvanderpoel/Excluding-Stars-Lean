import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Binomial coefficients under capacity enlargement

This file gives an elementary comparison between `N.choose m` and
`(N + Q).choose m`.  The proof iterates the exact adjacent-factor recurrence
for binomial coefficients and uses `1 + x ≤ exp x`; it does not use Stirling's
formula.
-/

noncomputable section

namespace DenseGraph

private theorem choose_le_choose_add_mul_pow_ratio
    {N Q m : ℕ} (hm : m ≤ N) (hpos : 0 < N + Q) :
    (Nat.choose N m : ℝ) ≤
      (Nat.choose (N + Q) m : ℝ) *
        ((N : ℝ) / (N + Q : ℝ)) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hmN : m < N := by omega
      have hmNle : m ≤ N := hmN.le
      have hmNQ : m ≤ N + Q := hmNle.trans (Nat.le_add_right N Q)
      have hden' : (0 : ℝ) < (N : ℝ) + (Q : ℝ) := by exact_mod_cast hpos
      have hratio_nonneg : (0 : ℝ) ≤ (N : ℝ) / (N + Q : ℝ) := by positivity
      have hfactor :
          ((N - m : ℕ) : ℝ) ≤
            ((N : ℝ) / (N + Q : ℝ)) * ((N + Q - m : ℕ) : ℝ) := by
        rw [Nat.cast_sub hmNle, Nat.cast_sub hmNQ, div_mul_eq_mul_div]
        apply (le_div_iff₀ hden').2
        push_cast
        nlinarith
      have hcrossN :
          (Nat.choose N (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) =
            (Nat.choose N m : ℝ) * ((N - m : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq N m
      have hcrossNQ :
          (Nat.choose (N + Q) (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) =
            (Nat.choose (N + Q) m : ℝ) * ((N + Q - m : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_succ_right_eq (N + Q) m
      have hmul :
          (Nat.choose N (m + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) ≤
            ((Nat.choose (N + Q) (m + 1) : ℝ) *
              ((N : ℝ) / (N + Q : ℝ)) ^ (m + 1)) *
                ((m + 1 : ℕ) : ℝ) := by
        rw [hcrossN]
        calc
          (Nat.choose N m : ℝ) * ((N - m : ℕ) : ℝ) ≤
              ((Nat.choose (N + Q) m : ℝ) *
                ((N : ℝ) / (N + Q : ℝ)) ^ m) *
                  ((N - m : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_right (ih hmNle) (by positivity)
          _ ≤ ((Nat.choose (N + Q) m : ℝ) *
                ((N : ℝ) / (N + Q : ℝ)) ^ m) *
                  (((N : ℝ) / (N + Q : ℝ)) *
                    ((N + Q - m : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hfactor
              (mul_nonneg (by positivity) (pow_nonneg hratio_nonneg _))
          _ = ((Nat.choose (N + Q) m : ℝ) *
                ((N + Q - m : ℕ) : ℝ)) *
                  (((N : ℝ) / (N + Q : ℝ)) ^ m *
                    ((N : ℝ) / (N + Q : ℝ))) := by ring
          _ = ((Nat.choose (N + Q) (m + 1) : ℝ) *
                ((m + 1 : ℕ) : ℝ)) *
                  ((N : ℝ) / (N + Q : ℝ)) ^ (m + 1) := by
            rw [← hcrossNQ, pow_succ]
          _ = ((Nat.choose (N + Q) (m + 1) : ℝ) *
                ((N : ℝ) / (N + Q : ℝ)) ^ (m + 1)) *
                  ((m + 1 : ℕ) : ℝ) := by ring
      exact le_of_mul_le_mul_right hmul (by positivity)

/-- Enlarging the ambient capacity from `N` to `N + Q` incurs an explicit
exponential gain in the binomial coefficient.  The edge cases `m = 0` and
`Q = 0` are included. -/
theorem choose_le_choose_add_mul_exp_neg
    {N Q m : ℕ} (hm : m ≤ N) (hpos : 0 < N + Q) :
    (Nat.choose N m : ℝ) ≤
      (Nat.choose (N + Q) m : ℝ) *
        Real.exp (-((m : ℝ) * (Q : ℝ) / (N + Q : ℝ))) := by
  have hden' : (0 : ℝ) < (N : ℝ) + (Q : ℝ) := by exact_mod_cast hpos
  have hratio_nonneg : (0 : ℝ) ≤ (N : ℝ) / (N + Q : ℝ) := by positivity
  have hratio_exp :
      (N : ℝ) / (N + Q : ℝ) ≤
        Real.exp (-((Q : ℝ) / (N + Q : ℝ))) := by
    calc
      (N : ℝ) / (N + Q : ℝ) =
          1 + (-((Q : ℝ) / (N + Q : ℝ))) := by
        field_simp [hden'.ne']
        ring
      _ ≤ Real.exp (-((Q : ℝ) / (N + Q : ℝ))) :=
        by simpa [add_comm] using Real.add_one_le_exp (-((Q : ℝ) / (N + Q : ℝ)))
  have hpow :
      ((N : ℝ) / (N + Q : ℝ)) ^ m ≤
        Real.exp (-((m : ℝ) * (Q : ℝ) / (N + Q : ℝ))) := by
    calc
      ((N : ℝ) / (N + Q : ℝ)) ^ m ≤
          (Real.exp (-((Q : ℝ) / (N + Q : ℝ)))) ^ m :=
        pow_le_pow_left₀ hratio_nonneg hratio_exp m
      _ = Real.exp (-((m : ℝ) * (Q : ℝ) / (N + Q : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  exact (choose_le_choose_add_mul_pow_ratio hm hpos).trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))

end DenseGraph
