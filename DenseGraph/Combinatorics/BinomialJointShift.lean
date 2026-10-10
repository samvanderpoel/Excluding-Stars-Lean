import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic

/-!
# Sharp binomial comparisons for joint capacity and count shifts

This file proves three elementary estimates by iterating the exact adjacent
recurrences for binomial coefficients.  In particular, no asymptotic estimate
such as Stirling's formula is used.
-/

noncomputable section

namespace DenseGraph

private theorem choose_capacity_succ_sharp
    {A L : ℕ} {lambda : ℝ}
    (hLA : L ≤ A)
    (hdensity : lambda * ((A + 1 : ℕ) : ℝ) ≤ (L : ℝ)) :
    (Nat.choose A L : ℝ) ≤
      (Nat.choose (A + 1) L : ℝ) * (1 - lambda) := by
  have hsucc_pos : (0 : ℝ) < ((A + 1 : ℕ) : ℝ) := by positivity
  have hLsucc : L ≤ A + 1 := hLA.trans (Nat.le_succ A)
  have hfactor :
      (((A + 1 - L : ℕ) : ℝ)) ≤
        (1 - lambda) * ((A + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hLsucc]
    push_cast at hdensity ⊢
    nlinarith
  have hcross :
      (Nat.choose A L : ℝ) * ((A + 1 : ℕ) : ℝ) =
        (Nat.choose (A + 1) L : ℝ) *
          ((A + 1 - L : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq A L
  apply le_of_mul_le_mul_right _ hsucc_pos
  rw [hcross]
  calc
    (Nat.choose (A + 1) L : ℝ) * (((A + 1 - L : ℕ) : ℝ)) ≤
        (Nat.choose (A + 1) L : ℝ) *
          ((1 - lambda) * ((A + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = ((Nat.choose (A + 1) L : ℝ) * (1 - lambda)) *
          ((A + 1 : ℕ) : ℝ) := by ring

/-- Sharp capacity enlargement for a binomial slice.  If the selected density
in the larger capacity is at least `lambda`, every newly added coordinate
contributes a factor at most `1 - lambda`.  The cases `A = B` and `L = 0`
are included. -/
theorem choose_capacity_enlargement_sharp
    {A B L : ℕ} {lambda : ℝ}
    (hAB : A ≤ B) (hLA : L ≤ A)
    (hlambda_pos : 0 < lambda) (hlambda_one : lambda < 1)
    (hdensity : lambda * (B : ℝ) ≤ (L : ℝ)) :
    (Nat.choose A L : ℝ) ≤
      (Nat.choose B L : ℝ) * (1 - lambda) ^ (B - A) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
      have hLB : L ≤ B := hLA.trans hAB
      have hBsucc : B + 1 - A = (B - A) + 1 := by omega
      have hprev_density : lambda * (B : ℝ) ≤ (L : ℝ) := by
        have hcast : (B : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by norm_num
        exact (mul_le_mul_of_nonneg_left hcast hlambda_pos.le).trans hdensity
      have hadjacent :
          (Nat.choose B L : ℝ) ≤
            (Nat.choose (B + 1) L : ℝ) * (1 - lambda) :=
        choose_capacity_succ_sharp hLB hdensity
      calc
        (Nat.choose A L : ℝ) ≤
            (Nat.choose B L : ℝ) * (1 - lambda) ^ (B - A) :=
          ih hprev_density
        _ ≤ ((Nat.choose (B + 1) L : ℝ) * (1 - lambda)) *
              (1 - lambda) ^ (B - A) :=
          mul_le_mul_of_nonneg_right hadjacent
            (pow_nonneg (by linarith) _)
        _ = (Nat.choose (B + 1) L : ℝ) *
              (1 - lambda) ^ (B + 1 - A) := by
          rw [hBsucc, pow_succ]
          ring

private theorem choose_succ_selected_sharp
    {B L : ℕ} {lambda : ℝ}
    (hLB : L < B) (hlambda_pos : 0 < lambda)
    (hlambda_one : lambda < 1)
    (hdensity : lambda * (B : ℝ) ≤ (L : ℝ)) :
    (Nat.choose B (L + 1) : ℝ) ≤
      (Nat.choose B L : ℝ) * ((1 - lambda) / lambda) := by
  have hLleB : L ≤ B := hLB.le
  have hfactor :
      (((B - L : ℕ) : ℝ)) ≤
        ((1 - lambda) / lambda) * ((L + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hLleB]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hlambda_pos).2
    push_cast at hdensity ⊢
    nlinarith
  have hcross :
      (Nat.choose B (L + 1) : ℝ) * ((L + 1 : ℕ) : ℝ) =
        (Nat.choose B L : ℝ) * (((B - L : ℕ) : ℝ)) := by
    exact_mod_cast Nat.choose_succ_right_eq B L
  apply le_of_mul_le_mul_right _ (by positivity : (0 : ℝ) < ((L + 1 : ℕ) : ℝ))
  rw [hcross]
  calc
    (Nat.choose B L : ℝ) * (((B - L : ℕ) : ℝ)) ≤
        (Nat.choose B L : ℝ) *
          (((1 - lambda) / lambda) * ((L + 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = ((Nat.choose B L : ℝ) * ((1 - lambda) / lambda)) *
          ((L + 1 : ℕ) : ℝ) := by ring

/-- Sharp comparison after reducing the selected count.  This remains valid
when `1 / 2 < lambda`, in which case the displayed ratio is less than one.
The case `LStar = L` is exact. -/
theorem choose_selected_count_reduction_sharp
    {B LStar L : ℕ} {lambda : ℝ}
    (hStarL : LStar ≤ L) (hLB : L ≤ B)
    (hlambda_pos : 0 < lambda) (hlambda_one : lambda < 1)
    (hdensity : lambda * (B : ℝ) ≤ (LStar : ℝ)) :
    (Nat.choose B L : ℝ) ≤
      (Nat.choose B LStar : ℝ) *
        ((1 - lambda) / lambda) ^ (L - LStar) := by
  let R : ℝ := (1 - lambda) / lambda
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  induction L, hStarL using Nat.le_induction with
  | base => simp
  | succ L hStarL ih =>
      have hLltB : L < B := by omega
      have hdiff : L + 1 - LStar = (L - LStar) + 1 := by omega
      have hLdensity : lambda * (B : ℝ) ≤ (L : ℝ) := by
        exact hdensity.trans (by exact_mod_cast hStarL)
      have hadjacent :
          (Nat.choose B (L + 1) : ℝ) ≤
            (Nat.choose B L : ℝ) * R := by
        simpa [R] using
          choose_succ_selected_sharp hLltB hlambda_pos hlambda_one hLdensity
      calc
        (Nat.choose B (L + 1) : ℝ) ≤
            (Nat.choose B L : ℝ) * R := hadjacent
        _ ≤ ((Nat.choose B LStar : ℝ) * R ^ (L - LStar)) * R :=
          mul_le_mul_of_nonneg_right (ih (by omega)) hRnonneg
        _ = (Nat.choose B LStar : ℝ) * R ^ (L + 1 - LStar) := by
          rw [hdiff, pow_succ]
          ring

/-- The logarithmic adjacent-ratio constant for selected counts in the compact
band `[lambda * N, (1 - lambda) * N]`. -/
def binomialCompactBandShiftConstant (lambda : ℝ) : ℝ :=
  Real.log ((1 - lambda) / lambda)

theorem binomialCompactBandShiftConstant_pos
    {lambda : ℝ} (hlambda_pos : 0 < lambda)
    (hlambda_half : lambda < 1 / 2) :
    0 < binomialCompactBandShiftConstant lambda := by
  unfold binomialCompactBandShiftConstant
  apply Real.log_pos
  apply (lt_div_iff₀ hlambda_pos).2
  linarith

private theorem ratio_pow_eq_exp_compactBandShiftConstant
    {d : ℕ} {lambda : ℝ}
    (hlambda_pos : 0 < lambda) (hlambda_one : lambda < 1) :
    ((1 - lambda) / lambda) ^ d =
      Real.exp (binomialCompactBandShiftConstant lambda * (d : ℝ)) := by
  have hratio_pos : 0 < (1 - lambda) / lambda := by positivity
  rw [← Real.exp_log (pow_pos hratio_pos d), Real.log_pow]
  unfold binomialCompactBandShiftConstant
  congr 1
  ring

/-- If the reference selected count `y` lies in the compact band
`[lambda * N, (1 - lambda) * N]`, then its binomial coefficient controls the
coefficient at any other admissible selected count `x` by an exponential in
their natural-number distance.  In particular, applying the result in both
orders compares any two counts in the band, and `Nat.dist x y` handles
positive, negative, and zero integer shifts uniformly. -/
theorem choose_le_choose_mul_exp_abs_shift_of_compact_band
    {N x y : ℕ} {lambda : ℝ}
    (hxN : x ≤ N) (hyN : y ≤ N)
    (hlambda_pos : 0 < lambda) (hlambda_half : lambda < 1 / 2)
    (hyLower : lambda * (N : ℝ) ≤ (y : ℝ))
    (hyUpper : (y : ℝ) ≤ (1 - lambda) * (N : ℝ)) :
    (Nat.choose N x : ℝ) ≤
      (Nat.choose N y : ℝ) *
        Real.exp (binomialCompactBandShiftConstant lambda * (Nat.dist x y : ℝ)) := by
  have hlambda_one : lambda < 1 := by linarith
  rcases le_total y x with hyx | hxy
  · have hchoose := choose_selected_count_reduction_sharp
      (B := N) (LStar := y) (L := x)
      hyx hxN hlambda_pos hlambda_one hyLower
    rw [ratio_pow_eq_exp_compactBandShiftConstant hlambda_pos hlambda_one] at hchoose
    simpa [Nat.dist_eq_sub_of_le_right hyx] using hchoose
  · have hcompOrder : N - y ≤ N - x := Nat.sub_le_sub_left hxy N
    have hcompN : N - x ≤ N := Nat.sub_le N x
    have hcompDensity : lambda * (N : ℝ) ≤ ((N - y : ℕ) : ℝ) := by
      rw [Nat.cast_sub hyN]
      nlinarith
    have hchoose := choose_selected_count_reduction_sharp
      (B := N) (LStar := N - y) (L := N - x)
      hcompOrder hcompN hlambda_pos hlambda_one hcompDensity
    rw [ratio_pow_eq_exp_compactBandShiftConstant hlambda_pos hlambda_one] at hchoose
    have hdist : Nat.dist x y = y - x := Nat.dist_eq_sub_of_le hxy
    have hsub : (N - x) - (N - y) = y - x := by omega
    rw [Nat.choose_symm hxN, Nat.choose_symm hyN, hsub] at hchoose
    simpa [hdist] using hchoose

end DenseGraph
