import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Binomial-coefficient comparison on compact density bands

The estimates here are deliberately elementary: adjacent binomial ratios
are iterated, with no use of Stirling's formula.
-/

noncomputable section

namespace DenseGraph

/-- A uniform adjacent-ratio bound for densities in a compact subinterval
about `rho`. -/
def binomialDensityBandRatio (rho : ℝ) : ℝ :=
  2 / rho + 2 / (1 - rho)

/-- The exponential Lipschitz constant used for binomial profiles. -/
def binomialDensityBandConstant (rho : ℝ) : ℝ :=
  2 * Real.log (binomialDensityBandRatio rho)

private theorem choose_succ_le_mul_of_ratio
    {N r : ℕ} {M : ℝ} (hr : r < N)
    (hM : ((N - r : ℕ) : ℝ) ≤ M * ((r + 1 : ℕ) : ℝ)) :
    (Nat.choose N (r + 1) : ℝ) ≤ (Nat.choose N r : ℝ) * M := by
  have hcross :
      (Nat.choose N (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) =
        (Nat.choose N r : ℝ) * ((N - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N r
  have hmul :
      (Nat.choose N (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) ≤
        ((Nat.choose N r : ℝ) * M) * ((r + 1 : ℕ) : ℝ) := by
    rw [hcross]
    calc
      (Nat.choose N r : ℝ) * ((N - r : ℕ) : ℝ) ≤
          (Nat.choose N r : ℝ) *
            (M * ((r + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ((Nat.choose N r : ℝ) * M) * ((r + 1 : ℕ) : ℝ) := by ring
  exact le_of_mul_le_mul_right hmul (by positivity)

private theorem choose_le_choose_succ_mul_of_ratio
    {N r : ℕ} {M : ℝ} (hr : r < N)
    (hM : ((r + 1 : ℕ) : ℝ) ≤ M * ((N - r : ℕ) : ℝ)) :
    (Nat.choose N r : ℝ) ≤ (Nat.choose N (r + 1) : ℝ) * M := by
  have hsub : 0 < ((N - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hr
  have hcross :
      (Nat.choose N (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) =
        (Nat.choose N r : ℝ) * ((N - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq N r
  have hmul :
      (Nat.choose N r : ℝ) * ((N - r : ℕ) : ℝ) ≤
        ((Nat.choose N (r + 1) : ℝ) * M) * ((N - r : ℕ) : ℝ) := by
    rw [← hcross]
    calc
      (Nat.choose N (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) ≤
          (Nat.choose N (r + 1) : ℝ) *
            (M * ((N - r : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = ((Nat.choose N (r + 1) : ℝ) * M) *
          ((N - r : ℕ) : ℝ) := by ring
  exact le_of_mul_le_mul_right hmul hsub

private theorem choose_le_choose_mul_pow_of_le
    {N a b : ℕ} {M : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hstep : ∀ r, a ≤ r → r < b →
      (Nat.choose N (r + 1) : ℝ) ≤ (Nat.choose N r : ℝ) * M) :
    (Nat.choose N b : ℝ) ≤ (Nat.choose N a : ℝ) * M ^ (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hpow : b + 1 - a = (b - a) + 1 := by omega
      calc
        (Nat.choose N (b + 1) : ℝ) ≤
            (Nat.choose N b : ℝ) * M := hstep b hab (by omega)
        _ ≤ ((Nat.choose N a : ℝ) * M ^ (b - a)) * M :=
          mul_le_mul_of_nonneg_right
            (ih (fun r har hrb ↦ hstep r har (by omega))) hM
        _ = (Nat.choose N a : ℝ) * M ^ (b + 1 - a) := by
          rw [hpow, pow_succ]
          ring

private theorem choose_le_choose_mul_pow_of_le_reverse
    {N a b : ℕ} {M : ℝ} (hM : 0 ≤ M) (hab : a ≤ b)
    (hstep : ∀ r, a ≤ r → r < b →
      (Nat.choose N r : ℝ) ≤ (Nat.choose N (r + 1) : ℝ) * M) :
    (Nat.choose N a : ℝ) ≤ (Nat.choose N b : ℝ) * M ^ (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      have hpow : b + 1 - a = (b - a) + 1 := by omega
      calc
        (Nat.choose N a : ℝ) ≤
            (Nat.choose N b : ℝ) * M ^ (b - a) :=
          ih (fun r har hrb ↦ hstep r har (by omega))
        _ ≤ ((Nat.choose N (b + 1) : ℝ) * M) * M ^ (b - a) := by
          exact mul_le_mul_of_nonneg_right
            (hstep b hab (by omega)) (pow_nonneg hM _)
        _ = (Nat.choose N (b + 1) : ℝ) * M ^ (b + 1 - a) := by
          rw [hpow, pow_succ]
          ring

private theorem densityBandRatio_pos {rho delta : ℝ}
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1) :
    0 < binomialDensityBandRatio rho := by
  have hrho : 0 < rho := by linarith
  have hone : 0 < 1 - rho := by linarith
  unfold binomialDensityBandRatio
  positivity

private theorem densityBandRatio_one_le {rho delta : ℝ}
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1) :
    1 ≤ binomialDensityBandRatio rho := by
  have hrho : 0 < rho := by linarith
  have hrhoOne : rho < 1 := by linarith
  unfold binomialDensityBandRatio
  have htwo : 2 ≤ 2 / rho := by
    rw [le_div_iff₀ hrho]
    nlinarith
  have hsecond : 0 ≤ 2 / (1 - rho) := by positivity
  linarith

theorem binomialDensityBandConstant_nonneg
    {rho delta : ℝ} (hdelta : 0 ≤ delta)
    (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1) :
    0 ≤ binomialDensityBandConstant rho := by
  unfold binomialDensityBandConstant
  exact mul_nonneg (by norm_num)
    (Real.log_nonneg (densityBandRatio_one_le hdelta hlower hupper))

private theorem densityBand_N_pos
    {N a : ℕ} {rho delta : ℝ}
    (haN : a ≤ N) (hdelta : 0 ≤ delta)
    (hlower : 0 < rho - 2 * delta)
    (haLower : rho - delta ≤ (a : ℝ) / (N : ℝ)) :
    0 < N := by
  by_contra hN
  have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
  have ha0 : a = 0 := by omega
  simp [hN0, ha0] at haLower
  linarith

private theorem upward_ratio_bound
    {N a r : ℕ} {rho delta : ℝ}
    (haN : a ≤ N) (hdelta : 0 ≤ delta)
    (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (haLower : rho - delta ≤ (a : ℝ) / (N : ℝ))
    (har : a ≤ r) (hrN : r < N) :
    (((N - r : ℕ) : ℝ) ≤
      binomialDensityBandRatio rho * ((r + 1 : ℕ) : ℝ)) := by
  have hN : 0 < N := densityBand_N_pos haN hdelta hlower haLower
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrho : 0 < rho := by linarith
  have hhalf : rho / 2 ≤ rho - delta := by linarith
  have haLower' : (rho - delta) * (N : ℝ) ≤ a :=
    (le_div_iff₀ hNr).mp haLower
  have hrLower : (rho / 2) * (N : ℝ) ≤ r := by
    exact le_trans (mul_le_mul_of_nonneg_right hhalf hNr.le)
      (haLower'.trans (by exact_mod_cast har))
  have hscale : (N : ℝ) ≤ (2 / rho) * (r : ℝ) := by
    calc
      (N : ℝ) = (2 / rho) * ((rho / 2) * (N : ℝ)) := by field_simp
      _ ≤ (2 / rho) * (r : ℝ) :=
        mul_le_mul_of_nonneg_left hrLower (by positivity)
  have hratio : 2 / rho ≤ binomialDensityBandRatio rho := by
    unfold binomialDensityBandRatio
    have : 0 ≤ 2 / (1 - rho) := by
      have : 0 < 1 - rho := by linarith
      positivity
    linarith
  have hrnonneg : (0 : ℝ) ≤ r := by positivity
  calc
    (((N - r : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N r
    _ ≤ (2 / rho) * (r : ℝ) := hscale
    _ ≤ binomialDensityBandRatio rho * (r : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hrnonneg
    _ ≤ binomialDensityBandRatio rho * ((r + 1 : ℕ) : ℝ) := by
      gcongr
      · exact (densityBandRatio_pos hdelta hlower hupper).le
      · norm_num

private theorem downward_ratio_bound
    {N a r : ℕ} {rho delta : ℝ}
    (haN : a ≤ N) (hdelta : 0 ≤ delta)
    (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (haLower : rho - delta ≤ (a : ℝ) / (N : ℝ))
    (haUpper : (a : ℝ) / (N : ℝ) ≤ rho + delta)
    (hr : r < a) :
    (((r + 1 : ℕ) : ℝ) ≤
      binomialDensityBandRatio rho * ((N - r : ℕ) : ℝ)) := by
  have hN : 0 < N := densityBand_N_pos haN hdelta hlower haLower
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hone : 0 < 1 - rho := by linarith
  have haUpper' : (a : ℝ) ≤ (rho + delta) * (N : ℝ) :=
    (div_le_iff₀ hNr).mp haUpper
  have hhalf : rho + delta ≤ (1 + rho) / 2 := by linarith
  have hNa : ((1 - rho) / 2) * (N : ℝ) ≤ (N - a : ℕ) := by
    have ha : (a : ℝ) ≤ ((1 + rho) / 2) * (N : ℝ) :=
      haUpper'.trans (mul_le_mul_of_nonneg_right hhalf hNr.le)
    have hsubcast : ((N - a : ℕ) : ℝ) = (N : ℝ) - a := by
      rw [Nat.cast_sub haN]
    rw [hsubcast]
    nlinarith
  have hNrLower : ((1 - rho) / 2) * (N : ℝ) ≤ (N - r : ℕ) := by
    exact hNa.trans (by exact_mod_cast Nat.sub_le_sub_left (Nat.le_of_lt hr) N)
  have hscale : (N : ℝ) ≤ (2 / (1 - rho)) * ((N - r : ℕ) : ℝ) := by
    calc
      (N : ℝ) = (2 / (1 - rho)) * (((1 - rho) / 2) * (N : ℝ)) := by
        field_simp
      _ ≤ (2 / (1 - rho)) * ((N - r : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hNrLower (by positivity)
  have hratio : 2 / (1 - rho) ≤ binomialDensityBandRatio rho := by
    unfold binomialDensityBandRatio
    have : 0 ≤ 2 / rho := by
      have : 0 < rho := by linarith
      positivity
    linarith
  calc
    (((r + 1 : ℕ) : ℝ)) ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt (hr.trans_le haN))
    _ ≤ (2 / (1 - rho)) * ((N - r : ℕ) : ℝ) := hscale
    _ ≤ binomialDensityBandRatio rho * ((N - r : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)

private theorem density_band_sub_le
    {N a b : ℕ} {rho delta : ℝ}
    (haN : a ≤ N) (hdelta : 0 ≤ delta)
    (hlower : 0 < rho - 2 * delta)
    (haLower : rho - delta ≤ (a : ℝ) / (N : ℝ))
    (hbUpper : (b : ℝ) / (N : ℝ) ≤ rho + delta)
    (hab : a ≤ b) :
    ((b - a : ℕ) : ℝ) ≤ 2 * delta * N := by
  have hN : 0 < N := densityBand_N_pos haN hdelta hlower haLower
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Nat.cast_sub hab]
  have ha' := (le_div_iff₀ hNr).mp haLower
  have hb' := (div_le_iff₀ hNr).mp hbUpper
  nlinarith

private theorem ratio_pow_le_exp
    {N d : ℕ} {rho delta : ℝ}
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hd : (d : ℝ) ≤ 2 * delta * N) :
    binomialDensityBandRatio rho ^ d ≤
      Real.exp (binomialDensityBandConstant rho * delta * N) := by
  let M := binomialDensityBandRatio rho
  have hMpos : 0 < M := densityBandRatio_pos hdelta hlower hupper
  have hMone : 1 ≤ M := densityBandRatio_one_le hdelta hlower hupper
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hMone
  rw [← Real.exp_log (pow_pos hMpos _), Real.log_pow]
  apply Real.exp_le_exp.mpr
  unfold binomialDensityBandConstant
  change (d : ℝ) * Real.log M ≤ 2 * Real.log M * delta * N
  nlinarith

/-- Binomial coefficients with densities in the same compact band differ
by at most an exponential in the band width.  The constant depends only on
the central density `rho`. -/
theorem choose_le_choose_mul_exp_of_density_band
    {N a b : ℕ} {rho delta : ℝ}
    (haN : a ≤ N) (hbN : b ≤ N)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (ha : rho - delta ≤ (a : ℝ) / (N : ℝ) ∧
      (a : ℝ) / (N : ℝ) ≤ rho + delta)
    (hb : rho - delta ≤ (b : ℝ) / (N : ℝ) ∧
      (b : ℝ) / (N : ℝ) ≤ rho + delta) :
    (Nat.choose N a : ℝ) ≤ (Nat.choose N b : ℝ) *
      Real.exp (binomialDensityBandConstant rho * delta * N) := by
  let M := binomialDensityBandRatio rho
  have hM : 0 ≤ M := (densityBandRatio_pos hdelta hlower hupper).le
  rcases le_total a b with hab | hba
  · have hchoose : (Nat.choose N a : ℝ) ≤
        (Nat.choose N b : ℝ) * M ^ (b - a) :=
      choose_le_choose_mul_pow_of_le_reverse hM hab
        (fun r har hrb ↦ choose_le_choose_succ_mul_of_ratio
          (hrb.trans_le hbN)
          (downward_ratio_bound hbN hdelta hlower hupper hb.1 hb.2 hrb))
    have hdist : ((b - a : ℕ) : ℝ) ≤ 2 * delta * N :=
      density_band_sub_le haN hdelta hlower ha.1 hb.2 hab
    have hpow : M ^ (b - a) ≤
        Real.exp (binomialDensityBandConstant rho * delta * N) := by
      simpa [M] using ratio_pow_le_exp hdelta hlower hupper hdist
    exact hchoose.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  · have hchoose : (Nat.choose N a : ℝ) ≤
        (Nat.choose N b : ℝ) * M ^ (a - b) :=
      choose_le_choose_mul_pow_of_le hM hba
        (fun r hbr hra ↦ choose_succ_le_mul_of_ratio
          (hra.trans_le haN)
          (upward_ratio_bound hbN hdelta hlower hupper hb.1 hbr
            (hra.trans_le haN)))
    have hdist : ((a - b : ℕ) : ℝ) ≤ 2 * delta * N :=
      density_band_sub_le hbN hdelta hlower hb.1 ha.2 hba
    have hpow : M ^ (a - b) ≤
        Real.exp (binomialDensityBandConstant rho * delta * N) := by
      simpa [M] using ratio_pow_le_exp hdelta hlower hupper hdist
    exact hchoose.trans (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- Iterate an upper bound for the inverse adjacent ratios. -/
theorem choose_le_choose_mul_pow_of_adjacent_up
    {N a b : ℕ} {M : ℝ} (hM : 0 ≤ M) (hab : a ≤ b) (hbN : b ≤ N)
    (hstep : ∀ r, a ≤ r → r < b →
      ((r + 1 : ℕ) : ℝ) ≤ M * ((N - r : ℕ) : ℝ)) :
    (Nat.choose N a : ℝ) ≤ (Nat.choose N b : ℝ) * M ^ (b - a) :=
  choose_le_choose_mul_pow_of_le_reverse hM hab
    (fun r har hrb ↦ choose_le_choose_succ_mul_of_ratio (hrb.trans_le hbN)
      (hstep r har hrb))

/-- Iterate an upper bound for the forward adjacent ratios. -/
theorem choose_le_choose_mul_pow_of_adjacent_down
    {N a b : ℕ} {M : ℝ} (hM : 0 ≤ M) (hab : a ≤ b) (hbN : b ≤ N)
    (hstep : ∀ r, a ≤ r → r < b →
      ((N - r : ℕ) : ℝ) ≤ M * ((r + 1 : ℕ) : ℝ)) :
    (Nat.choose N b : ℝ) ≤ (Nat.choose N a : ℝ) * M ^ (b - a) :=
  choose_le_choose_mul_pow_of_le hM hab
    (fun r har hrb ↦ choose_succ_le_mul_of_ratio (hrb.trans_le hbN)
      (hstep r har hrb))

end DenseGraph
