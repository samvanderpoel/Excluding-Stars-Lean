import InducedStars.C4.ColoredStabilityAlgebra
import Mathlib.Data.Nat.Find

/-!
# Finite parameters for the split-template comparison

The blue-clique size is chosen by an actual greatest-integer construction.
Degree inversion retains the successor-clique rounding term, and a positive
entropy level keeps the selected density uniformly away from both endpoints.
-/

open Set Filter

namespace InducedStars

/-- Largest possible blue clique whose forced edges do not exceed `blue`. -/
def c4BalancedBlueSize (n blue : ℕ) : ℕ :=
  Nat.findGreatest (fun b => b.choose 2 ≤ blue) n

theorem c4BalancedBlueSize_le (n blue : ℕ) : c4BalancedBlueSize n blue ≤ n :=
  Nat.findGreatest_le n

theorem c4BalancedBlueSize_choose_le (n blue : ℕ) :
    (c4BalancedBlueSize n blue).choose 2 ≤ blue := by
  exact Nat.findGreatest_spec (P := fun b => b.choose 2 ≤ blue)
    (m := 0) (Nat.zero_le n) (by simp)

theorem c4BalancedBlueSize_pos {n blue : ℕ} (hn : 1 ≤ n) :
    1 ≤ c4BalancedBlueSize n blue :=
  Nat.le_findGreatest (P := fun b => b.choose 2 ≤ blue) hn (by simp)

private theorem choose_two_succ (b : ℕ) : (b + 1).choose 2 = b + b.choose 2 := by
  simpa only [Nat.reduceAdd, Nat.choose_one_right] using Nat.choose_succ_succ' b 1

/-- Maximality includes the endpoint `blue = choose n 2`, where the chosen
blue size is `n` and the next clique is still strictly too large. -/
theorem c4BalancedBlueSize_succ_choose_gt {n blue : ℕ}
    (hn : 1 ≤ n) (hblue : blue ≤ n.choose 2) :
    blue < (c4BalancedBlueSize n blue + 1).choose 2 := by
  have hle := c4BalancedBlueSize_le n blue
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun b => b.choose 2 ≤ blue)
      (n := n)
      (show c4BalancedBlueSize n blue < c4BalancedBlueSize n blue + 1 by omega)
      (show c4BalancedBlueSize n blue + 1 ≤ n by omega))
  · rw [heq, choose_two_succ]
    omega

theorem c4BalancedBlueSize_rounding {n blue : ℕ}
    (hn : 1 ≤ n) (hblue : blue ≤ n.choose 2) :
    blue - (c4BalancedBlueSize n blue).choose 2 < c4BalancedBlueSize n blue := by
  have hsucc := c4BalancedBlueSize_succ_choose_gt hn hblue
  rw [choose_two_succ] at hsucc
  have hspec := c4BalancedBlueSize_choose_le n blue
  omega

theorem c4BalancedBlueSize_rounding_abs {n blue : ℕ}
    (hn : 1 ≤ n) (hblue : blue ≤ n.choose 2) :
    |((c4BalancedBlueSize n blue).choose 2 : ℝ) - blue| ≤ n := by
  have hspec := c4BalancedBlueSize_choose_le n blue
  have hround := (c4BalancedBlueSize_rounding hn hblue).le.trans
    (c4BalancedBlueSize_le n blue)
  have hspecR : ((c4BalancedBlueSize n blue).choose 2 : ℝ) ≤ blue := by
    exact_mod_cast hspec
  rw [abs_of_nonpos (sub_nonpos.mpr hspecR), neg_sub]
  have hcast : ((blue - (c4BalancedBlueSize n blue).choose 2 : ℕ) : ℝ) =
      (blue : ℝ) - (c4BalancedBlueSize n blue).choose 2 := Nat.cast_sub hspec
  rw [← hcast]
  exact_mod_cast hround

theorem c4BalancedBlueSize_lt_of_blue_lt {n blue : ℕ}
    (hblue : blue < n.choose 2) : c4BalancedBlueSize n blue < n := by
  have hspec := c4BalancedBlueSize_choose_le n blue
  have hle := c4BalancedBlueSize_le n blue
  by_contra h
  have heq : c4BalancedBlueSize n blue = n := by omega
  rw [heq] at hspec
  omega

/-- Finite degree inversion. The exact next-clique upper bound absorbs its
linear rounding term as soon as `sqrt eta * n ≥ 1`. -/
theorem c4_red_degree_le_of_choose_bound
    {n d bs : ℕ} {blue missing eta : ℝ}
    (heta : 0 ≤ eta) (hthreshold : 1 ≤ Real.sqrt eta * n)
    (hdegree : (d.choose 2 : ℝ) ≤ blue + missing)
    (hblue : blue < ((bs + 1).choose 2 : ℝ))
    (hmissing : missing ≤ eta * (n : ℝ) ^ 2) :
    (d : ℝ) ≤ bs + 2 * Real.sqrt eta * n := by
  let t : ℝ := Real.sqrt eta * n
  have ht : 1 ≤ t := hthreshold
  have ht2 : t ^ 2 = eta * (n : ℝ) ^ 2 := by
    dsimp [t]
    rw [mul_pow, Real.sq_sqrt heta]
  have hchoose : (d : ℝ) * (d - 1) <
      (bs : ℝ) * (bs + 1) + 2 * t ^ 2 := by
    rw [Nat.cast_choose_two] at hdegree hblue
    push_cast at hblue
    nlinarith
  by_contra h
  have hlt : (bs : ℝ) + 2 * t < d := by dsimp [t]; linarith
  have hpositive : 0 < (d : ℝ) + bs + 2 * t - 1 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) bs]
  have hpoly := mul_pos (sub_pos.mpr hlt) hpositive
  have hbs := mul_nonneg (Nat.cast_nonneg (α := ℝ) bs)
    (show 0 ≤ 2 * t - 1 by linarith)
  have hterr := mul_nonneg (show 0 ≤ t by linarith) (show 0 ≤ t - 1 by linarith)
  nlinarith

/-- A single large-`n` threshold for all red-neighborhood degree comparisons. -/
theorem eventually_c4_red_degree_le_of_choose_bound {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ n : ℕ in atTop, ∀ d bs : ℕ, ∀ blue missing : ℝ,
      (d.choose 2 : ℝ) ≤ blue + missing →
      blue < ((bs + 1).choose 2 : ℝ) → missing ≤ eta * (n : ℝ) ^ 2 →
      (d : ℝ) ≤ bs + 2 * Real.sqrt eta * n := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / Real.sqrt eta)
  have hs : 0 < Real.sqrt eta := Real.sqrt_pos.2 heta
  filter_upwards [eventually_ge_atTop n₀] with n hn
  intro d bs blue missing hd hb hm
  apply c4_red_degree_le_of_choose_bound heta.le ?_ hd hb hm
  have hh : 1 / Real.sqrt eta < (n : ℝ) := hn₀.trans_le (by exact_mod_cast hn)
  have hh' := (div_lt_iff₀ hs).1 hh
  nlinarith

/-- Positive entropy levels are uniformly separated from the density endpoints.
Only positivity of the level is needed; the conclusion is vacuous for levels
larger than the entropy maximum. -/
theorem c4_entropy_level_compact_band {kappa : ℝ} (hk : 0 < kappa) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha < 1 / 2 ∧
      ∀ q ∈ Icc (0 : ℝ) 1, kappa / 4 ≤ binaryEntropy q →
        q ∈ Icc alpha (1 - alpha) := by
  have hc := Metric.continuousAt_iff.mp (binaryEntropy_continuous.continuousAt (x := 0))
    (kappa / 4) (by positivity)
  obtain ⟨r, hr, hsmall⟩ := hc
  let alpha : ℝ := min (r / 2) (1 / 4)
  have ha : 0 < alpha := lt_min (by positivity) (by norm_num)
  have har : alpha < r := (min_le_left _ _).trans_lt (by linarith)
  have ha1 : alpha < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hendpoint : ∀ q : ℝ, 0 ≤ q → q < alpha → binaryEntropy q < kappa / 4 := by
    intro q hq hqa
    have hdist : dist q 0 < r := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hq] using hqa.trans har
    have hh := hsmall hdist
    simp only [binaryEntropy_zero, Real.dist_eq, sub_zero] at hh
    exact (le_abs_self _).trans_lt hh
  refine ⟨alpha, ha, ha1, ?_⟩
  intro q hq hlevel
  constructor
  · by_contra h
    exact (not_lt_of_ge hlevel) (hendpoint q hq.1 (lt_of_not_ge h))
  · by_contra h
    have hh := hendpoint (1 - q) (by linarith [hq.2]) (by linarith)
    rw [binaryEntropy_one_sub] at hh
    exact (not_lt_of_ge hlevel) hh

end InducedStars
