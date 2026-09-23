import DenseGraph.Analysis.EntropyBoost
import Mathlib.Data.Nat.Choose.Cast

/-!
# Arithmetic for colored induced-C4 stability

These finite inequalities retain integer clique sizes and their exact rounding
terms. Graph-theoretic hypotheses are supplied by the colored configuration
lemmas; this module isolates the three red-capacity comparisons.
-/

namespace InducedStars

/-- Exact real-valued difference of two integer clique capacities. -/
theorem c4_choose_two_sub_eq (a b : ℕ) :
    (a.choose 2 : ℝ) - b.choose 2 =
      ((a : ℝ) - b) * ((a : ℝ) + b - 1) / 2 := by
  rw [Nat.cast_choose_two, Nat.cast_choose_two]
  ring

/-- The complete split template's three capacities partition all vertex pairs. -/
theorem c4_split_capacity_sum {n g b : ℕ} (h : g + b = n) :
    (g : ℝ) * b + g.choose 2 + b.choose 2 = n.choose 2 := by
  subst n
  rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  ring

/-- Positive quadratic red mass forces both the old green part and the new
blue part to be linear-sized. All finite denominator conditions are explicit. -/
theorem c4_part_sizes_lower_of_red_count
    {n g bs kappa rho R : ℝ}
    (hn : 0 < n) (hg : 0 ≤ g) (hgn : g ≤ n) (hbs : 0 ≤ bs) (hbsn : bs ≤ n)
    (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1) (hrho : 0 ≤ rho)
    (hrhosmall : rho ≤ kappa / 40)
    (hred : kappa / 8 * n ^ 2 ≤ R) (hR : R ≤ g * (bs + rho * n)) :
    kappa / 10 * n ≤ g ∧ kappa / 10 * n ≤ bs := by
  have hrho1 : rho ≤ 1 / 4 := by linarith
  have hgerr := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hrho1 hn.le) hg
  have hgb := mul_le_mul_of_nonneg_left hbsn hg
  have hbig := mul_le_mul_of_nonneg_right hgn (show 0 ≤ bs + rho * n by positivity)
  have hsmall := mul_le_mul_of_nonneg_right hrhosmall (sq_nonneg n)
  constructor
  · by_contra h
    have hh := mul_lt_mul_of_pos_right (lt_of_not_ge h) hn
    nlinarith
  · by_contra h
    have hh := mul_lt_mul_of_pos_right (lt_of_not_ge h) hn
    nlinarith

/-- Case 1: increasing the green side gains red capacity beyond the small
red-neighborhood error. Here `kappa` is later `gamma * (1-gamma)`. -/
theorem c4_red_gain_of_green_increase
    {n g gs bs epsilon kappa rho R : ℝ}
    (hn : 0 ≤ n) (hg : 0 ≤ g) (hgn : g ≤ n)
    (he : 0 ≤ epsilon) (hk : 0 ≤ kappa) (hrho : 0 ≤ rho)
    (hrhosmall : rho ≤ epsilon * kappa / 1500)
    (hbs : kappa / 10 * n ≤ bs)
    (hgap : epsilon / 16 * n ≤ gs - g)
    (hR : R ≤ g * (bs + rho * n)) :
    epsilon * kappa / 320 * n ^ 2 ≤ gs * bs - R := by
  have hbs0 : 0 ≤ bs := (mul_nonneg (by positivity) hn).trans hbs
  have hgap0 : 0 ≤ gs - g := (mul_nonneg (by positivity) hn).trans hgap
  have hmain := mul_le_mul hgap hbs (mul_nonneg (by positivity) hn) hgap0
  have herr1 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgn hrho) hn
  have herr2 := mul_le_mul_of_nonneg_right hrhosmall (sq_nonneg n)
  have hsign := mul_nonneg (mul_nonneg he hk) (sq_nonneg n)
  nlinarith

/-- Case 2 with its exact finite rounding requirement. Positivity of the
new green part gives `gs ≥ 1`, retaining the source constant without hiding
the `-1` in the difference of binomial coefficients. -/
theorem c4_red_gain_of_green_decrease
    {n g gs : ℕ} {epsilon kappa Rstar R : ℝ}
    (he : 0 ≤ epsilon) (hk : 0 ≤ kappa) (hgs : 1 ≤ gs)
    (hg : kappa / 10 * n ≤ g)
    (hgap : epsilon / 16 * n ≤ (g : ℝ) - gs)
    (hgreen : (g.choose 2 : ℝ) - gs.choose 2 ≤ Rstar - R) :
    epsilon * kappa / 320 * (n : ℝ) ^ 2 ≤ Rstar - R := by
  have hgsR : (1 : ℝ) ≤ gs := by exact_mod_cast hgs
  have hfac : kappa / 10 * n ≤ (g : ℝ) + gs - 1 := by linarith
  have hgap0 : 0 ≤ (g : ℝ) - gs :=
    (show 0 ≤ epsilon / 16 * n by positivity).trans hgap
  have hm := mul_le_mul hgap hfac
    (show 0 ≤ kappa / 10 * n by positivity) hgap0
  rw [c4_choose_two_sub_eq] at hgreen
  nlinarith

/-- Exact conservation of the three colors and missing pairs transfers a
green-capacity lower bound to a red-capacity lower bound. -/
theorem c4_red_gain_of_green_count
    {n g gs bs : ℕ} {R green blue missing extra : ℝ}
    (hs : gs + bs = n)
    (hcounts : R + green + blue + missing = n.choose 2)
    (hblue : (bs.choose 2 : ℝ) ≤ blue)
    (hgreen : (g.choose 2 : ℝ) + extra - missing ≤ green) :
    (g.choose 2 : ℝ) - gs.choose 2 + extra ≤ (gs : ℝ) * bs - R := by
  have hsplit := c4_split_capacity_sum hs
  linarith

/-- The clique-capacity Lipschitz bound is absolute, so it is valid
for either sign of the change in green-part size. -/
theorem c4_abs_choose_two_sub_le {n a b : ℕ} (ha : a ≤ n) (hb : b ≤ n) :
    |(a.choose 2 : ℝ) - b.choose 2| ≤ (n : ℝ) * |(a : ℝ) - b| := by
  by_cases hn : n = 0
  · subst n
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    simp [ha0, hb0]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have haR : (a : ℝ) ≤ n := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ n := by exact_mod_cast hb
  have hab : |(a : ℝ) + b - 1| ≤ 2 * n := by
    apply abs_le.mpr
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  rw [c4_choose_two_sub_eq, abs_div, abs_mul]
  norm_num only [abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hm := mul_le_mul_of_nonneg_left hab (abs_nonneg ((a : ℝ) - b))
  nlinarith

/-- The complete cross capacity is `n`-Lipschitz on the part-size interval. -/
theorem c4_abs_cross_capacity_sub_le {n g gs : ℝ}
    (hg : 0 ≤ g) (hgn : g ≤ n) (hgs : 0 ≤ gs) (hgsn : gs ≤ n) :
    |gs * (n - gs) - g * (n - g)| ≤ n * |gs - g| := by
  have hf : |n - gs - g| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : gs * (n - gs) - g * (n - g) = (gs - g) * (n - gs - g) := by ring
  rw [he, abs_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hf (abs_nonneg (gs - g))

/-- Case 3, green-edge failure. Exact missing-pair accounting cancels the
missing-pair contribution before the absolute binomial comparison. -/
theorem c4_red_gain_of_near_green_failure
    {n g gs : ℕ} {epsilon Rstar R : ℝ}
    (he : 0 ≤ epsilon) (hg : g ≤ n) (hgs : gs ≤ n)
    (hgap : |(gs : ℝ) - g| ≤ epsilon / 16 * n)
    (hgreen : (g.choose 2 : ℝ) - gs.choose 2 + epsilon / 3 * (n : ℝ) ^ 2 ≤
      Rstar - R) :
    epsilon / 4 * (n : ℝ) ^ 2 ≤ Rstar - R := by
  have hchoose := c4_abs_choose_two_sub_le hgs hg
  have hsize := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) n)
  have hupper := le_of_abs_le hchoose
  have heps := mul_nonneg he (sq_nonneg (n : ℝ))
  nlinarith

/-- Case 3, nonred-cross failure, using the inequality `1/3 - 1/16 ≥ 1/4`. -/
theorem c4_red_gain_of_near_cross_failure
    {n g b gs bs : ℕ} {epsilon R : ℝ}
    (he : 0 ≤ epsilon) (hpart : g + b = n) (hstar : gs + bs = n)
    (hgap : |(gs : ℝ) - g| ≤ epsilon / 16 * n)
    (hcross : R ≤ (g : ℝ) * b - epsilon / 3 * (n : ℝ) ^ 2) :
    epsilon / 4 * (n : ℝ) ^ 2 ≤ (gs : ℝ) * bs - R := by
  have hpartR : (g : ℝ) + b = n := by exact_mod_cast hpart
  have hstarR : (gs : ℝ) + bs = n := by exact_mod_cast hstar
  have hprod := c4_abs_cross_capacity_sub_le
    (Nat.cast_nonneg (α := ℝ) g) (show (g : ℝ) ≤ n by linarith [Nat.cast_nonneg (α := ℝ) b])
    (Nat.cast_nonneg (α := ℝ) gs) (show (gs : ℝ) ≤ n by linarith [Nat.cast_nonneg (α := ℝ) bs])
  have heqg : (n : ℝ) - g = b := by linarith
  have heqs : (n : ℝ) - gs = bs := by linarith
  rw [heqg, heqs] at hprod
  have hsize := mul_le_mul_of_nonneg_left hgap (Nat.cast_nonneg (α := ℝ) n)
  have hneg := neg_le_of_abs_le hprod
  nlinarith [mul_nonneg he (sq_nonneg (n : ℝ))]

/-- The three-case red-capacity gain from actual color counts. Here `missing`
is the actual missing-pair count. Missing-pair terms cancel exactly in
the close-part-size branch. -/
theorem c4_red_capacity_gain_of_edit_failure
    {n g b gs bs : ℕ} {epsilon kappa rho R green blue missing : ℝ}
    (he : 0 ≤ epsilon) (hk : 0 ≤ kappa) (hk1 : kappa ≤ 1)
    (hpart : g + b = n) (hstar : gs + bs = n) (hgs : 1 ≤ gs)
    (hg : kappa / 10 * n ≤ g) (hbs : kappa / 10 * n ≤ bs)
    (hrho : 0 ≤ rho) (hrhosmall : rho ≤ epsilon * kappa / 1500)
    (hR : R ≤ (g : ℝ) * (bs + rho * n))
    (hcounts : R + green + blue + missing = n.choose 2)
    (hblue : (bs.choose 2 : ℝ) ≤ blue)
    (hgreen : (g.choose 2 : ℝ) - missing ≤ green)
    (hfailure : (g.choose 2 : ℝ) + epsilon / 3 * (n : ℝ) ^ 2 - missing ≤ green ∨
      R ≤ (g : ℝ) * b - epsilon / 3 * (n : ℝ) ^ 2) :
    epsilon * kappa / 320 * (n : ℝ) ^ 2 ≤ (gs : ℝ) * bs - R := by
  have hgn : g ≤ n := by omega
  have hgsn : gs ≤ n := by omega
  by_cases hincrease : epsilon / 16 * n ≤ (gs : ℝ) - g
  · exact c4_red_gain_of_green_increase (Nat.cast_nonneg n) (Nat.cast_nonneg g)
      (by exact_mod_cast hgn) he hk hrho hrhosmall hbs hincrease hR
  by_cases hdecrease : epsilon / 16 * n ≤ (g : ℝ) - gs
  · apply c4_red_gain_of_green_decrease he hk hgs hg hdecrease
    simpa only [add_zero] using c4_red_gain_of_green_count hstar hcounts hblue
      (show (g.choose 2 : ℝ) + 0 - missing ≤ green by simpa using hgreen)
  have hclose : |(gs : ℝ) - g| ≤ epsilon / 16 * n := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hstrong : epsilon / 4 * (n : ℝ) ^ 2 ≤ (gs : ℝ) * bs - R := by
    rcases hfailure with hfailure | hfailure
    · exact c4_red_gain_of_near_green_failure he hgn hgsn hclose
        (c4_red_gain_of_green_count hstar hcounts hblue hfailure)
    · exact c4_red_gain_of_near_cross_failure he hpart hstar hclose hfailure
  have hsmall := mul_le_mul_of_nonneg_left hk1
    (show 0 ≤ epsilon * (n : ℝ) ^ 2 by positivity)
  nlinarith [mul_nonneg he (sq_nonneg (n : ℝ))]

/-- Entropy boosting excludes a quadratic red-capacity gain for any candidate
whose feasible entropy is bounded by the benchmark. This numerical adapter
requires no maximizer assumption on partial templates. -/
theorem c4_near_benchmark_excludes_red_gain {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ R B Rstar Bstar target benchmark : ℝ,
        alpha ≤ (target - B) / R → (target - B) / R ≤ 1 - alpha →
        alpha * (n : ℝ) ^ 2 ≤ R → alpha * (n : ℝ) ^ 2 ≤ Rstar - R →
        |Bstar - B| ≤ (n : ℝ) →
        benchmark - delta * (n : ℝ) ^ 2 ≤ R * binaryEntropy ((target - B) / R) →
        Rstar * binaryEntropy ((target - Bstar) / Rstar) ≤ benchmark → False := by
  obtain ⟨d, hd, n₀, hboost⟩ := DenseGraph.entropy_quadratic_boost ha ha1
  refine ⟨d / 2, by positivity, max n₀ 1, ?_⟩
  intro n hn R B Rstar Bstar target benchmark hlo hhi hR hgain hblue hnear hmax
  have hn0 : n₀ ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  obtain ⟨_, _, _, _, hg⟩ := hboost n hn0 R B (Rstar - R) (Bstar - B) target
    hlo hhi hR hgain hblue
  have heqR : R + (Rstar - R) = Rstar := by ring
  have heqB : B + (Bstar - B) = Bstar := by ring
  rw [heqR, heqB] at hg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith [mul_pos hd (sq_pos_of_pos hnpos)]

end InducedStars
