import DenseGraph.Combinatorics.BinomialProfiles
import DenseGraph.Combinatorics.SecondOrderBinomial

/-!
# Integer headroom and tilted binomial ratios

Finite allocation and directional binomial comparisons. All exponential
expressions use natural logarithms; no asymptotic approximation is assumed.
-/

noncomputable section

open Finset
open scoped BigOperators Classical

namespace DenseGraph

/-- Allocate an integer among finitely many integer capacities. Empty
coordinate sets are allowed. -/
theorem exists_allocation_of_le_sum {I : Type*} [DecidableEq I]
    (s : Finset I) (room : I → ℕ) (d : ℕ) (hd : d ≤ ∑ i ∈ s, room i) :
    ∃ a : I → ℕ, (∀ i, a i ≤ room i) ∧ (∑ i ∈ s, a i) = d := by
  induction s using Finset.induction_on generalizing d with
  | empty =>
      refine ⟨fun _ ↦ 0, fun _ ↦ Nat.zero_le _, ?_⟩
      simpa using (hd.antisymm (Nat.zero_le d)).symm
  | @insert i s his ih =>
      rw [Finset.sum_insert his] at hd
      obtain ⟨a, ha, hsum⟩ := ih (d - min d (room i)) (by omega)
      refine ⟨Function.update a i (min d (room i)), ?_, ?_⟩
      · intro j
        by_cases hji : j = i
        · subst j
          simpa using min_le_right d (room i)
        · simpa [Function.update_of_ne hji] using ha j
      · rw [Finset.sum_insert his, Function.update_self]
        have hu : ∑ j ∈ s, Function.update a i (min d (room i)) j = ∑ j ∈ s, a j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Function.update_of_ne (ne_of_mem_of_not_mem hj his) _ _
        rw [hu, hsum]
        omega

/-- Integer rounding consumes at most half the available real headroom
once every coordinate has at least two units of reserve. -/
theorem half_mul_le_floor_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one x
  linarith

/-- A common density perturbation provides enough integer coordinate
headroom for a quarter of its total real capacity. -/
theorem exists_allocation_le_floor_density {I : Type*} [Fintype I]
    (N : I → ℕ) {delta : ℝ} (d : ℕ)
    (hreserve : ∀ i, 2 ≤ delta * N i)
    (hd : (d : ℝ) ≤ delta * (∑ i, N i : ℕ) / 4) :
    ∃ a : I → ℕ, (∀ i, a i ≤ ⌊delta * N i⌋₊) ∧ ∑ i, a i = d := by
  apply exists_allocation_of_le_sum univ (fun i ↦ ⌊delta * N i⌋₊) d
  have hf : ∑ i, delta * (N i : ℝ) / 2 ≤ ∑ i, (⌊delta * N i⌋₊ : ℝ) :=
    Finset.sum_le_sum (fun i _ ↦ half_mul_le_floor_of_two_le (hreserve i))
  have hs : (0 : ℝ) ≤ delta * (∑ i, N i : ℕ) := by
    rw [Nat.cast_sum, Finset.mul_sum]
    exact Finset.sum_nonneg (fun i _ ↦ (by linarith [hreserve i]))
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum] at hf
  have : (d : ℝ) ≤ ∑ i, (⌊delta * N i⌋₊ : ℝ) := by linarith
  exact_mod_cast this

/-- Natural-log Lipschitz constant for tilted adjacent binomial ratios. -/
def binomialLogOddsConstant (p : ℝ) : ℝ := 6 / p + 6 / (1 - p)

theorem binomialLogOddsConstant_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 < binomialLogOddsConstant p := by
  unfold binomialLogOddsConstant
  positivity

/-- Log odds vary by at most this explicit linear amount in a compact
three-delta band. -/
theorem abs_logOdds_sub_le {p delta q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ p) (hdq : 6 * delta ≤ 1 - p)
    (hq : |q - p| ≤ 3 * delta) :
    |Real.log (q / (1 - q)) - Real.log (p / (1 - p))| ≤
      binomialLogOddsConstant p * delta := by
  have hqband := abs_le.mp hq
  have hql : p / 2 ≤ q := by linarith
  have hqu : (1 - p) / 2 ≤ 1 - q := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < 1 - q := by linarith
  have hpq : 0 < 1 - p := by linarith
  have h1 := abs_log_sub_log_le_div_of_lower (by positivity : 0 < p / 2)
    hql (by linarith : p / 2 ≤ p)
  have h2 := abs_log_sub_log_le_div_of_lower (by positivity : 0 < (1 - p) / 2)
    hqu (by linarith : (1 - p) / 2 ≤ 1 - p)
  rw [show (1 - q) - (1 - p) = -(q - p) by ring, abs_neg] at h2
  have ht : |(Real.log q - Real.log p) -
      (Real.log (1 - q) - Real.log (1 - p))| ≤
      |Real.log q - Real.log p| + |Real.log (1 - q) - Real.log (1 - p)| :=
    abs_sub _ _
  rw [Real.log_div hq0.ne' hq1.ne', Real.log_div hp.ne' hpq.ne']
  calc
    |(Real.log q - Real.log (1 - q)) -
        (Real.log p - Real.log (1 - p))| =
      |(Real.log q - Real.log p) -
        (Real.log (1 - q) - Real.log (1 - p))| := by congr 1; ring
    _ ≤ |q - p| / (p / 2) + |q - p| / ((1 - p) / 2) := by linarith
    _ ≤ (3 * delta) / (p / 2) + (3 * delta) / ((1 - p) / 2) := by gcongr
    _ = binomialLogOddsConstant p * delta := by
      unfold binomialLogOddsConstant
      field_simp
      <;> ring

/-- Upward count shifts retain the leading natural-log odds. The larger
endpoint is in the wide band. -/
theorem choose_up_le_mul_exp_logOdds {N a b : ℕ} {p delta : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ p) (hdq : 6 * delta ≤ 1 - p)
    (hN : 0 < N) (hab : a ≤ b) (hbN : b ≤ N)
    (hb : (b : ℝ) / N ≤ p + 2 * delta) :
    (Nat.choose N a : ℝ) ≤ (Nat.choose N b : ℝ) *
      Real.exp ((-Real.log ((1 - p) / p) + binomialLogOddsConstant p * delta) *
        (b - a : ℕ)) := by
  let q := p + 3 * delta
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : 0 < 1 - q := by dsimp [q]; linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hb' := (div_le_iff₀ hNr).mp hb
  have hpow := choose_le_choose_mul_pow_of_adjacent_up
    (show 0 ≤ q / (1 - q) by positivity) hab hbN (fun r har hrb ↦ by
      have hrN : r ≤ N := by omega
      rw [Nat.cast_sub hrN]
      have hr : (r : ℝ) + 1 ≤ b := by exact_mod_cast hrb
      have hrq : (r : ℝ) + 1 ≤ q * N := by
        dsimp [q]
        nlinarith
      have hden : (1 - q) * N ≤ (N : ℝ) - r := by nlinarith
      have hscale := mul_le_mul_of_nonneg_left hden (show 0 ≤ q / (1 - q) by positivity)
      have hid : q / (1 - q) * ((1 - q) * N) = q * N := by field_simp
      rw [hid] at hscale
      simpa only [Nat.cast_add, Nat.cast_one] using hrq.trans hscale)
  have hlog := (abs_le.mp (abs_logOdds_sub_le hp hp1 hd hdp hdq
    (q := q) (by dsimp [q]; rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]))).2
  have hlogid : Real.log (p / (1 - p)) = -Real.log ((1 - p) / p) := by
    rw [Real.log_div hp.ne' (by linarith : 1 - p ≠ 0),
      Real.log_div (by linarith : 1 - p ≠ 0) hp.ne']
    ring
  have he : (q / (1 - q)) ^ (b - a) ≤
      Real.exp ((-Real.log ((1 - p) / p) + binomialLogOddsConstant p * delta) *
        (b - a : ℕ)) := by
    rw [← Real.exp_log (pow_pos (div_pos hq0 hq1) _), Real.log_pow]
    apply Real.exp_le_exp.mpr
    rw [hlogid] at hlog
    nlinarith [show (0 : ℝ) ≤ (b - a : ℕ) by positivity]
  exact hpow.trans (mul_le_mul_of_nonneg_left he (by positivity))

/-- Downward count shifts use the opposite log odds. The reserve handles
the `+1` in the exact adjacent binomial ratio. -/
theorem choose_down_le_mul_exp_logOdds {N a b : ℕ} {p delta : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ p) (hdq : 6 * delta ≤ 1 - p)
    (hN : 0 < N) (hab : a ≤ b) (hbN : b ≤ N)
    (ha : p - 2 * delta ≤ (a : ℝ) / N) (hreserve : 1 ≤ delta * N) :
    (Nat.choose N b : ℝ) ≤ (Nat.choose N a : ℝ) *
      Real.exp ((Real.log ((1 - p) / p) + binomialLogOddsConstant p * delta) *
        (b - a : ℕ)) := by
  let q := p - 3 * delta
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : 0 < 1 - q := by dsimp [q]; linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha' := (le_div_iff₀ hNr).mp ha
  have hpow := choose_le_choose_mul_pow_of_adjacent_down
    (show 0 ≤ (1 - q) / q by positivity) hab hbN (fun r har hrb ↦ by
      have hrN : r ≤ N := by omega
      rw [Nat.cast_sub hrN]
      have har' : (a : ℝ) ≤ r := by exact_mod_cast har
      have hnum : (N : ℝ) - r ≤ (1 - q) * N := by dsimp [q]; nlinarith
      have hden : q * N ≤ (r + 1 : ℕ) := by
        push_cast
        dsimp [q]
        nlinarith
      have hscale := mul_le_mul_of_nonneg_left hden (show 0 ≤ (1 - q) / q by positivity)
      have hid : (1 - q) / q * (q * N) = (1 - q) * N := by field_simp
      rw [hid] at hscale
      exact hnum.trans hscale)
  have hlog := (abs_le.mp (abs_logOdds_sub_le hp hp1 hd hdp hdq
    (q := q) (by dsimp [q]; rw [sub_sub_cancel_left, abs_neg,
      abs_of_nonneg (by positivity)]))).1
  have hlogid : Real.log ((1 - q) / q) = -Real.log (q / (1 - q)) := by
    rw [Real.log_div hq1.ne' hq0.ne', Real.log_div hq0.ne' hq1.ne']
    ring
  have hpid : Real.log (p / (1 - p)) = -Real.log ((1 - p) / p) := by
    rw [Real.log_div hp.ne' (by linarith : 1 - p ≠ 0),
      Real.log_div (by linarith : 1 - p ≠ 0) hp.ne']
    ring
  have he : ((1 - q) / q) ^ (b - a) ≤
      Real.exp ((Real.log ((1 - p) / p) + binomialLogOddsConstant p * delta) *
        (b - a : ℕ)) := by
    rw [← Real.exp_log (pow_pos (div_pos hq1 hq0) _), Real.log_pow]
    apply Real.exp_le_exp.mpr
    rw [hpid] at hlog
    rw [hlogid]
    nlinarith [show (0 : ℝ) ≤ (b - a : ℕ) by positivity]
  exact hpow.trans (mul_le_mul_of_nonneg_left he (by positivity))

end DenseGraph
