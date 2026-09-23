import InducedStars.Structure.Critical.CoPartiteComparison
import DenseGraph.Combinatorics.BinomialEntropy
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Logarithmic prefactors in the critical window

Choosing the exceptional labels contributes on the squared-logarithm scale.
Balanced multinomial ratios and the multiplicity of an empty exceptional
graph contribute only lower-order terms.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators

namespace InducedStars

def criticalWindowBalancedMultinomial (r n : ℕ) : ℕ :=
  Nat.multinomial Finset.univ (DenseGraph.balancedPartSize r n)

theorem criticalWindowBalancedMultinomial_pos (r n : ℕ) :
    0 < criticalWindowBalancedMultinomial r n :=
  Nat.multinomial_pos _ _

theorem criticalWindowBalancedMultinomial_le_pow
    {r : ℕ} (hr : 0 < r) (n : ℕ) :
    criticalWindowBalancedMultinomial r n ≤ r ^ n := by
  have h := DenseGraph.multinomial_le_card_assignmentsOfFiberSizes
    (V := Fin n) (DenseGraph.balancedPartSize r n)
    (by simpa using DenseGraph.sum_balancedPartSize (q := n) hr)
  calc
    criticalWindowBalancedMultinomial r n ≤
      (DenseGraph.assignmentsOfFiberSizes (V := Fin n)
        (DenseGraph.balancedPartSize r n)).card := h
    _ ≤ Fintype.card (Fin n → Fin r) := Finset.card_le_univ _
    _ = r ^ n := by simp

theorem abs_log_criticalWindowBalancedMultinomial_sub_le
    {r : ℕ} (hr : 0 < r) (n : ℕ) :
    |Real.log (criticalWindowBalancedMultinomial r n : ℝ) -
        (n : ℝ) * Real.log (r : ℝ)| ≤ (r : ℝ) * Real.log ((n : ℝ) + 1) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hM : (0 : ℝ) < criticalWindowBalancedMultinomial r n := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos r n
  have hup : (criticalWindowBalancedMultinomial r n : ℝ) ≤ (r : ℝ) ^ n := by
    exact_mod_cast criticalWindowBalancedMultinomial_le_pow hr n
  have hlo : (r : ℝ) ^ n ≤ ((n : ℝ) + 1) ^ r *
      (criticalWindowBalancedMultinomial r n : ℝ) := by
    exact_mod_cast DenseGraph.pow_le_succ_pow_mul_multinomial_balancedPartSize
      (q := n) hr
  have hlogup := Real.log_le_log hM hup
  rw [Real.log_pow] at hlogup
  have hloglo := Real.log_le_log (pow_pos hrR n) hlo
  rw [Real.log_mul (by positivity) hM.ne', Real.log_pow, Real.log_pow] at hloglo
  have hnonneg : 0 ≤ (r : ℝ) * Real.log ((n : ℝ) + 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem criticalWindowLog_nat_tendsto_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem criticalWindowLinearLog_div_logSq_tendsto_zero (a b : ℝ) :
    Tendsto (fun n : ℕ ↦ (a * Real.log (n : ℝ) + b) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ ↦ a / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop criticalWindowLog_nat_tendsto_atTop
  have h2 : Tendsto (fun n : ℕ ↦ b / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        criticalWindowLog_nat_tendsto_atTop)
  have h := h1.add h2
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn
  change 0 < Real.log (n : ℝ) at hn
  field_simp

theorem criticalWindowLogSucc_div_logSq_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.log ((n : ℝ) + 1) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])) (sq_nonneg _))
    ?_ (criticalWindowLinearLog_div_logSq_tendsto_zero 1 (Real.log 2))
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log (n : ℝ) + Real.log 2 := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) + 1)
      (by linarith : (n : ℝ) + 1 ≤ (n : ℝ) * 2)
    rwa [Real.log_mul (by linarith) (by norm_num)] at h
  exact div_le_div_of_nonneg_right (by simpa using hlog) (sq_nonneg _)

theorem criticalWindowSize_div_nat_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (s n : ℝ) / n) atTop (𝓝 0) := by
  have hl : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have h := hs.mul hl
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn
  change 0 < Real.log (n : ℝ) at hn
  field_simp

theorem criticalWindow_eventually_size_le_nat
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    ∀ᶠ n : ℕ in atTop, s n ≤ n := by
  filter_upwards [(criticalWindowSize_div_nat_tendsto_zero hs).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact_mod_cast ((div_lt_one hnR).mp hn).le

theorem criticalWindowSize_div_logSq_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  convert hs.div_atTop criticalWindowLog_nat_tendsto_atTop using 1
  simp only [div_div, pow_two]

theorem criticalWindow_logBound_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x))
    (a b : ℝ) {f : ℕ → ℝ}
    (hbound : ∀ᶠ n : ℕ in atTop,
      |f n| ≤ a * (s n : ℝ) + b * Real.log ((n : ℝ) + 1)) :
    Tendsto (fun n ↦ f n / Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := ((criticalWindowSize_div_logSq_tendsto_zero hs).const_mul a).add
    (criticalWindowLogSucc_div_logSq_tendsto_zero.const_mul b)
  simp only [mul_zero, zero_add] at h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ h
  filter_upwards [hbound] with n hn
  rw [abs_div, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ)))]
  calc
    |f n| / Real.log (n : ℝ) ^ 2 ≤
        (a * (s n : ℝ) + b * Real.log ((n : ℝ) + 1)) / Real.log (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = _ := by ring

/-- The balanced multinomial ratio costs only a lower-order logarithm. -/
theorem criticalWindowBalancedMultinomialRatio_log_tendsto
    {r : ℕ} (hr : 0 < r) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log
      ((criticalWindowBalancedMultinomial r (n - s n) : ℝ) /
        (criticalWindowBalancedMultinomial r n : ℝ)) /
          Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  apply criticalWindow_logBound_tendsto_zero hs (Real.log (r : ℝ)) (2 * r)
  filter_upwards [criticalWindow_eventually_size_le_nat hs] with n hn
  have hnR : ((n - s n : ℕ) : ℝ) = (n : ℝ) - s n := Nat.cast_sub hn
  have hq := abs_le.mp (abs_log_criticalWindowBalancedMultinomial_sub_le hr (n - s n))
  have hn' := abs_le.mp (abs_log_criticalWindowBalancedMultinomial_sub_le hr n)
  have hlog : (r : ℝ) * Real.log ((n - s n : ℕ) + 1 : ℝ) ≤
      (r : ℝ) * Real.log ((n : ℝ) + 1) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le n (s n)) 1
  have hrlog : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  have hslog : 0 ≤ (s n : ℝ) * Real.log (r : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) hrlog
  rw [Real.log_div (by exact_mod_cast (criticalWindowBalancedMultinomial_pos r (n - s n)).ne')
    (by exact_mod_cast (criticalWindowBalancedMultinomial_pos r n).ne')]
  rw [hnR] at hq hlog
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The decomposition multiplicity has negligible logarithm. -/
theorem criticalWindowAssemblyMultiplicity_log_tendsto
    (r : ℕ) {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log ((s n + r).choose r : ℝ) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  apply criticalWindow_logBound_tendsto_zero hs 0 r
  filter_upwards [criticalWindow_eventually_size_le_nat hs] with n hn
  have hpos : (0 : ℝ) < (s n + r).choose r := by
    exact_mod_cast Nat.choose_pos (by omega : r ≤ s n + r)
  have hupper : ((s n + r).choose r : ℝ) ≤ ((s n : ℝ) + 1) ^ r := by
    exact_mod_cast Nat.choose_add_le_add_one_pow (s n) r
  have hlog := Real.log_le_log hpos hupper
  rw [Real.log_pow] at hlog
  have hmono : Real.log ((s n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  have hnonneg : 0 ≤ Real.log ((s n + r).choose r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
      (Nat.choose_pos (by omega : r ≤ s n + r)).ne'))
  rw [abs_of_nonneg hnonneg]
  simpa only [zero_mul, zero_add] using hlog.trans
    (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg r))

/-- A logarithmic-size exceptional set has a negligible iterated logarithm. -/
theorem criticalWindowLogSize_div_log_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ Real.log ((s n : ℝ) + 1) / Real.log (n : ℝ))
      atTop (𝓝 0) := by
  have hC : 0 < |x| + 2 := by positivity
  have h1 : Tendsto (fun n : ℕ ↦ Real.log (|x| + 2) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop criticalWindowLog_nat_tendsto_atTop
  have h2 : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      criticalWindowLog_nat_tendsto_atTop
  have hsum := h1.add h2
  simp only [zero_add] at hsum
  have hbound := hs.eventually
    (Iio_mem_nhds (by linarith [le_abs_self x] : x < |x| + 1))
  have hlog := criticalWindowLog_nat_tendsto_atTop.eventually (eventually_gt_atTop (1 : ℝ))
  apply squeeze_zero' ?_ ?_ hsum
  · filter_upwards [hlog] with n hn
    exact div_nonneg (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (s n)]))
      (le_of_lt (lt_trans (by norm_num) hn))
  · filter_upwards [hbound, hlog] with n hn hl
    change 1 < Real.log (n : ℝ) at hl
    have hsbound : (s n : ℝ) < (|x| + 1) * Real.log (n : ℝ) :=
      (div_lt_iff₀ (by linarith)).mp hn
    have hlogbound := Real.log_le_log
      (by positivity : (0 : ℝ) < (s n : ℝ) + 1)
      (by nlinarith : (s n : ℝ) + 1 ≤ (|x| + 2) * Real.log (n : ℝ))
    rw [Real.log_mul hC.ne' (by linarith)] at hlogbound
    simpa only [add_div] using
      div_le_div_of_nonneg_right hlogbound (by linarith : 0 ≤ Real.log (n : ℝ))

theorem criticalWindowSizeLogSize_div_logSq_tendsto_zero
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n ↦ (s n : ℝ) * Real.log ((s n : ℝ) + 1) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := hs.mul (criticalWindowLogSize_div_log_tendsto_zero hs)
  simp only [mul_zero] at h
  convert h using 1
  ext n
  ring

/-- The label-choice binomial has a lower bound uniform down to an empty
exceptional set. -/
theorem criticalWindow_log_choose_sandwich {n s : ℕ} (hs : s ≤ n) :
    (s : ℝ) * Real.log (n : ℝ) - (s : ℝ) * Real.log ((s : ℝ) + 1) -
        Real.log ((n : ℝ) + 1) ≤ Real.log (n.choose s : ℝ) ∧
      Real.log (n.choose s : ℝ) ≤ (s : ℝ) * Real.log (n : ℝ) := by
  have hchoose : (0 : ℝ) < n.choose s := by exact_mod_cast Nat.choose_pos hs
  constructor
  · by_cases hs0 : s = 0
    · subst s
      simp only [Nat.cast_zero, zero_mul, sub_zero, zero_sub,
        Nat.choose_zero_right, Nat.cast_one, Real.log_one]
      exact neg_nonpos.mpr (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n]))
    have hsR : (0 : ℝ) < s := by exact_mod_cast Nat.pos_of_ne_zero hs0
    have hnR : (0 : ℝ) < n := lt_of_lt_of_le hsR (by exact_mod_cast hs)
    have hp0 : (0 : ℝ) ≤ (s : ℝ) / n := div_nonneg hsR.le hnR.le
    have hp1 : (s : ℝ) / n ≤ 1 := (div_le_one hnR).mpr (by exact_mod_cast hs)
    have hterm : 0 ≤ -((1 - (s : ℝ) / n) * Real.log (1 - (s : ℝ) / n)) := by
      apply neg_nonneg.mpr
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith)
        (Real.log_nonpos (by linarith) (by linarith))
    have hentropy : (s : ℝ) * (Real.log (n : ℝ) - Real.log (s : ℝ)) ≤
        DenseGraph.binomialEntropyPerspective n s := by
      unfold DenseGraph.binomialEntropyPerspective Real.binEntropy
      rw [Real.log_inv, Real.log_inv, Real.log_div hsR.ne' hnR.ne']
      have hid : (n : ℝ) * ((s : ℝ) / n) = s := by field_simp
      calc
        (s : ℝ) * (Real.log (n : ℝ) - Real.log (s : ℝ)) ≤
            (s : ℝ) * (Real.log (n : ℝ) - Real.log (s : ℝ)) +
              (n : ℝ) * (-((1 - (s : ℝ) / n) * Real.log (1 - (s : ℝ) / n))) :=
          le_add_of_nonneg_right (mul_nonneg hnR.le hterm)
        _ = ((n : ℝ) * ((s : ℝ) / n)) * (Real.log (n : ℝ) - Real.log (s : ℝ)) +
              (n : ℝ) * (-((1 - (s : ℝ) / n) * Real.log (1 - (s : ℝ) / n))) := by rw [hid]
        _ = _ := by ring
    have hlogs : Real.log (s : ℝ) ≤ Real.log ((s : ℝ) + 1) :=
      Real.log_le_log hsR (by linarith)
    have h := DenseGraph.log_choose_lower_binEntropy hs
    push_cast at h
    nlinarith [mul_le_mul_of_nonneg_left hlogs hsR.le]
  · have hpow : (n.choose s : ℝ) ≤ (n : ℝ) ^ s := by
      exact_mod_cast Nat.choose_le_pow n s
    have h := Real.log_le_log hchoose hpow
    rwa [Real.log_pow] at h

/-- Choosing `s ~ x log n` exceptional labels contributes `x log² n`. -/
theorem criticalWindowChoose_log_tendsto
    {s : ℕ → ℕ} {x : ℝ}
    (hs : Tendsto (fun n ↦ (s n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 x)) :
    Tendsto (fun n : ℕ ↦ Real.log (n.choose (s n) : ℝ) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 x) := by
  have hmain : Tendsto (fun n ↦ (s n : ℝ) * Real.log (n : ℝ) /
      Real.log (n : ℝ) ^ 2) atTop (𝓝 x) := by
    apply hs.congr'
    filter_upwards [criticalWindowLog_nat_tendsto_atTop.eventually
      (eventually_gt_atTop (0 : ℝ))] with n hn
    change 0 < Real.log (n : ℝ) at hn
    field_simp
  have hlower := (hmain.sub (criticalWindowSizeLogSize_div_logSq_tendsto_zero hs)).sub
    criticalWindowLogSucc_div_logSq_tendsto_zero
  simp only [sub_zero] at hlower
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [criticalWindow_eventually_size_le_nat hs] with n hn
    have h := div_le_div_of_nonneg_right (criticalWindow_log_choose_sandwich hn).1
      (sq_nonneg (Real.log (n : ℝ)))
    convert h using 1
    ring
  · filter_upwards [criticalWindow_eventually_size_le_nat hs] with n hn
    exact div_le_div_of_nonneg_right (criticalWindow_log_choose_sandwich hn).2
      (sq_nonneg (Real.log (n : ℝ)))


/-- Exact consecutive balanced multinomial recurrence. -/
theorem criticalWindowBalancedMultinomial_succ
    {r : ℕ} (hr : 0 < r) (n : ℕ) :
    (n / r + 1) * criticalWindowBalancedMultinomial r (n + 1) =
      (n + 1) * criticalWindowBalancedMultinomial r n := by
  let P := ∏ i : Fin r, (DenseGraph.balancedPartSize r n i).factorial
  have hP : 0 < P := Nat.prod_factorial_pos _ _
  have h0 : P * criticalWindowBalancedMultinomial r n = n.factorial := by
    simpa [P, criticalWindowBalancedMultinomial, DenseGraph.sum_balancedPartSize hr] using
      Nat.multinomial_spec (Finset.univ : Finset (Fin r)) (DenseGraph.balancedPartSize r n)
  have h1 : ((n / r + 1) * P) * criticalWindowBalancedMultinomial r (n + 1) =
      (n + 1).factorial := by
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin r))
      (DenseGraph.balancedPartSize r (n + 1))
    rw [DenseGraph.prod_factorial_balancedPartSize_succ hr] at h
    simpa only [DenseGraph.sum_balancedPartSize hr, P, criticalWindowBalancedMultinomial] using h
  apply Nat.eq_of_mul_eq_mul_left hP
  calc
    P * ((n / r + 1) * criticalWindowBalancedMultinomial r (n + 1)) =
        ((n / r + 1) * P) * criticalWindowBalancedMultinomial r (n + 1) := by ring
    _ = (n + 1).factorial := h1
    _ = (n + 1) * n.factorial := Nat.factorial_succ n
    _ = P * ((n + 1) * criticalWindowBalancedMultinomial r n) := by rw [← h0]; ring

theorem criticalWindowBalancedMultinomial_succ_bounds
    {r : ℕ} (hr : 0 < r) (n : ℕ) :
    criticalWindowBalancedMultinomial r n ≤ criticalWindowBalancedMultinomial r (n + 1) ∧
      criticalWindowBalancedMultinomial r (n + 1) ≤
        r * criticalWindowBalancedMultinomial r n := by
  have heq := criticalWindowBalancedMultinomial_succ hr n
  have hdiv : n / r + 1 ≤ n + 1 := Nat.add_le_add_right (Nat.div_le_self n r) 1
  have hbig : n + 1 ≤ r * (n / r + 1) := by
    have hmod := Nat.mod_lt n hr
    have hid := Nat.mod_add_div n r
    nlinarith
  constructor
  · have h := Nat.mul_le_mul_right (criticalWindowBalancedMultinomial r n) hdiv
    nlinarith
  · have h := Nat.mul_le_mul_right (criticalWindowBalancedMultinomial r n) hbig
    nlinarith

/-- Removing `s` labels costs between one and `r^s`, uniformly in the
ambient order, including `s=1`. -/
theorem criticalWindowBalancedMultinomial_add_bounds
    {r : ℕ} (hr : 0 < r) (n s : ℕ) :
    criticalWindowBalancedMultinomial r n ≤ criticalWindowBalancedMultinomial r (n + s) ∧
      criticalWindowBalancedMultinomial r (n + s) ≤
        r ^ s * criticalWindowBalancedMultinomial r n := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hstep := criticalWindowBalancedMultinomial_succ_bounds hr (n + s)
      constructor
      · exact ih.1.trans hstep.1
      · calc
          criticalWindowBalancedMultinomial r (n + (s + 1)) ≤
              r * criticalWindowBalancedMultinomial r (n + s) := by
            simpa only [Nat.add_assoc] using hstep.2
          _ ≤ r * (r ^ s * criticalWindowBalancedMultinomial r n) :=
            Nat.mul_le_mul_left r ih.2
          _ = r ^ (s + 1) * criticalWindowBalancedMultinomial r n := by rw [pow_succ]; ring

theorem abs_log_criticalWindowBalancedMultinomialRatio_le
    {r n s : ℕ} (hr : 0 < r) (hs : s ≤ n) :
    |Real.log ((criticalWindowBalancedMultinomial r (n - s) : ℝ) /
      (criticalWindowBalancedMultinomial r n : ℝ))| ≤ (s : ℝ) * Real.log (r : ℝ) := by
  have h := criticalWindowBalancedMultinomial_add_bounds hr (n - s) s
  rw [Nat.sub_add_cancel hs] at h
  have hq : (0 : ℝ) < criticalWindowBalancedMultinomial r (n - s) := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos r (n - s)
  have hn : (0 : ℝ) < criticalWindowBalancedMultinomial r n := by
    exact_mod_cast criticalWindowBalancedMultinomial_pos r n
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hlo := Real.log_le_log hq (by exact_mod_cast h.1 :
    (criticalWindowBalancedMultinomial r (n - s) : ℝ) ≤ criticalWindowBalancedMultinomial r n)
  have hup := Real.log_le_log hn (by exact_mod_cast h.2 :
    (criticalWindowBalancedMultinomial r n : ℝ) ≤
      (r : ℝ) ^ s * criticalWindowBalancedMultinomial r (n - s))
  rw [Real.log_mul (pow_pos hrR s).ne' hq.ne', Real.log_pow] at hup
  rw [Real.log_div hq.ne' hn.ne', abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith

/-- The stronger normalization needed for the above-transition conclusion.
Only eventual feasibility `s≤n` is required; zero sizes are totalized. -/
theorem criticalWindowBalancedMultinomialRatio_log_smallScale_tendsto
    {r : ℕ} (hr : 0 < r) {s : ℕ → ℕ}
    (hs : ∀ᶠ n : ℕ in atTop, s n ≤ n) :
    Tendsto (fun n ↦ Real.log
      ((criticalWindowBalancedMultinomial r (n - s n) : ℝ) /
        (criticalWindowBalancedMultinomial r n : ℝ)) /
          ((s n : ℝ) * Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ ↦ Real.log (r : ℝ) / Real.log (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop criticalWindowLog_nat_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ abs_nonneg _) ?_ hlim
  filter_upwards [hs, criticalWindowLog_nat_tendsto_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with n hn hl
  change 0 < Real.log (n : ℝ) at hl
  have hrlog : 0 ≤ Real.log (r : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ r by omega))
  by_cases hsz : s n = 0
  · simp only [hsz, Nat.cast_zero, zero_mul, div_zero, abs_zero]
    exact div_nonneg hrlog hl.le
  have hsR : (0 : ℝ) < s n := by exact_mod_cast Nat.pos_of_ne_zero hsz
  rw [abs_div, abs_of_pos (mul_pos hsR hl)]
  calc
    |Real.log ((criticalWindowBalancedMultinomial r (n - s n) : ℝ) /
        (criticalWindowBalancedMultinomial r n : ℝ))| /
          ((s n : ℝ) * Real.log (n : ℝ)) ≤
        ((s n : ℝ) * Real.log (r : ℝ)) / ((s n : ℝ) * Real.log (n : ℝ)) :=
      div_le_div_of_nonneg_right (abs_log_criticalWindowBalancedMultinomialRatio_le hr hn)
        (mul_pos hsR hl).le
    _ = _ := by field_simp


end InducedStars
