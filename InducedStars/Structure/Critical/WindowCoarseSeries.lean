import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Finite Gaussian sums in the logarithmic window

A completed square bounds the full sum by exp(O(log² n)).  Beyond a
constant multiple of log n, the remaining quadratic decay absorbs any
fixed polynomial prefactor and makes the finite tail tend to zero.
-/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace InducedStars

def criticalWindowCoarseSeriesTerm (c C : ℝ) (n s : ℕ) : ℝ :=
  Real.exp (-4 * c * (s : ℝ)^2 +
    (C + 1) * s * Real.log ((n + 1 : ℕ) : ℝ) +
    C * Real.log ((n + 1 : ℕ) : ℝ))

def criticalWindowCoarseSeries (c C : ℝ) (r : ℕ) (K : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)^r * K *
    ∑ s ∈ Finset.range (n + 1), criticalWindowCoarseSeriesTerm c C n s

def criticalWindowCoarseTail (c C : ℝ) (r : ℕ) (K L : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ)^r * K *
    ∑ s ∈ (Finset.range (n + 1)).filter
      (fun s : ℕ ↦ L * Real.log ((n + 1 : ℕ) : ℝ) ≤ (s : ℝ)),
        criticalWindowCoarseSeriesTerm c C n s

theorem criticalWindowCoarseLog_tendsto :
    Tendsto (fun n : ℕ ↦ Real.log ((n + 1 : ℕ) : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))

/-- Keep half of the Gaussian decay after completing the square. -/
theorem criticalWindowCoarseExponent_le {c C x ell : ℝ} (hc : 0 < c) :
    -4 * c * x^2 + (C + 1) * x * ell + C * ell ≤
      -2 * c * x^2 + ((C + 1)^2 / (8 * c)) * ell^2 + C * ell := by
  have hd : (8 * c) * ((C + 1)^2 / (8 * c)) = (C + 1)^2 := by
    field_simp
  have hsq := sq_nonneg (4 * c * x - (C + 1) * ell)
  have he := congrArg (fun z : ℝ ↦ z * ell^2) hd
  nlinarith

/-- A finite maximum-term estimate, including a fixed polynomial prefactor. -/
theorem criticalWindowCoarseWeightedSum_le_exp
    {n r : ℕ} {K E : ℝ} {S : Finset ℕ} {f : ℕ → ℝ}
    (hK : 0 ≤ K) (hKn : K ≤ ((n + 1 : ℕ) : ℝ))
    (hcard : S.card ≤ n + 1) (hf : ∀ s ∈ S, f s ≤ Real.exp E) :
    ((n + 1 : ℕ) : ℝ)^r * K * ∑ s ∈ S, f s ≤
      Real.exp (E + ((r : ℝ) + 2) * Real.log ((n + 1 : ℕ) : ℝ)) := by
  have hn : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hsum : ∑ s ∈ S, f s ≤ ((n + 1 : ℕ) : ℝ) * Real.exp E := by
    calc
      _ ≤ (S.card : ℝ) * Real.exp E := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul S f (Real.exp E) hf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.exp_pos E).le
  have hpow : ((n + 1 : ℕ) : ℝ)^r =
      Real.exp ((r : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hn r)]
  have hbase := Real.exp_log hn
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)^r * K *
        (((n + 1 : ℕ) : ℝ) * Real.exp E) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (pow_nonneg hn.le _) hK)
    _ ≤ ((n + 1 : ℕ) : ℝ)^r * ((n + 1 : ℕ) : ℝ) *
        (((n + 1 : ℕ) : ℝ) * Real.exp E) := by
      gcongr
    _ = Real.exp ((r : ℝ) * Real.log ((n + 1 : ℕ) : ℝ)) *
        Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) *
        (Real.exp (Real.log ((n + 1 : ℕ) : ℝ)) * Real.exp E) := by
      rw [hbase, hpow]
    _ = _ := by
      simp only [← Real.exp_add]
      congr 1
      ring

/-- The full finite series grows at most exponentially in log² n. -/
theorem exists_eventually_criticalWindowCoarseSeries_le
    {c C K : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ) (hK : 0 < K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      criticalWindowCoarseSeries c C r K n ≤
        Real.exp (B * (Real.log ((n + 1 : ℕ) : ℝ))^2) := by
  let D := (C + 1)^2 / (8 * c)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let B := D + C + (r : ℝ) + 3
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  have hKn : ∀ᶠ n : ℕ in atTop, K ≤ ((n + 1 : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_ge_atTop K)
  filter_upwards [hKn, criticalWindowCoarseLog_tendsto.eventually (eventually_ge_atTop 1)]
    with n hn hl
  have hell : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := by linarith
  have hs : ∀ s ∈ Finset.range (n + 1), criticalWindowCoarseSeriesTerm c C n s ≤
      Real.exp (D * (Real.log ((n + 1 : ℕ) : ℝ))^2 +
        C * Real.log ((n + 1 : ℕ) : ℝ)) := by
    intro s _
    apply Real.exp_le_exp.mpr
    have h := criticalWindowCoarseExponent_le (x := (s : ℝ))
      (ell := Real.log ((n + 1 : ℕ) : ℝ)) (C := C) hc
    dsimp [D] at *
    nlinarith [sq_nonneg (s : ℝ)]
  have hbound := criticalWindowCoarseWeightedSum_le_exp (r := r) hK.le hn
    (by simp : (Finset.range (n + 1)).card ≤ n + 1) hs
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  have hsquare : Real.log ((n + 1 : ℕ) : ℝ) ≤
      (Real.log ((n + 1 : ℕ) : ℝ))^2 := by nlinarith
  dsimp [B]
  nlinarith [mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ C + (r : ℝ) + 2 by positivity)]

/-- A sufficiently distant logarithmic tail decays even after any fixed
polynomial prefactor. -/
theorem exists_eventually_criticalWindowCoarseTail_le
    {c C K : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ) (hK : 0 < K) :
    ∃ L : ℝ, 0 < L ∧ ∀ᶠ n : ℕ in atTop,
      criticalWindowCoarseTail c C r K L n ≤
        Real.exp (-c * (Real.log ((n + 1 : ℕ) : ℝ))^2) := by
  let D := (C + 1)^2 / (8 * c)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let A := D + C + (r : ℝ) + 2 + c
  have hA : 0 < A := by dsimp [A]; positivity
  let L := A / c + 1
  have hLone : 1 ≤ L := by
    dsimp [L]
    linarith [div_nonneg hA.le hc.le]
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hLone
  have hLc : c * L = A + c := by dsimp [L]; field_simp
  have hLsq : A ≤ c * L^2 := by
    have h := mul_le_mul_of_nonneg_left
      (show L ≤ L^2 by nlinarith) hc.le
    nlinarith
  refine ⟨L, hL, ?_⟩
  have hKn : ∀ᶠ n : ℕ in atTop, K ≤ ((n + 1 : ℕ) : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_ge_atTop K)
  filter_upwards [hKn, criticalWindowCoarseLog_tendsto.eventually (eventually_ge_atTop 1)]
    with n hn hl
  let ell := Real.log ((n + 1 : ℕ) : ℝ)
  have hell : 0 ≤ ell := by dsimp [ell]; linarith
  have hellsq : ell ≤ ell^2 := by dsimp [ell]; nlinarith
  let S := (Finset.range (n + 1)).filter
    (fun s : ℕ ↦ L * ell ≤ (s : ℝ))
  have hs : ∀ s ∈ S, criticalWindowCoarseSeriesTerm c C n s ≤
      Real.exp ((-2 * c * L^2 + D) * ell^2 + C * ell) := by
    intro s hs
    have htail : L * ell ≤ (s : ℝ) := (Finset.mem_filter.mp hs).2
    have hsquare : (L * ell)^2 ≤ (s : ℝ)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr htail)
        (show 0 ≤ (s : ℝ) + L * ell by positivity)]
    apply Real.exp_le_exp.mpr
    have h := criticalWindowCoarseExponent_le (x := (s : ℝ))
      (ell := ell) (C := C) hc
    change -4 * c * (s : ℝ)^2 + (C + 1) * s * ell + C * ell ≤ _
    change -4 * c * (s : ℝ)^2 + (C + 1) * s * ell + C * ell ≤
      -2 * c * (s : ℝ)^2 + D * ell^2 + C * ell at h
    nlinarith [mul_le_mul_of_nonneg_left hsquare (show 0 ≤ 2 * c by positivity)]
  have hcard : S.card ≤ n + 1 := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hbound := criticalWindowCoarseWeightedSum_le_exp (r := r) hK.le hn hcard hs
  refine hbound.trans (Real.exp_le_exp.mpr ?_)
  change (-2 * c * L^2 + D) * ell^2 + C * ell +
    ((r : ℝ) + 2) * ell ≤ -c * ell^2
  have hpoly := mul_le_mul_of_nonneg_left hellsq
    (show 0 ≤ C + (r : ℝ) + 2 by positivity)
  have hgap : -2 * c * L^2 + D + C + (r : ℝ) + 2 ≤ -c := by
    dsimp [A] at hLsq
    nlinarith [sq_nonneg L]
  have hgapMul := mul_le_mul_of_nonneg_right hgap (sq_nonneg ell)
  nlinarith

theorem criticalWindowCoarseGaussian_tendsto_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦
      Real.exp (-c * (Real.log ((n + 1 : ℕ) : ℝ))^2)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun n : ℕ ↦
      (Real.log ((n + 1 : ℕ) : ℝ))^2) atTop atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp criticalWindowCoarseLog_tendsto
  exact Real.tendsto_exp_atBot.comp
    (hsq.const_mul_atTop_of_neg (neg_neg_of_pos hc))

/-- The polynomially weighted logarithmic tail tends to zero. -/
theorem exists_criticalWindowCoarseTail_tendsto_zero
    {c C K : ℝ} (hc : 0 < c) (hC : 0 < C) (r : ℕ) (hK : 0 < K) :
    ∃ L : ℝ, 0 < L ∧
      Tendsto (criticalWindowCoarseTail c C r K L) atTop (𝓝 0) := by
  obtain ⟨L, hL, hbound⟩ := exists_eventually_criticalWindowCoarseTail_le hc hC r hK
  refine ⟨L, hL, squeeze_zero' ?_ hbound (criticalWindowCoarseGaussian_tendsto_zero hc)⟩
  exact Eventually.of_forall fun n ↦ by
    dsimp [criticalWindowCoarseTail, criticalWindowCoarseSeriesTerm]
    positivity

end InducedStars
