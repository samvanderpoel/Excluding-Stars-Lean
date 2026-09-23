import DenseGraph.Analysis
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform entropy gain from quadratic capacity growth

Binary entropy is measured in bits.  The capacity increment creates a quadratic
gain, uniformly over a compact initial density band, while changing the forced
edge count by a linear amount has only a linear entropy cost.
-/

open Set

namespace DenseGraph

/-- The scale derivative of the binary-entropy perspective. -/
theorem hasDerivAt_entropyPerspective_scale {a x : ℝ}
    (hx : 0 < x) (ha : 0 < a) (hax : a < x) :
    HasDerivAt (entropyPerspective a) (-log2 (1 - a / x)) x := by
  have hq0 : 0 < a / x := div_pos ha hx
  have hq1 : a / x < 1 := (div_lt_one hx).2 hax
  have hratio : HasDerivAt (fun y : ℝ => a / y) (-(a / x ^ 2)) x := by
    convert! (hasDerivAt_const x a).fun_div (hasDerivAt_id x) hx.ne' using 1 <;>
      first | rfl | simp only [id_eq, zero_mul, mul_one, zero_sub, neg_div]
  have hd := (hasDerivAt_id x).mul
    ((hasDerivAt_binaryEntropy hq0 hq1).comp x hratio)
  have he : binaryEntropy (a / x) +
      x * (log2 ((1 - a / x) / (a / x)) * (-(a / x ^ 2))) =
      -log2 (1 - a / x) := by
    calc
      _ = binaryEntropy (a / x) -
          (a / x) * log2 ((1 - a / x) / (a / x)) := by field_simp; ring
      _ = _ := binaryEntropy_sub_mul_log2_div hq0.ne' (ne_of_lt hq1)
  convert! hd.congr_deriv (by simpa only [one_mul, Function.comp_apply, id_eq] using he)
    using 1

/-- Binary entropy is uniformly Lipschitz on every closed interior density band. -/
theorem binaryEntropy_exists_lipschitz_on_band {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Icc (alpha / 2) (1 - alpha / 2),
      ∀ y ∈ Icc (alpha / 2) (1 - alpha / 2),
        |binaryEntropy y - binaryEntropy x| ≤ L * |y - x| := by
  have hc : ContinuousOn (fun x : ℝ => |log2 ((1 - x) / x)|)
      (Icc (alpha / 2) (1 - alpha / 2)) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have hx1 : x < 1 := by linarith [hx.2]
    have hd : ContinuousAt (fun y : ℝ => (1 - y) / y) x :=
      (continuousAt_const.sub continuousAt_id).div continuousAt_id hx0.ne'
    have hlog : ContinuousAt (fun y : ℝ => Real.log ((1 - y) / y)) x :=
      (Real.continuousAt_log (x := (1 - x) / x)
        (ne_of_gt (div_pos (by linarith) hx0))).comp
          (f := fun y : ℝ => (1 - y) / y) hd
    exact (hlog.div_const (Real.log 2)).abs.continuousWithinAt
  obtain ⟨L, hL⟩ := isCompact_Icc.bddAbove_image hc
  refine ⟨max L 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx y hy
  have hb : ∀ z ∈ Icc (alpha / 2) (1 - alpha / 2),
      ‖deriv binaryEntropy z‖ ≤ max L 1 := by
    intro z hz
    rw [deriv_binaryEntropy (by linarith [hz.1]) (by linarith [hz.2]),
      Real.norm_eq_abs]
    exact (hL (mem_image_of_mem _ hz)).trans (le_max_left _ _)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (alpha / 2) (1 - alpha / 2)).norm_image_sub_le_of_norm_deriv_le
      (fun z hz => binaryEntropy_differentiableAt (by linarith [hz.1])
        (by linarith [hz.2])) hb hx hy

/-- A uniform first-order capacity gain, while density remains at least one
quarter of the input band parameter. -/
theorem entropyPerspective_capacity_gain {alpha a R d : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1 / 2) (hR : 0 < R)
    (hd : 0 ≤ d) (hdR : d ≤ R)
    (hlo : alpha / 2 ≤ a / R) (hhi : a / R ≤ 1 - alpha / 2) :
    (-log2 (1 - alpha / 4)) * d ≤
      entropyPerspective a (R + d) - entropyPerspective a R := by
  have ha0 : 0 < a := by
    have hh : 0 < a / R := by linarith
    exact (div_pos_iff_of_pos_right hR).1 hh
  have haR : a < R := (div_lt_one hR).1 (by linarith)
  have hax : ∀ x ∈ Icc R (R + d), 0 < x ∧ a < x := by
    intro x hx
    exact ⟨hR.trans_le hx.1, haR.trans_le hx.1⟩
  have hdiff : ∀ x ∈ Icc R (R + d),
      HasDerivAt (entropyPerspective a) (-log2 (1 - a / x)) x := by
    intro x hx
    exact hasDerivAt_entropyPerspective_scale (hax x hx).1 ha0 (hax x hx).2
  have hmvt := (convex_Icc R (R + d)).mul_sub_le_image_sub_of_le_deriv
    (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hdiff x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    (C := -log2 (1 - alpha / 4))
  suffices hderiv : ∀ x ∈ interior (Icc R (R + d)),
      -log2 (1 - alpha / 4) ≤ deriv (entropyPerspective a) x by
    simpa only [add_sub_cancel_left] using
      hmvt hderiv R ⟨le_rfl, by linarith⟩ (R + d) ⟨by linarith, le_rfl⟩ (by linarith)
  intro x hx
  have hxI := interior_subset hx
  rw [(hdiff x hxI).deriv]
  have hxpos := (hax x hxI).1
  have hqx : alpha / 4 ≤ a / x := by
    apply (le_div_iff₀ hxpos).2
    have hamin : alpha / 2 * R ≤ a := (le_div_iff₀ hR).1 hlo
    nlinarith [hxI.2, mul_nonneg ha.le (sub_nonneg.mpr hdR)]
  have hq1 : a / x < 1 := (div_lt_one hxpos).2 (hax x hxI).2
  apply neg_le_neg
  unfold log2
  exact div_le_div_of_nonneg_right
    (Real.log_le_log (by linarith) (by linarith)) realLogTwo_pos.le

/-- Uniform entropy boost under a quadratic capacity increment and a linear
change in the forced count.  The constants depend only on the initial density
band, not on the target count or either capacity.

This is the scalar statement used in paper Lemma `lemma:entropy-BOOST`, with
the target count left arbitrary rather than fixed to a graph edge density. -/
theorem entropy_quadratic_boost {alpha : ℝ}
    (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n → ∀ R B Dr Db target : ℝ,
        alpha ≤ (target - B) / R → (target - B) / R ≤ 1 - alpha →
        alpha * (n : ℝ) ^ 2 ≤ R → alpha * (n : ℝ) ^ 2 ≤ Dr →
        |Db| ≤ (n : ℝ) →
        0 < R ∧ 0 < R + Dr ∧
        0 < (target - (B + Db)) / (R + Dr) ∧
        (target - (B + Db)) / (R + Dr) < 1 ∧
        R * binaryEntropy ((target - B) / R) + delta * (n : ℝ) ^ 2 ≤
          (R + Dr) * binaryEntropy ((target - (B + Db)) / (R + Dr)) := by
  obtain ⟨L, hL, hLip⟩ := binaryEntropy_exists_lipschitz_on_band ha ha1
  let c : ℝ := -log2 (1 - alpha / 4)
  have hc : 0 < c := by
    dsimp [c, log2]
    exact neg_pos.mpr (div_neg_of_neg_of_pos
      (Real.log_neg (by linarith) (by linarith)) realLogTwo_pos)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt
    (max (max (1 : ℝ) (2 / alpha ^ 2)) (2 * L / (c * alpha)))
  refine ⟨c * alpha / 2, by positivity, n₀, ?_⟩
  intro n hn R B Dr Db target hlo hhi hR hDr hDb
  have hnlarge : max (max (1 : ℝ) (2 / alpha ^ 2))
      (2 * L / (c * alpha)) < (n : ℝ) :=
    hn₀.trans_le (by exact_mod_cast hn)
  have hn1 : 1 < (n : ℝ) :=
    (le_max_left _ _).trans (le_max_left _ _) |>.trans_lt hnlarge
  have hnpos : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hnsmall : 2 / alpha ^ 2 < (n : ℝ) :=
    (le_max_right _ _).trans (le_max_left _ _) |>.trans_lt hnlarge
  have hnerror : 2 * L / (c * alpha) < (n : ℝ) :=
    (le_max_right _ _).trans_lt hnlarge
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hDrpos : 0 < Dr := lt_of_lt_of_le (by positivity) hDr
  have hDbsmall : |Db| ≤ alpha / 2 * R := by
    have h2 : 2 ≤ (n : ℝ) * alpha ^ 2 :=
      ((div_lt_iff₀ (sq_pos_of_pos ha)).1 hnsmall).le
    have hh := mul_le_mul_of_nonneg_right h2 hnpos.le
    have hhR := mul_le_mul_of_nonneg_left hR (show 0 ≤ alpha / 2 by positivity)
    nlinarith
  have hdbbounds := abs_le.mp hDbsmall
  let a : ℝ := target - (B + Db)
  have haBand : a / R ∈ Icc (alpha / 2) (1 - alpha / 2) := by
    dsimp [a]
    constructor
    · apply (le_div_iff₀ hRpos).2
      have hh := (le_div_iff₀ hRpos).1 hlo
      nlinarith [hdbbounds.2]
    · apply (div_le_iff₀ hRpos).2
      have hh := (div_le_iff₀ hRpos).1 hhi
      nlinarith [hdbbounds.1]
  have ha0 : 0 < a := (div_pos_iff_of_pos_right hRpos).1 (by linarith [haBand.1])
  have haR : a < R := (div_lt_one hRpos).1 (by linarith [haBand.2])
  have hdiff : |a / R - (target - B) / R| = |Db| / R := by
    have he : a / R - (target - B) / R = -Db / R := by dsimp [a]; ring
    rw [he, abs_div, abs_neg, abs_of_pos hRpos]
  have hblue := hLip ((target - B) / R)
    ⟨by linarith, by linarith⟩ (a / R) haBand
  rw [hdiff] at hblue
  have hblue' := mul_le_mul_of_nonneg_left (neg_abs_le
    (binaryEntropy (a / R) - binaryEntropy ((target - B) / R))) hRpos.le
  have hblue'' := mul_le_mul_of_nonneg_left hblue hRpos.le
  have hcancel : R * (L * (|Db| / R)) = L * |Db| := by field_simp
  rw [hcancel] at hblue''
  have hcost : R * binaryEntropy ((target - B) / R) - L * (n : ℝ) ≤
      entropyPerspective a R := by
    dsimp [entropyPerspective]
    nlinarith [mul_le_mul_of_nonneg_left hDb hL.le]
  have hgain := entropyPerspective_capacity_gain ha ha1 hRpos
    (show 0 ≤ alpha * (n : ℝ) ^ 2 by positivity) hR haBand.1 haBand.2
  have hmono := entropyPerspective_mono ha0.le
    (show 0 < R + alpha * (n : ℝ) ^ 2 by positivity)
    (show a ≤ R + alpha * (n : ℝ) ^ 2 by nlinarith [sq_nonneg (n : ℝ)])
    (show R + alpha * (n : ℝ) ^ 2 ≤ R + Dr by linarith)
  have herr : L * (n : ℝ) ≤ c * alpha / 2 * (n : ℝ) ^ 2 := by
    have hh := ((div_lt_iff₀ (mul_pos hc ha)).1 hnerror).le
    nlinarith [mul_le_mul_of_nonneg_right hh hnpos.le]
  refine ⟨hRpos, by positivity, div_pos ha0 (by positivity),
    (div_lt_one (by positivity)).2 (by linarith), ?_⟩
  change R * binaryEntropy ((target - B) / R) +
    c * alpha / 2 * (n : ℝ) ^ 2 ≤ entropyPerspective a (R + Dr)
  dsimp [c] at herr ⊢
  nlinarith

end DenseGraph
