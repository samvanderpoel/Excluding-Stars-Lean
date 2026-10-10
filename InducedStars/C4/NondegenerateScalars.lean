import InducedStars.C4.ScalarAnalytic
import InducedStars.Asymptotics.SampledEdgeCount
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Uniform feasibility near a nondegenerate split partition

Paper: Remark `rem:c4-nondeg-bounds`, equation `eqn:c4-p-bounded`.
The finite formulas retain the exact clique-edge rounding term, signed
defects, and up to `n` deleted coordinates or forced successes.
-/

namespace InducedStars

open Filter Set
open scoped Topology

private lemma exists_c4SamplingPerturbationWindow {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ∃ δ > 0, ∃ β > 0, β < 1 / 2 ∧
      ∀ d x a b c : ℝ,
        |d - γ| < δ → |x - c4Lambda γ| < δ →
        |a| < δ → |b| < δ → |c| < δ →
        β < x ∧ β < 1 - x ∧ 0 < x * (1 - x) - b ∧
          (d / 2 - x ^ 2 / 2 + x * c / 2 - a) / (x * (1 - x) - b) ∈
            Ioo β (1 - β) := by
  have hx := c4Lambda_mem_Ioo hγ
  have hq := c4OptimalCrossDensity_mem_Ioo hγ
  obtain ⟨β, hβ, hβmin⟩ := exists_between
    (lt_min (lt_min hx.1 (sub_pos.mpr hx.2)) (lt_min hq.1 (sub_pos.mpr hq.2)))
  have hβx := hβmin.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hβx' := hβmin.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hβq := hβmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hβq' := hβmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hβhalf : β < 1 / 2 := by linarith
  let v : Fin 5 → ℝ := ![γ, c4Lambda γ, 0, 0, 0]
  let D : (Fin 5 → ℝ) → ℝ := fun y => y 1 * (1 - y 1) - y 3
  let F : (Fin 5 → ℝ) → ℝ := fun y =>
    (y 0 / 2 - y 1 ^ 2 / 2 + y 1 * y 4 / 2 - y 2) / D y
  have hDv : 0 < D v := by
    simpa [D, v] using mul_pos hx.1 (sub_pos.mpr hx.2)
  have hFv : F v = c4OptimalCrossDensity γ := by
    dsimp [F, D, v, c4OptimalCrossDensity, c4SplitCrossDensity]
    field_simp [hx.1.ne', sub_ne_zero.mpr hx.2.ne']
    ring
  have hDc : ContinuousAt D v := by dsimp [D]; fun_prop
  have hFc : ContinuousAt F v := by
    change ContinuousAt (fun y =>
      (y 0 / 2 - y 1 ^ 2 / 2 + y 1 * y 4 / 2 - y 2) / D y) v
    exact ContinuousAt.div (by fun_prop) hDc hDv.ne'
  have hxevent : ∀ᶠ y : Fin 5 → ℝ in 𝓝 v, β < y 1 :=
    (continuous_apply 1).continuousAt.eventually (lt_mem_nhds hβx)
  have hxevent' : ∀ᶠ y : Fin 5 → ℝ in 𝓝 v, β < 1 - y 1 :=
    (continuousAt_const.sub (continuous_apply 1).continuousAt).eventually (lt_mem_nhds hβx')
  have hDevent : ∀ᶠ y in 𝓝 v, 0 < D y := hDc.eventually (lt_mem_nhds hDv)
  have hFevent : ∀ᶠ y in 𝓝 v, F y ∈ Ioo β (1 - β) :=
    hFc.eventually (isOpen_Ioo.mem_nhds (by rw [hFv]; exact ⟨hβq, by linarith⟩))
  have hall : ∀ᶠ y in 𝓝 v,
      β < y 1 ∧ β < 1 - y 1 ∧ 0 < D y ∧ F y ∈ Ioo β (1 - β) := by
    filter_upwards [hxevent, hxevent', hDevent, hFevent] with y h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨δ, hδ, hwindow⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, β, hβ, hβhalf, ?_⟩
  intro d x a b c hd hx ha hb hc
  have hv : dist (![d, x, a, b, c] : Fin 5 → ℝ) v < δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro i
    fin_cases i <;> simpa [v, Real.dist_eq] using (by assumption)
  exact hwindow hv

private lemma eventually_c4SamplingBand_of_real_shift {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ∃ ζ > 0, ∃ ε > 0, ∃ β > 0, β < 1 / 2 ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m γ →
      ∀ᶠ n in atTop, 0 < n ∧
        ∀ b : ℕ, b ≤ n → |(b : ℝ) / n - c4Lambda γ| ≤ ζ →
        ∀ u : ℝ, |u| ≤ ε * (n : ℝ) ^ 2 + 2 * n →
        ∀ z : ℕ, z ≤ n →
          β * n < (b : ℝ) ∧ β * n < ((n - b : ℕ) : ℝ) ∧
          0 < ((b * (n - b) : ℕ) : ℝ) - z ∧
          ((m n : ℝ) - (b.choose 2 : ℝ) - u) /
              (((b * (n - b) : ℕ) : ℝ) - z) ∈ Ioo β (1 - β) := by
  obtain ⟨δ, hδ, β, hβ, hβhalf, hwindow⟩ := exists_c4SamplingPerturbationWindow hγ
  refine ⟨δ / 2, by positivity, δ / 8, by positivity, β, hβ, hβhalf, ?_⟩
  intro m hm
  have hmclose : ∀ᶠ n in atTop, |2 * (m n : ℝ) / (n : ℝ) ^ 2 - γ| < δ := by
    simpa only [Real.dist_eq] using
      (hasAsymptoticEdgeDensity_orderedSquare hm).eventually (Metric.ball_mem_nhds γ hδ)
  have hinv : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ / 8 :=
    tendsto_one_div_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hmclose, hinv, eventually_ge_atTop 1] with n hmn hin hn
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnN : (n : ℝ) ≠ 0 := hnR.ne'
  have hnSq : (0 : ℝ) < (n : ℝ) ^ 2 := sq_pos_of_pos hnR
  refine ⟨hn0, ?_⟩
  intro b hb hbclose u hu z hz
  have hxclose : |(b : ℝ) / n - c4Lambda γ| < δ := by linarith
  have huclose : |u / (n : ℝ) ^ 2| < δ := by
    rw [abs_div, abs_of_pos hnSq]
    apply (div_lt_iff₀ hnSq).mpr
    have hin' := (div_lt_iff₀ hnR).mp hin
    have hin'' := mul_lt_mul_of_pos_right hin' hnR
    nlinarith
  have hzR : (z : ℝ) ≤ n := by exact_mod_cast hz
  have hzclose : |(z : ℝ) / (n : ℝ) ^ 2| < δ := by
    rw [abs_of_nonneg (by positivity)]
    have hzn : (z : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) := by
      apply (div_le_iff₀ hnSq).mpr
      field_simp
      nlinarith
    exact hzn.trans_lt (hin.trans (by linarith))
  have hinclose : |(1 : ℝ) / n| < δ := by
    rw [abs_of_pos (by positivity)]
    linarith
  obtain ⟨hbside, haside, hden, hratio⟩ := hwindow
    (2 * (m n : ℝ) / (n : ℝ) ^ 2) ((b : ℝ) / n)
    (u / (n : ℝ) ^ 2) ((z : ℝ) / (n : ℝ) ^ 2) (1 / (n : ℝ))
    hmn hxclose huclose hzclose hinclose
  have hdenEq : (b : ℝ) / n * (1 - (b : ℝ) / n) - (z : ℝ) / (n : ℝ) ^ 2 =
      (((b * (n - b) : ℕ) : ℝ) - z) / (n : ℝ) ^ 2 := by
    rw [Nat.cast_mul, Nat.cast_sub hb]
    field_simp
  have hnumEq : (2 * (m n : ℝ) / (n : ℝ) ^ 2) / 2 - ((b : ℝ) / n) ^ 2 / 2 +
      (b : ℝ) / n * (1 / (n : ℝ)) / 2 - u / (n : ℝ) ^ 2 =
      ((m n : ℝ) - (b.choose 2 : ℝ) - u) / (n : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    field_simp
    ring
  have hdenPos : 0 < ((b * (n - b) : ℕ) : ℝ) - z := by
    rw [hdenEq] at hden
    exact (div_pos_iff.mp hden).resolve_right (by simp [hnSq.not_gt]) |>.1
  refine ⟨(lt_div_iff₀ hnR).mp hbside, ?_, hdenPos, ?_⟩
  · rw [Nat.cast_sub hb]
    have h := (mul_lt_mul_of_pos_right haside hnR)
    field_simp at h
    nlinarith
  · rw [hnumEq, hdenEq, div_div_div_cancel_right₀ hnSq.ne'] at hratio
    exact hratio

/-- Explicit finite feasibility and compact sampling bands. -/
structure C4NondegenerateSamplingBounds (n m b z : ℕ) (t : ℤ) (β : ℝ) : Prop where
  clique_size : β * n < (b : ℝ)
  independent_size : β * n < ((n - b : ℕ) : ℝ)
  capacity_pos : 0 < ((b * (n - b) : ℕ) : ℝ) - z
  selected_pos : 0 < (m : ℝ) - (b.choose 2 : ℝ) - t
  selected_lt_capacity : (m : ℝ) - (b.choose 2 : ℝ) - t < ((b * (n - b) : ℕ) : ℝ) - z
  forced_selected_pos : 0 < (m : ℝ) - (b.choose 2 : ℝ) - t - z
  forced_selected_lt_capacity :
    (m : ℝ) - (b.choose 2 : ℝ) - t - z < ((b * (n - b) : ℕ) : ℝ) - z
  ratio_mem : ((m : ℝ) - (b.choose 2 : ℝ) - t) /
    (((b * (n - b) : ℕ) : ℝ) - z) ∈ Icc β (1 - β)
  forced_ratio_mem : ((m : ℝ) - (b.choose 2 : ℝ) - t - z) /
    (((b * (n - b) : ℕ) : ℝ) - z) ∈ Icc β (1 - β)

/-- Paper: Remark `rem:c4-nondeg-bounds`, equation `eqn:c4-p-bounded`.
The constants precede the choice of the density sequence and thus depend
only on `γ`.  Feasibility is part of the conclusion, including after
deleting coordinates and forcing their successes. -/
theorem exists_c4NondegenerateSamplingBand {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ∃ ζ > 0, ∃ ε > 0, ∃ β > 0, β < 1 / 2 ∧
      ∀ m : ℕ → ℕ, HasAsymptoticEdgeDensity m γ →
      ∀ᶠ n in atTop, 0 < n ∧
        ∀ b : ℕ, b ≤ n → |(b : ℝ) / n - c4Lambda γ| ≤ ζ →
        ∀ t : ℤ, |(t : ℝ)| ≤ ε * (n : ℝ) ^ 2 + n →
        ∀ z : ℕ, z ≤ n → C4NondegenerateSamplingBounds n (m n) b z t β := by
  obtain ⟨ζ, hζ, ε, hε, β, hβ, hβhalf, hband⟩ := eventually_c4SamplingBand_of_real_shift hγ
  refine ⟨ζ, hζ, ε, hε, β, hβ, hβhalf, ?_⟩
  intro m hm
  filter_upwards [hband m hm] with n hn
  refine ⟨hn.1, ?_⟩
  intro b hb hbc t ht z hz
  have ht' : |(t : ℝ)| ≤ ε * (n : ℝ) ^ 2 + 2 * n := by
    linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have htz : |(t : ℝ) + z| ≤ ε * (n : ℝ) ^ 2 + 2 * n := by
    have hzR : (z : ℝ) ≤ n := by exact_mod_cast hz
    calc
      |(t : ℝ) + z| ≤ |(t : ℝ)| + |(z : ℝ)| := abs_add_le _ _
      _ ≤ ε * (n : ℝ) ^ 2 + 2 * n := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ z from Nat.cast_nonneg z)]
        linarith
  obtain ⟨hcl, hin, hcap, hrat⟩ := hn.2 b hb hbc t ht' z hz
  have hforced := (hn.2 b hb hbc ((t : ℝ) + z) htz z hz).2.2.2
  have hforced' : ((m n : ℝ) - (b.choose 2 : ℝ) - t - z) /
      (((b * (n - b) : ℕ) : ℝ) - z) ∈ Ioo β (1 - β) := by
    simpa only [sub_add_eq_sub_sub] using hforced
  have hfeas (a : ℝ) (ha : a / (((b * (n - b) : ℕ) : ℝ) - z) ∈ Ioo β (1 - β)) :
      0 < a ∧ a < ((b * (n - b) : ℕ) : ℝ) - z := by
    have hlo := (lt_div_iff₀ hcap).mp (hβ.trans ha.1)
    have hhi := (div_lt_iff₀ hcap).mp (ha.2.trans (show 1 - β < 1 by linarith))
    constructor <;> linarith
  exact ⟨hcl, hin, hcap, (hfeas _ hrat).1, (hfeas _ hrat).2,
    (hfeas _ hforced').1, (hfeas _ hforced').2,
    ⟨hrat.1.le, hrat.2.le⟩, ⟨hforced'.1.le, hforced'.2.le⟩⟩

end InducedStars
