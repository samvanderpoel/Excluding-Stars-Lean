import InducedStars.C4.ScalarDerivatives
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The unique split-model optimizer

Compactness and strict concavity prove the scalar assertion in the final
counting argument of `paper/c4-free.tex`.  The quantitative entropy gap is
uniform in the density, and is stated also in the paper's base-two units.
-/

namespace InducedStars

open Filter Set
open scoped Topology

lemma exists_c4SplitEntropyNat_maximizer {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    ∃ x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ),
      IsMaxOn (c4SplitEntropyNat γ)
        (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) x := by
  obtain ⟨hl, hlr, hr⟩ := c4Split_feasible_endpoints hγ
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hlr.le) (continuousOn_c4SplitEntropyNat hγ)
  obtain ⟨y, hyl, hyr⟩ := exists_between hlr
  have hp : 0 < c4SplitEntropyNat γ x :=
    (c4SplitEntropyNat_pos hγ ⟨hyl, hyr⟩).trans_le (hmax ⟨hyl.le, hyr.le⟩)
  have hxl : 1 - Real.sqrt (1 - γ) < x := by
    rcases hx.1.eq_or_lt with h | h
    · rw [← h, c4SplitEntropyNat_lowerEndpoint hγ] at hp
      exact (lt_irrefl _ hp).elim
    · exact h
  have hxr : x < Real.sqrt γ := by
    rcases hx.2.eq_or_lt with h | h
    · rw [h, c4SplitEntropyNat_upperEndpoint hγ] at hp
      exact (lt_irrefl _ hp).elim
    · exact h
  exact ⟨x, ⟨hxl, hxr⟩, hmax⟩

/-- The unique optimizing clique proportion.  Outside the relevant density
range the harmless fallback value is one half. -/
noncomputable def c4Lambda (γ : ℝ) : ℝ :=
  if hγ : γ ∈ Ioo 0 1 then
    Classical.choose (exists_c4SplitEntropyNat_maximizer hγ)
  else 1 / 2

lemma c4Lambda_spec {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4Lambda γ ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ) ∧
      IsMaxOn (c4SplitEntropyNat γ)
        (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) (c4Lambda γ) := by
  simpa only [c4Lambda, dite_eq_left hγ] using
    Classical.choose_spec (exists_c4SplitEntropyNat_maximizer hγ)

lemma c4Lambda_mem_feasibleInterior {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4Lambda γ ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ) :=
  (c4Lambda_spec hγ).1

lemma c4Lambda_mem_Ioo {γ : ℝ} (hγ : γ ∈ Ioo 0 1) : c4Lambda γ ∈ Ioo 0 1 :=
  c4Split_mem_unitInterval hγ
    ⟨(c4Lambda_mem_feasibleInterior hγ).1.le, (c4Lambda_mem_feasibleInterior hγ).2.le⟩

lemma c4SplitCrossDensity_c4Lambda_mem_Ioo {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitCrossDensity γ (c4Lambda γ) ∈ Ioo 0 1 :=
  c4SplitCrossDensity_mem_Ioo hγ (c4Lambda_mem_feasibleInterior hγ)

lemma c4Lambda_isMaxOn {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    IsMaxOn (c4SplitEntropyNat γ)
      (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) (c4Lambda γ) :=
  (c4Lambda_spec hγ).2

lemma c4Lambda_unique {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ))
    (hmax : IsMaxOn (c4SplitEntropyNat γ)
      (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) x) : x = c4Lambda γ := by
  exact (strictConcaveOn_c4SplitEntropyNat hγ).eq_of_isMaxOn hmax (c4Lambda_isMaxOn hγ)
    hx ⟨(c4Lambda_mem_feasibleInterior hγ).1.le, (c4Lambda_mem_feasibleInterior hγ).2.le⟩

lemma c4SplitEntropyNatDerivative_c4Lambda_eq_zero {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    c4SplitEntropyNatDerivative γ (c4Lambda γ) = 0 := by
  have hlocal := (c4Lambda_isMaxOn hγ).isLocalMax
    (Icc_mem_nhds (c4Lambda_mem_feasibleInterior hγ).1 (c4Lambda_mem_feasibleInterior hγ).2)
  exact hlocal.hasDerivAt_eq_zero (hasDerivAt_c4SplitEntropyNat hγ
    (c4Lambda_mem_feasibleInterior hγ))

lemma deriv_c4SplitEntropyNat_c4Lambda_eq_zero {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    deriv (c4SplitEntropyNat γ) (c4Lambda γ) = 0 := by
  rw [deriv_c4SplitEntropyNat hγ (c4Lambda_mem_feasibleInterior hγ),
    c4SplitEntropyNatDerivative_c4Lambda_eq_zero hγ]

/-- Uniform strict curvature: the logarithmic term alone is at most `-log 4`,
and the rational term is strictly negative throughout the feasible interior. -/
lemma c4SplitEntropyNatSecondDerivative_lt_neg_two_log_two {γ x : ℝ}
    (hx : x ∈ Ioo 0 1) (hq : c4SplitCrossDensity γ x ∈ Ioo 0 1) :
    c4SplitEntropyNatSecondDerivative γ x < -(2 * Real.log 2) := by
  have hp : 0 < c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x) :=
    mul_pos hq.1 (sub_pos.mpr hq.2)
  have hp4 : c4SplitCrossDensity γ x * (1 - c4SplitCrossDensity γ x) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (c4SplitCrossDensity γ x - 1 / 2)]
  have hlog := Real.log_le_log hp hp4
  have hlog4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
    rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  rw [hlog4] at hlog
  have ha : 0 < x + c4SplitCrossDensity γ x * (1 - 2 * x) := by
    nlinarith [mul_pos hx.1 (sub_pos.mpr hq.2), mul_pos hq.1 (sub_pos.mpr hx.2)]
  have hd : 0 < x * (1 - x) * c4SplitCrossDensity γ x *
      (1 - c4SplitCrossDensity γ x) :=
    mul_pos (mul_pos (mul_pos hx.1 (sub_pos.mpr hx.2)) hq.1) (sub_pos.mpr hq.2)
  have hquot := div_pos (sq_pos_of_pos ha) hd
  unfold c4SplitEntropyNatSecondDerivative
  linarith

private lemma hasDerivAt_c4SplitQuadraticLift {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) (a : ℝ) :
    HasDerivAt (fun y => c4SplitEntropyNat γ y + Real.log 2 * (y - a) ^ 2)
      (c4SplitEntropyNatDerivative γ x + 2 * Real.log 2 * (x - a)) x := by
  have hd := (hasDerivAt_c4SplitEntropyNat hγ hx).add
    ((((hasDerivAt_id x).sub_const a).pow 2).const_mul (Real.log 2))
  convert hd using 1 <;> try rfl
  dsimp
  ring

private lemma hasDerivAt_deriv_c4SplitQuadraticLift {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Ioo (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) (a : ℝ) :
    HasDerivAt (deriv (fun y => c4SplitEntropyNat γ y + Real.log 2 * (y - a) ^ 2))
      (c4SplitEntropyNatSecondDerivative γ x + 2 * Real.log 2) x := by
  have hd : HasDerivAt (fun y => c4SplitEntropyNatDerivative γ y + 2 * Real.log 2 * (y - a))
      (c4SplitEntropyNatSecondDerivative γ x + 2 * Real.log 2) x := by
    convert (hasDerivAt_c4SplitEntropyNatDerivative hγ hx).add
      (((hasDerivAt_id x).sub_const a).const_mul (2 * Real.log 2))
      using 1 <;> first | rfl | simp
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact (hasDerivAt_c4SplitQuadraticLift hγ hy a).deriv

private lemma strictConcaveOn_c4SplitQuadraticLift {γ : ℝ} (hγ : γ ∈ Ioo 0 1) (a : ℝ) :
    StrictConcaveOn ℝ (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ))
      (fun y => c4SplitEntropyNat γ y + Real.log 2 * (y - a) ^ 2) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
    ((continuousOn_c4SplitEntropyNat hγ).add (by fun_prop))
  intro x hx
  rw [interior_Icc] at hx
  change deriv (deriv (fun y => c4SplitEntropyNat γ y + Real.log 2 * (y - a) ^ 2)) x < 0
  rw [(hasDerivAt_deriv_c4SplitQuadraticLift hγ hx a).deriv]
  have h := c4SplitEntropyNatSecondDerivative_lt_neg_two_log_two
    (c4Split_mem_unitInterval hγ ⟨hx.1.le, hx.2.le⟩) (c4SplitCrossDensity_mem_Ioo hγ hx)
  linarith

/-- A uniform quadratic entropy gap, valid on the entire feasible interval.
The coefficient `log 2` is exactly `log 4 / 2`. -/
lemma c4SplitEntropyNat_quadratic_gap {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    Real.log 2 * (x - c4Lambda γ) ^ 2 ≤
      c4SplitEntropyNat γ (c4Lambda γ) - c4SplitEntropyNat γ x := by
  let f : ℝ → ℝ := fun y => c4SplitEntropyNat γ y + Real.log 2 * (y - c4Lambda γ) ^ 2
  have hc := (strictConcaveOn_c4SplitQuadraticLift hγ (c4Lambda γ)).concaveOn
  have hl := c4Lambda_mem_feasibleInterior hγ
  have hlc : c4Lambda γ ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ) := ⟨hl.1.le, hl.2.le⟩
  have hd : HasDerivAt f 0 (c4Lambda γ) := by
    simpa only [sub_self, mul_zero, add_zero, c4SplitEntropyNatDerivative_c4Lambda_eq_zero hγ]
      using hasDerivAt_c4SplitQuadraticLift hγ hl (c4Lambda γ)
  have hmax : f x ≤ f (c4Lambda γ) := by
    rcases lt_trichotomy (c4Lambda γ) x with h | h | h
    · have hs := hc.slope_le_of_hasDerivAt hlc hx h hd
      rw [slope_def_field] at hs
      have hh := (div_le_iff₀ (sub_pos.mpr h)).mp hs
      linarith
    · exact le_of_eq (congrArg f h.symm)
    · have hs := hc.le_slope_of_hasDerivAt hx hlc h hd
      rw [slope_def_field] at hs
      have hh := (le_div_iff₀ (sub_pos.mpr h)).mp hs
      linarith
  dsimp only [f] at hmax
  simpa only [sub_self, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero, le_sub_iff_add_le,
    add_comm] using hmax

/-- In the paper's base-two normalization, the universal quadratic-gap
coefficient is exactly one. -/
lemma c4SplitEntropy_quadratic_gap {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    (x - c4Lambda γ) ^ 2 ≤ c4SplitEntropy γ (c4Lambda γ) - c4SplitEntropy γ x := by
  rw [c4SplitEntropy_eq_nat_div_log_two, c4SplitEntropy_eq_nat_div_log_two, ← sub_div]
  apply (le_div_iff₀ realLogTwo_pos).mpr
  simpa only [mul_comm] using c4SplitEntropyNat_quadratic_gap hγ hx

lemma c4SplitEntropy_isMaxOn {γ : ℝ} (hγ : γ ∈ Ioo 0 1) :
    IsMaxOn (c4SplitEntropy γ)
      (Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) (c4Lambda γ) := by
  intro x hx
  have hgap := c4SplitEntropy_quadratic_gap hγ hx
  exact sub_nonneg.mp ((sq_nonneg (x - c4Lambda γ)).trans hgap)

lemma c4SplitEntropy_eq_max_iff {γ x : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ)) :
    c4SplitEntropy γ x = c4SplitEntropy γ (c4Lambda γ) ↔ x = c4Lambda γ := by
  constructor
  · intro h
    have hgap := c4SplitEntropy_quadratic_gap hγ hx
    rw [h] at hgap
    nlinarith [sq_nonneg (x - c4Lambda γ)]
  · rintro rfl
    rfl

/-- The nondegeneracy gap at distance at least `ζ` from the optimizer. -/
lemma c4SplitEntropy_gap_of_abs_sub_ge {γ x ζ : ℝ} (hγ : γ ∈ Ioo 0 1)
    (hx : x ∈ Icc (1 - Real.sqrt (1 - γ)) (Real.sqrt γ))
    (hζ : 0 ≤ ζ) (hfar : ζ ≤ |x - c4Lambda γ|) :
    c4SplitEntropy γ x ≤ c4SplitEntropy γ (c4Lambda γ) - ζ ^ 2 := by
  have hsq : ζ ^ 2 ≤ (x - c4Lambda γ) ^ 2 := by
    nlinarith [sq_abs (x - c4Lambda γ), sq_nonneg (|x - c4Lambda γ| - ζ)]
  linarith [c4SplitEntropy_quadratic_gap hγ hx]

end InducedStars
