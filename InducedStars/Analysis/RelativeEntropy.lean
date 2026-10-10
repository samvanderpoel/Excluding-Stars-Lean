import InducedStars.Analysis.Entropy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Scalar binary relative entropy

This file develops the base-two Bernoulli relative entropy used in the
conditioned graphon variational problem.  Its endpoint convention agrees
with the project's totalized logarithm because each singular logarithm is
multiplied by a zero coefficient.
-/

namespace InducedStars

open Set

/-- Binary relative entropy in bits.  This is the paper's scalar integrand
from `eqn:rel-ent-dfn`. -/
noncomputable def binaryRelativeEntropy (p x : ℝ) : ℝ :=
  x * log2 (x / p) +
    (1 - x) * log2 ((1 - x) / (1 - p))

/-- Relative entropy at the all-zero endpoint. -/
@[simp] theorem binaryRelativeEntropy_zero {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    binaryRelativeEntropy p 0 = -log2 (1 - p) := by
  have hpOne : 1 - p ≠ 0 := sub_ne_zero.mpr hp.2.ne'
  rw [binaryRelativeEntropy]
  simp only [zero_div, log2_zero, zero_mul, sub_zero, one_mul, zero_add]
  rw [log2_div one_ne_zero hpOne, log2_one]
  ring

/-- The inverse spelling of relative entropy at the all-zero endpoint. -/
theorem binaryRelativeEntropy_zero_eq_log2_inv {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    binaryRelativeEntropy p 0 = log2 (1 / (1 - p)) := by
  rw [binaryRelativeEntropy_zero hp, one_div, log2_inv]

/-- Relative entropy at the all-one endpoint. -/
@[simp] theorem binaryRelativeEntropy_one {p : ℝ}
    (_hp : p ∈ Ioo (0 : ℝ) 1) :
    binaryRelativeEntropy p 1 = -log2 p := by
  rw [binaryRelativeEntropy]
  simp only [one_div, one_mul, sub_self, zero_div, log2_zero, zero_mul, add_zero]
  rw [log2_inv]

/-- The inverse spelling of relative entropy at the all-one endpoint. -/
theorem binaryRelativeEntropy_one_eq_log2_inv {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    binaryRelativeEntropy p 1 = log2 (1 / p) := by
  rw [binaryRelativeEntropy_one hp, one_div, log2_inv]

/-- Exact base-two entropy decomposition of Bernoulli relative entropy.
The endpoint cases are handled separately so no logarithm law is applied
with a zero numerator. -/
theorem binaryRelativeEntropy_eq_negEntropy_add {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    binaryRelativeEntropy p x =
      -binaryEntropy x + x * log2 ((1 - p) / p) - log2 (1 - p) := by
  rcases eq_or_ne x 0 with rfl | hxZero
  · simp [binaryRelativeEntropy_zero hp]
  rcases eq_or_ne x 1 with rfl | hxOne
  · rw [binaryRelativeEntropy_one hp, binaryEntropy_one,
      log2_div (sub_ne_zero.mpr hp.2.ne') hp.1.ne']
    ring
  have hxOneSub : 1 - x ≠ 0 := sub_ne_zero.mpr hxOne.symm
  have hpOneSub : 1 - p ≠ 0 := sub_ne_zero.mpr hp.2.ne'
  rw [binaryRelativeEntropy, binaryEntropy_eq_formula,
    log2_div hxZero hp.1.ne', log2_div hxOneSub hpOneSub,
    log2_div hpOneSub hp.1.ne']
  ring

/-- A tangent-line form of binary relative entropy.  It makes the Gibbs
inequality a direct consequence of strict concavity of binary entropy. -/
theorem binaryRelativeEntropy_eq_entropy_tangent {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    binaryRelativeEntropy p x =
      binaryEntropy p - binaryEntropy x +
        (x - p) * log2 ((1 - p) / p) := by
  rw [binaryRelativeEntropy_eq_negEntropy_add hp hx]
  calc
    -binaryEntropy x + x * log2 ((1 - p) / p) - log2 (1 - p) =
        -binaryEntropy x + x * log2 ((1 - p) / p) +
          (-log2 (1 - p)) := by ring
    _ = -binaryEntropy x + x * log2 ((1 - p) / p) +
          (binaryEntropy p - p * log2 ((1 - p) / p)) := by
      rw [binaryEntropy_sub_mul_log2_div hp.1.ne' hp.2.ne]
    _ = binaryEntropy p - binaryEntropy x +
          (x - p) * log2 ((1 - p) / p) := by ring

/-- For fixed interior `p`, binary relative entropy is continuous on the
closed probability interval, including both totalized-log endpoints. -/
theorem binaryRelativeEntropy_continuousOn {p : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (binaryRelativeEntropy p) (Icc (0 : ℝ) 1) := by
  have hcontinuous : Continuous
      (fun x : ℝ ↦
        -binaryEntropy x + x * log2 ((1 - p) / p) - log2 (1 - p)) :=
    (binaryEntropy_continuous.neg.add
      (continuous_id.mul continuous_const)).sub continuous_const
  exact hcontinuous.continuousOn.congr fun x hx ↦
    binaryRelativeEntropy_eq_negEntropy_add hp hx

/-- Binary relative entropy is strictly positive away from its reference
probability. -/
theorem binaryRelativeEntropy_pos_of_ne {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1)
    (hxp : x ≠ p) :
    0 < binaryRelativeEntropy p x := by
  rw [binaryRelativeEntropy_eq_entropy_tangent hp hx]
  rcases lt_or_gt_of_ne hxp with hlt | hgt
  · have hslope := binaryEntropy_strictConcaveOn.deriv_lt_slope
      hx ⟨hp.1.le, hp.2.le⟩ hlt
      (binaryEntropy_differentiableAt hp.1 hp.2)
    rw [deriv_binaryEntropy hp.1 hp.2, slope_def_field] at hslope
    have hmul := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hslope
    nlinarith
  · have hslope := binaryEntropy_strictConcaveOn.slope_lt_deriv
      ⟨hp.1.le, hp.2.le⟩ hx hgt
      (binaryEntropy_differentiableAt hp.1 hp.2)
    rw [deriv_binaryEntropy hp.1 hp.2, slope_def_field] at hslope
    have hmul := (div_lt_iff₀ (sub_pos.mpr hgt)).mp hslope
    nlinarith

/-- Gibbs' inequality for the project's base-two Bernoulli relative
entropy. -/
theorem binaryRelativeEntropy_nonneg {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ binaryRelativeEntropy p x := by
  by_cases hxp : x = p
  · subst x
    rw [binaryRelativeEntropy_eq_entropy_tangent hp ⟨hp.1.le, hp.2.le⟩]
    norm_num
  · exact (binaryRelativeEntropy_pos_of_ne hp hx hxp).le

/-- Binary relative entropy vanishes exactly at its reference probability. -/
theorem binaryRelativeEntropy_eq_zero_iff {p x : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    binaryRelativeEntropy p x = 0 ↔ x = p := by
  constructor
  · intro hzero
    by_contra hxp
    exact (binaryRelativeEntropy_pos_of_ne hp hx hxp).ne' hzero
  · rintro rfl
    rw [binaryRelativeEntropy_eq_entropy_tangent hp ⟨hp.1.le, hp.2.le⟩]
    ring

end InducedStars
