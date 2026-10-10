import DenseGraph.Combinatorics.BinomialEntropy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# A finite binomial Chernoff comparison

The point-mass upper bound and the maximum-at-least-average lower bound at
the mean give the binomial comparison used for large critical remainders.
All logarithms in this module are natural.
-/

noncomputable section
open Set
namespace InducedStars

private theorem log_le_linear_sub_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    Real.log t ≤ t - 1 - (1 - t) ^ 2 / 2 := by
  let f : ℝ → ℝ := fun u ↦ Real.log u - u + 1 + (1 - u) ^ 2 / 2
  have hf : ∀ u ∈ Icc t 1,
      HasDerivAt f (u⁻¹ - 1 - (1 - u)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt (ht.trans_le hu.1)
    convert! (((Real.hasDerivAt_log hu0).sub (hasDerivAt_id u)).add_const 1).add
      ((((hasDerivAt_const u 1).sub (hasDerivAt_id u)).pow 2).div_const 2) using 1
    dsimp [f]
    ring
  have hmono : MonotoneOn f (Icc t 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc t 1)
    · intro u hu
      exact (hf u hu).continuousAt.continuousWithinAt
    · intro u hu
      exact (hf u (interior_subset hu)).differentiableAt.differentiableWithinAt
    · intro u hu
      have hu' : u ∈ Icc t 1 := interior_subset hu
      have hu0 : 0 < u := ht.trans_le hu'.1
      rw [(hf u hu').deriv]
      have hsq := sq_nonneg (1 - u)
      have hid : u * (u⁻¹ - 1 - (1 - u)) = (1 - u) ^ 2 := by
        field_simp
      exact nonneg_of_mul_nonneg_left (by rw [mul_comm, hid]; exact hsq) hu0
  have h := hmono ⟨le_rfl, ht1⟩ ⟨ht1, le_rfl⟩ ht1
  dsimp [f] at h
  norm_num at h
  linarith

/-- The binary relative-entropy estimate behind the upper-tail Chernoff
bound, with the upper endpoint q = 1 included. -/
theorem binEntropy_add_log_weights_le_chernoff
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q ≤ 1) (hpq : p ≤ q) :
    Real.binEntropy q + q * Real.log p + (1 - q) * Real.log (1 - p) ≤
      -(q - p) ^ 2 / (2 * q) := by
  have hratio : 0 < p / q := div_pos hp hq
  have hratio1 : p / q ≤ 1 := (div_le_one hq).2 hpq
  have hlog := mul_le_mul_of_nonneg_left
    (log_le_linear_sub_sq hratio hratio1) hq.le
  have hfirst : q * Real.log (p / q) ≤
      p - q - (q - p) ^ 2 / (2 * q) := by
    calc
      _ ≤ q * (p / q - 1 - (1 - p / q) ^ 2 / 2) := hlog
      _ = _ := by field_simp
  rcases eq_or_lt_of_le hq1 with hqeq | hqlt
  · subst q
    simpa using hfirst.trans (by
      have hpm : p - 1 ≤ 0 := sub_nonpos.mpr hp1.le
      linarith)
  have hqsub : 0 < 1 - q := sub_pos.mpr hqlt
  have hpsub : 0 < 1 - p := sub_pos.mpr hp1
  have hsecond : (1 - q) * Real.log ((1 - p) / (1 - q)) ≤ q - p := by
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hpsub hqsub)) hqsub.le
    calc
      _ ≤ (1 - q) * ((1 - p) / (1 - q) - 1) := h
      _ = _ := by field_simp; ring
  have hsum := add_le_add hfirst hsecond
  rw [Real.log_div hp.ne' hq.ne',
    Real.log_div hpsub.ne' hqsub.ne'] at hsum
  simp only [Real.binEntropy, Real.log_inv]
  calc
    _ = q * (Real.log p - Real.log q) +
        (1 - q) * (Real.log (1 - p) - Real.log (1 - q)) := by ring
    _ ≤ p - q - (q - p) ^ 2 / (2 * q) + (q - p) := hsum
    _ = _ := by ring

/-- An entropy upper bound in the upper tail, in the original binomial
coordinates. -/
theorem binomialEntropyPerspective_le_chernoff
    {A x : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (hxA : x ≤ A) (hmean : p * (A : ℝ) ≤ x) :
    DenseGraph.binomialEntropyPerspective A x ≤
      -(x : ℝ) * Real.log p - ((A : ℝ) - x) * Real.log (1 - p) -
        ((x : ℝ) - p * A) ^ 2 / (2 * x) := by
  have hA : (0 : ℝ) < A := by exact_mod_cast hx.trans_le hxA
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hxAR : (x : ℝ) ≤ A := by exact_mod_cast hxA
  have h := mul_le_mul_of_nonneg_left
    (binEntropy_add_log_weights_le_chernoff hp hp1 (div_pos hxR hA)
      ((div_le_one hA).2 hxAR) ((le_div_iff₀ hA).2 hmean)) hA.le
  have hleft : (A : ℝ) *
      (Real.binEntropy ((x : ℝ) / A) + ((x : ℝ) / A) * Real.log p +
        (1 - (x : ℝ) / A) * Real.log (1 - p)) =
      DenseGraph.binomialEntropyPerspective A x +
        x * Real.log p + ((A : ℝ) - x) * Real.log (1 - p) := by
    unfold DenseGraph.binomialEntropyPerspective
    field_simp
  have hright : (A : ℝ) * (-((x : ℝ) / A - p) ^ 2 / (2 * ((x : ℝ) / A))) =
      -((x : ℝ) - p * A) ^ 2 / (2 * x) := by
    field_simp
  rw [hleft, hright, neg_div] at h
  linarith

/-- Compare an upper-tail binomial coefficient with a binomial coefficient
at its mean. The polynomial factor is the exact finite mode bound. -/
theorem choose_le_choose_mul_chernoff
    {N M A x : ℕ} {p : ℝ} (hN : 0 < N)
    (hp : 0 < p) (hp1 : p < 1) (hNp : (N : ℝ) * p = M)
    (hx : 0 < x) (hxA : x ≤ A) (hmean : p * (A : ℝ) ≤ x) :
    (Nat.choose A x : ℝ) ≤ (Nat.choose N M : ℝ) * ((N : ℝ) + 1) *
      Real.exp (((N : ℝ) - A) * Real.log (1 - p) +
        ((M : ℝ) - x) * Real.log (p / (1 - p)) -
          ((x : ℝ) - p * A) ^ 2 / (2 * x)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : M ≤ N := by
    have hm : (M : ℝ) ≤ N := by nlinarith
    exact_mod_cast hm
  have hquota : (M : ℝ) / N = p := (div_eq_iff hNR.ne').2 (by linarith)
  have hE : DenseGraph.binomialEntropyPerspective N M =
      -(M : ℝ) * Real.log p - ((N : ℝ) - M) * Real.log (1 - p) := by
    simp only [DenseGraph.binomialEntropyPerspective, hquota, Real.binEntropy,
      Real.log_inv]
    rw [← hNp]
    ring
  have hlower := DenseGraph.exp_binomialEntropyPerspective_div_succ_le_choose hMN
  have hscale : Real.exp (DenseGraph.binomialEntropyPerspective N M) ≤
      (Nat.choose N M : ℝ) * ((N : ℝ) + 1) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < ((N + 1 : ℕ) : ℝ))).1 hlower
    simpa only [Nat.cast_add, Nat.cast_one] using h
  have hupper := DenseGraph.choose_le_exp_binomialEntropyPerspective hxA
  have htail := binomialEntropyPerspective_le_chernoff hp hp1 hx hxA hmean
  have hexponent :
      -(x : ℝ) * Real.log p - ((A : ℝ) - x) * Real.log (1 - p) -
        ((x : ℝ) - p * A) ^ 2 / (2 * x) =
      DenseGraph.binomialEntropyPerspective N M +
        (((N : ℝ) - A) * Real.log (1 - p) +
        ((M : ℝ) - x) * Real.log (p / (1 - p)) -
          ((x : ℝ) - p * A) ^ 2 / (2 * x)) := by
    rw [hE, Real.log_div hp.ne' (sub_pos.mpr hp1).ne']
    ring
  calc
    (Nat.choose A x : ℝ) ≤ Real.exp (DenseGraph.binomialEntropyPerspective A x) := hupper
    _ ≤ Real.exp (-(x : ℝ) * Real.log p -
        ((A : ℝ) - x) * Real.log (1 - p) -
          ((x : ℝ) - p * A) ^ 2 / (2 * x)) := Real.exp_le_exp.mpr htail
    _ = Real.exp (DenseGraph.binomialEntropyPerspective N M) *
        Real.exp (((N : ℝ) - A) * Real.log (1 - p) +
          ((M : ℝ) - x) * Real.log (p / (1 - p)) -
            ((x : ℝ) - p * A) ^ 2 / (2 * x)) := by
      rw [hexponent, Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right hscale (Real.exp_pos _).le

end InducedStars
