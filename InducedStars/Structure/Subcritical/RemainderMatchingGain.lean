import InducedStars.Structure.Subcritical.SparseMatchingSwitching
import InducedStars.Structure.Subcritical.RemainderMatchingParameters
import DenseGraph.Combinatorics.LogarithmicGain
import Mathlib.Data.Nat.Choose.Bounds

/-!
# The marked matching gain on each low remainder level

Paper: `lemma:sub-Wstar-sparse-lower-tail-K1k`. The finite switching
is applied to actual induced-free remainders. Its marked inverse factor is
cancelled explicitly, not assumed to be one.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

theorem subcriticalSparseMatchingSwitching_exp_gain
    {k s b q : ℕ} (hk : 3 ≤ k) (hb : b ≤ q) (hs : 4*q ≤ s)
    {E : ℝ} (hgain : (4 : ℝ)^q * Real.exp E ≤
      (DenseGraph.labeledMatchingCoefficient (s-2*q) q : ℝ)) :
    (inducedStarFreeGraphCountWithEdges k s b : ℝ) * Real.exp E ≤
      inducedStarFreeGraphCountWithEdges k s (b+q) := by
  have hchoose : (b+q).choose q ≤ 4^q := by
    calc
      _ ≤ 2^(b+q) := Nat.choose_le_two_pow _ _
      _ ≤ 2^(2*q) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4^q := by rw [pow_mul]; norm_num
  have hswitch :
      (DenseGraph.labeledMatchingCoefficient (s-2*q) q : ℝ) *
        inducedStarFreeGraphCountWithEdges k s b ≤
      ((b+q).choose q : ℝ) * inducedStarFreeGraphCountWithEdges k s (b+q) := by
    exact_mod_cast subcriticalSparseMatchingSwitching hk hb hs
  apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < 4^q by positivity)).mp
  calc
    _ = ((4 : ℝ)^q * Real.exp E) * inducedStarFreeGraphCountWithEdges k s b := by ring
    _ ≤ (DenseGraph.labeledMatchingCoefficient (s-2*q) q : ℝ) *
        inducedStarFreeGraphCountWithEdges k s b :=
      mul_le_mul_of_nonneg_right hgain (by positivity)
    _ ≤ ((b+q).choose q : ℝ) * inducedStarFreeGraphCountWithEdges k s (b+q) := hswitch
    _ ≤ (4 : ℝ)^q * inducedStarFreeGraphCountWithEdges k s (b+q) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)
    _ = _ := by ring

/-- A genuine shifted full-slice denominator consumes the switching gain.
Zero partition functions are allowed throughout. -/
theorem subcriticalLowRemainderTerm_le_of_shifted_denominator
    {k s b q : ℕ} (hk : 3 ≤ k) (hb : b ≤ q) (hs : 4*q ≤ s)
    {E cost Z N : ℝ} (hZ : 0 ≤ Z)
    (hgain : (4 : ℝ)^q * Real.exp E ≤
      (DenseGraph.labeledMatchingCoefficient (s-2*q) q : ℝ))
    (hden : Z * inducedStarFreeGraphCountWithEdges k s (b+q) ≤ N * Real.exp cost) :
    Z * inducedStarFreeGraphCountWithEdges k s b ≤ N * Real.exp (cost-E) := by
  have h := mul_le_mul_of_nonneg_left
    (subcriticalSparseMatchingSwitching_exp_gain hk hb hs hgain) hZ
  have ht : (Z * inducedStarFreeGraphCountWithEdges k s b) * Real.exp E ≤
      N * Real.exp cost := by simpa only [mul_assoc] using h.trans hden
  have hh := mul_le_mul_of_nonneg_right ht (Real.exp_pos (-E)).le
  simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one,
    sub_eq_add_neg] using hh

end InducedStars
