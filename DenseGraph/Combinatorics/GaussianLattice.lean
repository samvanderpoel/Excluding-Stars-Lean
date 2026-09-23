import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Gaussian tails on the natural-number lattice

Elementary summability and moving-cutoff estimates for a polynomially
weighted Gaussian sequence.  This module is independent of graph theory.
-/

noncomputable section

open Filter Finset
open scoped BigOperators Topology

namespace DenseGraph

/-- A polynomially weighted Gaussian term on the natural-number lattice. -/
def gaussianLatticeWeight (r : ℕ) (c : ℝ) (d : ℕ) : ℝ :=
  (((d + 1 : ℕ) : ℝ) ^ r) * Real.exp (-c * (d : ℝ) ^ 2)

theorem gaussianLatticeWeight_nonneg (r : ℕ) (c : ℝ) (d : ℕ) :
    0 ≤ gaussianLatticeWeight r c d := by
  unfold gaussianLatticeWeight
  positivity

/-- A polynomially weighted Gaussian is summable on the natural-number
lattice for every positive Gaussian coefficient. -/
theorem summable_gaussianLatticeWeight
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (gaussianLatticeWeight r c) := by
  have hbase :
      Summable (fun d : ℕ ↦
        (d : ℝ) ^ r * Real.exp (-c * (d : ℝ))) :=
    Real.summable_pow_mul_exp_neg_nat_mul r hc
  have hshift :
      Summable (fun d : ℕ ↦
        (((d + 1 : ℕ) : ℝ) ^ r) *
          Real.exp (-c * (((d + 1 : ℕ) : ℝ)))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2 hbase)
  have hlinear :
      Summable (fun d : ℕ ↦
        (((d + 1 : ℕ) : ℝ) ^ r) * Real.exp (-c * (d : ℝ))) := by
    have h := hshift.mul_left (Real.exp c)
    refine h.congr (fun d ↦ ?_)
    calc
      Real.exp c *
          ((((d + 1 : ℕ) : ℝ) ^ r) *
            Real.exp (-c * (((d + 1 : ℕ) : ℝ)))) =
          (((d + 1 : ℕ) : ℝ) ^ r) *
            (Real.exp c * Real.exp (-c * (((d + 1 : ℕ) : ℝ)))) := by ring
      _ = (((d + 1 : ℕ) : ℝ) ^ r) *
            Real.exp (c + -c * (((d + 1 : ℕ) : ℝ))) := by
          rw [Real.exp_add]
      _ = (((d + 1 : ℕ) : ℝ) ^ r) * Real.exp (-c * (d : ℝ)) := by
          congr 2
          push_cast
          ring
  refine hlinear.of_nonneg_of_le
      (fun d ↦ gaussianLatticeWeight_nonneg r c d) ?_
  intro d
  unfold gaussianLatticeWeight
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  rcases d.eq_zero_or_pos with rfl | hd
  · norm_num
  · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have hsq : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonpos_left hsq (neg_nonpos.mpr hc.le)

/-- The natural-number cutoff corresponding exactly to
`sqrt (log₂ n)`. -/
def sqrtLogTwoCutoff (n : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (Real.logb 2 (n : ℝ)))

theorem tendsto_sqrtLogTwoCutoff_atTop :
    Tendsto sqrtLogTwoCutoff atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    (Real.tendsto_sqrt_atTop.comp
      ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
        tendsto_natCast_atTop_atTop))

/-- The finite Gaussian shell above the coefficient-one
`sqrt (log₂ n)` cutoff.  The strict inequality agrees with the usual
"imbalance greater than the cutoff" convention. -/
def gaussianRangeShellTail (r : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 0 n).filter
      (fun d : ℕ ↦ Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ)),
    gaussianLatticeWeight r c d

/-- The infinite lattice tail beginning at `a`. -/
def gaussianLatticeTail (r : ℕ) (c : ℝ) (a : ℕ) : ℝ :=
  ∑' e : ℕ, gaussianLatticeWeight r c (e + a)

private theorem gaussianRangeShellTail_le_latticeTail
    (r : ℕ) {c : ℝ} (hc : 0 < c) (n : ℕ) :
    gaussianRangeShellTail r c n ≤
      gaussianLatticeTail r c (sqrtLogTwoCutoff n) := by
  let a := sqrtLogTwoCutoff n
  let shell := (Finset.Icc 0 n).filter
    (fun d : ℕ ↦ Real.sqrt (Real.logb 2 (n : ℝ)) < (d : ℝ))
  have hshell : shell ⊆ Finset.Icc a n := by
    intro d hd
    have hd' := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hd'.2.le,
      (Finset.mem_Icc.mp hd'.1).2⟩
  have hfinite :
      ∑ d ∈ Finset.Icc a n, gaussianLatticeWeight r c d ≤
        ∑' e : ℕ, gaussianLatticeWeight r c (a + e) := by
    have hIcc : Finset.Icc a n = Finset.Ico a (n + 1) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Summable.sum_le_tsum (Finset.range (n + 1 - a))
      (fun e _ ↦ gaussianLatticeWeight_nonneg r c (a + e)) ?_
    exact (summable_gaussianLatticeWeight r hc).comp_injective
      (fun _ _ h ↦ Nat.add_left_cancel h)
  calc
    gaussianRangeShellTail r c n =
        ∑ d ∈ shell, gaussianLatticeWeight r c d := by
      rfl
    _ ≤ ∑ d ∈ Finset.Icc a n, gaussianLatticeWeight r c d :=
      Finset.sum_le_sum_of_subset_of_nonneg hshell
        (fun d _ _ ↦ gaussianLatticeWeight_nonneg r c d)
    _ ≤ ∑' e : ℕ, gaussianLatticeWeight r c (a + e) := hfinite
    _ = gaussianLatticeTail r c (sqrtLogTwoCutoff n) := by
      simp only [gaussianLatticeTail, a, Nat.add_comm]

private theorem tendsto_gaussianLatticeTail_zero
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (gaussianLatticeTail r c) atTop (nhds 0) := by
  have _hsum := summable_gaussianLatticeWeight r hc
  change Tendsto
    (fun a ↦ ∑' e : ℕ, gaussianLatticeWeight r c (e + a))
    atTop (nhds 0)
  exact tendsto_sum_nat_add (gaussianLatticeWeight r c)

/-- For every positive Gaussian coefficient and every fixed polynomial
degree, the finite lattice shell above the coefficient-one
`sqrt (log₂ n)` cutoff tends to zero.  In particular, no enlargement of the
square-root cutoff depending on `c` is needed. -/
theorem gaussianRangeShellTail_tendsto_zero
    (r : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (gaussianRangeShellTail r c) atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold gaussianRangeShellTail
    exact Finset.sum_nonneg fun d _ ↦ gaussianLatticeWeight_nonneg r c d
  · filter_upwards with n
    exact gaussianRangeShellTail_le_latticeTail r hc n
  · exact (tendsto_gaussianLatticeTail_zero r hc).comp
      tendsto_sqrtLogTwoCutoff_atTop

end DenseGraph
