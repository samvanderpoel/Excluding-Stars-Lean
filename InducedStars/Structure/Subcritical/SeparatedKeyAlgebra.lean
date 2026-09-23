import InducedStars.Structure.Subcritical.ReferenceRemainderGap
import DenseGraph.Combinatorics.MatchingCoefficientGrowth
import InducedStars.Structure.Supercritical.AlmostAllLimits

/-!
# Scalar and finite-sum bookkeeping for separated retained keys

The matching gain absorbs every fixed exponential and polynomial overhead.
The positive rate is chosen from the geometric gap, before the candidate.
-/

noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators
namespace InducedStars

def subcriticalSeparatedComparisonRate (gap : ℝ) : ℝ := gap / 512

theorem subcriticalSeparatedComparisonRate_pos {gap : ℝ} (hg : 0 < gap) :
    0 < subcriticalSeparatedComparisonRate gap := by
  unfold subcriticalSeparatedComparisonRate
  positivity

theorem perfectMatchingCoefficient_pos (q : ℕ) :
    0 < DenseGraph.labeledMatchingCoefficient (2 * q) q :=
  (Nat.factorial_pos q).trans_le (DenseGraph.factorial_le_labeledMatchingCoefficient le_rfl)

theorem sparseLevelCount_le_exp {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n) :
    ((Nat.floor (B * (n : ℝ)^2) + 1 : ℕ) : ℝ) ≤ Real.exp ((B + 3) * n) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hf := Nat.floor_le (show 0 ≤ B * (n : ℝ)^2 by positivity)
  have hbase : B + 1 ≤ Real.exp (B + 1) := by linarith [Real.add_one_le_exp (B + 1)]
  have horder : (n : ℝ) ≤ Real.exp n := by linarith [Real.add_one_le_exp (n : ℝ)]
  calc
    _ ≤ (B + 1) * (n : ℝ)^2 := by push_cast; nlinarith
    _ ≤ Real.exp (B + 1) * (Real.exp (n : ℝ))^2 :=
      mul_le_mul hbase (pow_le_pow_left₀ (by positivity) horder 2) (by positivity) (by positivity)
    _ = Real.exp (B + 1 + 2 * (n : ℝ)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

theorem eventually_separatedMatching_absorbs_linear {gap : ℝ} (hg : 0 < gap) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp (C * n) ≤
        (DenseGraph.labeledMatchingCoefficient
          (2 * subcriticalSeparatedMatchingSize gap n)
          (subcriticalSeparatedMatchingSize gap n) : ℝ) *
        Real.exp (-subcriticalSeparatedComparisonRate gap * n * Real.log n) := by
  let a := gap / 32
  have ha : 0 < a := by dsimp [a]; positivity
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_subcriticalSeparatedMatchingSize_lower hg,
    DenseGraph.eventually_matchingCoefficient_exponential_gain a ha,
    hlog.eventually (eventually_ge_atTop (16 * C / a))] with n hn hgain hlog
  let q := subcriticalSeparatedMatchingSize gap n
  have hgain' := hgain q (2 * q) (by dsimp [a]; linarith) le_rfl
  have hfour : (1 : ℝ) ≤ 4^q := one_le_pow₀ (by norm_num)
  have hmatch : Real.exp ((a / 8) * n * Real.log n) ≤
      (DenseGraph.labeledMatchingCoefficient (2 * q) q : ℝ) := by
    apply le_trans _ hgain'
    nlinarith [Real.exp_pos ((a / 8) * n * Real.log n)]
  have hlog' := (div_le_iff₀ ha).mp hlog
  have hmul := mul_le_mul_of_nonneg_right hlog' (show (0 : ℝ) ≤ n by positivity)
  calc
    _ ≤ Real.exp ((a / 8) * n * Real.log n) *
        Real.exp (-subcriticalSeparatedComparisonRate gap * n * Real.log n) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      dsimp [subcriticalSeparatedComparisonRate, a] at *
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hmatch (Real.exp_pos _).le

theorem tendsto_subcriticalSeparatedComparison_zero {gap : ℝ} (hg : 0 < gap) :
    Tendsto (fun n : ℕ ↦ Real.exp (-subcriticalSeparatedComparisonRate gap * n * Real.log n))
      atTop (𝓝 0) := by
  have hc := subcriticalSeparatedComparisonRate_pos hg
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun n ↦ (Real.exp_pos _).le)
    (g := fun n : ℕ ↦ Real.exp (-subcriticalSeparatedComparisonRate gap * n))
  · filter_upwards [hlog.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
    apply Real.exp_le_exp.mpr
    have hcN : 0 ≤ subcriticalSeparatedComparisonRate gap * n := by positivity
    nlinarith [mul_nonneg hcN (sub_nonneg.mpr hn)]
  · exact tendsto_exp_neg_mul_natCast_zero hc

end InducedStars
