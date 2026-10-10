import InducedStars.Structure.Subcritical.RetainedFullSliceComparison
import InducedStars.Structure.Subcritical.DistinguishedReferenceUniform

/-!
# Uniform linear shifts of the distinguished full-slice denominator

Paper: the active-level shift in the subcritical matching transfer.
The balanced reference has a quadratic active capacity. Its explicit
linear mean error and every prescribed linear shift stay in one fixed
interior band. The shifted family is the full slice, not the old window.
-/

noncomputable section
open Filter Finset Set Topology
open scoped BigOperators Classical
namespace InducedStars

def subcriticalReferenceShiftBand (k : ℕ) : ℝ := min (pK k) (1 - pK k) / 4

theorem subcriticalReferenceShiftBand_bounds {k : ℕ} (hk : 3 ≤ k) :
    0 < subcriticalReferenceShiftBand k ∧ subcriticalReferenceShiftBand k < 1 / 2 ∧
      2 * subcriticalReferenceShiftBand k ≤ pK k ∧
      2 * subcriticalReferenceShiftBand k ≤ 1 - pK k := by
  have hp := pK_pos (by omega : 2 ≤ k)
  have hq : 0 < 1 - pK k := sub_pos.mpr (pK_lt_one (by omega : 2 ≤ k))
  have hmin : 0 < min (pK k) (1-pK k) := lt_min hp hq
  have hl := min_le_left (pK k) (1-pK k)
  have hr := min_le_right (pK k) (1-pK k)
  unfold subcriticalReferenceShiftBand
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

theorem subcriticalReference_shift_headroom {k n A M q : ℕ} (hk : 3 ≤ k)
    {Qmax : ℝ} (hq : (q : ℝ) ≤ Qmax * n)
    (hmean : |(M : ℝ) - pK k * A| ≤ 4 * k * n)
    (hroom : (4 * k + Qmax) * n ≤ subcriticalReferenceShiftBand k * A) :
    M ≤ A ∧ q ≤ M ∧
      subcriticalReferenceShiftBand k * A ≤ ((M-q : ℕ) : ℝ) ∧
      ((M-q : ℕ) : ℝ) ≤ (1 - subcriticalReferenceShiftBand k) * A := by
  obtain ⟨hlambda, hlambdaHalf, hlp, hlq⟩ := subcriticalReferenceShiftBand_bounds hk
  have hA : (0 : ℝ) ≤ A := by positivity
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have helo := (abs_le.mp hmean).1
  have hehi := (abs_le.mp hmean).2
  have hcost : (4 : ℝ) * k * n + q ≤ subcriticalReferenceShiftBand k * A := by nlinarith
  have hpA := mul_le_mul_of_nonneg_right hlp hA
  have hqA := mul_le_mul_of_nonneg_right hlq hA
  have hMA : (M : ℝ) ≤ A := by nlinarith [mul_nonneg hlambda.le hA]
  have hqM : (q : ℝ) ≤ M := by nlinarith [mul_nonneg hlambda.le hA]
  have hqMnat : q ≤ M := by exact_mod_cast hqM
  refine ⟨by exact_mod_cast hMA, hqMnat, ?_, ?_⟩ <;>
    rw [Nat.cast_sub hqMnat] <;> nlinarith

/-- Every linear-size active shift is controlled by the same fixed
logarithmic adjacent-ratio constant. The reference key is kept fixed when
adding the new matching to its remainder. -/
theorem eventually_subcriticalReference_denominator_shift
    {k : ℕ} (hk : 3 ≤ k) {gLower gUpper delta Qmax : ℝ}
    (hgLower : 0 < gLower) (hband : gLower ≤ gUpper)
    (hgUpper : gUpper < gammaK k) (hd : 0 < delta)
    (hdp : delta ≤ pK k / 2) (hdq : delta ≤ (1 - pK k) / 2) (hQ : 0 ≤ Qmax) :
    ∃ Cshift : ℝ, 0 < Cshift ∧ ∀ᶠ n : ℕ in atTop, ∀ m b q : ℕ,
      gLower ≤ subcriticalReferenceDensity n m b →
      subcriticalReferenceDensity n m b ≤ gUpper →
      (q : ℝ) ≤ Qmax * n →
      (retainedKeyPartitionFunction (subcriticalDistinguishedReferenceKey hk n m b)
          m delta (b : ℤ) : ℝ) *
        inducedStarFreeGraphCountWithEdges k
          (subcriticalDistinguishedReferenceKey hk n m b).remainder.card (b+q) ≤
        (inducedStarFreeGraphCountWithEdges k n m : ℝ) * Real.exp (Cshift * q) := by
  obtain ⟨hlambda, hlambdaHalf, hlp, hlq⟩ := subcriticalReferenceShiftBand_bounds hk
  let a := Real.sqrt (gLower / gammaK k)
  have ha : 0 < a := Real.sqrt_pos.mpr (div_pos hgLower (gammaK_pos hk))
  have hden : 0 < subcriticalReferenceShiftBand k * a^2 := by positivity
  obtain ⟨C, hC, href⟩ := eventually_subcriticalReference_fiber
    hk hgLower hband hgUpper hd hdp hdq
  have hscale := eventually_subcriticalReference_scale (k := k) ha (by norm_num : (0 : ℝ) < 1)
  have hlinear : ∀ᶠ n : ℕ in atTop,
      32 * (4 * k + Qmax) ≤ subcriticalReferenceShiftBand k * a^2 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (32 * (4 * k + Qmax) /
        (subcriticalReferenceShiftBand k * a^2)))] with n hn
    exact (div_le_iff₀ hden).mp hn |>.trans_eq (by ring)
  refine ⟨DenseGraph.binomialCompactBandShiftConstant (subcriticalReferenceShiftBand k),
    DenseGraph.binomialCompactBandShiftConstant_pos hlambda hlambdaHalf, ?_⟩
  filter_upwards [href, hscale, hlinear] with n href hn hlinear
  intro m b q hgl hgu hq
  have hgamma : subcriticalReferenceDensity n m b ∈ Ioo (0 : ℝ) (gammaK k) :=
    ⟨hgLower.trans_le hgl, hgu.trans_lt hgUpper⟩
  have hmu : a ≤ subcriticalReferenceMass k n m b :=
    Real.sqrt_le_sqrt ((div_le_div_iff_of_pos_right (gammaK_pos hk)).mpr hgl)
  obtain ⟨hrq, hqn, hmeanRoom, hpairRoom, hAlow, hNlow⟩ :=
    subcriticalReference_headroom_of_scale hk hn.1 hgamma ha (by norm_num : (0 : ℝ) ≤ 1)
      hmu hn.2.1 hn.2.2.1 hn.2.2.2
  obtain ⟨_, _, v, hv, hvdens, hvcount, hvpos, hrem⟩ := href m b hgl hgu
  let D := balancedRetainedDivision hk hrq hqn
  let M := retainedEdgeCountTotal v
  have hid : retainedCliqueCapacity D 0 n + M + b = m := by
    have h := (mem_retainedEdgeCountLevel.mp hv).1
    dsimp [D, M]
    omega
  have hidR : (retainedCliqueCapacity D 0 n : ℝ) + M + b = m := by exact_mod_cast hid
  have he := subcriticalReference_expectedCapacity_error hk hn.1 hgamma
  rw [← balancedRetainedDivision_cliqueCapacity hk hrq hqn,
    ← balancedRetainedDivision_activeTotalCapacity hk hrq hqn] at he
  have hmean : |(M : ℝ) - pK k * retainedActiveTotalCapacity D 0 n| ≤ 4 * k * n := by
    have heq : ((m : ℝ) - b) -
        ((retainedCliqueCapacity D 0 n : ℝ) + pK k * retainedActiveTotalCapacity D 0 n) =
        (M : ℝ) - pK k * retainedActiveTotalCapacity D 0 n := by linarith
    change |((m : ℝ) - b) -
        ((retainedCliqueCapacity D 0 n : ℝ) + pK k * retainedActiveTotalCapacity D 0 n)| ≤ _ at he
    rwa [heq] at he
  have hroom : (4 * k + Qmax) * n ≤
      subcriticalReferenceShiftBand k * retainedActiveTotalCapacity D 0 n := by
    have h₁ := mul_le_mul_of_nonneg_right hlinear (show (0 : ℝ) ≤ n by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hAlow hlambda.le
    dsimp [D] at *
    nlinarith
  obtain ⟨hM, hqM, hlo, hhi⟩ := subcriticalReference_shift_headroom hk hq hmean hroom
  have hbound := retainedPartitionFunction_mul_remainder_le_shifted_total hk D 0 n delta
    hid hM hqM hlambda hlambdaHalf hlo hhi
  have hkey : subcriticalDistinguishedReferenceKey hk n m b = retainedKey D 0 n := by
    unfold subcriticalDistinguishedReferenceKey
    rw [dif_pos ⟨hrq, hqn⟩]
    rfl
  rw [hkey, retainedKeyPartitionFunction_retainedKey]
  simpa only [retainedKey_remainder] using hbound

end InducedStars
