import InducedStars.Structure.Subcritical.DistinguishedReference
import DenseGraph.Combinatorics.MatchingCoefficientGrowth

/-!
# Accuracy-independent matching parameters for the remainder lower tail

The positive lower-edge coefficient is chosen from k and gamma
alone. It is not taken from a radius or accuracy which later tends to zero.
-/

noncomputable section
open Filter Set Topology
namespace InducedStars

def subcriticalRemainderMatchingRate (k : ℕ) (gamma : ℝ) : ℝ :=
  (1 - subcriticalOneBlockLength k gamma) / 16

def subcriticalRemainderLowerCoefficient (k : ℕ) (gamma : ℝ) : ℝ :=
  subcriticalRemainderMatchingRate k gamma / 2

def subcriticalRemainderMatchingSize (k : ℕ) (gamma : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (subcriticalRemainderMatchingRate k gamma * n)

theorem subcriticalRemainderMatchingRate_pos {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    0 < subcriticalRemainderMatchingRate k gamma := by
  have h := subcriticalOneBlockLength_lt_one hk hgamma.2
  unfold subcriticalRemainderMatchingRate
  positivity

theorem subcriticalRemainderLowerCoefficient_pos {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    0 < subcriticalRemainderLowerCoefficient k gamma :=
  half_pos (subcriticalRemainderMatchingRate_pos hk hgamma)

theorem subcriticalRemainderMatchingSize_cast_le {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) (n : ℕ) :
    (subcriticalRemainderMatchingSize k gamma n : ℝ) ≤
      subcriticalRemainderMatchingRate k gamma * n :=
  Nat.floor_le (mul_nonneg (subcriticalRemainderMatchingRate_pos hk hgamma).le (Nat.cast_nonneg _))

/-- The integer matching size eventually dominates the final fixed lower
coefficient, uniformly in every subsequent accuracy choice. -/
theorem eventually_subcriticalRemainderMatchingSize_lower {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∀ᶠ n : ℕ in atTop, subcriticalRemainderLowerCoefficient k gamma * n ≤
      subcriticalRemainderMatchingSize k gamma n := by
  have ht : Tendsto (fun n : ℕ ↦ subcriticalRemainderLowerCoefficient k gamma * n)
      atTop atTop := tendsto_natCast_atTop_atTop.const_mul_atTop
    (subcriticalRemainderLowerCoefficient_pos hk hgamma)
  filter_upwards [ht.eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  have hf := Nat.lt_floor_add_one (subcriticalRemainderMatchingRate k gamma * n)
  change subcriticalRemainderMatchingRate k gamma / 2 * n ≤ _
  change (1 : ℝ) ≤ subcriticalRemainderMatchingRate k gamma / 2 * n at hn
  unfold subcriticalRemainderMatchingSize
  linarith

/-- A remainder containing half the limiting unused mass has room for four
copies of the chosen matching size. This reserve is independent of xi. -/
theorem four_mul_subcriticalRemainderMatchingSize_le
    {k n s : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k))
    (hs : (1 - subcriticalOneBlockLength k gamma) / 2 * n ≤ s) :
    4 * subcriticalRemainderMatchingSize k gamma n ≤ s := by
  have hq := subcriticalRemainderMatchingSize_cast_le hk hgamma n
  have hmu := subcriticalOneBlockLength_lt_one hk hgamma.2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  unfold subcriticalRemainderMatchingRate at hq
  have hmul := mul_nonneg (sub_nonneg.mpr hmu.le) hn
  exact_mod_cast (show (4 : ℝ) * subcriticalRemainderMatchingSize k gamma n ≤ s by nlinarith)

/-- The actual fixed matching sizes supply the required superlinear
exponential gain even after the marked-inverse factor 4^q. -/
theorem eventually_subcriticalRemainderMatching_gain
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Ioo (0 : ℝ) (gammaK k)) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℕ,
      2 * subcriticalRemainderMatchingSize k gamma n ≤ t →
      (4 : ℝ) ^ subcriticalRemainderMatchingSize k gamma n *
        Real.exp ((subcriticalRemainderLowerCoefficient k gamma / 8) * n * Real.log n) ≤
        (DenseGraph.labeledMatchingCoefficient t (subcriticalRemainderMatchingSize k gamma n) : ℝ) := by
  filter_upwards [eventually_subcriticalRemainderMatchingSize_lower hk hgamma,
    DenseGraph.eventually_matchingCoefficient_exponential_gain
      (subcriticalRemainderLowerCoefficient k gamma)
      (subcriticalRemainderLowerCoefficient_pos hk hgamma)] with n hn hgain
  intro t ht
  exact hgain _ t hn ht

end InducedStars
