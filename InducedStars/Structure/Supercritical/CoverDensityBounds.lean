import InducedStars.Structure.Supercritical.CoverMultiplicity

/-!
# Uniform cross-density bounds for balanced full covers

This file isolates the compact cross-density interface used in the
supercritical cover argument.  If an ordered full division is sufficiently
balanced and the total edge density is sufficiently close to a fixed
strictly supercritical density, then its free cross-edge density stays in a
fixed compact subinterval of `(0,1)`.  All constants are explicit functions
of `k` and `gamma`, and the proof is finite and axiom-free.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-- Positive lower endpoint for the balanced-fiber cross density. -/
def supercriticalCoverCrossDensityLower (k : Nat) (gamma : Real) : Real :=
  (gamma - 1 / (k - 1 : Nat)) / 4

/-- Upper endpoint for the balanced-fiber cross density.  This is the same
strict upper-density buffer already used by the cover-uniqueness argument. -/
def supercriticalCoverCrossDensityUpper (gamma : Real) : Real :=
  (gamma + 1) / 2

/-- Balance radius used by the compact cross-density interface. -/
def supercriticalCoverCrossDensityBalanceRadius
    (k : Nat) (gamma : Real) : Real :=
  (gamma - 1 / (k - 1 : Nat)) / 16

/-- Total-density tolerance used by the compact cross-density interface. -/
def supercriticalCoverCrossDensityTolerance
    (k : Nat) (gamma : Real) : Real :=
  min ((gamma - 1 / (k - 1 : Nat)) / 16)
    (supercriticalCoverDensityTolerance gamma)

private theorem one_div_parts_lt_gammaK_for_coverDensity
    {k : Nat} (hk : 3 ≤ k) :
    (1 : Real) / (k - 1 : Nat) < gammaK k := by
  have hr : (0 : Real) < (k - 1 : Nat) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  rw [div_lt_iff₀ hr]
  rw [gammaK_mul_denominator k hk]
  have hp : 0 < ((k - 2 : Nat) : Real) * pK k := by
    exact mul_pos (by exact_mod_cast (show 0 < k - 2 by omega))
      (pK_pos (by omega))
  linarith

theorem supercriticalCoverCrossDensityLower_pos
    {k : Nat} (hk : 3 ≤ k) {gamma : Real}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalCoverCrossDensityLower k gamma := by
  unfold supercriticalCoverCrossDensityLower
  have hgap : (1 : Real) / (k - 1 : Nat) < gamma :=
    (one_div_parts_lt_gammaK_for_coverDensity hk).trans hgamma.1
  linarith

theorem supercriticalCoverCrossDensityUpper_lt_one
    {gamma : Real} (hgamma : gamma < 1) :
    supercriticalCoverCrossDensityUpper gamma < 1 := by
  unfold supercriticalCoverCrossDensityUpper
  linarith

theorem supercriticalCoverCrossDensityBalanceRadius_pos
    {k : Nat} (hk : 3 ≤ k) {gamma : Real}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalCoverCrossDensityBalanceRadius k gamma := by
  unfold supercriticalCoverCrossDensityBalanceRadius
  have hgap : (1 : Real) / (k - 1 : Nat) < gamma :=
    (one_div_parts_lt_gammaK_for_coverDensity hk).trans hgamma.1
  linarith

theorem supercriticalCoverCrossDensityTolerance_pos
    {k : Nat} (hk : 3 ≤ k) {gamma : Real}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    0 < supercriticalCoverCrossDensityTolerance k gamma := by
  unfold supercriticalCoverCrossDensityTolerance
  exact lt_min
    (supercriticalCoverCrossDensityBalanceRadius_pos hk hgamma)
    (supercriticalCoverDensityTolerance_pos hgamma.2)

/-- A balanced full division has at most the expected diagonal capacity,
up to its displayed balance error.  The factor `2` avoids floors and keeps
the estimate exact over natural capacities. -/
private theorem two_mul_divisionInternalCliqueCapacity_le_of_balanced
    {k n : Nat} (_hk : 3 ≤ k) {beta : Real}
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : IsBalancedFullDivision D beta) :
    2 * (divisionInternalCliqueCapacity D : Real) ≤
      (n : Real) * ((n : Real) / (k - 1 : Nat) + beta * n) := by
  classical
  have hsum : ∑ i : Fin (k - 1), (D.parts i).card = n := by
    rw [← D.card_support, D.support_eq_univ hbalanced.1]
    simp
  have hterm : ∀ i : Fin (k - 1),
      ((D.parts i).card : Real) * (((D.parts i).card : Real) - 1) ≤
        ((D.parts i).card : Real) *
          ((n : Real) / (k - 1 : Nat) + beta * n) := by
    intro i
    have hiUpper := (abs_le.mp (hbalanced.2 i)).2
    have hi0 : (0 : Real) ≤ (D.parts i).card := by positivity
    apply mul_le_mul_of_nonneg_left _ hi0
    linarith
  calc
    2 * (divisionInternalCliqueCapacity D : Real) =
        ∑ i : Fin (k - 1),
          ((D.parts i).card : Real) * (((D.parts i).card : Real) - 1) := by
      unfold divisionInternalCliqueCapacity
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Nat.cast_choose_two]
      ring
    _ ≤ ∑ i : Fin (k - 1),
        ((D.parts i).card : Real) *
          ((n : Real) / (k - 1 : Nat) + beta * n) :=
      Finset.sum_le_sum fun i _hi ↦ hterm i
    _ = (n : Real) * ((n : Real) / (k - 1 : Nat) + beta * n) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]

/-- Uniform compactness of the cross density in every balanced full exact
fiber near a fixed strict supercritical density.  The conclusion is uniform
in both the edge count `m` and the ordered full division `D`.

Here `m - divisionInternalCliqueCapacity D` is the number of selected cross
edges and `supercriticalTotalCrossCapacity D` is the available cross capacity.
-/
theorem eventually_balancedFullDivision_crossDensity_mem_Icc
    {k : Nat} (hk : 3 ≤ k) (gamma : Real)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1) :
    ∀ᶠ n : Nat in Filter.atTop, ∀ m : Nat,
      ∀ D : SupercriticalDivision k (Fin n),
        IsBalancedFullDivision D
            (supercriticalCoverCrossDensityBalanceRadius k gamma) →
        |(m : Real) / (completeEdgeCount n : Real) - gamma| <
            supercriticalCoverCrossDensityTolerance k gamma →
        ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
              (supercriticalTotalCrossCapacity D : Real) ∈
          Set.Icc (supercriticalCoverCrossDensityLower k gamma)
            (supercriticalCoverCrossDensityUpper gamma) := by
  let r : Real := (k - 1 : Nat)
  let gap : Real := gamma - 1 / r
  let beta : Real := gap / 16
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast (show 0 < k - 1 by omega)
  have hgap : 0 < gap := by
    dsimp [gap, r]
    exact sub_pos.mpr
      ((one_div_parts_lt_gammaK_for_coverDensity hk).trans hgamma.1)
  have hbeta : 0 < beta := div_pos hgap (by norm_num)
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / r + 2 * beta) / beta)
  filter_upwards [Filter.eventually_ge_atTop N,
    Filter.eventually_ge_atTop 2] with n hnN hnTwo m D hbalanced hdensity
  have hn0 : (0 : Real) ≤ n := by positivity
  have hnPos : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
  have hcompleteNat : 0 < completeEdgeCount n := by
    exact Nat.choose_pos hnTwo
  have hcomplete : (0 : Real) < completeEdgeCount n := by
    exact_mod_cast hcompleteNat
  have hbetaDef :
      supercriticalCoverCrossDensityBalanceRadius k gamma = beta := by
    simp [supercriticalCoverCrossDensityBalanceRadius, beta, gap, r]
  have hIraw :=
    two_mul_divisionInternalCliqueCapacity_le_of_balanced hk D hbalanced
  rw [hbetaDef] at hIraw
  have hthreshold : 1 / r + 2 * beta < beta * (n : Real) := by
    have hNreal : ((N : Nat) : Real) ≤ n := by exact_mod_cast hnN
    have hratio : (1 / r + 2 * beta) / beta < (N : Real) := hN
    have hmul := mul_lt_mul_of_pos_right hratio hbeta
    rw [div_mul_cancel₀ _ hbeta.ne'] at hmul
    exact hmul.trans_le (by
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hNreal hbeta.le)
  have hcompleteFormula : (completeEdgeCount n : Real) =
      (n : Real) * ((n : Real) - 1) / 2 := by
    rw [completeEdgeCount, Nat.cast_choose_two]
  have hIrelative :
      (divisionInternalCliqueCapacity D : Real) ≤
        (1 / r + 2 * beta) * (completeEdgeCount n : Real) := by
    have hrDef : ((k - 1 : Nat) : Real) = r := rfl
    rw [hrDef] at hIraw
    have hIraw' :
        2 * (divisionInternalCliqueCapacity D : Real) ≤
          (1 / r + beta) * (n : Real) ^ 2 := by
      calc
        2 * (divisionInternalCliqueCapacity D : Real) ≤
            (n : Real) * ((n : Real) / r + beta * n) := hIraw
        _ = (1 / r + beta) * (n : Real) ^ 2 := by ring
    have hthreshold' :
        (1 / r + 2 * beta) * (n : Real) ≤
          beta * (n : Real) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hthreshold.le hn0
      nlinarith
    rw [hcompleteFormula]
    nlinarith
  have htoleranceGap :
      supercriticalCoverCrossDensityTolerance k gamma ≤ gap / 16 := by
    unfold supercriticalCoverCrossDensityTolerance
    simp [gap, r]
  have htoleranceUpper :
      supercriticalCoverCrossDensityTolerance k gamma ≤
        supercriticalCoverDensityTolerance gamma := by
    exact min_le_right _ _
  have hmDensityLower :
      gamma - gap / 16 <
        (m : Real) / (completeEdgeCount n : Real) := by
    have habs := (abs_lt.mp hdensity).1
    linarith
  have hmDensityUpper :
      (m : Real) / (completeEdgeCount n : Real) < (gamma + 1) / 2 := by
    have habs := (abs_lt.mp hdensity).2
    unfold supercriticalCoverDensityTolerance at htoleranceUpper
    linarith
  have hmLower :
      (gamma - gap / 16) * (completeEdgeCount n : Real) < (m : Real) :=
    (lt_div_iff₀ hcomplete).mp hmDensityLower
  have hqGap :
      supercriticalCoverCrossDensityLower k gamma ≤ gap / 2 := by
    have heq : supercriticalCoverCrossDensityLower k gamma = gap / 4 := by
      simp [supercriticalCoverCrossDensityLower, gap, r]
    rw [heq]
    linarith
  have hbudget :
      supercriticalCoverCrossDensityLower k gamma +
          (1 / r + 2 * beta) ≤ gamma - gap / 16 := by
    have hbetaEq : beta = gap / 16 := rfl
    rw [hbetaEq]
    dsimp [gap]
    linarith [hqGap]
  have hqI_le_m :
      supercriticalCoverCrossDensityLower k gamma *
          (completeEdgeCount n : Real) +
        (divisionInternalCliqueCapacity D : Real) ≤ (m : Real) := by
    have hq0 := (supercriticalCoverCrossDensityLower_pos hk hgamma).le
    have hbudgetMul := mul_le_mul_of_nonneg_right hbudget hcomplete.le
    calc
      supercriticalCoverCrossDensityLower k gamma *
            (completeEdgeCount n : Real) +
          (divisionInternalCliqueCapacity D : Real) ≤
          (supercriticalCoverCrossDensityLower k gamma +
            (1 / r + 2 * beta)) * (completeEdgeCount n : Real) := by
        nlinarith
      _ ≤ (gamma - gap / 16) * (completeEdgeCount n : Real) :=
        hbudgetMul
      _ ≤ (m : Real) := hmLower.le
  have hInternalLe : divisionInternalCliqueCapacity D ≤ m := by
    have hq0 := (supercriticalCoverCrossDensityLower_pos hk hgamma).le
    have hInternalReal : (divisionInternalCliqueCapacity D : Real) ≤ m := by
      calc
        (divisionInternalCliqueCapacity D : Real) ≤
            supercriticalCoverCrossDensityLower k gamma *
                (completeEdgeCount n : Real) +
              (divisionInternalCliqueCapacity D : Real) :=
          le_add_of_nonneg_left (mul_nonneg hq0 hcomplete.le)
        _ ≤ (m : Real) := hqI_le_m
    exact_mod_cast hInternalReal
  have hmComplete : m ≤ completeEdgeCount n := by
    have hmLt : (m : Real) < completeEdgeCount n := by
      apply (div_lt_one hcomplete).mp
      exact hmDensityUpper.trans
        (by linarith [hgamma.2])
    exact_mod_cast hmLt.le
  have hcrossNat := supercriticalTotalCrossCapacity_pos hk D
  have hcross : (0 : Real) < supercriticalTotalCrossCapacity D := by
    exact_mod_cast hcrossNat
  have hsum := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hbalanced.1] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hcrossLeComplete : supercriticalTotalCrossCapacity D ≤
      completeEdgeCount n := by
    unfold completeEdgeCount
    omega
  have hlower : supercriticalCoverCrossDensityLower k gamma ≤
      ((m - divisionInternalCliqueCapacity D : Nat) : Real) /
        (supercriticalTotalCrossCapacity D : Real) := by
    rw [le_div_iff₀ hcross, Nat.cast_sub hInternalLe]
    have hq0 := (supercriticalCoverCrossDensityLower_pos hk hgamma).le
    have hscale := mul_le_mul_of_nonneg_left
      (by exact_mod_cast hcrossLeComplete :
        (supercriticalTotalCrossCapacity D : Real) ≤
          (completeEdgeCount n : Real)) hq0
    nlinarith
  have hupper := coPartiteFiber_crossDensity_le_totalDensity
    D hbalanced.1 hInternalLe hcrossNat hmComplete
  exact ⟨hlower, hupper.trans hmDensityUpper.le⟩

end InducedStars
