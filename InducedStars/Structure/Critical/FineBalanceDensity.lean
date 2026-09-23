import InducedStars.Structure.Critical.CapacityBookkeeping
import Mathlib.Tactic

/-!
# Uniform missing-coordinate density for critical fine balance

For a sparse set occupying a sufficiently small, `k`-dependent fraction of
the vertices, a fixed positive fraction of the maximum combined coordinate
universe is missing.  The estimate is uniform in the sparse-set size and is
the compact-density input to the critical fine-balance comparison.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A fixed sparse-set fraction on which the critical missing-coordinate
density stays uniformly away from zero. -/
noncomputable def criticalFineBalanceSparseFraction (k : ℕ) : ℝ :=
  (1 - gammaK k) / 16

/-- The uniform lower bound for the missing-coordinate density used in the
critical fine-balance argument. -/
noncomputable def criticalFineBalanceMissingDensity (k : ℕ) : ℝ :=
  (1 - gammaK k) / 8

theorem criticalFineBalanceSparseFraction_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalFineBalanceSparseFraction k := by
  unfold criticalFineBalanceSparseFraction
  positivity [gammaK_lt_one hk]

theorem criticalFineBalanceMissingDensity_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalFineBalanceMissingDensity k := by
  unfold criticalFineBalanceMissingDensity
  positivity [gammaK_lt_one hk]

/-- The balanced maximum capacity at the sparse size of an actual division
is nonzero: two nonempty main parts already contribute a cross coordinate. -/
theorem criticalMaximumCombinedCapacity_pos_of_division
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n)) :
    0 < criticalMaximumCombinedCapacity k n D.sparse.card := by
  have hcross : 0 < supercriticalTotalCrossCapacity D :=
    supercriticalTotalCrossCapacity_pos hk D
  have hcrossLe : supercriticalTotalCrossCapacity D ≤
      criticalCombinedVariableCapacity D := by
    simp [criticalCombinedVariableCapacity]
  exact hcross.trans_le
    (hcrossLe.trans (criticalCombinedVariableCapacity_le_maximum D))

/-- Explicit finite form of the uniform missing-coordinate density estimate.
The threshold `2 ≤ n` is the only large-`n` input. -/
theorem criticalFineBalanceMissingDensity_mul_capacity_le
    {k n s : ℕ} (hk : 3 ≤ k) (hn : 2 ≤ n) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    criticalFineBalanceMissingDensity k *
        (criticalMaximumCombinedCapacity k n s : ℝ) ≤
      (criticalCombinedMissingCount k n s : ℝ) := by
  let a : ℝ := 1 - gammaK k
  let T : ℕ := Nat.choose (n - s) 2 + Nat.choose s 2
  let R : ℕ := (n - s) * s
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (gammaK_lt_one hk)
  have hdecompNat : completeEdgeCount n = T + R := by
    have hadd := DenseGraph.choose_two_add (n - s) s
    rw [Nat.sub_add_cancel hs] at hadd
    dsimp [completeEdgeCount, T, R]
    omega
  have hdecompReal :
      (completeEdgeCount n : ℝ) = (T : ℝ) + (R : ℝ) := by
    exact_mod_cast hdecompNat
  have hCnonneg : 0 ≤ (completeEdgeCount n : ℝ) := by positivity
  have hnReal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnNonneg : 0 ≤ (n : ℝ) := by positivity
  have hsNonneg : 0 ≤ (s : ℝ) := by positivity
  have hnSubLe : ((n - s : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n s
  have hRfirst : (R : ℝ) ≤ a / 16 * (n : ℝ) ^ 2 := by
    have hsSmall' : (s : ℝ) ≤ a / 16 * (n : ℝ) := by
      simpa [criticalFineBalanceSparseFraction, a] using hsSmall
    calc
      (R : ℝ) = (s : ℝ) * ((n - s : ℕ) : ℝ) := by
        simp [R, Nat.mul_comm]
      _ ≤ (s : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnSubLe hsNonneg
      _ ≤ (a / 16 * (n : ℝ)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hsSmall' hnNonneg
      _ = a / 16 * (n : ℝ) ^ 2 := by ring
  have hchooseFormula :
      (completeEdgeCount n : ℝ) =
        (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    rw [completeEdgeCount, Nat.cast_choose_two]
  have hsquare :
      (n : ℝ) ^ 2 / 16 ≤ (completeEdgeCount n : ℝ) / 4 := by
    rw [hchooseFormula]
    nlinarith
  have hRquarter :
      (R : ℝ) ≤ a / 4 * (completeEdgeCount n : ℝ) := by
    calc
      (R : ℝ) ≤ a / 16 * (n : ℝ) ^ 2 := hRfirst
      _ = a * ((n : ℝ) ^ 2 / 16) := by ring
      _ ≤ a * ((completeEdgeCount n : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hsquare ha.le
      _ = a / 4 * (completeEdgeCount n : ℝ) := by ring
  have hgap :
      3 * a / 4 * (completeEdgeCount n : ℝ) ≤
        (T : ℝ) - gammaK k * (completeEdgeCount n : ℝ) := by
    dsimp [a] at ha ⊢
    nlinarith
  have hgapNonneg :
      0 ≤ 3 * a / 4 * (completeEdgeCount n : ℝ) := by positivity
  have htargetLe :
      gammaK k * (completeEdgeCount n : ℝ) ≤ (T : ℝ) := by
    linarith
  have hedgeReal : (criticalEdgeCount k n : ℝ) ≤ (T : ℝ) :=
    (criticalEdgeCount_cast_le hk n).trans htargetLe
  have hedgeNat : criticalEdgeCount k n ≤ T := by
    exact_mod_cast hedgeReal
  have hmissingCast :
      (criticalCombinedMissingCount k n s : ℝ) =
        (T : ℝ) - (criticalEdgeCount k n : ℝ) := by
    rw [criticalCombinedMissingCount, Nat.cast_sub]
    simpa [T] using hedgeNat
  have hcapNat : criticalMaximumCombinedCapacity k n s ≤ T := by
    have htotal := criticalMaximumCombinedCapacity_add_balancedInternal k n s
    dsimp [T]
    omega
  have hcapReal :
      (criticalMaximumCombinedCapacity k n s : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast hcapNat
  have hTleC : (T : ℝ) ≤ (completeEdgeCount n : ℝ) := by
    nlinarith [hdecompReal]
  have hdNonneg : 0 ≤ criticalFineBalanceMissingDensity k :=
    (criticalFineBalanceMissingDensity_pos hk).le
  calc
    criticalFineBalanceMissingDensity k *
          (criticalMaximumCombinedCapacity k n s : ℝ)
        ≤ criticalFineBalanceMissingDensity k * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hcapReal hdNonneg
    _ ≤ criticalFineBalanceMissingDensity k *
          (completeEdgeCount n : ℝ) :=
      mul_le_mul_of_nonneg_left hTleC hdNonneg
    _ = a / 8 * (completeEdgeCount n : ℝ) := by
      simp [criticalFineBalanceMissingDensity, a]
    _ ≤ 3 * a / 4 * (completeEdgeCount n : ℝ) := by
      nlinarith [mul_nonneg ha.le hCnonneg]
    _ ≤ (T : ℝ) - gammaK k * (completeEdgeCount n : ℝ) := hgap
    _ ≤ (T : ℝ) - (criticalEdgeCount k n : ℝ) := by
      linarith [criticalEdgeCount_cast_le hk n]
    _ = (criticalCombinedMissingCount k n s : ℝ) := hmissingCast.symm

/-- The three finite facts needed by the exact binomial comparison, packaged
for a nonempty clean division fiber. -/
theorem criticalFineBalance_missing_coordinate_data_of_nonempty
    {k n : ℕ} {tau : ℝ} (hk : 3 ≤ k) (hn : 2 ≤ n)
    (hnParts : k - 1 ≤ n) (D : SupercriticalDivision k (Fin n))
    (hD : (criticalCleanDivisionGraphFinset k hk n tau hnParts D).Nonempty)
    (hsSmall : (D.sparse.card : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ)) :
    0 < criticalMaximumCombinedCapacity k n D.sparse.card ∧
      criticalCombinedMissingCount k n D.sparse.card ≤
        criticalMaximumCombinedCapacity k n D.sparse.card ∧
      criticalFineBalanceMissingDensity k *
          (criticalMaximumCombinedCapacity k n D.sparse.card : ℝ) ≤
        (criticalCombinedMissingCount k n D.sparse.card : ℝ) := by
  have hs : D.sparse.card ≤ n := by
    simpa using Finset.card_le_univ D.sparse
  exact ⟨criticalMaximumCombinedCapacity_pos_of_division hk D,
    criticalCombinedMissingCount_le_maximum_of_nonempty hD,
    criticalFineBalanceMissingDensity_mul_capacity_le
      hk hn hs hsSmall⟩

/-- Eventual, sparse-size-uniform form consumed by the critical fine-balance
argument. -/
theorem eventually_criticalFineBalanceMissingDensity_mul_capacity_le
    {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ n in atTop, ∀ s : ℕ, s ≤ n →
      (s : ℝ) ≤ criticalFineBalanceSparseFraction k * (n : ℝ) →
      criticalFineBalanceMissingDensity k *
          (criticalMaximumCombinedCapacity k n s : ℝ) ≤
        (criticalCombinedMissingCount k n s : ℝ) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn s hs hsSmall
  exact criticalFineBalanceMissingDensity_mul_capacity_le
    hk hn hs hsSmall

end InducedStars
