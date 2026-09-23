import InducedStars.Structure.Critical.FineBalanceDensity
import InducedStars.Structure.Supercritical.CoverMultiplicity
import Mathlib.Tactic

/-!
# Uniform upper cross density after a small critical deletion

The uniqueness-of-balanced-covers argument needs its selected cross density
bounded strictly below one.  This file supplies that bound uniformly after
deleting a sufficiently small vertex set and prescribing an arbitrary graph
on the deleted set.
-/

noncomputable section

open Filter Set Topology

namespace InducedStars

/-- A fixed upper endpoint, strictly between the critical density and one. -/
noncomputable def criticalFineBalanceCoverDensityUpper (k : ℕ) : ℝ :=
  (gammaK k + 1) / 2

/-- The positive logarithmic rate corresponding to the fixed upper endpoint. -/
noncomputable def criticalFineBalanceCoverLogRate (k : ℕ) : ℝ :=
  supercriticalCoverLogRate (gammaK k)

theorem criticalFineBalanceCoverDensityUpper_mem_Ioo
    {k : ℕ} (hk : 3 ≤ k) :
    criticalFineBalanceCoverDensityUpper k ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold criticalFineBalanceCoverDensityUpper
  constructor <;> linarith [gammaK_pos hk, gammaK_lt_one hk]

theorem criticalFineBalanceCoverLogRate_pos
    {k : ℕ} (hk : 3 ≤ k) :
    0 < criticalFineBalanceCoverLogRate k := by
  unfold criticalFineBalanceCoverLogRate
  exact supercriticalCoverLogRate_pos
    ⟨gammaK_pos hk, gammaK_lt_one hk⟩

@[simp] theorem exp_neg_criticalFineBalanceCoverLogRate
    {k : ℕ} (hk : 3 ≤ k) :
    Real.exp (-criticalFineBalanceCoverLogRate k) =
      criticalFineBalanceCoverDensityUpper k := by
  unfold criticalFineBalanceCoverLogRate
  rw [exp_neg_supercriticalCoverLogRate (gammaK_pos hk)]
  rfl

/-- The chosen sparse fraction leaves enough quadratic cross capacity for
the critical edge count to have density at most the fixed upper endpoint. -/
theorem criticalFineBalance_coverDensity_scalar_le
    {k : ℕ} (hk : 3 ≤ k) :
    gammaK k ≤ criticalFineBalanceCoverDensityUpper k *
      (1 - criticalFineBalanceSparseFraction k) *
      (1 - 2 * criticalFineBalanceSparseFraction k) := by
  let g : ℝ := gammaK k
  let d : ℝ := criticalFineBalanceSparseFraction k
  let u : ℝ := criticalFineBalanceCoverDensityUpper k
  have hg0 : 0 < g := gammaK_pos hk
  have hg1 : g < 1 := gammaK_lt_one hk
  have hd0 : 0 < d := criticalFineBalanceSparseFraction_pos hk
  have hd16 : d ≤ 1 / 16 := by
    dsimp [d, criticalFineBalanceSparseFraction, g]
    linarith
  have hu0 : 0 < u := (criticalFineBalanceCoverDensityUpper_mem_Ioo hk).1
  have hu1 : u < 1 := (criticalFineBalanceCoverDensityUpper_mem_Ioo hk).2
  have hbase : g ≤ u - 3 * d := by
    dsimp [u, d, criticalFineBalanceCoverDensityUpper,
      criticalFineBalanceSparseFraction, g]
    linarith
  have hud : u * d ≤ d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu1.le) hd0.le]
  have hmiddle : u - 3 * d ≤ u * (1 - 3 * d) := by
    nlinarith
  have hfactor : 1 - 3 * d ≤ (1 - d) * (1 - 2 * d) := by
    nlinarith [sq_nonneg d]
  change g ≤ u * (1 - d) * (1 - 2 * d)
  calc
    g ≤ u - 3 * d := hbase
    _ ≤ u * (1 - 3 * d) := hmiddle
    _ ≤ u * ((1 - d) * (1 - 2 * d)) :=
      mul_le_mul_of_nonneg_left hfactor hu0.le
    _ = u * (1 - d) * (1 - 2 * d) := by ring

/-- Finite upper-density estimate.  The hypothesis `1 ≤ δ n` is the sole
large-order input; it absorbs the linear term in `choose (n-s) 2`.

The conclusion is uniform in the prescribed sparse-edge count `t` and in
the balanced full division of the retained `n-s` vertices. -/
theorem criticalSmallDeletion_balancedFullDivision_crossDensity_le
    {k n s t : ℕ} (hk : 3 ≤ k) (hs : s ≤ n)
    (hsSmall : (s : ℝ) ≤
      criticalFineBalanceSparseFraction k * (n : ℝ))
    (hnLarge : 1 ≤ criticalFineBalanceSparseFraction k * (n : ℝ))
    (_ht : t ≤ Nat.choose s 2)
    (D : SupercriticalDivision k (Fin (n - s)))
    (hbalanced : IsBalancedFullDivision D
      (supercriticalCoverBalanceRadius k)) :
    ((criticalEdgeCount k n - t - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
        (supercriticalTotalCrossCapacity D : ℝ) ≤
      criticalFineBalanceCoverDensityUpper k := by
  let g : ℝ := gammaK k
  let d : ℝ := criticalFineBalanceSparseFraction k
  let u : ℝ := criticalFineBalanceCoverDensityUpper k
  let q : ℕ := n - s
  let m : ℕ := criticalEdgeCount k n - t
  change (s : ℝ) ≤ d * (n : ℝ) at hsSmall
  change 1 ≤ d * (n : ℝ) at hnLarge
  have hg0 : 0 ≤ g := (gammaK_pos hk).le
  have hg1 : g < 1 := gammaK_lt_one hk
  have hd0 : 0 ≤ d := (criticalFineBalanceSparseFraction_pos hk).le
  have hd16 : d ≤ 1 / 16 := by
    dsimp [d, criticalFineBalanceSparseFraction, g]
    linarith [gammaK_pos hk]
  have hu0 : 0 ≤ u :=
    (criticalFineBalanceCoverDensityUpper_mem_Ioo hk).1.le
  have hu1 : u ≤ 1 :=
    (criticalFineBalanceCoverDensityUpper_mem_Ioo hk).2.le
  have hfactorOne : 0 ≤ 1 - d := by linarith
  have hfactorTwo : 0 ≤ 1 - 2 * d := by linarith
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hqCast : (q : ℝ) = (n : ℝ) - (s : ℝ) := by
    dsimp [q]
    rw [Nat.cast_sub hs]
  have hqLower : (1 - d) * (n : ℝ) ≤ (q : ℝ) := by
    rw [hqCast]
    nlinarith
  have hqPredLower : (1 - 2 * d) * (n : ℝ) ≤ (q : ℝ) - 1 := by
    rw [hqCast]
    nlinarith
  have hproductLower :
      ((1 - d) * (n : ℝ)) * ((1 - 2 * d) * (n : ℝ)) ≤
        (q : ℝ) * ((q : ℝ) - 1) := by
    exact mul_le_mul hqLower hqPredLower
      (mul_nonneg hfactorTwo hn0) (by positivity)
  have hscalar : g ≤ u * (1 - d) * (1 - 2 * d) := by
    simpa [g, u, d] using criticalFineBalance_coverDensity_scalar_le hk
  have hscaled :
      g * (n : ℝ) ^ 2 ≤
        u * (((1 - d) * (n : ℝ)) * ((1 - 2 * d) * (n : ℝ))) := by
    have h := mul_le_mul_of_nonneg_right hscalar (sq_nonneg (n : ℝ))
    nlinarith
  have hchooseScale :
      g * (completeEdgeCount n : ℝ) ≤
        u * (completeEdgeCount q : ℝ) := by
    simp only [completeEdgeCount, Nat.cast_choose_two]
    calc
      g * ((n : ℝ) * ((n : ℝ) - 1) / 2) ≤
          g * ((n : ℝ) ^ 2 / 2) := by
        apply mul_le_mul_of_nonneg_left _ hg0
        nlinarith
      _ ≤ u *
          ((((1 - d) * (n : ℝ)) * ((1 - 2 * d) * (n : ℝ))) / 2) := by
        nlinarith
      _ ≤ u * ((q : ℝ) * ((q : ℝ) - 1) / 2) := by
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hproductLower (by norm_num)) hu0
  have hmEdge : m ≤ criticalEdgeCount k n := by
    dsimp [m]
    omega
  have hmUpper : (m : ℝ) ≤ u * (completeEdgeCount q : ℝ) := by
    calc
      (m : ℝ) ≤ (criticalEdgeCount k n : ℝ) := by exact_mod_cast hmEdge
      _ ≤ g * (completeEdgeCount n : ℝ) := by
        simpa [g] using criticalEdgeCount_cast_le hk n
      _ ≤ u * (completeEdgeCount q : ℝ) := hchooseScale
  have hcrossNat : 0 < supercriticalTotalCrossCapacity D :=
    supercriticalTotalCrossCapacity_pos hk D
  have hsum := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hbalanced.1] at hsum
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  have hcompletePos : (0 : ℝ) < completeEdgeCount q := by
    have hnat : 0 < completeEdgeCount q := by
      have hcrossLe : supercriticalTotalCrossCapacity D ≤ Nat.choose q 2 := by
        dsimp [q]
        omega
      simpa [completeEdgeCount] using hcrossNat.trans_le hcrossLe
    exact_mod_cast hnat
  have hmCompleteReal : (m : ℝ) ≤ completeEdgeCount q := by
    exact hmUpper.trans (mul_le_of_le_one_left (by positivity) hu1)
  have hmComplete : m ≤ completeEdgeCount q := by
    exact_mod_cast hmCompleteReal
  by_cases hinternal : divisionInternalCliqueCapacity D ≤ m
  · have htotal := coPartiteFiber_crossDensity_le_totalDensity
      D hbalanced.1 hinternal hcrossNat hmComplete
    have hmDensity : (m : ℝ) / (completeEdgeCount q : ℝ) ≤ u := by
      exact (div_le_iff₀ hcompletePos).2 hmUpper
    change ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
        (supercriticalTotalCrossCapacity D : ℝ) ≤ u
    exact htotal.trans hmDensity
  · have hzero : m - divisionInternalCliqueCapacity D = 0 :=
      Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hinternal)
    change ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
        (supercriticalTotalCrossCapacity D : ℝ) ≤ u
    rw [hzero, Nat.cast_zero, zero_div]
    exact hu0

/-- Uniform compact upper density for every balanced full retained-core
division.  The existential rate and sparse radius depend only on `k`; the
eventual assertion is simultaneous in `s`, `t`, and the displayed division. -/
theorem eventually_criticalSmallDeletion_balancedFullDivision_crossDensity_le
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
        (s : ℝ) ≤ delta * (n : ℝ) →
        ∀ t : ℕ, t ≤ Nat.choose s 2 →
          ∀ D : SupercriticalDivision k (Fin (n - s)),
            IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
            ((criticalEdgeCount k n - t -
                  divisionInternalCliqueCapacity D : ℕ) : ℝ) /
                (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c) := by
  refine ⟨criticalFineBalanceCoverLogRate k,
    criticalFineBalanceCoverLogRate_pos hk,
    criticalFineBalanceSparseFraction k,
    criticalFineBalanceSparseFraction_pos hk, ?_⟩
  have htend : Tendsto
      (fun n : ℕ ↦ criticalFineBalanceSparseFraction k * (n : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop
      (criticalFineBalanceSparseFraction_pos hk)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      1 ≤ criticalFineBalanceSparseFraction k * (n : ℝ) :=
    htend.eventually (eventually_ge_atTop 1)
  filter_upwards [hlarge] with n hnLarge
  intro s hs hsSmall t ht D hbalanced
  rw [exp_neg_criticalFineBalanceCoverLogRate hk]
  exact criticalSmallDeletion_balancedFullDivision_crossDensity_le
    hk hs hsSmall hnLarge ht D hbalanced

end InducedStars
