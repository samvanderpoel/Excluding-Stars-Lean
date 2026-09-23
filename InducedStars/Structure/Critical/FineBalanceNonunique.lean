import InducedStars.Structure.Critical.FineBalance
import InducedStars.Structure.Critical.FineBalanceCoverDensity
import InducedStars.Structure.Critical.FineBalanceReferenceEntropy
import InducedStars.Structure.Critical.FixedSparseCoverMultiplicity

/-!
# Nonunique-cover error in the critical fixed-support calculation

This file combines the deterministic fixed-support restriction with the
balanced-cover uniqueness estimate.  The resulting bound is uniform over
all sufficiently small prescribed sparse sets and over every prescribed
sparse induced graph.
-/

noncomputable section

open Filter Finset Set Topology
open scoped BigOperators

namespace InducedStars

noncomputable local instance fineBalanceNonuniqueEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance fineBalanceNonuniqueAdjDecidable
    {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-- The normalized retained-support theorem supplies the two natural-number
guards needed to identify selected and missing cross coordinates. -/
theorem eventually_criticalRetainedSupport_edge_guards
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ s : ℕ, s ≤ n →
        (s : ℝ) ≤ delta * (n : ℝ) →
        ∀ t : ℕ, t ≤ Nat.choose s 2 →
          t ≤ criticalEdgeCount k n ∧
          criticalEdgeCount k n - t ≤ Nat.choose (n - s) 2 := by
  let a := criticalReferenceSelectedSquareDensity k
  let b := criticalReferenceCapacitySquareDensity k -
    criticalReferenceSelectedSquareDensity k
  let zeta := min a b / 8
  have ha : 0 < a := criticalReferenceSelectedSquareDensity_pos hk
  have hb : 0 < b := sub_pos.mpr
    (criticalReferenceSelectedSquareDensity_lt_capacity hk)
  have hzeta : 0 < zeta := by
    dsimp [zeta]
    positivity
  have hzetaA : 4 * zeta < a := by
    have hmin := min_le_left a b
    dsimp [zeta]
    nlinarith
  have hzetaB : 4 * zeta < b := by
    have hmin := min_le_right a b
    dsimp [zeta]
    nlinarith
  obtain ⟨delta, hdelta, hnormalized⟩ :=
    eventually_criticalRetainedSupport_normalized_close
      k hk hzeta hzetaA hzetaB
  refine ⟨delta, hdelta, ?_⟩
  filter_upwards [hnormalized] with n hn s hs hsSmall t ht
  obtain ⟨hpositive, hselected, _hcapClose, _hselectedClose⟩ :=
    hn s hs hsSmall t ht
  have htotal := DenseGraph.balancedCross_add_internal
    (k - 1) (n - s)
  constructor
  · unfold criticalRetainedSupportSelectedCount at hpositive
    omega
  · unfold criticalRetainedSupportSelectedCount at hpositive hselected
    unfold criticalRetainedSupportCapacity at hselected
    omega

/-- Casted form of the coarse balanced-pair estimate, with the natural
missing-coordinate expression rewritten to the critical fixed-sparse slice
used by the fine-balance calculation. -/
theorem card_fixedSparseBalancedCleanCoverPairFinset_real_le_poly_mul_balancedMass
    {k n : ℕ} (hk : 3 ≤ k) (S : Finset (Fin n))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (ht : R.edgeFinset.card ≤ criticalEdgeCount k n)
    (hm : criticalEdgeCount k n - R.edgeFinset.card ≤
      Nat.choose (n - S.card) 2) :
    ((fixedSparseBalancedCleanCoverPairFinset k n S
      (supercriticalCoverBalanceRadius k)
      (criticalEdgeCount k n - R.edgeFinset.card) R).card : ℝ) ≤
      (((n - S.card + 1) ^ (k - 1) : ℕ) : ℝ) *
        criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card := by
  have hmissing :
      Nat.choose (n - S.card) 2 -
          (criticalEdgeCount k n - R.edgeFinset.card) =
        criticalFixedSparseCrossMissingCount
          k n S.card R.edgeFinset.card := by
    unfold criticalFixedSparseCrossMissingCount
    omega
  have hnat :=
    card_fixedSparseBalancedCleanCoverPairFinset_le_succ_pow_mul_multinomial_mul_choose_missing
      (m := criticalEdgeCount k n - R.edgeFinset.card)
      hk S (supercriticalCoverBalanceRadius k) R
        (by simpa [fixedSparseCoreCard] using hm)
  rw [show fixedSparseCoreCard S = n - S.card by rfl, hmissing] at hnat
  unfold criticalFixedSparseBalancedCrossSliceMass
  exact_mod_cast hnat

/-- Uniform critical fixed-support nonuniqueness estimate.  Its constants
depend only on `k`; the assertion is simultaneous in the sparse set and in
the entire graph prescribed on that set. -/
theorem eventually_criticalFixedSparseBalancedNonunique_le_balancedMass
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧
      ∀ᶠ n : ℕ in atTop, ∀ S : Finset (Fin n),
        (S.card : ℝ) ≤ delta * (n : ℝ) →
        ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
        ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
          (supercriticalCoverBalanceRadius k)
          (criticalEdgeCount k n - R.edgeFinset.card) R).card : ℝ) ≤
          criticalFixedSparseBalancedCrossSliceMass
              k n S.card R.edgeFinset.card *
            Real.exp (-(c * (n : ℝ))) := by
  obtain ⟨cCover, hcCover, deltaCover, hdeltaCover, hdensity⟩ :=
    eventually_criticalSmallDeletion_balancedFullDivision_crossDensity_le k hk
  obtain ⟨deltaGuard, hdeltaGuard, hguards⟩ :=
    eventually_criticalRetainedSupport_edge_guards k hk
  let delta : ℝ := min deltaCover (min deltaGuard (1 / 2))
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaCoverLe : delta ≤ deltaCover := min_le_left _ _
  have hdeltaGuardLe : delta ≤ deltaGuard :=
    (min_le_right deltaCover _).trans (min_le_left _ _)
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 :=
    (min_le_right deltaCover _).trans (min_le_right _ _)
  let a : ℝ := supercriticalCoverUniquenessRate k cCover
  have ha : 0 < a := supercriticalCoverUniquenessRate_pos hk hcCover
  let c : ℝ := a / 4
  have hc : 0 < c := div_pos ha (by norm_num)
  have hnonunique :=
    eventually_card_fixedSparseBalancedNonunique_le_raw_of_density hk hcCover
  rw [eventually_atTop] at hnonunique
  obtain ⟨q₀, hq₀⟩ := hnonunique
  have habsorb :=
    DenseGraph.eventually_pow_succ_mul_exp_neg_le_of_le_two_mul
      (k - 1) ha
  refine ⟨delta, hdelta, c, hc, ?_⟩
  filter_upwards [hdensity, hguards, habsorb,
    eventually_ge_atTop (2 * q₀)] with n hnDensity hnGuards hnAbsorb hnLarge
  intro S hsSmall R
  have hs : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hsCover : (S.card : ℝ) ≤ deltaCover * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaCoverLe (by positivity))
  have hsGuard : (S.card : ℝ) ≤ deltaGuard * (n : ℝ) :=
    hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaGuardLe (by positivity))
  have hsHalf : (2 * S.card : ℕ) ≤ n := by
    have hsHalfReal : (S.card : ℝ) ≤ (1 / 2 : ℝ) * (n : ℝ) :=
      hsSmall.trans (mul_le_mul_of_nonneg_right hdeltaHalf (by positivity))
    exact_mod_cast (show (2 : ℝ) * S.card ≤ n by nlinarith)
  have ht : R.edgeFinset.card ≤ Nat.choose S.card 2 := by
    simpa using SimpleGraph.card_edgeFinset_le_card_choose_two (G := R)
  obtain ⟨htCritical, hmComplete⟩ := hnGuards S.card hs hsGuard
    R.edgeFinset.card ht
  let q := n - S.card
  have hqDef : fixedSparseCoreCard S = q := by
    rfl
  have hqLe : q ≤ n := Nat.sub_le _ _
  have hnLeTwoQ : n ≤ 2 * q := by
    dsimp [q]
    omega
  have hqLarge : q₀ ≤ q := by
    dsimp [q]
    omega
  have hDensityCore :
      ∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        (((criticalEdgeCount k n - R.edgeFinset.card) -
              divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-cCover) := by
    intro D hD
    exact hnDensity S.card hs hsCover R.edgeFinset.card ht D hD
  have hnon := hq₀ q hqLarge n S hqDef
    (criticalEdgeCount k n - R.edgeFinset.card) hDensityCore R
  have hraw :=
    card_fixedSparseBalancedCleanCoverPairFinset_real_le_poly_mul_balancedMass
      hk S R htCritical hmComplete
  have hpoly := hnAbsorb q hnLeTwoQ hqLe
  change (((q + 1 : ℕ) : ℝ) ^ (k - 1)) *
      Real.exp (-(a * (q : ℝ))) ≤
        Real.exp (-(c * (n : ℝ))) at hpoly
  calc
    ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k)
        (criticalEdgeCount k n - R.edgeFinset.card) R).card : ℝ) ≤
        ((fixedSparseBalancedCleanCoverPairFinset k n S
          (supercriticalCoverBalanceRadius k)
          (criticalEdgeCount k n - R.edgeFinset.card) R).card : ℝ) *
          Real.exp (-(a * (q : ℝ))) := by
      simpa [a] using hnon
    _ ≤ ((((q + 1 : ℕ) : ℝ) ^ (k - 1)) *
          criticalFixedSparseBalancedCrossSliceMass
            k n S.card R.edgeFinset.card) *
          Real.exp (-(a * (q : ℝ))) := by
      apply mul_le_mul_of_nonneg_right
      · simpa [q, Nat.cast_pow] using hraw
      · positivity
    _ = criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card *
        ((((q + 1 : ℕ) : ℝ) ^ (k - 1)) *
          Real.exp (-(a * (q : ℝ)))) := by ring
    _ ≤ criticalFixedSparseBalancedCrossSliceMass
          k n S.card R.edgeFinset.card *
        Real.exp (-(c * (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hpoly (by
        unfold criticalFixedSparseBalancedCrossSliceMass
        positivity)

end InducedStars
