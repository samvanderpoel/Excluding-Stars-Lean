import InducedStars.Structure.Supercritical.GlobalAggregation
import InducedStars.Structure.Supercritical.AbsorptionPreimages
import Mathlib.Tactic

/-!
# Global aggregation of the clean sparse branch

This file groups the repaired whole clean-family comparison by sparse size
and absorbed full division.  The grouping is exact; the only multiplicity is
the finite absorption-preimage count.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

attribute [local instance] graphFamiliesEdgeSetFintype

noncomputable local instance cleanGlobalDivisionDecidableEq (k n : ℕ) :
    DecidableEq (SupercriticalDivision k (Fin n)) := Classical.decEq _

noncomputable local instance cleanGlobalGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-- Absorbing a sparse set into one balanced part preserves balance after
doubling the radius. -/
theorem isBalancedFullDivision_absorbSparse
    {k n : ℕ} (hk : 3 ≤ k) (D : SupercriticalDivision k (Fin n))
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ delta * n / 2) :
    IsBalancedFullDivision
      (supercriticalAbsorbSparseDivision hk D) (2 * delta) := by
  refine ⟨D.absorbSparse_isFull hk, ?_⟩
  intro i
  by_cases hi : i = supercriticalSmallestPartIndex hk D
  · subst i
    rw [supercriticalAbsorbSparseDivision_part_smallest_card, Nat.cast_add]
    have hs0 : (0 : ℝ) ≤ D.sparse.card := by positivity
    have habs := hbalanced (supercriticalSmallestPartIndex hk D)
    calc
      |((D.parts (supercriticalSmallestPartIndex hk D)).card : ℝ) +
          (D.sparse.card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤
          |((D.parts (supercriticalSmallestPartIndex hk D)).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| +
            (D.sparse.card : ℝ) := by
              rw [show ((D.parts
                (supercriticalSmallestPartIndex hk D)).card : ℝ) +
                  (D.sparse.card : ℝ) -
                  (n : ℝ) / ((k - 1 : ℕ) : ℝ) =
                (((D.parts
                  (supercriticalSmallestPartIndex hk D)).card : ℝ) -
                  (n : ℝ) / ((k - 1 : ℕ) : ℝ)) +
                    (D.sparse.card : ℝ) by ring]
              exact (abs_add_le _ _).trans
                (add_le_add_right (abs_of_nonneg hs0).le _)
      _ ≤ (2 * delta) * n := by nlinarith
  · rw [supercriticalAbsorbSparseDivision_part_card_of_ne hk D hi]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have := hbalanced i
    nlinarith

/-- A nonempty clean canonical fiber receives the repaired joint-absorption
penalty and its absorbed full division is balanced. -/
theorem supercriticalCleanDivision_card_le_fiber_and_balanced
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (n m : ℕ)
    (hnLarge : supercriticalCloseStructureVertexThreshold k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (hDnonempty : (supercriticalCleanDivisionGraphFinset
      k hk gamma P.density_mem m n P.tau
        ((supercriticalCloseStructureVertexThreshold_large k hk gamma
          P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
            P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
              P.epsilon_pos).trans hnLarge) D).Nonempty) :
    IsBalancedFullDivision (supercriticalAbsorbSparseDivision hk D)
        (2 * P.delta) ∧
      ((supercriticalCleanDivisionGraphFinset
        k hk gamma P.density_mem m n P.tau
          ((supercriticalCloseStructureVertexThreshold_large k hk gamma
            P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
              P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
                P.epsilon_pos).trans hnLarge) D).card : ℝ) ≤
        (supercriticalCoPartiteFiber
          (supercriticalAbsorbSparseDivision hk D) m).card *
          Real.exp (-(P.cAbs * (D.sparse.card : ℝ) * n)) := by
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos).trans hnLarge
  obtain ⟨G, hG⟩ := hDnonempty
  have hGclose := (mem_supercriticalCleanDivisionGraphFinset.mp hG).1
  have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
      supercriticalFarGraphFinset k hk gamma P.density_mem m n P.tau := by
    rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hGclose
  obtain ⟨R⟩ := superCloseStructureK1k k hk gamma P.density_mem
    P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
        m hnLarge G (by simpa [P.tau_eq] using hfamily)
  have hdivision :=
    (mem_supercriticalCleanDivisionGraphFinset.mp hG).2.1
  have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n := by
    intro i
    simpa only [hdivision, hcastSub] using R.part_card_close i
  have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
    simpa only [hdivision] using R.sparse_card_le
  refine ⟨isBalancedFullDivision_absorbSparse hk D P.delta_pos.le
    hbalanced hsparse, ?_⟩
  let profile := crossEdgeProfile G D
  let t := inducedEdgeCount G D.sparse
  have hdensity : ∀ e : SupercriticalPartPair k,
      supercriticalOffDiagonal k gamma - P.delta ≤
          profileDensity profile e ∧
        profileDensity profile e ≤
          supercriticalOffDiagonal k gamma + P.delta := by
    intro e
    have hcloseDensity := R.cross_density_close
      e.left e.right e.left_ne_right
    have habs :
        |profileDensity profile e - supercriticalOffDiagonal k gamma| ≤
          P.delta := by
      dsimp [profile]
      rw [profileDensity_crossEdgeProfile]
      simpa only [hdivision] using hcloseDensity
    rw [abs_le] at habs
    exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) P.delta (t : ℤ) profile := by
    dsimp [profile, t]
    exact crossEdgeProfile_atShift_inducedEdgeCount_of_mem_clean hG hdensity
  have ht : t ≤ Nat.choose D.sparse.card 2 := by
    have hsum := inducedEdgeCount_add_compl G D.sparse
    dsimp [t]
    omega
  simpa [P.cAbs_eq, supercriticalAbsorbedCoPartiteGraphFinset_eq_fiber]
    using card_supercriticalCleanDivisionGraphFinset_le_absorbedCoPartite
      hk hgamma P.delta_pos.le P.joint_absorption_delta D hbalanced
        hsparse profile hprofile ht hn

/-! ## Exact grouping by absorption fibers -/

/-- Divisions which actually occur in the clean comparison and whose
absorbed cover has the prescribed balance radius. -/
noncomputable def supercriticalCleanActiveDivisions
    (k n : ℕ) (hk : 3 ≤ k) (beta : ℝ) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦
    D.sparse.Nonempty ∧
      IsBalancedFullDivision (supercriticalAbsorbSparseDivision hk D) beta

@[simp] theorem mem_supercriticalCleanActiveDivisions
    {k n : ℕ} {hk : 3 ≤ k} {beta : ℝ}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ supercriticalCleanActiveDivisions k n hk beta ↔
      D.sparse.Nonempty ∧
        IsBalancedFullDivision
          (supercriticalAbsorbSparseDivision hk D) beta := by
  simp [supercriticalCleanActiveDivisions]

/-- The real clean total is bounded by the exact sum grouped by sparse size
and absorbed balanced cover.  This is the finite bookkeeping step preceding
the exponential and unique-cover estimates. -/
theorem supercriticalCleanTotal_le_groupedAbsorptionSum
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (n m : ℕ)
    (hnLarge : supercriticalCloseStructureVertexThreshold k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos ≤ n) :
    (supercriticalCleanTotal k hk gamma P.density_mem m n P.tau : ℝ) ≤
      ∑ s ∈ Finset.Icc 1 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(P.cAbs * (s : ℝ) * n)) := by
  classical
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos).trans hnLarge
  let active := supercriticalCleanActiveDivisions
    k n hk (2 * P.delta)
  let encode : SupercriticalDivision k (Fin n) →
      ℕ × SupercriticalDivision k (Fin n) := fun D ↦
    (D.sparse.card, supercriticalAbsorbSparseDivision hk D)
  let targets : Finset (ℕ × SupercriticalDivision k (Fin n)) :=
    Finset.Icc 1 n ×ˢ
      balancedFullSupercriticalDivisions k n (2 * P.delta)
  let targetWeight : ℕ × SupercriticalDivision k (Fin n) → ℝ :=
    fun p ↦ (supercriticalCoPartiteFiber p.2 m).card *
      Real.exp (-(P.cAbs * (p.1 : ℝ) * n))
  have hfirst :
      (supercriticalCleanTotal k hk gamma P.density_mem m n P.tau : ℝ) ≤
        ∑ D ∈ active, targetWeight (encode D) := by
    rw [supercriticalCleanTotal, dif_pos hn, Nat.cast_sum]
    calc
      (∑ D ∈ allSupercriticalDivisions k n,
          ((if D.sparse.Nonempty then
              (supercriticalCleanDivisionGraphFinset
                k hk gamma P.density_mem m n P.tau hn D).card
            else 0 : ℕ) : ℝ)) ≤
          ∑ D ∈ allSupercriticalDivisions k n,
            if D ∈ active then targetWeight (encode D) else 0 := by
        apply Finset.sum_le_sum
        intro D _hD
        by_cases hs : D.sparse.Nonempty
        · rw [if_pos hs]
          let F := supercriticalCleanDivisionGraphFinset
            k hk gamma P.density_mem m n P.tau hn D
          by_cases hF : F.Nonempty
          · have H := supercriticalCleanDivision_card_le_fiber_and_balanced
              k hk gamma hgamma P n m hnLarge D (by simpa [F] using hF)
            have hactive : D ∈ active := by
              rw [show active = supercriticalCleanActiveDivisions
                k n hk (2 * P.delta) by rfl,
                mem_supercriticalCleanActiveDivisions]
              exact ⟨hs, H.1⟩
            rw [if_pos hactive]
            simpa [F, targetWeight, encode] using H.2
          · have hFzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
            have hcardzero :
                ((supercriticalCleanDivisionGraphFinset
                  k hk gamma P.density_mem m n P.tau hn D).card : ℝ) = 0 := by
              simp [F, hFzero]
            rw [hcardzero]
            positivity
        · rw [if_neg hs]
          have hnotActive : D ∉ active := by
            intro hactive
            exact hs (mem_supercriticalCleanActiveDivisions.mp hactive).1
          rw [if_neg hnotActive]
          norm_num
      _ = ∑ D ∈ active, targetWeight (encode D) := by
        rw [← Finset.sum_filter]
        simp [active, supercriticalCleanActiveDivisions]
  have hmaps : ∀ D ∈ active, encode D ∈ targets := by
    intro D hD
    have hactive := mem_supercriticalCleanActiveDivisions.mp hD
    rw [Finset.mem_product]
    refine ⟨Finset.mem_Icc.mpr ⟨hactive.1.card_pos, ?_⟩, ?_⟩
    · simpa using Finset.card_le_univ D.sparse
    · exact mem_balancedFullSupercriticalDivisions.mpr hactive.2
  have hregroup :
      (∑ D ∈ active, targetWeight (encode D)) =
        ∑ p ∈ targets, ∑ D ∈ active with encode D = p, targetWeight p := by
    exact (Finset.sum_fiberwise_of_maps_to' hmaps targetWeight).symm
  rw [hregroup] at hfirst
  refine hfirst.trans ?_
  rw [show targets = Finset.Icc 1 n ×ˢ
      balancedFullSupercriticalDivisions k n (2 * P.delta) by rfl,
    Finset.sum_product]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro E hE
  let localFiber := active.filter fun D ↦ encode D = (s, E)
  have hlocalSubset : localFiber ⊆
      supercriticalAbsorptionPreimageFinset hk E s := by
    intro D hD
    have hdata := Finset.mem_filter.mp hD
    have heq := hdata.2
    rw [mem_supercriticalAbsorptionPreimageFinset]
    exact ⟨congrArg Prod.fst heq,
      congrArg Prod.snd heq⟩
  have hcard : localFiber.card ≤
      (supercriticalAbsorptionPreimageFinset hk E s).card :=
    Finset.card_le_card hlocalSubset
  have hnonneg : 0 ≤ targetWeight (s, E) := by
    dsimp [targetWeight]
    positivity
  have hcastCard : (localFiber.card : ℝ) ≤
      (supercriticalAbsorptionPreimageFinset hk E s).card := by
    exact_mod_cast hcard
  have hmul := mul_le_mul_of_nonneg_right hcastCard hnonneg
  simpa [localFiber, targetWeight, encode, mul_assoc] using hmul

/-- Applying the sharp preimage count separates the sparse-size sum from
the balanced-cover pair sum. -/
theorem supercriticalGroupedAbsorptionSum_le_product
    (k n m : ℕ) (hk : 3 ≤ k) (beta c : ℝ) :
    (∑ s ∈ Finset.Icc 1 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(c * (s : ℝ) * n))) ≤
      (∑ s ∈ Finset.Icc 1 n,
        (((k - 1) * n.choose s : ℕ) : ℝ) *
          Real.exp (-(c * (s : ℝ) * n))) *
      (∑ E ∈ balancedFullSupercriticalDivisions k n beta,
        ((supercriticalCoPartiteFiber E m).card : ℝ)) := by
  calc
    (∑ s ∈ Finset.Icc 1 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(c * (s : ℝ) * n))) ≤
      ∑ s ∈ Finset.Icc 1 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(c * (s : ℝ) * n)) := by
        apply Finset.sum_le_sum
        intro s _hs
        apply Finset.sum_le_sum
        intro E _hE
        have hcard := card_supercriticalAbsorptionPreimageFinset_le hk E s
        have hcast :
            ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) ≤
              ((k - 1) * n.choose s : ℕ) := by exact_mod_cast hcard
        gcongr
    _ = (∑ s ∈ Finset.Icc 1 n,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * n))) *
        (∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalCoPartiteFiber E m).card : ℝ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _hE
      ring

/-- Enlarging a nonnegative balance radius only enlarges the corresponding
sum of full-cover fibers. -/
theorem sum_supercriticalCoPartiteFiber_mono_balance
    (k n m : ℕ) {beta beta' : ℝ} (hbeta : beta ≤ beta') :
    (∑ D ∈ balancedFullSupercriticalDivisions k n beta,
        ((supercriticalCoPartiteFiber D m).card : ℝ)) ≤
      ∑ D ∈ balancedFullSupercriticalDivisions k n beta',
        ((supercriticalCoPartiteFiber D m).card : ℝ) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro D hD
    have H := mem_balancedFullSupercriticalDivisions.mp hD
    rw [mem_balancedFullSupercriticalDivisions]
    refine ⟨H.1, ?_⟩
    intro i
    exact H.2 i |>.trans <|
      mul_le_mul_of_nonneg_right hbeta (by positivity)
  · intro D _hD _hnot
    positivity

/-- Every Goal-7e parameter package makes the absorbed balance radius much
smaller than the fixed radius used in the cover-uniqueness theorem. -/
theorem two_mul_delta_lt_supercriticalCoverBalanceRadius
    {k : ℕ} {gamma : ℝ}
    (P : SupercriticalAggregationParameters k gamma) :
    2 * P.delta < supercriticalCoverBalanceRadius k := by
  have hk : 3 ≤ k := P.rank
  have hkReal : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrReal : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hrLeK : (((k - 1 : ℕ) : ℝ)) ≤ (k : ℝ) := by
    exact_mod_cast Nat.sub_le k 1
  have hdeltaAlpha : P.delta < P.alpha / 100 := P.delta_lt_alpha
  have halpha := P.alpha_lt
  have hscaledAlpha : (k : ℝ) * P.alpha < 1 / 100 := by
    have hmul := mul_lt_mul_of_pos_left halpha hkReal
    calc
      (k : ℝ) * P.alpha <
          (k : ℝ) * (1 / (100 * (k : ℝ))) := hmul
      _ = 1 / 100 := by
        field_simp [ne_of_gt hkReal]
  have hscaledDelta :
      16 * (((k - 1 : ℕ) : ℝ)) * P.delta < 1 := by
    have hscalePos :
        0 < (16 : ℝ) * (((k - 1 : ℕ) : ℝ)) :=
      mul_pos (by norm_num) hrReal
    have hmulDelta := mul_lt_mul_of_pos_left hdeltaAlpha
      hscalePos
    have hpart :
        16 * (((k - 1 : ℕ) : ℝ)) * (P.alpha / 100) ≤
          16 * (k : ℝ) * (P.alpha / 100) := by
      gcongr
      exact div_nonneg P.alpha_pos.le (by norm_num)
    have hfinal : 16 * (k : ℝ) * (P.alpha / 100) < 1 := by
      nlinarith [hscaledAlpha]
    exact hmulDelta.trans (hpart.trans_lt hfinal)
  rw [supercriticalCoverBalanceRadius]
  apply (lt_div_iff₀ (mul_pos (by norm_num) hrReal)).2
  nlinarith

/-- The global clean nonempty-sparse contribution has a uniform linear
exponential penalty relative to the exact co-multipartite count.  The rate
is deliberately recorded explicitly: the sparse-size summation spends three
quarters of the joint-absorption rate, and the fixed ordered-cover
multiplicity spends half of what remains. -/
theorem eventually_supercriticalCleanTotal_le
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (supercriticalCleanTotal k hk gamma P.density_mem
        (m n) n P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          Real.exp (-((P.cAbs / 8) * (n : ℝ))) := by
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma
    P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  have hbeta : 2 * P.delta ≤ supercriticalCoverBalanceRadius k :=
    (two_mul_delta_lt_supercriticalCoverBalanceRadius P).le
  have hcQuarter : 0 < P.cAbs / 4 := div_pos P.cAbs_pos (by norm_num)
  filter_upwards
      [Filter.eventually_ge_atTop nClose,
       DenseGraph.eventually_sum_mul_choose_mul_exp_neg_le
        (k - 1) P.cAbs_pos,
       eventually_edgeDensity_error_lt hm
        (supercriticalCoverDensityTolerance_pos hgamma.2),
       eventually_card_balancedCoMultipartiteCoverPairFinset_le
        hk gamma hgamma,
       eventually_natCast_mul_exp_neg_linear_le
        (2 * (k - 1).factorial) hcQuarter]
      with n hnClose hsparse hdensity hcover hconstant
  let sparseSum : ℝ :=
    ∑ s ∈ Finset.Icc 1 n,
      (((k - 1) * n.choose s : ℕ) : ℝ) *
        Real.exp (-(P.cAbs * (s : ℝ) * (n : ℝ)))
  let smallCoverSum : ℝ :=
    ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
      ((supercriticalCoPartiteFiber E (m n)).card : ℝ)
  let coverSum : ℝ :=
    ∑ E ∈ balancedFullSupercriticalDivisions k n
        (supercriticalCoverBalanceRadius k),
      ((supercriticalCoPartiteFiber E (m n)).card : ℝ)
  let good : ℝ :=
    coMultipartiteGraphCountWithEdges (k - 1) n (m n)
  have hsparse' : sparseSum ≤
      Real.exp (-((P.cAbs / 4) * (n : ℝ))) := by
    simpa [sparseSum] using hsparse
  have hsmallCover : smallCoverSum ≤ coverSum := by
    simpa [smallCoverSum, coverSum] using
      sum_supercriticalCoPartiteFiber_mono_balance
        k n (m n) hbeta
  have hcoverSum : coverSum =
      ((balancedCoMultipartiteCoverPairFinset k n (m n)
        (supercriticalCoverBalanceRadius k)).card : ℝ) := by
    dsimp [coverSum]
    rw [← Nat.cast_sum,
      ← card_balancedCoMultipartiteCoverPairFinset]
  have hcover' : coverSum ≤
      (2 * (k - 1).factorial : ℕ) * good := by
    rw [hcoverSum]
    simpa [good] using hcover (m n) hdensity
  have hsparseNonneg : 0 ≤ sparseSum := by
    dsimp [sparseSum]
    exact Finset.sum_nonneg fun s _hs ↦
      mul_nonneg (by positivity) (Real.exp_pos _).le
  have hcoverNonneg : 0 ≤ coverSum := by
    dsimp [coverSum]
    exact Finset.sum_nonneg fun E _hE ↦ by positivity
  have hgoodNonneg : 0 ≤ good := by
    dsimp [good]
    exact Nat.cast_nonneg _
  have hconstant' :
      ((2 * (k - 1).factorial : ℕ) : ℝ) *
          Real.exp (-((P.cAbs / 4) * (n : ℝ))) ≤
        Real.exp (-((P.cAbs / 8) * (n : ℝ))) := by
    convert hconstant using 1 <;> ring
  calc
    (supercriticalCleanTotal k hk gamma P.density_mem
        (m n) n P.tau : ℝ) ≤
        ∑ s ∈ Finset.Icc 1 n,
          ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
            ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
              (supercriticalCoPartiteFiber E (m n)).card *
                Real.exp (-(P.cAbs * (s : ℝ) * n)) :=
      supercriticalCleanTotal_le_groupedAbsorptionSum
        k hk gamma hgamma P n (m n) hnClose
    _ ≤ sparseSum * smallCoverSum := by
      simpa [sparseSum, smallCoverSum] using
        supercriticalGroupedAbsorptionSum_le_product
          k n (m n) hk (2 * P.delta) P.cAbs
    _ ≤ sparseSum * coverSum :=
      mul_le_mul_of_nonneg_left hsmallCover hsparseNonneg
    _ ≤ Real.exp (-((P.cAbs / 4) * (n : ℝ))) *
          ((2 * (k - 1).factorial : ℕ) : ℝ) * good := by
      calc
        sparseSum * coverSum ≤
            Real.exp (-((P.cAbs / 4) * (n : ℝ))) * coverSum :=
          mul_le_mul_of_nonneg_right hsparse' hcoverNonneg
        _ ≤ Real.exp (-((P.cAbs / 4) * (n : ℝ))) *
            (((2 * (k - 1).factorial : ℕ) : ℝ) * good) :=
          mul_le_mul_of_nonneg_left hcover' (Real.exp_nonneg _)
        _ = Real.exp (-((P.cAbs / 4) * (n : ℝ))) *
            ((2 * (k - 1).factorial : ℕ) : ℝ) * good := by ring
    _ = good *
        (((2 * (k - 1).factorial : ℕ) : ℝ) *
          Real.exp (-((P.cAbs / 4) * (n : ℝ)))) := by ring
    _ ≤ good * Real.exp (-((P.cAbs / 8) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hconstant' hgoodNonneg
    _ = (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
        Real.exp (-((P.cAbs / 8) * (n : ℝ))) := by rfl

end InducedStars
