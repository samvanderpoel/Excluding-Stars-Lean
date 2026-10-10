import InducedStars.Structure.Supercritical.CleanGlobalAggregation
import InducedStars.Structure.Supercritical.FixedDivisionTotal

/-!
# Global aggregation of the supercritical fixed-defect family

This module groups the divisionwise matching-defect estimate first by sparse
size and then by the full division obtained by sparse absorption.  The sharp
absorption-preimage bound pays for the first grouping, while the balanced
cover-pair estimate compares the second grouping with the exact global
co-multipartite family.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

set_option maxHeartbeats 800000 in
-- The nested finite regrouping and close-structure transport are expensive to elaborate.
/-- Divisions whose fixed-defect contribution is genuinely nonempty. -/
noncomputable def supercriticalFixedActiveDivisions
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact (allSupercriticalDivisions k n).filter fun D ↦
    ∃ T ∈ supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D,
      (supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).Nonempty

@[simp] theorem mem_supercriticalFixedActiveDivisions
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ supercriticalFixedActiveDivisions
        k hk gamma hgamma alpha m n tau hn ↔
      ∃ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D T).Nonempty := by
  classical
  simp [supercriticalFixedActiveDivisions]

/-! ## Exact grouping by sparse absorption -/

/-- A uniform divisionwise estimate can be regrouped exactly by sparse size
and absorbed balanced full division.  Close structure is used only to show
that every nonzero summand satisfies the two geometric hypotheses of the
divisionwise estimate. -/
theorem supercriticalFixedDefectTotal_le_groupedAbsorptionSum_of_divisionPenalty
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (n m : ℕ)
    (hnClose : supercriticalCloseStructureVertexThreshold k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos ≤ n)
    (hdivisionPenalty : ∀ D : SupercriticalDivision k (Fin n),
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      ((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m n P.tau
            ((supercriticalCloseStructureVertexThreshold_large k hk gamma
              P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
                P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
                  P.epsilon_pos).trans hnClose) D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha m n P.tau
            ((supercriticalCloseStructureVertexThreshold_large k hk gamma
              P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
                P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
                  P.epsilon_pos).trans hnClose) D T).card : ℕ) : ℝ) ≤
        ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
          Real.exp (-(P.linearRate * (n : ℝ)) -
            (P.cAbs / 2) * (D.sparse.card : ℝ) * (n : ℝ))) :
    (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
      m n P.tau : ℝ) ≤
      ∑ s ∈ Finset.Icc 0 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(P.linearRate * (n : ℝ)) -
                (P.cAbs / 2) * (s : ℝ) * (n : ℝ)) := by
  classical
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos).trans hnClose
  let active := supercriticalFixedActiveDivisions
    k hk gamma P.density_mem P.alpha m n P.tau hn
  let encode : SupercriticalDivision k (Fin n) →
      ℕ × SupercriticalDivision k (Fin n) := fun D ↦
    (D.sparse.card, supercriticalAbsorbSparseDivision hk D)
  let targets : Finset (ℕ × SupercriticalDivision k (Fin n)) :=
    Finset.Icc 0 n ×ˢ
      balancedFullSupercriticalDivisions k n (2 * P.delta)
  let targetWeight : ℕ × SupercriticalDivision k (Fin n) → ℝ :=
    fun p ↦ (supercriticalCoPartiteFiber p.2 m).card *
      Real.exp (-(P.linearRate * (n : ℝ)) -
        (P.cAbs / 2) * (p.1 : ℝ) * (n : ℝ))
  have hactiveBound (D : SupercriticalDivision k (Fin n))
      (hD : D ∈ active) :
      IsBalancedFullDivision (supercriticalAbsorbSparseDivision hk D)
          (2 * P.delta) ∧
        (((∑ T ∈ supercriticalCombinedDefectPatternFinset
            k hk gamma P.density_mem m n P.tau hn D,
          (supercriticalFixedDefectGraphFinset
            k hk gamma P.density_mem P.alpha m n P.tau hn D T).card : ℕ) : ℝ) ≤
          targetWeight (encode D)) := by
    have hmem : D ∈ supercriticalFixedActiveDivisions
        k hk gamma P.density_mem P.alpha m n P.tau hn := by
      simpa [active] using hD
    obtain ⟨T, hT, G, hG⟩ :=
      mem_supercriticalFixedActiveDivisions.mp hmem
    have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hG).1
    have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
    have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
        supercriticalFarGraphFinset k hk gamma P.density_mem m n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hclose
    obtain ⟨R⟩ := superCloseStructureK1k k hk gamma P.density_mem
      P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
        P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
          m hnClose G (by simpa [P.tau_eq] using hfamily)
    have hdivision :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
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
    simpa [targetWeight, encode,
      supercriticalAbsorbedCoPartiteGraphFinset_eq_fiber] using
        hdivisionPenalty D hbalanced hsparse
  have hfirst :
      (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
          m n P.tau : ℝ) ≤
        ∑ D ∈ active, targetWeight (encode D) := by
    rw [supercriticalFixedDefectTotal, dif_pos hn, Nat.cast_sum]
    calc
      ∑ D ∈ allSupercriticalDivisions k n,
          ((∑ T ∈ supercriticalCombinedDefectPatternFinset
              k hk gamma P.density_mem m n P.tau hn D,
            (supercriticalFixedDefectGraphFinset
              k hk gamma P.density_mem P.alpha m n P.tau hn D T).card : ℕ) : ℝ) ≤
          ∑ D ∈ allSupercriticalDivisions k n,
            if D ∈ active then targetWeight (encode D) else 0 := by
        apply Finset.sum_le_sum
        intro D hDall
        by_cases hD : D ∈ active
        · rw [if_pos hD]
          exact (hactiveBound D hD).2
        · rw [if_neg hD]
          have hempty (T : SimpleGraph (Fin n))
              (hT : T ∈ supercriticalCombinedDefectPatternFinset
                k hk gamma P.density_mem m n P.tau hn D) :
              supercriticalFixedDefectGraphFinset
                k hk gamma P.density_mem P.alpha m n P.tau hn D T = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro hne
            apply hD
            rw [show active = supercriticalFixedActiveDivisions
              k hk gamma P.density_mem P.alpha m n P.tau hn by rfl,
              mem_supercriticalFixedActiveDivisions]
            exact ⟨T, hT, hne⟩
          have hzero :
              ∑ T ∈ supercriticalCombinedDefectPatternFinset
                  k hk gamma P.density_mem m n P.tau hn D,
                (supercriticalFixedDefectGraphFinset
                  k hk gamma P.density_mem P.alpha m n P.tau hn D T).card = 0 := by
            apply Finset.sum_eq_zero
            intro T hT
            simp [hempty T hT]
          rw [hzero, Nat.cast_zero]
      _ = ∑ D ∈ active, targetWeight (encode D) := by
        rw [← Finset.sum_filter]
        simp [active, supercriticalFixedActiveDivisions]
  have hmaps : ∀ D ∈ active, encode D ∈ targets := by
    intro D hD
    rw [Finset.mem_product]
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
    · simpa using Finset.card_le_univ D.sparse
    · exact mem_balancedFullSupercriticalDivisions.mpr (hactiveBound D hD).1
  have hregroup :
      (∑ D ∈ active, targetWeight (encode D)) =
        ∑ p ∈ targets,
          ∑ D ∈ active with encode D = p, targetWeight p := by
    exact (Finset.sum_fiberwise_of_maps_to' hmaps targetWeight).symm
  rw [hregroup] at hfirst
  refine hfirst.trans ?_
  rw [show targets = Finset.Icc 0 n ×ˢ
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
    exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
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

/-- The absorption-preimage estimate separates the sparse-size sum from the
balanced full-cover sum, while retaining the common matching penalty. -/
theorem supercriticalFixedGroupedAbsorptionSum_le_product
    (k n m : ℕ) (hk : 3 ≤ k) (beta a c : ℝ) :
    (∑ s ∈ Finset.Icc 0 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(a * (n : ℝ)) -
                c * (s : ℝ) * (n : ℝ))) ≤
      Real.exp (-(a * (n : ℝ))) *
        (∑ s ∈ Finset.Icc 0 n,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ)))) *
        (∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalCoPartiteFiber E m).card : ℝ)) := by
  calc
    (∑ s ∈ Finset.Icc 0 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(a * (n : ℝ)) -
                c * (s : ℝ) * (n : ℝ))) ≤
      ∑ s ∈ Finset.Icc 0 n,
        ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            (supercriticalCoPartiteFiber E m).card *
              Real.exp (-(a * (n : ℝ)) -
                c * (s : ℝ) * (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro s _hs
      apply Finset.sum_le_sum
      intro E _hE
      have hcard := card_supercriticalAbsorptionPreimageFinset_le hk E s
      have hcast :
          ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) ≤
            ((k - 1) * n.choose s : ℕ) := by
        exact_mod_cast hcard
      gcongr
    _ = ∑ s ∈ Finset.Icc 0 n,
        ((((k - 1) * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ)))) *
          (Real.exp (-(a * (n : ℝ))) *
            ∑ E ∈ balancedFullSupercriticalDivisions k n beta,
              ((supercriticalCoPartiteFiber E m).card : ℝ)) := by
      apply Finset.sum_congr rfl
      intro s _hs
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E _hE
      rw [show -(a * (n : ℝ)) - c * (s : ℝ) * (n : ℝ) =
          -(a * (n : ℝ)) + -(c * (s : ℝ) * (n : ℝ)) by ring,
        Real.exp_add]
      ring
    _ = Real.exp (-(a * (n : ℝ))) *
        (∑ s ∈ Finset.Icc 0 n,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ)))) *
        (∑ E ∈ balancedFullSupercriticalDivisions k n beta,
          ((supercriticalCoPartiteFiber E m).card : ℝ)) := by
      rw [← Finset.sum_mul]
      ring

/-! ## The sparse-size sum, including the zero-sparse case -/

/-- The zero-sparse term contributes exactly `k - 1`; every positive sparse
size is exponentially negligible.  This is the reason the divisionwise
matching penalty survives global absorption grouping with only a fixed
multiplicity loss. -/
theorem eventually_supercriticalFixedSparseSum_le
    (k : ℕ) (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (∑ s ∈ Finset.Icc 0 n,
          (((k - 1) * n.choose s : ℕ) : ℝ) *
            Real.exp (-(c * (s : ℝ) * (n : ℝ)))) ≤ (k : ℝ) := by
  filter_upwards
      [DenseGraph.eventually_sum_mul_choose_mul_exp_neg_le
        (k - 1) hc]
      with n hpositive
  let f : ℕ → ℝ := fun s ↦
    (((k - 1) * n.choose s : ℕ) : ℝ) *
      Real.exp (-(c * (s : ℝ) * (n : ℝ)))
  have herase : (Finset.Icc 0 n).erase 0 = Finset.Icc 1 n := by
    ext s
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hzero : f 0 = ((k - 1 : ℕ) : ℝ) := by
    simp [f]
  have hexp : Real.exp (-((c / 4) * (n : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hnonneg : 0 ≤ (c / 4) * (n : ℝ) :=
      mul_nonneg (div_nonneg hc.le (by norm_num)) (by positivity)
    linarith
  calc
    (∑ s ∈ Finset.Icc 0 n,
        (((k - 1) * n.choose s : ℕ) : ℝ) *
          Real.exp (-(c * (s : ℝ) * (n : ℝ)))) =
        f 0 + ∑ s ∈ Finset.Icc 1 n, f s := by
      rw [← Finset.sum_erase_add (a := 0) (Finset.Icc 0 n) f (by simp),
        herase, add_comm]
    _ ≤ ((k - 1 : ℕ) : ℝ) + Real.exp (-((c / 4) * (n : ℝ))) := by
      rw [hzero]
      exact add_le_add (le_refl _) hpositive
    _ ≤ ((k - 1 : ℕ) : ℝ) + 1 := add_le_add (le_refl _) hexp
    _ = (k : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      ring

/-! ## The global fixed-defect estimate -/

/-- The global fixed-defect contribution is exponentially smaller than the
exact co-multipartite family.  Sparse absorption removes the exponential
number of ordered divisions; the remaining fixed cover multiplicity costs
only half of the divisionwise linear rate. -/
theorem eventually_supercriticalFixedDefectTotal_le_of_divisionPenalty
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma)
    (hdivisionPenalty : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (m₀ : ℕ) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n)),
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      ((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m₀ n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha m₀ n P.tau hn D T).card : ℕ) : ℝ) ≤
        ((supercriticalAbsorbedCoPartiteGraphFinset hk D m₀).card : ℝ) *
          Real.exp (-(P.linearRate * (n : ℝ)) -
            (P.cAbs / 2) * (D.sparse.card : ℝ) * (n : ℝ))) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
        (m n) n P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          Real.exp (-((P.linearRate / 2) * (n : ℝ))) := by
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma
    P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  have hbeta : 2 * P.delta ≤ supercriticalCoverBalanceRadius k :=
    (two_mul_delta_lt_supercriticalCoverBalanceRadius P).le
  have hcSparse : 0 < P.cAbs / 2 := half_pos P.cAbs_pos
  filter_upwards
      [Filter.eventually_ge_atTop nClose,
       hdivisionPenalty,
       eventually_supercriticalFixedSparseSum_le k hk hcSparse,
       eventually_edgeDensity_error_lt hm
        (supercriticalCoverDensityTolerance_pos hgamma.2),
       eventually_card_balancedCoMultipartiteCoverPairFinset_le
        hk gamma hgamma,
       eventually_natCast_mul_exp_neg_linear_le
        (k * (2 * (k - 1).factorial)) P.linearRate_pos]
      with n hnClose hdivision hsparse hdensity hcover hconstant
  let sparseSum : ℝ :=
    ∑ s ∈ Finset.Icc 0 n,
      (((k - 1) * n.choose s : ℕ) : ℝ) *
        Real.exp (-((P.cAbs / 2) * (s : ℝ) * (n : ℝ)))
  let smallCoverSum : ℝ :=
    ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
      ((supercriticalCoPartiteFiber E (m n)).card : ℝ)
  let coverSum : ℝ :=
    ∑ E ∈ balancedFullSupercriticalDivisions k n
        (supercriticalCoverBalanceRadius k),
      ((supercriticalCoPartiteFiber E (m n)).card : ℝ)
  let good : ℝ :=
    coMultipartiteGraphCountWithEdges (k - 1) n (m n)
  have hsparse' : sparseSum ≤ (k : ℝ) := by
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
      ((k * (2 * (k - 1).factorial) : ℕ) : ℝ) *
          Real.exp (-(P.linearRate * (n : ℝ))) ≤
        Real.exp (-((P.linearRate / 2) * (n : ℝ))) := by
    simpa using hconstant
  have hgrouped :
      (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
        (m n) n P.tau : ℝ) ≤
        Real.exp (-(P.linearRate * (n : ℝ))) *
          sparseSum * smallCoverSum := by
    calc
      (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
          (m n) n P.tau : ℝ) ≤
          ∑ s ∈ Finset.Icc 0 n,
            ∑ E ∈ balancedFullSupercriticalDivisions k n (2 * P.delta),
              ((supercriticalAbsorptionPreimageFinset hk E s).card : ℝ) *
                (supercriticalCoPartiteFiber E (m n)).card *
                  Real.exp (-(P.linearRate * (n : ℝ)) -
                    (P.cAbs / 2) * (s : ℝ) * (n : ℝ)) := by
        apply supercriticalFixedDefectTotal_le_groupedAbsorptionSum_of_divisionPenalty
          k hk gamma hgamma P n (m n) hnClose
        intro D hbalanced hsparseD
        exact hdivision (m n)
          ((supercriticalCloseStructureVertexThreshold_large k hk gamma
            P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
              P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
                P.epsilon_pos).trans hnClose)
          D hbalanced hsparseD
      _ ≤ Real.exp (-(P.linearRate * (n : ℝ))) *
          sparseSum * smallCoverSum := by
        simpa [sparseSum, smallCoverSum] using
          supercriticalFixedGroupedAbsorptionSum_le_product
            k n (m n) hk (2 * P.delta) P.linearRate (P.cAbs / 2)
  calc
    (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
        (m n) n P.tau : ℝ) ≤
        Real.exp (-(P.linearRate * (n : ℝ))) *
          sparseSum * smallCoverSum := hgrouped
    _ ≤ Real.exp (-(P.linearRate * (n : ℝ))) *
          sparseSum * coverSum :=
      mul_le_mul_of_nonneg_left hsmallCover
        (mul_nonneg (Real.exp_nonneg _) hsparseNonneg)
    _ ≤ Real.exp (-(P.linearRate * (n : ℝ))) *
          (k : ℝ) * coverSum :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsparse' (Real.exp_nonneg _))
        hcoverNonneg
    _ ≤ Real.exp (-(P.linearRate * (n : ℝ))) *
          (k : ℝ) *
            (((2 * (k - 1).factorial : ℕ) : ℝ) * good) :=
      mul_le_mul_of_nonneg_left hcover'
        (mul_nonneg (Real.exp_nonneg _) (by positivity))
    _ = good *
        (((k * (2 * (k - 1).factorial) : ℕ) : ℝ) *
          Real.exp (-(P.linearRate * (n : ℝ)))) := by
      push_cast
      ring
    _ ≤ good * Real.exp (-((P.linearRate / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hconstant' hgoodNonneg
    _ = (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
        Real.exp (-((P.linearRate / 2) * (n : ℝ))) := by rfl

/-- Concrete global fixed-defect estimate supplied by the locally proved
divisionwise matching, support-pattern, and shifted-absorption aggregation. -/
theorem eventually_supercriticalFixedDefectTotal_le
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (m : ℕ → ℕ) (hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (supercriticalFixedDefectTotal k hk gamma P.density_mem P.alpha
        (m n) n P.tau : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
          Real.exp (-((P.linearRate / 2) * (n : ℝ))) :=
  eventually_supercriticalFixedDefectTotal_le_of_divisionPenalty
    k hk gamma hgamma P m hm
      (eventually_supercriticalFixedDefectDivisionTotal_le
        k hk gamma hgamma P)

end InducedStars
