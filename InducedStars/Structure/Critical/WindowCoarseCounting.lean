import InducedStars.Structure.Critical.FixedRemainderTotal
import InducedStars.Structure.Critical.WindowReference
import InducedStars.Structure.Critical.CoPartiteComparison

/-!
# Finite counting for the coarse critical-window tails

Prescribed sparse graphs are summed before divisions. The feasibility guard
is retained throughout, so natural subtraction never contributes a spurious
zero-selected slice.
-/

noncomputable section
open Filter Finset Set
open scoped BigOperators
namespace InducedStars

private instance windowGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-- A guarded convolution over prescribed subsets is bounded by one binomial
slice on the disjoint union of the two coordinate sets. -/
theorem sum_powerset_guarded_choose_le
    {α β : Type*} (A : Finset α) (B : Finset β) (I m : ℕ) :
    (∑ H ∈ B.powerset,
      if I + H.card ≤ m then Nat.choose A.card (m - (I + H.card)) else 0) ≤
        if I ≤ m then Nat.choose (A.card + B.card) (m - I) else 0 := by
  classical
  by_cases hI : I ≤ m
  · rw [ite_eq_left hI]
    let F : Finset (Σ _H : Finset β, Finset α) :=
      B.powerset.sigma fun H ↦
        if I + H.card ≤ m then A.powersetCard (m - (I + H.card)) else ∅
    let f : (Σ _H : Finset β, Finset α) → Finset (α ⊕ β) :=
      fun x ↦ x.2.disjSum x.1
    have hcard : F.card = ∑ H ∈ B.powerset,
        if I + H.card ≤ m then Nat.choose A.card (m - (I + H.card)) else 0 := by
      simp only [F, Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro H _
      split_ifs <;> simp
    rw [← hcard, ← Finset.card_disjSum A B, ← Finset.card_powersetCard]
    apply Finset.card_le_card_of_injOn f
    · intro x hx
      obtain ⟨hH, hX⟩ := Finset.mem_sigma.mp hx
      split_ifs at hX with hfeas
      · obtain ⟨hXA, hXcard⟩ := Finset.mem_powersetCard.mp hX
        apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.disjSum_mono hXA (Finset.mem_powerset.mp hH), ?_⟩
        dsimp [f]
        rw [Finset.card_disjSum, hXcard]
        omega
      · simp at hX
    · intro x _ y _ hxy
      have h := Finset.disjSum_inj.mp hxy
      obtain ⟨H, X⟩ := x
      obtain ⟨J, Y⟩ := y
      dsimp at h
      rcases h with ⟨rfl, rfl⟩
      rfl
  · rw [ite_eq_right hI]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro H _
    rw [ite_eq_right (by omega)]

/-- The prescribed-remainder estimate with its exact forced-edge guard. -/
theorem eventually_criticalFixedRemainderDefect_le_guarded_reference
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)) (H : Finset (Sym2 (Fin n))),
      ((supercriticalFixedRemainderDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          m n P.tau hn D H).card : ℝ) ≤
        (if divisionInternalCliqueCapacity D + H.card ≤ m then
          (Nat.choose (supercriticalTotalCrossCapacity D)
            (m - (divisionInternalCliqueCapacity D + H.card)) : ℝ) else 0) *
              Real.exp (-(P.cMat / 4) * n) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
  filter_upwards [eventually_criticalFixedRemainderDefect_le_reference k hk P,
    eventually_ge_atTop nClose] with n hbound hnClose
  intro m hn D H
  by_cases hfeas : divisionInternalCliqueCapacity D + H.card ≤ m
  · simpa only [ite_eq_left hfeas] using hbound m hn D H
  · have hempty : supercriticalFixedRemainderDefectGraphFinset
        k hk (gammaK k) hgamma m n P.tau hn D H = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro G hG
      obtain ⟨hdef, hH⟩ := mem_supercriticalFixedRemainderDefectGraphFinset.mp hG
      have hdata := mem_supercriticalDivisionDefectGraphFinset.mp hdef
      have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
          supercriticalFarGraphFinset k hk (gammaK k) hgamma m n P.tau := by
        rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
        exact hdata.1
      obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k) hgamma
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            m hnClose G (by simpa [P.tau_eq] using hfamily)
      have hedges : (finiteGraphEdges G).card = m := by
        simpa [finiteGraphEdges] using (mem_supercriticalCloseGraphFinset.mp hdata.1).2.1
      have hband := criticalFixedRemainderReferenceBand_of_close
        hk P G R D hdata.2.1 hedges
      rw [hH] at hband
      exact hfeas hband.1
    rw [ite_eq_right hfeas, hempty]
    simp

/-- Summing over all sparse edge sets leaves the combined-coordinate slice.
This estimate is uniform in the finite exact edge count. -/
theorem eventually_criticalDivisionDefect_le_combined_reference
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)),
      ((supercriticalDivisionDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          m n P.tau hn D).card : ℝ) ≤
        (if divisionInternalCliqueCapacity D ≤ m then
          (Nat.choose (criticalCombinedVariableCapacity D)
            (m - divisionInternalCliqueCapacity D) : ℝ) else 0) *
              Real.exp (-(P.cMat / 4) * n) := by
  classical
  filter_upwards [eventually_criticalFixedRemainderDefect_le_guarded_reference k hk P]
    with n hbound m hn D
  let F := supercriticalDivisionDefectGraphFinset k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) m n P.tau hn D
  let S := supercriticalSparsePotentialEdges D
  have hsplit : F.card =
      ∑ H ∈ S.powerset, (supercriticalFixedRemainderDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          m n P.tau hn D H).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro G _
    exact Finset.mem_powerset.mpr (supercriticalSparseInducedEdges_subset_potential G D)
  have hconv := sum_powerset_guarded_choose_le
    (supercriticalTaggedCrossChoiceUniverse D) S (divisionInternalCliqueCapacity D) m
  dsimp only [S] at hconv
  simp only [card_supercriticalTaggedCrossChoiceUniverse,
    card_supercriticalSparsePotentialEdges_eq_capacity,
    supercriticalSparsePotentialCapacity_eq] at hconv
  have hconvR :
      (∑ H ∈ S.powerset,
        if divisionInternalCliqueCapacity D + H.card ≤ m then
          (Nat.choose (supercriticalTotalCrossCapacity D)
            (m - (divisionInternalCliqueCapacity D + H.card)) : ℝ) else 0) ≤
      if divisionInternalCliqueCapacity D ≤ m then
        (Nat.choose (criticalCombinedVariableCapacity D)
          (m - divisionInternalCliqueCapacity D) : ℝ) else 0 := by
    dsimp [criticalCombinedVariableCapacity]
    exact_mod_cast hconv
  rw [show (supercriticalDivisionDefectGraphFinset k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) m n P.tau hn D).card = F.card from rfl,
    hsplit, Nat.cast_sum]
  calc
    _ ≤ ∑ H ∈ S.powerset,
        (if divisionInternalCliqueCapacity D + H.card ≤ m then
          (Nat.choose (supercriticalTotalCrossCapacity D)
            (m - (divisionInternalCliqueCapacity D + H.card)) : ℝ) else 0) *
              Real.exp (-(P.cMat / 4) * n) :=
      Finset.sum_le_sum (fun H _ ↦ hbound m hn D H)
    _ = _ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hconvR (Real.exp_pos _).le

/-- Balancing the main parts increases a guarded combined slice at a fixed
total edge count. The proof compares the same missing count. -/
theorem criticalCombined_reference_le_balanced
    {k n m : ℕ} (D : SupercriticalDivision k (Fin n)) :
    (if divisionInternalCliqueCapacity D ≤ m then
      Nat.choose (criticalCombinedVariableCapacity D)
        (m - divisionInternalCliqueCapacity D) else 0) ≤
    if criticalWindowCoreInternal k n D.sparse.card ≤ m then
      Nat.choose (criticalMaximumCombinedCapacity k n D.sparse.card)
        (m - criticalWindowCoreInternal k n D.sparse.card) else 0 := by
  have hAB := criticalCombinedVariableCapacity_le_maximum D
  have hactual := criticalCombinedVariableCapacity_add_internal_eq D
  have hbalanced := criticalMaximumCombinedCapacity_add_balancedInternal k n D.sparse.card
  change criticalMaximumCombinedCapacity k n D.sparse.card +
    criticalWindowCoreInternal k n D.sparse.card = _ at hbalanced
  by_cases hI : divisionInternalCliqueCapacity D ≤ m
  · rw [ite_eq_left hI, ite_eq_left (by omega)]
    by_cases hselected : m - divisionInternalCliqueCapacity D ≤
        criticalCombinedVariableCapacity D
    · have hbalancedSelected : m - criticalWindowCoreInternal k n D.sparse.card ≤
          criticalMaximumCombinedCapacity k n D.sparse.card := by omega
      rw [← Nat.choose_symm hselected, ← Nat.choose_symm hbalancedSelected]
      have heq : criticalCombinedVariableCapacity D -
          (m - divisionInternalCliqueCapacity D) =
        criticalMaximumCombinedCapacity k n D.sparse.card -
          (m - criticalWindowCoreInternal k n D.sparse.card) := by omega
      rw [heq]
      exact Nat.choose_le_choose _ hAB
    · rw [Nat.choose_eq_zero_of_lt (by omega)]
      exact Nat.zero_le _
  · rw [ite_eq_right hI]
    exact Nat.zero_le _

/-- Clean fibers satisfy the same guarded combined-coordinate bound without
an exponential penalty. -/
theorem card_supercriticalCleanDivisionGraphFinset_le_guarded_combined
    {k n m : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1} {tau : ℝ} {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) :
    (supercriticalCleanDivisionGraphFinset k hk gamma hgamma m n tau hn D).card ≤
      if divisionInternalCliqueCapacity D ≤ m then
        Nat.choose (criticalCombinedVariableCapacity D)
          (m - divisionInternalCliqueCapacity D) else 0 := by
  classical
  by_cases hI : divisionInternalCliqueCapacity D ≤ m
  · rw [ite_eq_left hI]
    exact card_supercriticalCleanDivisionGraphFinset_le_preAbsorptionChoose D
  · rw [ite_eq_right hI]
    apply le_of_eq
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro G hG
    have hGprofile : G ∈ supercriticalCleanDivisionProfileGraphFinset
        k hk gamma hgamma m n tau hn D (crossEdgeProfile G D) :=
      mem_supercriticalCleanDivisionProfileGraphFinset.mpr ⟨hG, rfl⟩
    have hidentity := supercriticalDefectShift_edgeCount_identity G D
    rw [finiteGraphEdges_card_eq_of_mem_cleanProfile hGprofile,
      supercriticalDefectShift_clean_eq_inducedEdgeCount hGprofile] at hidentity
    have hcount : m = divisionInternalCliqueCapacity D +
        profileTotal (crossEdgeProfile G D) + inducedEdgeCount G D.sparse := by
      exact_mod_cast hidentity
    omega

/-- Regrouping any set of divisions by sparse size costs at most the full
number of divisions in each size fiber. -/
theorem sum_division_sparse_weights_le
    {k n : ℕ} (A : Finset (SupercriticalDivision k (Fin n)))
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hmaps : ∀ D ∈ A, D.sparse.card ∈ S)
    (hnonneg : ∀ s ∈ S, 0 ≤ w s) :
    (∑ D ∈ A, w D.sparse.card) ≤
      ∑ s ∈ S, ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) * w s := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps w]
  apply Finset.sum_le_sum
  intro s hs
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (hnonneg s hs)
  exact_mod_cast (Finset.card_le_card (show
    (A.filter fun D ↦ D.sparse.card = s) ⊆
      supercriticalDivisionsWithSparseCard k n s from
        fun D hD ↦ mem_supercriticalDivisionsWithSparseCard.mpr
          (Finset.mem_filter.mp hD).2))

end InducedStars
