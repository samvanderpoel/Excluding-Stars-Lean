import InducedStars.Structure.Critical.ShiftedAggregate
import InducedStars.Structure.Supercritical.MediumGlobalAggregation

/-!
# Critical medium-degree aggregation

The already-proved endpoint Janson bound pays for the signed profile shift,
the linear and logarithmic critical errors, and all ordered divisions.  No
strict-supercritical absorption gap is used.
-/

noncomputable section

open Filter Finset Set Topology

namespace InducedStars

/-- The balanced reference fiber injects into the global co-partite family. -/
theorem criticalReferenceFiberCard_le_coMultipartiteCount
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n) :
    criticalReferenceFiberCard k n ≤
      coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n) := by
  rw [← card_criticalReferenceFiber_eq_balanced_choose hk hn]
  exact Finset.card_le_card (criticalReferenceFiber_subset_coMultipartite k hk n)

/-- The non-Gaussian part of the critical exponent is uniformly smaller
than any fixed positive quadratic rate, for all sparse sizes at once. -/
theorem eventually_criticalSparseAggregateExponent_le_quadratic
    {k : ℕ} (P : CriticalAggregationParameters k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ s ≤ n,
      criticalSparseAggregateExponent P n s ≤ c * (n : ℝ) ^ 2 := by
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      2 * P.cleanErrorConstant / c ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hthreshold] with n hn
  intro s hs
  have hsR : (s : ℝ) ≤ n := by exact_mod_cast hs
  have hlog : Real.log ((n + 1 : ℕ) : ℝ) ≤ n := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h
  have hlinear := (div_le_iff₀ hc).mp hn
  have hmul := mul_le_mul_of_nonneg_right hlinear (Nat.cast_nonneg (α := ℝ) n)
  have hsTerm := mul_le_mul_of_nonneg_left hsR P.cleanErrorConstant_nonneg
  have hlogTerm := mul_le_mul_of_nonneg_left hlog P.cleanErrorConstant_nonneg
  have hnegative := mul_nonneg P.cCrit_pos.le (sq_nonneg (s : ℝ))
  unfold criticalSparseAggregateExponent
  nlinarith only [hmul, hsTerm, hlogTerm, hnegative]

/-- Critical global medium-degree bound from the uniform shifted-profile
estimate.  The latter is discharged by the second-order binomial module. -/
theorem eventually_criticalMediumTotal_le_of_shiftedAggregate
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (haggregate : ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (u : ℤ)
        (profile : SupercriticalEdgeProfile D),
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      SupercriticalProfileAtShift D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta u profile →
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta u : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card u)) :
    ∀ᶠ n : ℕ in atTop,
      (criticalMediumTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
            Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
  have hsmall : 0 < P.cMed / 8 := by positivity [P.cMed_pos]
  filter_upwards [eventually_criticalMediumDegree_le_profileMultiplicity k hk P,
    haggregate, eventually_criticalSparseAggregateExponent_le_quadratic P hsmall,
    eventually_natPow_le_exp_quadratic k hsmall,
    eventually_ge_atTop nClose] with n hmediumN haggregateN herrorN hpowN hnClose
  have hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk (gammaK k)
      hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
        P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos).trans hnClose
  let C : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  have href : (criticalReferenceFiberCard k n : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast criticalReferenceFiberCard_le_coMultipartiteCount hk hn
  have hdivision (D : SupercriticalDivision k (Fin n)) :
      ((supercriticalMediumDegreeGraphFinset k hk (gammaK k) hgamma P.alpha
        (criticalEdgeCount k n) n P.tau hn D).card : ℝ) ≤
      C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2)) := by
    by_cases hnonempty : (supercriticalMediumDegreeGraphFinset k hk (gammaK k)
        hgamma P.alpha (criticalEdgeCount k n) n P.tau hn D).Nonempty
    · obtain ⟨G, hG⟩ := hnonempty
      have hdefect := (mem_supercriticalMediumDegreeGraphFinset.mp hG).1
      have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
      have hdivision := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
      have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n
          (criticalEdgeCount k n) \
          supercriticalFarGraphFinset k hk (gammaK k) hgamma
            (criticalEdgeCount k n) n P.tau := by
        rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
        exact hclose
      obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k) hgamma
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            (criticalEdgeCount k n) hnClose G (by simpa [P.tau_eq] using hfamily)
      have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
        simpa only [hdivision] using R.sparse_card_le
      let base := crossEdgeProfile G D
      have hedges : (finiteGraphEdges G).card = criticalEdgeCount k n := by
        simpa [finiteGraphEdges] using (mem_supercriticalCloseGraphFinset.mp hclose).2.1
      have hwindow : SupercriticalProfileWindow D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
          ⌊P.epsilon * (n : ℝ) ^ 2⌋₊ base := by
        have hw := canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
          hk hgamma G hn R (criticalEdgeCount k n) hedges
        dsimp [base]
        rw [← hdivision]
        exact hw
      obtain ⟨u, huFloor, hprofile⟩ := hwindow
      have hu : (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
        exact (show (u.natAbs : ℝ) ≤ (⌊P.epsilon * (n : ℝ) ^ 2⌋₊ : ℕ) by
          exact_mod_cast huFloor).trans
            (Nat.floor_le (mul_nonneg P.epsilon_pos.le (sq_nonneg _)))
      have hpenalty := hmediumN hn D base ⟨u, huFloor, hprofile⟩
      have hsingle : (supercriticalProfileMultiplicity base : ℝ) ≤
          (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
            (supercriticalOffDiagonal k (gammaK k)) P.delta u : ℝ) := by
        exact_mod_cast supercriticalProfileMultiplicity_le_shiftedProfileAggregate
          D (criticalEdgeCount k n) (supercriticalOffDiagonal k (gammaK k))
            P.delta u base hprofile
      have hprofileBound := hsingle.trans (haggregateN D u base hsparse hprofile)
      have hsle : D.sparse.card ≤ n := by simpa using Finset.card_le_univ D.sparse
      have herror := herrorN D.sparse.card hsle
      have hshift := mul_le_mul_of_nonneg_left hu P.cShift_pos.le
      have hbudget := mul_le_mul_of_nonneg_right P.medium_shift_small.le
        (sq_nonneg (n : ℝ))
      calc
        _ ≤ (supercriticalProfileMultiplicity base : ℝ) *
            Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := hpenalty
        _ ≤ ((criticalReferenceFiberCard k n : ℝ) *
            Real.exp (criticalShiftedAggregateExponent P n D.sparse.card u)) *
              Real.exp (-(P.cMed * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right hprofileBound (Real.exp_nonneg _)
        _ ≤ (criticalReferenceFiberCard k n : ℝ) *
            Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2)) := by
          rw [mul_assoc, ← Real.exp_add]
          apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          unfold criticalShiftedAggregateExponent
          nlinarith only [herror, hshift, hbudget]
        _ ≤ C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_right href (Real.exp_nonneg _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty, Finset.card_empty, Nat.cast_zero]
      positivity
  simp only [criticalMediumTotal, supercriticalMediumTotal, dif_pos hn, Nat.cast_sum]
  calc
    _ ≤ ∑ _D ∈ allSupercriticalDivisions k n,
        C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum fun D _ ↦ hdivision D
    _ = ((allSupercriticalDivisions k n).card : ℝ) *
        (C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2))) := by simp
    _ ≤ ((k ^ n : ℕ) : ℝ) *
        (C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_allSupercriticalDivisions_le (k := k) (n := n) (by omega)
    _ ≤ Real.exp ((P.cMed / 8) * (n : ℝ) ^ 2) *
        (C * Real.exp (-(5 * P.cMed / 8 * (n : ℝ) ^ 2))) :=
      mul_le_mul_of_nonneg_right hpowN (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      unfold CriticalAggregationParameters.mediumRate
      ring

/-- The critical medium-degree contribution is exponentially negligible
relative to the fixed-edge-count co-multipartite family.  This is the
critical-boundary specialization of the already-proved medium-degree Janson
penalty, with the second-order shifted-profile comparison supplying the
reference-fiber bound. -/
theorem eventually_criticalMediumTotal_le
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      (criticalMediumTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
            Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := by
  apply eventually_criticalMediumTotal_le_of_shiftedAggregate k hk P
  filter_upwards [criticalShiftedProfileAggregate_le_referenceFiber k hk P]
    with n hn
  intro D u profile hsparse hprofile
  simpa using hn D u profile 0 hsparse (by simpa using hprofile) (by simp)

end InducedStars
