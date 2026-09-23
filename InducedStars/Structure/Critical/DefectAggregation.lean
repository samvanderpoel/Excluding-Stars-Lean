import InducedStars.Structure.Critical.AggregationParameters
import InducedStars.Structure.Critical.DivisionCounting
import InducedStars.Structure.Supercritical.FixedDivisionTotal
import InducedStars.Structure.Supercritical.FixedSupportAggregation
import InducedStars.Structure.Supercritical.GlobalAggregation

/-!
# Defect aggregation at the critical density

This module supplies the finite transport from an actual critical division to
the balanced maximum slice, and then uses the endpoint binomial comparison to
aggregate the medium-degree and fixed-defect families.  The matching and
medium Janson estimates are imported from the supercritical development and
are specialized at `gammaK k`; they are not reproved here.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-! ## Exact aliases for the two critical exceptional totals -/

/-- The medium-degree total at the exact critical edge count. -/
noncomputable abbrev criticalMediumTotal
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (n : ℕ) : ℕ :=
  supercriticalMediumTotal k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha
      (criticalEdgeCount k n) n P.tau

/-- The fixed nonzero-defect total at the exact critical edge count. -/
noncomputable abbrev criticalFixedDefectTotal
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (n : ℕ) : ℕ :=
  supercriticalFixedDefectTotal k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha
      (criticalEdgeCount k n) n P.tau

/-! ## Transporting an actual shifted profile to the balanced slice -/

/-- Every cross-edge profile selects at most the total number of cross
coordinates of its division. -/
theorem criticalProfileTotal_le_totalCrossCapacity
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (profile : SupercriticalEdgeProfile D) :
    profileTotal profile ≤ supercriticalTotalCrossCapacity D := by
  unfold profileTotal supercriticalTotalCrossCapacity
  exact Finset.sum_le_sum fun e _ ↦ profile.count_le_capacity e

/-- A witness occurring in a shifted critical aggregate determines an
admissible selected count in the actual combined-coordinate universe. -/
theorem criticalShiftedProfileAggregate_le_actualSlice
    {k n t : ℕ} {delta : ℝ}
    (D : SupercriticalDivision k (Fin n)) {u : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D (criticalEdgeCount k n)
      (supercriticalOffDiagonal k (gammaK k)) delta
        (u + (t : ℤ)) profile) :
    supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) delta u ≤
      Nat.choose (criticalCombinedVariableCapacity D)
        (profileTotal profile + t) := by
  apply supercriticalShiftedProfileAggregate_le_choose
  have hcount := hprofile.1
  simpa only [criticalCombinedVariableCapacity_eq_preAbsorption] using
    (show ((profileTotal profile + t : ℕ) : ℤ) +
        (divisionInternalCliqueCapacity D : ℤ) + u =
          (criticalEdgeCount k n : ℕ) by
      push_cast
      omega)

/-- Fixed-missing-count transport from an actual division to the balanced
maximum capacity.  The transported selected count differs from the balanced
maximum selected count by exactly the absolute signed profile shift.

The two feasibility assumptions say that the division-independent pair
universe contains the prescribed edge count and that its missing count fits
inside the balanced maximum capacity.  These are precisely the guards used
by the critical signed-slice comparison. -/
theorem criticalShiftedProfileAggregate_le_maximumSlice
    {k n t : ℕ} {delta : ℝ}
    (D : SupercriticalDivision k (Fin n)) {u : ℤ}
    (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D (criticalEdgeCount k n)
      (supercriticalOffDiagonal k (gammaK k)) delta
        (u + (t : ℤ)) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2)
    (hedgeUpper : criticalEdgeCount k n ≤
      Nat.choose (n - D.sparse.card) 2 + Nat.choose D.sparse.card 2)
    (hmissingMax : criticalCombinedMissingCount k n D.sparse.card ≤
      criticalMaximumCombinedCapacity k n D.sparse.card) :
    ∃ L : ℕ,
      supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) delta u ≤
        Nat.choose
          (criticalMaximumCombinedCapacity k n D.sparse.card) L ∧
      Nat.dist L
          (criticalMaximumCombinedSelectedCount k n D.sparse.card) =
        u.natAbs := by
  let A := criticalCombinedVariableCapacity D
  let B := criticalMaximumCombinedCapacity k n D.sparse.card
  let Lshift := profileTotal profile + t
  let missing := criticalCombinedMissingCount k n D.sparse.card
  let q := A - Lshift
  let L := B - q
  have hprofileCap : profileTotal profile ≤
      supercriticalTotalCrossCapacity D :=
    criticalProfileTotal_le_totalCrossCapacity D profile
  have hLshiftA : Lshift ≤ A := by
    dsimp [Lshift, A, criticalCombinedVariableCapacity]
    exact Nat.add_le_add hprofileCap ht
  have hAB : A ≤ B := by
    simpa [A, B] using criticalCombinedVariableCapacity_le_maximum D
  have hmaxAdd :
      criticalMaximumCombinedSelectedCount k n D.sparse.card + missing = B := by
    simpa [B, missing] using
      criticalMaximumSelected_add_missing hmissingMax
  have htotal := criticalCombinedVariableCapacity_add_internal_eq D
  have hqMissingCast : (q : ℤ) = (missing : ℤ) + u := by
    have hpcount := hprofile.1
    dsimp [q, Lshift]
    rw [Nat.cast_sub hLshiftA]
    have hmissingCast : (missing : ℤ) =
        (Nat.choose (n - D.sparse.card) 2 : ℤ) +
          (Nat.choose D.sparse.card 2 : ℤ) -
            (criticalEdgeCount k n : ℤ) := by
      dsimp [missing, criticalCombinedMissingCount]
      rw [Nat.cast_sub hedgeUpper]
      push_cast
      rfl
    have htotalCast : (A : ℤ) +
        (divisionInternalCliqueCapacity D : ℤ) =
          (Nat.choose (n - D.sparse.card) 2 : ℤ) +
            (Nat.choose D.sparse.card 2 : ℤ) := by
      exact_mod_cast htotal
    omega
  have hqA : q ≤ A := by
    dsimp [q]
    exact Nat.sub_le _ _
  have hqB : q ≤ B := hqA.trans hAB
  have hchooseActual :=
    criticalShiftedProfileAggregate_le_actualSlice D profile hprofile
  have hchooseSymm : Nat.choose A Lshift = Nat.choose A q := by
    dsimp [q]
    exact (Nat.choose_symm hLshiftA).symm
  have hchooseMono : Nat.choose A q ≤ Nat.choose B q :=
    Nat.choose_le_choose q hAB
  have hchooseBalanced : Nat.choose B q = Nat.choose B L := by
    dsimp [L]
    exact (Nat.choose_symm hqB).symm
  refine ⟨L, ?_, ?_⟩
  · calc
      supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) delta u ≤
          Nat.choose A Lshift := by simpa [A, Lshift] using hchooseActual
      _ = Nat.choose A q := hchooseSymm
      _ ≤ Nat.choose B q := hchooseMono
      _ = Nat.choose B L := hchooseBalanced
  · have hLcast : (L : ℤ) =
        (criticalMaximumCombinedSelectedCount k n D.sparse.card : ℤ) - u := by
      dsimp [L, q]
      rw [Nat.cast_sub hqB, Nat.cast_sub hLshiftA]
      have hABcast : (A : ℤ) ≤ (B : ℤ) := by exact_mod_cast hAB
      have hmaxCast : (B : ℤ) =
          (criticalMaximumCombinedSelectedCount k n D.sparse.card : ℤ) +
            (missing : ℤ) := by
        exact_mod_cast hmaxAdd.symm
      omega
    let M := criticalMaximumCombinedSelectedCount k n D.sparse.card
    by_cases hu : 0 ≤ u
    · have huCast : (u.natAbs : ℤ) = u := Int.natAbs_of_nonneg hu
      have hNat : L + u.natAbs = M := by
        exact_mod_cast (show (L : ℤ) + (u.natAbs : ℤ) = (M : ℤ) by
          dsimp [M]
          rw [huCast]
          omega)
      have hLM : L ≤ M := by omega
      rw [Nat.dist_eq_sub_of_le hLM]
      omega
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have huCast : (u.natAbs : ℤ) = -u :=
        Int.ofNat_natAbs_of_nonpos hu'
      have hNat : L = M + u.natAbs := by
        exact_mod_cast (show (L : ℤ) = (M : ℤ) + (u.natAbs : ℤ) by
          dsimp [M]
          rw [huCast]
          omega)
      have hML : M ≤ L := by omega
      rw [Nat.dist_eq_sub_of_le_right hML]
      omega

/-! ## Endpoint specialization of the matching profile penalty -/

/-- The already-proved matching Janson estimate, specialized to the exact
critical density, uniformly over the finite edge count. This is the endpoint analogue of
`eventually_supercriticalFixedPattern_le_profileMass`; its proof only changes
the closed density witness and does not repeat the probabilistic argument. -/
theorem eventually_criticalFixedPattern_le_profileMass_anyEdgeCount
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (m : ℕ) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n))
        (T : SimpleGraph (Fin n)),
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            m n P.tau hn D →
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          m n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  have hcore := supercriticalMatchingPenalty_of_closeStructure
    k hk (gammaK k) hgamma
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  filter_upwards [hcore, eventually_ge_atTop nClose]
      with n hcoreN hnClose
  intro m hn D T hT hbalanced
  let F := supercriticalFixedDefectGraphFinset
    k hk (gammaK k) hgamma P.alpha m n P.tau hn D T
  by_cases hF : F.Nonempty
  · have hresult : ∀ G ∈ F,
        Nonempty (SupercriticalCloseStructureResult
          k hk (gammaK k) P.alpha P.delta P.epsilon hgamma G hn) := by
      intro G hG
      have hfixed : G ∈ supercriticalFixedDefectGraphFinset
          k hk (gammaK k) hgamma P.alpha m n P.tau hn D T := by
        simpa [F] using hG
      have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hfixed).1
      have hclose :=
        (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
      have hfamily : G ∈
          inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
            supercriticalFarGraphFinset
              k hk (gammaK k) hgamma m n P.tau := by
        rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
        exact hclose
      have hR := superCloseStructureK1k k hk (gammaK k) hgamma
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            m hnClose G (by simpa [P.tau_eq] using hfamily)
      simpa using hR
    obtain ⟨G, hG⟩ := hF
    have hGfixed : G ∈ supercriticalFixedDefectGraphFinset
        k hk (gammaK k) hgamma P.alpha m n P.tau hn D T := by
      simpa [F] using hG
    obtain ⟨R⟩ := hresult G hG
    have hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T P.alpha D v i :=
      low_degree_everywhere_of_mem_fixedDefect hGfixed R
    have hadmissible : ∀ H ∈ F,
        SupercriticalProfileAtShift D m
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) (crossEdgeProfile H D) := by
      intro H hH
      have hHfixed : H ∈ supercriticalFixedDefectGraphFinset
          k hk (gammaK k) hgamma P.alpha m n P.tau hn D T := by
        simpa [F] using hH
      obtain ⟨RH⟩ := hresult H hH
      have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hHfixed).1
      have hD := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
      have hT' := (mem_supercriticalFixedDefectGraphFinset.mp hHfixed).2.1
      refine ⟨?_, ?_⟩
      · have hid := supercriticalFixedDefectProfile_edgeCount_identity
          (hn := hn) (profile := crossEdgeProfile H D) hD hT' rfl
        have hedges : (finiteGraphEdges H).card = m := by
          have hclose :=
            (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
          simpa [finiteGraphEdges] using
            (mem_supercriticalCloseGraphFinset.mp hclose).2.1
        omega
      · intro e
        have hdensity := RH.cross_density_close
          e.left e.right e.left_ne_right
        have habs :
            |profileDensity (crossEdgeProfile H D) e -
              supercriticalOffDiagonal k (gammaK k)| ≤ P.delta := by
          rw [profileDensity_crossEdgeProfile]
          simpa only [hD] using hdensity
        rw [abs_le] at habs
        exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hdeltaCount :=
      (supercriticalMatchingDeltaBound_spec P.rank hgamma
        P.matching_delta).2.1
    have hdeltaFloor :=
      supercriticalMatchingDeltaBound_four_mul_le P.matching_delta
    apply card_supercriticalFixedDefectGraphFinset_le_profileMass_mul_exp
      D T (-(P.cMat *
        (supercriticalMatchingNumber D T : ℝ) * (n : ℝ)))
    · intro H hH
      exact hadmissible H (by simpa [F] using hH)
    · intro profile hprofile
      have hpenalty := hcoreN P.alpha m P.tau hn D T profile hT P.delta
        P.alpha_mem_Ioo P.delta_pos.le hdeltaCount hdeltaFloor
          hbalanced hlow hprofile
      simpa [P.cMat_eq] using hpenalty
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change ((F.card : ℕ) : ℝ) ≤ _
    rw [hzero, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Specialization to the exact floor critical edge sequence. -/
theorem eventually_criticalFixedPattern_le_profileMass
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n))
        (T : SimpleGraph (Fin n)),
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D →
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          (criticalEdgeCount k n) n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  filter_upwards [eventually_criticalFixedPattern_le_profileMass_anyEdgeCount k hk P] with n hnAll
  intro hn D T hT hbalanced
  exact hnAll (criticalEdgeCount k n) hn D T hT hbalanced

/-! ## Endpoint specialization of the medium-degree profile penalty -/

/-- The `superFPiPrime` medium-degree estimate at `gamma = gammaK k`, with
the synchronized critical parameters and arbitrary finite edge count. The
close-structure witnesses are supplied locally; the Janson argument remains
the imported supercritical theorem. -/
theorem eventually_criticalMediumDegree_le_profileMultiplicity_anyEdgeCount
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (m : ℕ) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n))
        (base : SupercriticalEdgeProfile D),
      SupercriticalProfileWindow D m
          (supercriticalOffDiagonal k (gammaK k)) P.delta
          ⌊P.epsilon * (n : ℝ) ^ 2⌋₊ base →
      ((supercriticalMediumDegreeGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          m n P.tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  have hcore := supercriticalMediumDegreePenalty_of_closeStructure
    k hk hgamma P.alpha_pos P.delta_pos P.medium_candidate_delta
      P.medium_janson_range P.medium_profile_lower P.medium_profile_upper
      P.epsilon_pos P.epsilon_pattern_small P.medium_candidate_epsilon
      P.medium_defect_rate P.medium_profile_rate
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  filter_upwards [hcore, eventually_ge_atTop nClose]
      with n hcoreN hnClose
  intro m hn D base hbase
  have hresult : ∀ G ∈ supercriticalDivisionDefectGraphFinset
      k hk (gammaK k) hgamma m n P.tau hn D,
      Nonempty (SupercriticalCloseStructureResult
        k hk (gammaK k) P.alpha P.delta P.epsilon hgamma G hn) := by
    intro G hG
    have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hG).1
    have hfamily : G ∈
        inducedFreeGraphFinsetWithEdges (inducedStar k) n
            m \
          supercriticalFarGraphFinset k hk (gammaK k) hgamma
            m n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hclose
    have hR := superCloseStructureK1k k hk (gammaK k) hgamma
      P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
        P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
          m hnClose G
            (by simpa [P.tau_eq] using hfamily)
    simpa using hR
  have hraw := hcoreN m P.tau hn D base hbase hresult
  simpa [P.cMed_eq] using hraw

/-- Specialization to the exact floor critical edge sequence. -/
theorem eventually_criticalMediumDegree_le_profileMultiplicity
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n))
        (base : SupercriticalEdgeProfile D),
      SupercriticalProfileWindow D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
          ⌊P.epsilon * (n : ℝ) ^ 2⌋₊ base →
      ((supercriticalMediumDegreeGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          (criticalEdgeCount k n) n P.tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := by
  filter_upwards
    [eventually_criticalMediumDegree_le_profileMultiplicity_anyEdgeCount k hk P]
    with n hnAll
  intro hn D base hbase
  exact hnAll (criticalEdgeCount k n) hn D base hbase

/-! ## Critical support-pattern overhead -/

/-- The support-incident pattern encoding costs at most one eighth of the
critical matching exponent.  This is the endpoint specialization of the
generic support-count argument, using the explicit budget stored in
`CriticalAggregationParameters`. -/
theorem eventually_card_criticalLowSupportPatternFinset_le_exp
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (h : ℕ),
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      0 < h →
      ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) ≤
        Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto ht).bound
    (show 0 < P.cMat / 64 by exact div_pos P.cMat_pos (by norm_num))
  have hlarge : ∀ᶠ n : ℕ in atTop, 1 ≤ 3 * P.alpha * (n : ℝ) := by
    have hgrow : Tendsto (fun n : ℕ ↦ 3 * P.alpha * (n : ℝ))
        atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop
        (mul_pos (by norm_num) P.alpha_pos)
    exact hgrow.eventually (eventually_ge_atTop 1)
  filter_upwards [hlog, hlarge, eventually_ge_atTop 1]
      with n hlogN hlargeN hn
  intro D h hsparse hh
  let b : ℕ := ⌊3 * P.alpha * (n : ℝ)⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hb : 0 < b := Nat.floor_pos.mpr hlargeN
  have hbReal : (b : ℝ) ≤ 3 * P.alpha * (n : ℝ) := by
    exact Nat.floor_le (by positivity)
  have hSix : 6 * P.alpha < 1 := by
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have halpha : P.alpha * (100 * (k : ℝ)) < 1 := by
      have h := P.alpha_lt
      rwa [lt_div_iff₀ (by positivity)] at h
    have hscale : (300 : ℝ) ≤ 100 * (k : ℝ) := by nlinarith
    have hmul : P.alpha * 300 ≤ P.alpha * (100 * (k : ℝ)) :=
      mul_le_mul_of_nonneg_left hscale P.alpha_pos.le
    linarith
  have hhalf : 2 * b ≤ n := by
    have hreal : (2 : ℝ) * b ≤ n := by
      have hn0 : (0 : ℝ) ≤ n := hnR.le
      have hSixMul := mul_le_mul_of_nonneg_right hSix.le hn0
      nlinarith [hbReal, hSixMul]
    exact_mod_cast hreal
  have hdegree : ∀ T ∈ supercriticalLowSupportPatternFinset
      D P.alpha h, ∀ v : Fin n,
      degreeInFinset T v Finset.univ ≤ b := by
    intro T hT v
    have hmem := mem_supercriticalLowSupportPatternFinset.mp hT
    have hdeg := supercriticalSupportPattern_degree_real_le D T
      P.alpha_pos.le P.delta_pos.le hmem.2.2.2 hsparse v
    have hreal : (degreeInFinset T v Finset.univ : ℝ) ≤
        3 * P.alpha * (n : ℝ) := by
      have had : P.alpha + P.delta ≤ 3 * P.alpha := by
        linarith [P.delta_lt_alpha, P.alpha_pos]
      exact hdeg.trans (mul_le_mul_of_nonneg_right had (by positivity))
    by_cases hz : degreeInFinset T v Finset.univ = 0
    · simp [hz]
    · exact (Nat.le_floor_iff' hz).2 hreal
  have hq0 : (0 : ℝ) ≤ (b : ℝ) / (n : ℝ) := by positivity
  have hqle : (b : ℝ) / (n : ℝ) ≤ 3 * P.alpha := by
    rw [div_le_iff₀ hnR]
    simpa [mul_assoc] using hbReal
  have hthreeHalf : 3 * P.alpha ≤ (2 : ℝ)⁻¹ := by
    have h := hSix.le
    norm_num at ⊢
    linarith
  have hqhalf : (b : ℝ) / (n : ℝ) ≤ (2 : ℝ)⁻¹ :=
    hqle.trans hthreeHalf
  have hbin := Real.binEntropy_strictMonoOn.monotoneOn
    ⟨hq0, hqhalf⟩ ⟨by nlinarith [P.alpha_pos], hthreeHalf⟩ hqle
  have hentropy : binaryEntropy ((b : ℝ) / (n : ℝ)) ≤
      binaryEntropy (3 * P.alpha) + P.delta := by
    unfold binaryEntropy
    have hdiv : Real.binEntropy ((b : ℝ) / (n : ℝ)) /
        Real.log 2 ≤ Real.binEntropy (3 * P.alpha) / Real.log 2 :=
      (div_le_div_iff_of_pos_right realLogTwo_pos).2 hbin
    linarith [P.delta_pos]
  have hcount := card_supercriticalLowSupportPatternFinset_real_le_exp
    D P.alpha P.delta h b (by omega) hh hb hhalf hdegree hentropy
  have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hlogBound : Real.log (((n + 1 : ℕ) : ℝ)) ≤
      (P.cMat / 32) * (n : ℝ) := by
    dsimp [Function.comp_def, id] at hlogN
    rw [abs_of_nonneg hlogNonneg,
      abs_of_nonneg (by positivity)] at hlogN
    norm_num at hlogN ⊢
    have hnTwo : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
      exact_mod_cast (show n + 1 ≤ 2 * n by omega)
    calc
      Real.log ((n : ℝ) + 1) ≤
          (P.cMat / 64) * ((n : ℝ) + 1) := hlogN
      _ ≤ (P.cMat / 64) * (2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hnTwo
          (div_nonneg P.cMat_pos.le (by norm_num))
      _ = (P.cMat / 32) * (n : ℝ) := by ring
  let x := binaryEntropy (3 * P.alpha) + P.delta
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact add_nonneg
      (binaryEntropy_nonneg (by nlinarith [P.alpha_pos])
        (hthreeHalf.trans (by norm_num))) P.delta_pos.le
  have hlogTwo1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hkOne : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k by omega)
  have hentropyCoeff : 2 * x * Real.log 2 < P.cMat / 16 := by
    have hsmall : 2 * (k : ℝ) * x < P.cMat / 16 := by
      have h := P.support_overhead_small
      unfold criticalSupportPatternBudgetRate at h
      nlinarith
    have hxk : 2 * x ≤ 2 * (k : ℝ) * x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkOne) hx0]
    calc
      2 * x * Real.log 2 ≤ 2 * x * 1 :=
        mul_le_mul_of_nonneg_left hlogTwo1 (by positivity)
      _ ≤ 2 * (k : ℝ) * x := by simpa using hxk
      _ < P.cMat / 16 := hsmall
  apply hcount.trans
  apply Real.exp_le_exp.mpr
  have hlogCost :
      2 * (h : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) ≤
        (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by
    calc
      2 * (h : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) ≤
          2 * (h : ℝ) * ((P.cMat / 32) * (n : ℝ)) := by gcongr
      _ = (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by ring
  have hentropyCost :
      (2 * (h : ℝ) * (n : ℝ)) * x * Real.log 2 ≤
        (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by
    have hnonneg : 0 ≤ (h : ℝ) * (n : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hentropyCoeff.le hnonneg
    dsimp [x] at hmul ⊢
    nlinarith
  dsimp [x] at hentropyCost
  nlinarith

/-! ## Endpoint support-fiber aggregation -/

/-- The part of the critical shifted-profile exponent which depends only on
the sparse size (and not on the signed support shift). -/
def criticalSparseAggregateExponent
    {k : ℕ} (P : CriticalAggregationParameters k) (n s : ℕ) : ℝ :=
  -P.cCrit * (s : ℝ) ^ 2 +
    P.cleanErrorConstant * (s : ℝ) +
    P.cleanErrorConstant * Real.log ((n + 1 : ℕ) : ℝ)

/-- Full critical shifted-profile exponent, including the adjacent-slice
cost of an integer shift. -/
def criticalShiftedAggregateExponent
    {k : ℕ} (P : CriticalAggregationParameters k)
    (n s : ℕ) (u : ℤ) : ℝ :=
  criticalSparseAggregateExponent P n s +
    P.cShift * (u.natAbs : ℝ)

/-- A positive support fiber inherits the matching penalty from `superFPiT`
and the critical shifted-binomial comparison.  The latter is supplied as a
uniform hypothesis here so the finite support regrouping remains independent
of the asymptotic slice theorem. -/
theorem criticalActiveSupportTotal_le_referenceFiber
    {k n : ℕ} (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {hn : k - 1 ≤ n}
    (hnClose : supercriticalCloseStructureVertexThreshold k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
        P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
          P.rho_three_upper P.epsilon P.epsilon_pos ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (T₀ : SimpleGraph (Fin n))
    (hT₀ : T₀ ∈ supercriticalActiveSupportImage hk
      (gammaK_mem_supercritical_Ico k hk) P.alpha
        (criticalEdgeCount k n) n P.tau hn D)
    (hpointwise : ∀ T : SimpleGraph (Fin n),
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D →
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          (criticalEdgeCount k n) n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))))
    (haggregate : ∀ (profile : SupercriticalEdgeProfile D) (t : ℕ),
      SupercriticalProfileAtShift D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalSupportDefectShift D T₀ + (t : ℤ)) profile →
      t ≤ Nat.choose D.sparse.card 2 →
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalSupportDefectShift D T₀) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card
            (supercriticalSupportDefectShift D T₀))) :
    0 < supercriticalMatchingNumber D T₀ ∧
      supercriticalMatchingNumber D T₀ ≤ n ∧
      T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha
        (supercriticalMatchingNumber D T₀) ∧
      supercriticalFixedSupportTotal hk
          (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T₀ ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalSparseAggregateExponent P n D.sparse.card -
            (15 * P.cMat / 16) *
              (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ)) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  have hactive := mem_supercriticalActiveSupportImage.mp hT₀
  have hsumPos := hactive.2
  unfold supercriticalFixedSupportTotal at hsumPos
  have hsummandNonneg : ∀ T ∈ supercriticalCombinedSupportFiber
      (hk := hk) (gamma := gammaK k) (hgamma := hgamma)
        (m := criticalEdgeCount k n) (tau := P.tau) (hn := hn) D T₀,
      0 ≤ ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) hgamma P.alpha (criticalEdgeCount k n)
          n P.tau hn D T).card : ℝ) := by
    intro T _hT
    positivity
  obtain ⟨T, hTfiber, hcardPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hsummandNonneg).mp hsumPos
  have hT := (mem_supercriticalCombinedSupportFiber.mp hTfiber).1
  have hsupport := (mem_supercriticalCombinedSupportFiber.mp hTfiber).2
  have hcardNat : 0 < (supercriticalFixedDefectGraphFinset
      k hk (gammaK k) hgamma P.alpha (criticalEdgeCount k n)
        n P.tau hn D T).card := by
    exact_mod_cast hcardPos
  obtain ⟨G, hG⟩ := Finset.card_pos.mp hcardNat
  have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hG).1
  have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
  have hD := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
  have hcanonicalT := (mem_supercriticalFixedDefectGraphFinset.mp hG).2.1
  have hfamily : G ∈
      inducedFreeGraphFinsetWithEdges (inducedStar k) n
          (criticalEdgeCount k n) \
        supercriticalFarGraphFinset k hk (gammaK k) hgamma
          (criticalEdgeCount k n) n P.tau := by
    rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hclose
  obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k) hgamma
    P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
        (criticalEdgeCount k n) hnClose G
          (by simpa [P.tau_eq] using hfamily)
  have hlowT : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart T P.alpha D v i :=
    low_degree_everywhere_of_mem_fixedDefect hG R
  have hcombined : combinedSupercriticalDefectGraph G D = T := by
    calc
      combinedSupercriticalDefectGraph G D =
          canonicalCombinedDefectGraph G (by simpa using hn) := by
        simp [canonicalCombinedDefectGraph, hD]
      _ = T := hcanonicalT
  have hlowCombined : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart (combinedSupercriticalDefectGraph G D)
        P.alpha D v i := by
    simpa only [hcombined] using hlowT
  have hsupportLow :=
    supercriticalSupportIncidentGraph_mem_lowSupportPattern
      G D P.alpha hlowCombined
  have hmatching : supercriticalMatchingNumber D T₀ =
      supercriticalMatchingNumber D T := by
    rw [← hsupport]
    exact supercriticalMatchingNumber_supportIncident D T
  have hT₀Low : T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha
      (supercriticalMatchingNumber D T₀) := by
    rw [hcombined, hsupport] at hsupportLow
    rwa [← hmatching] at hsupportLow
  have hmatchPos : 0 < supercriticalMatchingNumber D T₀ := by
    rw [hmatching]
    exact supercriticalMatchingNumber_pos_of_mem_pattern hT
  have hmatchLe : supercriticalMatchingNumber D T₀ ≤ n := by
    have hcard := Finset.card_le_univ
      (supercriticalCanonicalMatchingEndpoints D T₀)
    rw [card_supercriticalCanonicalMatchingEndpoints] at hcard
    have htwo : 2 * supercriticalMatchingNumber D T₀ ≤ n := by
      simpa using hcard
    omega
  let profile := crossEdgeProfile G D
  let t := inducedEdgeCount (supercriticalSparseInducedPattern D T) D.sparse
  have hprofileDefect : SupercriticalProfileAtShift D (criticalEdgeCount k n)
      (supercriticalOffDiagonal k (gammaK k)) P.delta
        (supercriticalDefectShift T D) profile := by
    refine ⟨?_, ?_⟩
    · have hid := supercriticalFixedDefectProfile_edgeCount_identity
        (hn := hn) (profile := profile) hD hcanonicalT rfl
      have hedges : (finiteGraphEdges G).card = criticalEdgeCount k n := by
        simpa [finiteGraphEdges] using
          (mem_supercriticalCloseGraphFinset.mp hclose).2.1
      omega
    · intro e
      have hdensity := R.cross_density_close
        e.left e.right e.left_ne_right
      have habs : |profileDensity profile e -
          supercriticalOffDiagonal k (gammaK k)| ≤ P.delta := by
        rw [profileDensity_crossEdgeProfile]
        simpa only [hD] using hdensity
      rw [abs_le] at habs
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hshift : supercriticalDefectShift T D =
      supercriticalSupportDefectShift D T₀ + (t : ℤ) := by
    simpa [t, hsupport] using
      (supercriticalDefectShift_eq_support_add_sparse D T)
  have hprofile : SupercriticalProfileAtShift D (criticalEdgeCount k n)
      (supercriticalOffDiagonal k (gammaK k)) P.delta
        (supercriticalSupportDefectShift D T₀ + (t : ℤ)) profile := by
    rwa [← hshift]
  have ht : t ≤ Nat.choose D.sparse.card 2 := by
    dsimp [t]
    have hadd := inducedEdgeCount_add_compl
      (supercriticalSparseInducedPattern D T) D.sparse
    omega
  have hfiberPointwise : ∀ U ∈ supercriticalCombinedSupportFiber
      (hk := hk) (gamma := gammaK k) (hgamma := hgamma)
        (m := criticalEdgeCount k n) (tau := P.tau) (hn := hn) D T₀,
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) hgamma P.alpha (criticalEdgeCount k n)
          n P.tau hn D U).card : ℝ) ≤
        (supercriticalProfileMassAtShift D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift U D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ))) := by
    intro U hU
    have hUdata := mem_supercriticalCombinedSupportFiber.mp hU
    have hmatchingU : supercriticalMatchingNumber D U =
        supercriticalMatchingNumber D T₀ := by
      rw [← supercriticalMatchingNumber_supportIncident D U, hUdata.2]
    simpa only [hmatchingU] using hpointwise U hUdata.1
  have hsum := supercriticalFixedSupportTotal_le_shiftedAggregate_mul_exp
    D T₀ hfiberPointwise
  have hagg := haggregate profile t hprofile ht
  have hmem := mem_supercriticalLowSupportPatternFinset.mp hT₀Low
  have hshiftNat := supercriticalSupportDefectShift_natAbs_le_edgeCount D T₀
  have hshiftEdge : (supercriticalSupportDefectShift D T₀).natAbs ≤
      (finiteGraphEdges T₀).card := by
    simpa [hmem.1] using hshiftNat
  have hedge := supercriticalSupportPattern_edgeCount_le D
    P.alpha_pos.le P.delta_pos.le hsparse hT₀Low
  have hshiftReal :
      ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
        2 * (supercriticalMatchingNumber D T₀ : ℝ) *
          (P.alpha + P.delta) * (n : ℝ) := by
    exact (by exact_mod_cast hshiftEdge :
      ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
        ((finiteGraphEdges T₀).card : ℝ)) |>.trans hedge
  have hsum0 : 0 ≤ P.alpha + P.delta := by
    linarith [P.alpha_pos, P.delta_pos]
  have hkOne : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k by omega)
  have hshiftCoeff :
      2 * P.cShift * (P.alpha + P.delta) < P.cMat / 16 := by
    have hsmall :
        2 * (k : ℝ) * P.cShift * (P.alpha + P.delta) <
          P.cMat / 16 := by
      have h := P.support_shift_small
      nlinarith
    have hle : 2 * P.cShift * (P.alpha + P.delta) ≤
        2 * (k : ℝ) * P.cShift * (P.alpha + P.delta) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkOne)
        (mul_nonneg P.cShift_pos.le hsum0)]
    exact hle.trans_lt hsmall
  have hshiftCost : P.cShift *
        ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
      (P.cMat / 16) * (supercriticalMatchingNumber D T₀ : ℝ) *
        (n : ℝ) := by
    calc
      P.cShift * ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
          P.cShift *
            (2 * (supercriticalMatchingNumber D T₀ : ℝ) *
              (P.alpha + P.delta) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hshiftReal P.cShift_pos.le
      _ = (2 * P.cShift * (P.alpha + P.delta)) *
          ((supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ)) := by ring
      _ ≤ (P.cMat / 16) *
          ((supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hshiftCoeff.le (by positivity)
      _ = _ := by ring
  refine ⟨hmatchPos, hmatchLe, hT₀Low, ?_⟩
  calc
    supercriticalFixedSupportTotal hk hgamma P.alpha
        (criticalEdgeCount k n) n P.tau hn D T₀ ≤
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
        (supercriticalOffDiagonal k (gammaK k)) P.delta
          (supercriticalSupportDefectShift D T₀) : ℝ) *
        Real.exp (-(P.cMat *
          (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ))) := hsum
    _ ≤ ((criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card
            (supercriticalSupportDefectShift D T₀))) *
        Real.exp (-(P.cMat *
          (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right hagg (Real.exp_nonneg _)
    _ = (criticalReferenceFiberCard k n : ℝ) *
        Real.exp (criticalShiftedAggregateExponent P n D.sparse.card
            (supercriticalSupportDefectShift D T₀) -
          P.cMat * (supercriticalMatchingNumber D T₀ : ℝ) *
            (n : ℝ)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
    _ ≤ (criticalReferenceFiberCard k n : ℝ) *
        Real.exp (criticalSparseAggregateExponent P n D.sparse.card -
          (15 * P.cMat / 16) *
            (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      unfold criticalShiftedAggregateExponent
      linarith

end InducedStars
