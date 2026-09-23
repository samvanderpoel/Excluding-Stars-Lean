import InducedStars.Structure.Supercritical.FixedDivisionAggregation

/-!
# The absorbed estimate for one support-incident pattern
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-- After sparse-index aggregation, signed absorption and the parameter
shift budget retain fifteen sixteenths of the raw matching exponent. -/
theorem supercriticalFixedSupportTotal_le_absorbedCoPartite
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    {m : ℕ} {tau : ℝ} (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (T₀ : SimpleGraph (Fin n)) (h : ℕ)
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (hT₀ : T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha h)
    (profile : SupercriticalEdgeProfile D) (t : ℕ)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) P.delta
      (supercriticalSupportDefectShift D T₀ + (t : ℤ)) profile)
    (ht : t ≤ Nat.choose D.sparse.card 2)
    (hpointwise : ∀ T ∈ supercriticalCombinedSupportFiber
        (hk := hk) (gamma := gamma)
          (hgamma := ⟨hgamma.1.le, hgamma.2⟩)
          (m := m) (tau := tau) (hn := hn) D T₀,
      ((supercriticalFixedDefectGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
          m n tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k gamma) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat * (h : ℝ) * (n : ℝ)))) :
    supercriticalFixedSupportTotal hk ⟨hgamma.1.le, hgamma.2⟩
        P.alpha m n tau hn D T₀ ≤
      ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
        Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
          P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) := by
  have hsum := supercriticalFixedSupportTotal_le_shiftedAggregate_mul_exp
    D T₀ hpointwise
  have Hgeometry :=
    supercriticalSignedShiftGeometryHypotheses_of_supportPattern
      hgamma P D hbalanced hsparse h T₀ hT₀
  have hdata := supercriticalShiftedAbsorptionData_of_profile
    P.rank hgamma D profile hprofile ht Hgeometry
  have haggregate :=
    supercriticalShiftedProfileAggregate_le_absorbedCoPartite
      P.rank hgamma P.delta_pos.le P.delta_le_jointAbsorptionBound
        (rho := supercriticalOffDiagonal k gamma) (D := D)
        (m := m) (LShift := profileTotal profile + t)
        (u := supercriticalSupportDefectShift D T₀)
        hdata.aggregate_count hbalanced hsparse
        hdata.sparseChoice_le_gain hdata.absorbedInternal_le_m
        hdata.shiftSelected_le_preAbsorption
        hdata.cleanSelected_le_preAbsorption
        hdata.absorbedSelected_le_capacity hdata.absorbedDensity_lower
        hdata.shiftBand_lower hdata.shiftBand_upper hdata.selected_distance
  have haggregate' :
      (supercriticalShiftedProfileAggregate D m
        (supercriticalOffDiagonal k gamma) P.delta
          (supercriticalSupportDefectShift D T₀) : ℝ) ≤
        ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
          Real.exp (-(P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) +
            P.cShift *
              ((supercriticalSupportDefectShift D T₀).natAbs : ℝ)) := by
    simpa [P.cAbs_eq, P.cShift_eq] using haggregate
  have hmem := mem_supercriticalLowSupportPatternFinset.mp hT₀
  have hshiftNat := supercriticalSupportDefectShift_natAbs_le_edgeCount D T₀
  have hshiftEdge : (supercriticalSupportDefectShift D T₀).natAbs ≤
      (finiteGraphEdges T₀).card := by
    simpa [hmem.1] using hshiftNat
  have hedge := supercriticalSupportPattern_edgeCount_le D
    P.alpha_pos.le P.delta_pos.le hsparse hT₀
  have hshiftReal :
      ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
        ((finiteGraphEdges T₀).card : ℝ) := by
    exact_mod_cast hshiftEdge
  have hshiftRaw :
      ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
        2 * (h : ℝ) * (P.alpha + P.delta) * (n : ℝ) :=
    hshiftReal.trans hedge
  have hsum0 : 0 ≤ P.alpha + P.delta := by
    linarith [P.alpha_pos, P.delta_pos]
  have hkOne : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
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
  have hshiftCost :
      P.cShift *
          ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
        (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by
    calc
      P.cShift *
          ((supercriticalSupportDefectShift D T₀).natAbs : ℝ) ≤
          P.cShift *
            (2 * (h : ℝ) * (P.alpha + P.delta) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hshiftRaw P.cShift_pos.le
      _ = (2 * P.cShift * (P.alpha + P.delta)) *
          ((h : ℝ) * (n : ℝ)) := by ring
      _ ≤ (P.cMat / 16) * ((h : ℝ) * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right hshiftCoeff.le (by positivity)
      _ = (P.cMat / 16) * (h : ℝ) * (n : ℝ) := by ring
  calc
    supercriticalFixedSupportTotal hk ⟨hgamma.1.le, hgamma.2⟩
        P.alpha m n tau hn D T₀ ≤
      (supercriticalShiftedProfileAggregate D m
        (supercriticalOffDiagonal k gamma) P.delta
          (supercriticalSupportDefectShift D T₀) : ℝ) *
        Real.exp (-(P.cMat * (h : ℝ) * (n : ℝ))) := hsum
    _ ≤ (((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
          Real.exp (-(P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) +
            P.cShift *
              ((supercriticalSupportDefectShift D T₀).natAbs : ℝ))) *
        Real.exp (-(P.cMat * (h : ℝ) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_right haggregate' (Real.exp_nonneg _)
    _ = ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
        Real.exp ((-(P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) +
            P.cShift *
              ((supercriticalSupportDefectShift D T₀).natAbs : ℝ)) +
          -(P.cMat * (h : ℝ) * (n : ℝ))) := by
      rw [mul_assoc, ← Real.exp_add]
    _ ≤ ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
        Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
          P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith

/-! ## The concrete fixed-pattern matching estimate -/

/-- Uniformly for every displayed pattern, the close-structure theorem
supplies the low-degree input needed by the matching penalty, while the exact
edge decomposition puts every actual cross profile at the literal shift. -/
theorem eventually_supercriticalFixedPattern_le_profileMass
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (m : ℕ) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n))
        (T : SimpleGraph (Fin n)),
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ m n P.tau hn D →
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
            (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      ((supercriticalFixedDefectGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
          m n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k gamma) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
  classical
  have hcore := supercriticalMatchingPenalty_of_closeStructure
    k hk gamma ⟨hgamma.1.le, hgamma.2⟩
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma
    P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  filter_upwards [hcore, eventually_ge_atTop nClose]
      with n hcoreN hnClose
  intro m hn D T hT hbalanced
  let F := supercriticalFixedDefectGraphFinset
    k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
      m n P.tau hn D T
  by_cases hF : F.Nonempty
  · have hresult : ∀ G ∈ F,
        Nonempty (SupercriticalCloseStructureResult
          k hk gamma P.alpha P.delta P.epsilon
            ⟨hgamma.1.le, hgamma.2⟩ G hn) := by
      intro G hG
      have hfixed : G ∈ supercriticalFixedDefectGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
            m n P.tau hn D T := by simpa [F] using hG
      have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hfixed).1
      have hclose :=
        (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
      have hfamily : G ∈
          inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
            supercriticalFarGraphFinset
              k hk gamma P.density_mem m n P.tau := by
        rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
        exact hclose
      have hR := superCloseStructureK1k k hk gamma P.density_mem
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            m hnClose G (by simpa [P.tau_eq] using hfamily)
      simpa using hR
    obtain ⟨G, hG⟩ := hF
    have hGfixed : G ∈ supercriticalFixedDefectGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
          m n P.tau hn D T := by simpa [F] using hG
    obtain ⟨R⟩ := hresult G hG
    have hlow : ∀ v : Fin n, ∀ i : Fin (k - 1),
        HasLowDegreeInPart T P.alpha D v i :=
      low_degree_everywhere_of_mem_fixedDefect hGfixed R
    have hadmissible : ∀ H ∈ F,
        SupercriticalProfileAtShift D m
          (supercriticalOffDiagonal k gamma) P.delta
            (supercriticalDefectShift T D) (crossEdgeProfile H D) := by
      intro H hH
      have hHfixed : H ∈ supercriticalFixedDefectGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
            m n P.tau hn D T := by simpa [F] using hH
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
              supercriticalOffDiagonal k gamma| ≤ P.delta := by
          rw [profileDensity_crossEdgeProfile]
          simpa only [hD] using hdensity
        rw [abs_le] at habs
        exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
    have hdeltaCount :=
      (supercriticalMatchingDeltaBound_spec P.rank P.density_mem
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

end InducedStars
