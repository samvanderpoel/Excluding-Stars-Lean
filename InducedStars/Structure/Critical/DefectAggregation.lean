import InducedStars.Structure.Critical.AggregationParameters
import InducedStars.Structure.Supercritical.FixedDivisionTotal
import InducedStars.Structure.Supercritical.FixedSupportAggregation

/-!
# Endpoint estimates for fixed-remainder counting

The matching-profile, medium-degree, and support-pattern estimates specialize
the supercritical finite counting arguments to `gammaK k`. They are uniform
in the finite edge count and supply the fixed-remainder comparison.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

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

end InducedStars
