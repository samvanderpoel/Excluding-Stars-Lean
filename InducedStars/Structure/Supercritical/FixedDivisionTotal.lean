import InducedStars.Structure.Supercritical.FixedTotalAggregation

/-!
# Final fixed-defect aggregation in one prescribed division
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance fixedDivisionTotalGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## Active support patterns -/

/-- All support-incident graphs displayed by a combined defect pattern. -/
noncomputable def supercriticalCombinedSupportImage
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCombinedDefectPatternFinset
    k hk gamma hgamma m n tau hn D).image
      (supercriticalSupportIncidentGraph D)

@[simp] theorem mem_supercriticalCombinedSupportImage
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {T₀ : SimpleGraph (Fin n)} :
    T₀ ∈ supercriticalCombinedSupportImage hk hgamma m n tau hn D ↔
      ∃ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma hgamma m n tau hn D,
        supercriticalSupportIncidentGraph D T = T₀ := by
  classical
  simp [supercriticalCombinedSupportImage, eq_comm]

/-- Support patterns with a nonzero fixed-defect contribution. -/
noncomputable def supercriticalActiveSupportImage
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCombinedSupportImage hk hgamma m n tau hn D).filter
    fun T₀ ↦ 0 <
      supercriticalFixedSupportTotal hk hgamma alpha m n tau hn D T₀

@[simp] theorem mem_supercriticalActiveSupportImage
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    {T₀ : SimpleGraph (Fin n)} :
    T₀ ∈ supercriticalActiveSupportImage
        hk hgamma alpha m n tau hn D ↔
      T₀ ∈ supercriticalCombinedSupportImage
          hk hgamma m n tau hn D ∧
        0 < supercriticalFixedSupportTotal
          hk hgamma alpha m n tau hn D T₀ := by
  classical
  simp [supercriticalActiveSupportImage]

/-- Exact regrouping of the real fixed-defect total by support graph. -/
theorem sum_supercriticalFixedDefect_eq_sum_supportTotal
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    (((∑ T ∈ supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D,
      (supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T).card : ℕ) : ℝ)) =
      ∑ T₀ ∈ supercriticalCombinedSupportImage
          hk hgamma m n tau hn D,
        supercriticalFixedSupportTotal
          hk hgamma alpha m n tau hn D T₀ := by
  classical
  let patterns := supercriticalCombinedDefectPatternFinset
    k hk gamma hgamma m n tau hn D
  let support := supercriticalSupportIncidentGraph D
  let w : SimpleGraph (Fin n) → ℝ := fun T ↦
    ((supercriticalFixedDefectGraphFinset
      k hk gamma hgamma alpha m n tau hn D T).card : ℝ)
  have hcast :
      (((∑ T ∈ patterns,
        (supercriticalFixedDefectGraphFinset
          k hk gamma hgamma alpha m n tau hn D T).card : ℕ) : ℝ)) =
        ∑ T ∈ patterns, w T := by
    rw [Nat.cast_sum]
  rw [hcast]
  have hregroup :
      ∑ T ∈ patterns, w T =
        ∑ T₀ ∈ patterns.image support,
          ∑ T ∈ patterns with support T = T₀, w T :=
    by
      have hglobal :
          ∑ T ∈ patterns, w T =
            ∑ T₀ : SimpleGraph (Fin n),
              ∑ T ∈ patterns with support T = T₀, w T :=
        (Finset.sum_fiberwise_of_maps_to (by simp) w).symm
      have hrestrict :
          (∑ T₀ ∈ patterns.image support,
              ∑ T ∈ patterns with support T = T₀, w T) =
            ∑ T₀ : SimpleGraph (Fin n),
              ∑ T ∈ patterns with support T = T₀, w T := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro T₀ hT₀ hnot
        have hempty : patterns.filter (fun T ↦ support T = T₀) = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          intro hne
          obtain ⟨T, hTfiber⟩ := hne
          have hTdata := Finset.mem_filter.mp hTfiber
          apply hnot
          exact Finset.mem_image.mpr ⟨T, hTdata.1, hTdata.2⟩
        simp [hempty]
      exact hglobal.trans hrestrict.symm
  calc
    ∑ T ∈ patterns, w T =
        ∑ T₀ ∈ patterns.image support,
          ∑ T ∈ patterns with support T = T₀, w T := hregroup
    _ = ∑ T₀ ∈ supercriticalCombinedSupportImage
          hk hgamma m n tau hn D,
        supercriticalFixedSupportTotal
          hk hgamma alpha m n tau hn D T₀ := by
      rfl

/-- Removing zero support fibers does not change the regrouped sum. -/
theorem sum_supportTotal_eq_sum_activeSupport
    {k : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    (∑ T₀ ∈ supercriticalCombinedSupportImage
        hk hgamma m n tau hn D,
      supercriticalFixedSupportTotal
        hk hgamma alpha m n tau hn D T₀) =
      ∑ T₀ ∈ supercriticalActiveSupportImage
          hk hgamma alpha m n tau hn D,
        supercriticalFixedSupportTotal
          hk hgamma alpha m n tau hn D T₀ := by
  classical
  rw [supercriticalActiveSupportImage]
  exact (Finset.sum_subset (Finset.filter_subset _ _) (by
    intro T₀ hT₀ hnot
    have hnotPos : ¬ 0 < supercriticalFixedSupportTotal
        hk hgamma alpha m n tau hn D T₀ := by
      intro hpos
      apply hnot
      exact Finset.mem_filter.mpr ⟨hT₀, hpos⟩
    have hnonneg : 0 ≤ supercriticalFixedSupportTotal
        hk hgamma alpha m n tau hn D T₀ := by
      unfold supercriticalFixedSupportTotal
      positivity
    exact le_antisymm (le_of_not_gt hnotPos) hnonneg)).symm

/-! ## The estimate for one active support fiber -/

/-- An active support fiber has a positive matching number, belongs to the
low-support family, and satisfies the absorbed estimate with the full sparse
penalty.  The witness profile is the actual cross profile of any graph in a
positive fixed-defect summand. -/
theorem supercriticalActiveSupportTotal_le
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    {m : ℕ} {hn : k - 1 ≤ n}
    (hnClose : supercriticalCloseStructureVertexThreshold k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (T₀ : SimpleGraph (Fin n))
    (hT₀ : T₀ ∈ supercriticalActiveSupportImage hk P.density_mem
      P.alpha m n P.tau hn D)
    (hpointwise : ∀ T : SimpleGraph (Fin n),
      T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m n P.tau hn D →
      ((supercriticalFixedDefectGraphFinset
        k hk gamma P.density_mem P.alpha m n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k gamma) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T : ℝ) * (n : ℝ)))) :
    0 < supercriticalMatchingNumber D T₀ ∧
      supercriticalMatchingNumber D T₀ ≤ n ∧
      T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha
        (supercriticalMatchingNumber D T₀) ∧
      supercriticalFixedSupportTotal hk P.density_mem P.alpha
          m n P.tau hn D T₀ ≤
        ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
          Real.exp (-((15 * P.cMat / 16) *
              (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ)) -
            P.cAbs * (D.sparse.card : ℝ) * (n : ℝ)) := by
  classical
  have hactive := mem_supercriticalActiveSupportImage.mp hT₀
  have hsumPos := hactive.2
  unfold supercriticalFixedSupportTotal at hsumPos
  have hsummandNonneg : ∀ T ∈ supercriticalCombinedSupportFiber
      (hk := hk) (gamma := gamma) (hgamma := P.density_mem)
        (m := m) (tau := P.tau) (hn := hn) D T₀,
      0 ≤ ((supercriticalFixedDefectGraphFinset
        k hk gamma P.density_mem P.alpha m n P.tau hn D T).card : ℝ) := by
    intro T hT
    positivity
  obtain ⟨T, hTfiber, hcardPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hsummandNonneg).mp hsumPos
  have hT := (mem_supercriticalCombinedSupportFiber.mp hTfiber).1
  have hsupport := (mem_supercriticalCombinedSupportFiber.mp hTfiber).2
  have hcardNat : 0 < (supercriticalFixedDefectGraphFinset
      k hk gamma P.density_mem P.alpha m n P.tau hn D T).card := by
    exact_mod_cast hcardPos
  obtain ⟨G, hG⟩ := Finset.card_pos.mp hcardNat
  have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hG).1
  have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
  have hD := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
  have hcanonicalT := (mem_supercriticalFixedDefectGraphFinset.mp hG).2.1
  have hfamily : G ∈
      inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
        supercriticalFarGraphFinset
          k hk gamma P.density_mem m n P.tau := by
    rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hclose
  obtain ⟨R⟩ := superCloseStructureK1k k hk gamma P.density_mem
    P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
        m hnClose G (by simpa [P.tau_eq] using hfamily)
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
  have hprofileDefect : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) P.delta
        (supercriticalDefectShift T D) profile := by
    refine ⟨?_, ?_⟩
    · have hid := supercriticalFixedDefectProfile_edgeCount_identity
        (hn := hn) (profile := profile) hD hcanonicalT rfl
      have hedges : (finiteGraphEdges G).card = m := by
        simpa [finiteGraphEdges] using
          (mem_supercriticalCloseGraphFinset.mp hclose).2.1
      omega
    · intro e
      have hdensity := R.cross_density_close
        e.left e.right e.left_ne_right
      have habs :
          |profileDensity profile e - supercriticalOffDiagonal k gamma| ≤
            P.delta := by
        rw [profileDensity_crossEdgeProfile]
        simpa only [hD] using hdensity
      rw [abs_le] at habs
      exact ⟨by linarith [habs.1], by linarith [habs.2]⟩
  have hshift : supercriticalDefectShift T D =
      supercriticalSupportDefectShift D T₀ + (t : ℤ) := by
    simpa [t, hsupport] using
      (supercriticalDefectShift_eq_support_add_sparse D T)
  have hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) P.delta
        (supercriticalSupportDefectShift D T₀ + (t : ℤ)) profile := by
    rwa [← hshift]
  have ht : t ≤ Nat.choose D.sparse.card 2 := by
    dsimp [t]
    have hadd := inducedEdgeCount_add_compl
      (supercriticalSparseInducedPattern D T) D.sparse
    omega
  have hfiberPointwise : ∀ U ∈ supercriticalCombinedSupportFiber
      (hk := hk) (gamma := gamma) (hgamma := P.density_mem)
        (m := m) (tau := P.tau) (hn := hn) D T₀,
      ((supercriticalFixedDefectGraphFinset
        k hk gamma P.density_mem P.alpha m n P.tau hn D U).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k gamma) P.delta
            (supercriticalDefectShift U D) : ℝ) *
          Real.exp (-(P.cMat *
            (supercriticalMatchingNumber D T₀ : ℝ) * (n : ℝ))) := by
    intro U hU
    have hUdata := mem_supercriticalCombinedSupportFiber.mp hU
    have hmatchingU : supercriticalMatchingNumber D U =
        supercriticalMatchingNumber D T₀ := by
      rw [← supercriticalMatchingNumber_supportIncident D U, hUdata.2]
    simpa only [hmatchingU] using hpointwise U hUdata.1
  refine ⟨hmatchPos, hmatchLe, hT₀Low, ?_⟩
  exact supercriticalFixedSupportTotal_le_absorbedCoPartite
    hk hgamma P hn D T₀ (supercriticalMatchingNumber D T₀)
      hbalanced hsparse hT₀Low profile t hprofile ht hfiberPointwise

/-! ## The divisionwise fixed-defect total -/

/-- The complete fixed-small-defect contribution in one balanced prescribed
division is exponentially smaller than its absorbed co-partite fiber.  The
matching-size sum retains half the matching penalty, and half the sparse
absorption penalty is reserved for the later global preimage sum. -/
theorem eventually_supercriticalFixedDefectDivisionTotal_le
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (m : ℕ) (hn : k - 1 ≤ n)
        (D : SupercriticalDivision k (Fin n)),
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha
            m n P.tau hn D T).card : ℕ) : ℝ)) ≤
        ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ) *
          Real.exp (-(P.linearRate * (n : ℝ)) -
            (P.cAbs / 2) * (D.sparse.card : ℝ) * (n : ℝ)) := by
  classical
  have hpattern := eventually_supercriticalFixedPattern_le_profileMass
    k hk gamma hgamma P
  have hsupport := eventually_card_supercriticalLowSupportPatternFinset_le_exp
    k hk gamma P
  have hseries :=
    eventually_sum_Icc_exp_neg_thirteen_sixteenths_le P.cMat_pos
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma
    P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  filter_upwards [hpattern, hsupport, hseries, eventually_ge_atTop nClose]
      with n hpatternN hsupportN hseriesN hnClose
  intro m hn D hbalanced hsparse
  let active := supercriticalActiveSupportImage hk P.density_mem
    P.alpha m n P.tau hn D
  let idx : SimpleGraph (Fin n) → ℕ :=
    fun T₀ ↦ supercriticalMatchingNumber D T₀
  let total : SimpleGraph (Fin n) → ℝ := fun T₀ ↦
    supercriticalFixedSupportTotal hk P.density_mem P.alpha
      m n P.tau hn D T₀
  let A : ℝ :=
    ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card : ℝ)
  let s : ℝ := (D.sparse.card : ℝ)
  have hdata (T₀ : SimpleGraph (Fin n)) (hT₀ : T₀ ∈ active) :
      0 < idx T₀ ∧ idx T₀ ≤ n ∧
        T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha (idx T₀) ∧
        total T₀ ≤ A *
          Real.exp (-((15 * P.cMat / 16) * (idx T₀ : ℝ) * (n : ℝ)) -
            P.cAbs * s * (n : ℝ)) := by
    have hpointwise : ∀ T : SimpleGraph (Fin n),
        T ∈ supercriticalCombinedDefectPatternFinset
            k hk gamma P.density_mem m n P.tau hn D →
        ((supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha
            m n P.tau hn D T).card : ℝ) ≤
          (supercriticalProfileMassAtShift D m
            (supercriticalOffDiagonal k gamma) P.delta
              (supercriticalDefectShift T D) : ℝ) *
            Real.exp (-(P.cMat *
              (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
      intro T hT
      exact hpatternN m hn D T hT hbalanced
    have h := supercriticalActiveSupportTotal_le hk hgamma P hnClose
      D hbalanced hsparse T₀ (by simpa [active] using hT₀) hpointwise
    simpa [idx, total, A, s] using h
  have horiginal :
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha
            m n P.tau hn D T).card : ℕ) : ℝ)) =
        ∑ T₀ ∈ active, total T₀ := by
    calc
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk gamma P.density_mem m n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk gamma P.density_mem P.alpha
            m n P.tau hn D T).card : ℕ) : ℝ)) =
          ∑ T₀ ∈ supercriticalCombinedSupportImage
              hk P.density_mem m n P.tau hn D,
            supercriticalFixedSupportTotal hk P.density_mem P.alpha
              m n P.tau hn D T₀ :=
        sum_supercriticalFixedDefect_eq_sum_supportTotal
          hk P.density_mem P.alpha m n P.tau hn D
      _ = ∑ T₀ ∈ supercriticalActiveSupportImage
              hk P.density_mem P.alpha m n P.tau hn D,
            supercriticalFixedSupportTotal hk P.density_mem P.alpha
              m n P.tau hn D T₀ :=
        sum_supportTotal_eq_sum_activeSupport
          hk P.density_mem P.alpha m n P.tau hn D
      _ = ∑ T₀ ∈ active, total T₀ := by rfl
  rw [horiginal]
  have hcover (T₀ : SimpleGraph (Fin n)) (hT₀ : T₀ ∈ active) :
      total T₀ ≤
        ∑ h ∈ Finset.Icc 1 n,
          if idx T₀ = h then total T₀ else 0 := by
    have hmem : idx T₀ ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨(hdata T₀ hT₀).1,
        (hdata T₀ hT₀).2.1⟩
    have heq : (∑ h ∈ Finset.Icc 1 n,
        if idx T₀ = h then total T₀ else 0) = total T₀ := by
      simp [hmem]
    exact heq.ge
  have hdouble :
      (∑ T₀ ∈ active, total T₀) ≤
        ∑ h ∈ Finset.Icc 1 n,
          ∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0 := by
    calc
      (∑ T₀ ∈ active, total T₀) ≤
          ∑ T₀ ∈ active,
            ∑ h ∈ Finset.Icc 1 n,
              if idx T₀ = h then total T₀ else 0 :=
        Finset.sum_le_sum fun T₀ hT₀ ↦ hcover T₀ hT₀
      _ = ∑ h ∈ Finset.Icc 1 n,
          ∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0 := by
        rw [Finset.sum_comm]
  have hfiber (h : ℕ) (hh : h ∈ Finset.Icc 1 n) :
      (∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0) ≤
        A * Real.exp (-(P.cAbs * s * (n : ℝ))) *
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
    let fiber := active.filter fun T₀ ↦ idx T₀ = h
    have hsumEq :
        (∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0) =
          ∑ T₀ ∈ fiber, total T₀ := by
      dsimp [fiber]
      rw [Finset.sum_filter]
    rw [hsumEq]
    have hfiberSubset : fiber ⊆
        supercriticalLowSupportPatternFinset D P.alpha h := by
      intro T₀ hT₀
      have hmem := Finset.mem_filter.mp hT₀
      have hlow := (hdata T₀ hmem.1).2.2.1
      rwa [hmem.2] at hlow
    have hcardNat : fiber.card ≤
        (supercriticalLowSupportPatternFinset D P.alpha h).card :=
      Finset.card_le_card hfiberSubset
    have hcardReal : (fiber.card : ℝ) ≤
        (supercriticalLowSupportPatternFinset D P.alpha h).card := by
      exact_mod_cast hcardNat
    have hbound (T₀ : SimpleGraph (Fin n)) (hT₀ : T₀ ∈ fiber) :
        total T₀ ≤ A *
          Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
            P.cAbs * s * (n : ℝ)) := by
      have hmem := Finset.mem_filter.mp hT₀
      have hb := (hdata T₀ hmem.1).2.2.2
      simpa only [hmem.2] using hb
    have hsupportCount := hsupportN D h hsparse
      (Finset.mem_Icc.mp hh).1
    calc
      (∑ T₀ ∈ fiber, total T₀) ≤
          ∑ T₀ ∈ fiber, A *
            Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
              P.cAbs * s * (n : ℝ)) :=
        Finset.sum_le_sum fun T₀ hT₀ ↦ hbound T₀ hT₀
      _ = (fiber.card : ℝ) * (A *
            Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
              P.cAbs * s * (n : ℝ))) := by simp
      _ ≤ ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) *
            (A * Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
              P.cAbs * s * (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hcardReal (by positivity)
      _ ≤ Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) *
            (A * Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
              P.cAbs * s * (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hsupportCount (by positivity)
      _ = A * Real.exp (-(P.cAbs * s * (n : ℝ))) *
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
        calc
          Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) *
              (A * Real.exp (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
                P.cAbs * s * (n : ℝ))) =
              A * Real.exp (((P.cMat / 8) * (h : ℝ) * (n : ℝ)) +
                (-((15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) -
                  P.cAbs * s * (n : ℝ))) := by
            rw [Real.exp_add]
            ring
          _ = A * Real.exp (-(P.cAbs * s * (n : ℝ)) +
                -((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
            congr 2
            ring
          _ = A * Real.exp (-(P.cAbs * s * (n : ℝ))) *
              Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
            rw [Real.exp_add]
            ring
  calc
    (∑ T₀ ∈ active, total T₀) ≤
        ∑ h ∈ Finset.Icc 1 n,
          ∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0 := hdouble
    _ ≤ ∑ h ∈ Finset.Icc 1 n,
        A * Real.exp (-(P.cAbs * s * (n : ℝ))) *
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) :=
      Finset.sum_le_sum fun h hh ↦ hfiber h hh
    _ = (A * Real.exp (-(P.cAbs * s * (n : ℝ)))) *
        (∑ h ∈ Finset.Icc 1 n,
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (A * Real.exp (-(P.cAbs * s * (n : ℝ)))) *
        Real.exp (-((P.cMat / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hseriesN (by positivity)
    _ = A * Real.exp (-((P.cMat / 2) * (n : ℝ)) -
        P.cAbs * s * (n : ℝ)) := by
      rw [show -((P.cMat / 2) * (n : ℝ)) - P.cAbs * s * (n : ℝ) =
          -(P.cAbs * s * (n : ℝ)) + -((P.cMat / 2) * (n : ℝ)) by ring,
        Real.exp_add]
      ring
    _ ≤ A * Real.exp (-(P.linearRate * (n : ℝ)) -
        (P.cAbs / 2) * s * (n : ℝ)) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have hrate : P.linearRate ≤ P.cMat / 2 := min_le_left _ _
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hrateCost : 0 ≤ (P.cMat / 2 - P.linearRate) * (n : ℝ) :=
        mul_nonneg (sub_nonneg.mpr hrate) hn0
      have hsparseCost : 0 ≤ (P.cAbs / 2) * s * (n : ℝ) := by
        dsimp [s]
        exact mul_nonneg
          (mul_nonneg (div_nonneg P.cAbs_pos.le (by norm_num)) (by positivity))
          (by positivity)
      nlinarith

end InducedStars
