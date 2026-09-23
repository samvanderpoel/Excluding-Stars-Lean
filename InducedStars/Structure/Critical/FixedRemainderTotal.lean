import InducedStars.Structure.Critical.FixedRemainder

/-!
# Uniform nonclean bounds with a prescribed remainder

The count is taken in the existing canonical nonclean family. The proof
splits the medium-degree and fixed-pattern branches before summing over the
remainder, as required by the logarithmic critical window.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

private theorem profileMultiplicity_le_profileMass
    {k n m : ℕ} (D : SupercriticalDivision k (Fin n))
    (p : SupercriticalEdgeProfile D) {rho delta : ℝ} {u : ℤ}
    (hp : SupercriticalProfileAtShift D m rho delta u p) :
    supercriticalProfileMultiplicity p ≤
      supercriticalProfileMassAtShift D m rho delta u := by
  classical
  unfold supercriticalProfileMassAtShift
  have hsingle := Finset.single_le_sum
    (s := supercriticalAllEdgeProfilesFinset D)
    (f := fun q ↦ if SupercriticalProfileAtShift D m rho delta u q then
      supercriticalProfileMultiplicity q else 0)
    (fun _ _ ↦ Nat.zero_le _) (mem_supercriticalAllEdgeProfilesFinset D p)
  simpa only [if_pos hp] using hsingle

/-- The medium-degree branch retains half its quadratic exponent when the
sparse graph is held fixed. -/
theorem criticalFixedRemainderMedium_le_reference
    {k n m M : ℕ} (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (t : ℕ)
    (base : SupercriticalEdgeProfile D)
    (hbudget : M + divisionInternalCliqueCapacity D + t = m)
    (hMC : M ≤ supercriticalTotalCrossCapacity D)
    (hMlo : criticalDensityMargin k * (supercriticalTotalCrossCapacity D : ℝ) ≤ M)
    (hMhi : (M : ℝ) ≤ (1 - criticalDensityMargin k) *
      (supercriticalTotalCrossCapacity D : ℝ))
    (ht : (t : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2)
    (hwindow : SupercriticalProfileWindow D m
      (supercriticalOffDiagonal k (gammaK k)) P.delta
        ⌊P.epsilon * (n : ℝ) ^ 2⌋₊ base)
    (hmedium :
      ((supercriticalMediumDegreeGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          m n P.tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2))) :
    ((supercriticalMediumDegreeGraphFinset
      k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
        m n P.tau hn D).card : ℝ) ≤
      (Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (-(P.cMed / 2) * (n : ℝ) ^ 2) := by
  obtain ⟨u, huFloor, hp⟩ := hwindow
  have hu : (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
    exact (show (u.natAbs : ℝ) ≤
      (⌊P.epsilon * (n : ℝ) ^ 2⌋₊ : ℕ) by exact_mod_cast huFloor).trans
        (Nat.floor_le (by positivity [P.epsilon_pos]))
  have hshift : ((u - (t : ℤ)).natAbs : ℝ) ≤
      2 * P.epsilon * (n : ℝ) ^ 2 := by
    have habs : (u - (t : ℤ)).natAbs ≤ u.natAbs + t := by
      simpa using Int.natAbs_sub_le u (t : ℤ)
    have hcast : ((u - (t : ℤ)).natAbs : ℝ) ≤ (u.natAbs : ℝ) + t := by
      exact_mod_cast habs
    linarith
  have hsingle : (supercriticalProfileMultiplicity base : ℝ) ≤
      (supercriticalProfileMassAtShift D m
        (supercriticalOffDiagonal k (gammaK k)) P.delta u : ℝ) := by
    exact_mod_cast profileMultiplicity_le_profileMass D base hp
  have hmass := supercriticalProfileMassAtShift_le_referenceCrossChoose
    D m M t (supercriticalOffDiagonal k (gammaK k)) P.delta
      (criticalDensityMargin k) (u - (t : ℤ))
        hbudget hMC (criticalDensityMargin_pos hk) (criticalDensityMargin_lt_half hk)
          hMlo hMhi
  simp only [sub_add_cancel] at hmass
  have hc : DenseGraph.binomialCompactBandShiftConstant (criticalDensityMargin k) =
      P.cShift := by rw [P.cShift_eq, criticalShiftErrorConstant]
  rw [hc] at hmass
  have hcost := mul_le_mul_of_nonneg_left hshift P.cShift_pos.le
  have hsmall := mul_le_mul_of_nonneg_right P.medium_shift_small.le
    (sq_nonneg (n : ℝ))
  calc
    _ ≤ (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := hmedium
    _ ≤ ((Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (P.cShift * ((u - (t : ℤ)).natAbs : ℝ))) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right (hsingle.trans hmass) (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      nlinarith only [hcost, hsmall]

/-- The endpoint version of the paper's fixed-remainder nonclean bound.
It is uniform in the finite edge count, hence applies to the exact
logarithmic-window floor sequence. -/
theorem eventually_criticalFixedRemainderDefect_le_reference
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop, ∀ (m : ℕ) (hn : k - 1 ≤ n)
      (D : SupercriticalDivision k (Fin n)) (H : Finset (Sym2 (Fin n))),
      ((supercriticalFixedRemainderDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          m n P.tau hn D H).card : ℝ) ≤
        (Nat.choose (supercriticalTotalCrossCapacity D)
          (m - (divisionInternalCliqueCapacity D + H.card)) : ℝ) *
            Real.exp (-(P.cMat / 4) * n) := by
  classical
  let hgamma := gammaK_mem_supercritical_Ico k hk
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    hgamma P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
      P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
  have hlarge : ∀ᶠ n : ℕ in atTop,
      P.cMat / P.cMed ≤ (n : ℝ) ∧
        4 * Real.log 2 / P.cMat ≤ (n : ℝ) := by
    exact (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)).and
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _))
  filter_upwards [
    eventually_criticalFixedPattern_le_profileMass_anyEdgeCount k hk P,
    eventually_criticalMediumDegree_le_profileMultiplicity_anyEdgeCount k hk P,
    eventually_card_criticalLowSupportPatternFinset_le_exp k hk P,
    eventually_sum_Icc_exp_neg_thirteen_sixteenths_le P.cMat_pos,
    eventually_ge_atTop nClose, hlarge]
    with n hpatternN hmediumN hsupportN hseriesN hnClose hlargeN
  intro m hn D H
  let F := supercriticalFixedRemainderDefectGraphFinset
    k hk (gammaK k) hgamma m n P.tau hn D H
  let M := m - (divisionInternalCliqueCapacity D + H.card)
  let A : ℝ := Nat.choose (supercriticalTotalCrossCapacity D) M
  have getClose (G : SimpleGraph (Fin n))
      (hG : G ∈ supercriticalDivisionDefectGraphFinset
        k hk (gammaK k) hgamma m n P.tau hn D) :
      Nonempty (SupercriticalCloseStructureResult k hk (gammaK k)
        P.alpha P.delta P.epsilon hgamma G hn) := by
    have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hG).1
    have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
        supercriticalFarGraphFinset k hk (gammaK k) hgamma m n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hclose
    exact superCloseStructureK1k k hk (gammaK k) hgamma P.alpha P.alpha_mem_Ioo
      P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower P.rho_three_upper
        P.epsilon P.epsilon_pos m hnClose G (by simpa [P.tau_eq] using hfamily)
  by_cases hF : F.Nonempty
  · obtain ⟨G, hG⟩ := hF
    obtain ⟨hGdef, hGH⟩ := mem_supercriticalFixedRemainderDefectGraphFinset.mp hG
    obtain ⟨R⟩ := getClose G hGdef
    have hGdata := mem_supercriticalDivisionDefectGraphFinset.mp hGdef
    have hedges : (finiteGraphEdges G).card = m := by
      simpa [finiteGraphEdges] using (mem_supercriticalCloseGraphFinset.mp hGdata.1).2.1
    have hband := criticalFixedRemainderReferenceBand_of_close
      hk P G R D hGdata.2.1 hedges
    rw [hGH] at hband
    have hbudget : M + divisionInternalCliqueCapacity D + H.card = m := by
      dsimp [M]; omega
    have hbalanced : ∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n := by
      intro i
      simpa only [hGdata.2.1, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
        using R.part_card_close i
    have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
      simpa only [hGdata.2.1] using R.sparse_card_le
    let S := (supercriticalCombinedDefectPatternFinset
      k hk (gammaK k) hgamma m n P.tau hn D).filter
        fun T ↦ supercriticalSparseInducedEdges T D = H ∧
          (supercriticalFixedDefectGraphFinset
            k hk (gammaK k) hgamma P.alpha m n P.tau hn D T).Nonempty
    let med := (supercriticalMediumDegreeGraphFinset
      k hk (gammaK k) hgamma P.alpha m n P.tau hn D).filter
        fun G ↦ supercriticalSparseInducedEdges G D = H
    let w : SimpleGraph (Fin n) → ℝ := fun T ↦
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) hgamma P.alpha m n P.tau hn D T).card : ℝ)
    have hdata (T : SimpleGraph (Fin n)) (hT : T ∈ S) :=
      criticalFixedDefectPattern_lowSupport hk P hnClose D T
        (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2.2
    have hsum : (∑ T ∈ S, w T) ≤ A * Real.exp (-((P.cMat / 2) * n)) := by
      apply criticalFixedRemainderPatternSum_le P D S H w A (by positivity)
        (fun T hT ↦ (Finset.mem_filter.mp hT).2.1) hdata
      · intro T hT
        exact criticalFixedRemainderPattern_le_reference hk P D T H
          (Finset.mem_filter.mp hT).2.1 hbudget hband.2.1
            hband.2.2.1 hband.2.2.2 hsparse (hdata T hT).2.2
              (hpatternN m hn D T (Finset.mem_filter.mp hT).1 hbalanced)
      · intro h hh
        exact hsupportN D h hsparse (Finset.mem_Icc.mp hh).1
      · exact hseriesN
    have hmed : (med.card : ℝ) ≤ A * Real.exp (-(P.cMed / 2) * (n : ℝ) ^ 2) := by
      by_cases hmedne : med.Nonempty
      · obtain ⟨J, hJ⟩ := hmedne
        have hJfilter := Finset.mem_filter.mp hJ
        have hJdef := (mem_supercriticalMediumDegreeGraphFinset.mp hJfilter.1).1
        have hJdata := mem_supercriticalDivisionDefectGraphFinset.mp hJdef
        obtain ⟨RJ⟩ := getClose J hJdef
        have hJedges : (finiteGraphEdges J).card = m := by
          simpa [finiteGraphEdges] using
            (mem_supercriticalCloseGraphFinset.mp hJdata.1).2.1
        have hwindow := canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
          hk hgamma J hn RJ m hJedges
        rw [hJdata.2.1] at hwindow
        have ht : (H.card : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
          have hcost : (supercriticalDefectCost J D : ℝ) ≤
              P.epsilon * (n : ℝ) ^ 2 := by
            simpa [canonicalSupercriticalDefectCost, hJdata.2.1] using
              RJ.canonicalDefectCost_le
          have htCost : ((supercriticalSparseInducedEdges J D).card : ℝ) ≤
              supercriticalDefectCost J D := by
            exact_mod_cast card_supercriticalSparseInducedEdges_le_cost J D
          rw [hJfilter.2] at htCost
          exact htCost.trans hcost
        have hraw := criticalFixedRemainderMedium_le_reference hk P D H.card
          (crossEdgeProfile J D) hbudget hband.2.1 hband.2.2.1 hband.2.2.2
            ht hwindow (hmediumN m hn D (crossEdgeProfile J D) hwindow)
        have hcard : (med.card : ℝ) ≤
            (supercriticalMediumDegreeGraphFinset
              k hk (gammaK k) hgamma P.alpha m n P.tau hn D).card := by
          exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
        exact hcard.trans hraw
      · rw [Finset.not_nonempty_iff_eq_empty.mp hmedne]
        simp only [Finset.card_empty, Nat.cast_zero]
        positivity
    have hcover : F ⊆ med ∪ S.biUnion
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) hgamma P.alpha m n P.tau hn D) :=
      supercriticalFixedRemainderDefect_subset_medium_union_fixed
        P.alpha m n P.tau hn D H
    have hcardNat : F.card ≤ med.card +
        ∑ T ∈ S, (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) hgamma P.alpha m n P.tau hn D T).card :=
      (Finset.card_le_card hcover).trans
        ((Finset.card_union_le _ _).trans
          (Nat.add_le_add_left (Finset.card_biUnion_le) _))
    have hcard : (F.card : ℝ) ≤ (med.card : ℝ) + ∑ T ∈ S, w T := by
      dsimp [w]
      exact_mod_cast hcardNat
    have hquadratic : P.cMat * (n : ℝ) ≤ P.cMed * (n : ℝ) ^ 2 := by
      have h := (div_le_iff₀ P.cMed_pos).mp hlargeN.1
      have hmul := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (α := ℝ) n)
      nlinarith only [hmul]
    have hlogTwo : Real.log 2 ≤ (P.cMat / 4) * (n : ℝ) := by
      have h := (div_le_iff₀ P.cMat_pos).mp hlargeN.2
      nlinarith only [h]
    calc
      (F.card : ℝ) ≤ (med.card : ℝ) + ∑ T ∈ S, w T := hcard
      _ ≤ A * Real.exp (-(P.cMed / 2) * (n : ℝ) ^ 2) +
          A * Real.exp (-((P.cMat / 2) * n)) := add_le_add hmed hsum
      _ ≤ A * Real.exp (-((P.cMat / 2) * n)) +
          A * Real.exp (-((P.cMat / 2) * n)) := by
        gcongr
        linarith
      _ = A * Real.exp (Real.log 2 - (P.cMat / 2) * n) := by
        rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          Real.exp_neg]
        ring
      _ ≤ A * Real.exp (-(P.cMat / 4) * n) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
        linarith
  · change (F.card : ℝ) ≤ A * Real.exp (-(P.cMat / 4) * n)
    rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end InducedStars
