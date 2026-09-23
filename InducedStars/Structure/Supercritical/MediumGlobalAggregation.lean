import InducedStars.Structure.Supercritical.FixedDefectAggregation
import InducedStars.Structure.Supercritical.GlobalAggregation
import InducedStars.Structure.Supercritical.ReferenceFiber

/-!
# Global aggregation of the supercritical medium-degree family

This module turns the uniform, per-division quadratic estimate of
`supercriticalMediumDegreePenalty_of_closeStructure` into the exact global
medium-family estimate used by the final supercritical theorem.  A profile
chosen from a nonempty medium fiber is compared with the co-multipartite
fiber of the sparse-absorbed division.  The signed profile shift is paid
explicitly, and the number of ordered divisions is absorbed into the
remaining quadratic exponential rate.
-/

noncomputable section

set_option maxHeartbeats 800000

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

/-! ## A single profile occurs in its shifted aggregate -/

/-- The `t = 0` term of the shifted aggregate contains every profile at the
displayed signed shift.  This elementary observation is the bridge from the
per-division medium penalty to the repaired signed absorption comparison. -/
theorem supercriticalProfileMultiplicity_le_shiftedProfileAggregate
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (u : ℤ) (profile : SupercriticalEdgeProfile D)
    (hprofile : SupercriticalProfileAtShift D m rho delta u profile) :
    supercriticalProfileMultiplicity profile ≤
      supercriticalShiftedProfileAggregate D m rho delta u := by
  classical
  unfold supercriticalShiftedProfileAggregate
  let inner : ℕ → ℕ := fun t ↦
    ∑ p ∈ supercriticalAllEdgeProfilesFinset D,
      if SupercriticalProfileAtShift D m rho delta
          (u + (t : ℤ)) p then
        supercriticalProfileMultiplicity p *
          Nat.choose (supercriticalSparsePotentialCapacity D) t
      else 0
  have hprofileAll : profile ∈ supercriticalAllEdgeProfilesFinset D :=
    mem_supercriticalAllEdgeProfilesFinset D profile
  have hterm : supercriticalProfileMultiplicity profile ≤ inner 0 := by
    dsimp [inner]
    have hsingle := Finset.single_le_sum
      (s := supercriticalAllEdgeProfilesFinset D)
      (f := fun p ↦
        if SupercriticalProfileAtShift D m rho delta
            (u + (0 : ℤ)) p then
          supercriticalProfileMultiplicity p *
            Nat.choose (supercriticalSparsePotentialCapacity D) 0
        else 0)
      (fun p _hp ↦ Nat.zero_le _) hprofileAll
    simpa [hprofile] using hsingle
  have hzero : 0 ∈ Finset.range
      (supercriticalSparsePotentialCapacity D + 1) := by simp
  exact hterm.trans <| Finset.single_le_sum
    (fun t _ht ↦ Nat.zero_le (inner t)) hzero

/-! ## Exponential absorption of ordered divisions -/

/-- Every fixed exponential `k^n` is eventually absorbed into an arbitrarily
small positive quadratic exponential. -/
theorem eventually_natPow_le_exp_quadratic (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ((k ^ n : ℕ) : ℝ) ≤ Real.exp (c * (n : ℝ) ^ 2) := by
  by_cases hk0 : k = 0
  · subst k
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [Nat.zero_pow (by omega : 0 < n), Nat.cast_zero]
    positivity
  · have hkpos : (0 : ℝ) < k := by
      exact_mod_cast (Nat.pos_of_ne_zero hk0)
    have htend : Tendsto (fun n : ℕ ↦ c * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc
    have hlinear : ∀ᶠ n : ℕ in atTop,
        Real.log (k : ℝ) ≤ c * (n : ℝ) :=
      htend.eventually (eventually_ge_atTop (Real.log (k : ℝ)))
    filter_upwards [hlinear, eventually_ge_atTop 1] with n hnlog hn
    calc
      ((k ^ n : ℕ) : ℝ) = (k : ℝ) ^ n := by norm_num
      _ = Real.exp ((n : ℝ) * Real.log (k : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hkpos]
      _ ≤ Real.exp (c * (n : ℝ) ^ 2) := by
        apply Real.exp_le_exp.mpr
        have hn0 : (0 : ℝ) ≤ n := by positivity
        calc
          (n : ℝ) * Real.log (k : ℝ) ≤
              (n : ℝ) * (c * (n : ℝ)) :=
            mul_le_mul_of_nonneg_left hnlog hn0
          _ = c * (n : ℝ) ^ 2 := by ring

/-! ## One medium fiber versus its absorbed co-partite fiber -/

/-- A per-profile medium penalty, a signed profile witness, and the exact
signed-absorption geometry give a quadratic bound relative to the absorbed
co-multipartite fiber.  The term `cAbs * |sparse| * n` is nonnegative and is
discarded here; only the signed shift cost is charged to the medium rate. -/
theorem card_supercriticalMediumDegreeGraphFinset_le_absorbedCoPartite
    {k n : ℕ} (hk : 3 ≤ k) {gamma : ℝ}
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    {m : ℕ} {tau : ℝ} (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n))
    (base : SupercriticalEdgeProfile D) (u : ℤ)
    (hprofile : SupercriticalProfileAtShift D m
      (supercriticalOffDiagonal k gamma) P.delta u base)
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n)
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (hu : (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2)
    (H : SupercriticalSignedShiftGeometryHypotheses
      (gamma := gamma) hk P.delta D u)
    (hmedium :
      ((supercriticalMediumDegreeGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha m n tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2))) :
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha m n tau hn D).card : ℝ) ≤
      (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2)) := by
  have hdata := supercriticalShiftedAbsorptionData_of_profile
    hk hgamma D base (u := u) (t := 0) (by simpa using hprofile) (by simp) H
  have haggregate :=
    supercriticalShiftedProfileAggregate_le_absorbedCoPartite
      hk hgamma P.delta_pos.le P.delta_le_jointAbsorptionBound
        (rho := supercriticalOffDiagonal k gamma) (D := D)
        (m := m) (LShift := profileTotal base) (u := u)
        hdata.aggregate_count hbalanced hsparse
        hdata.sparseChoice_le_gain hdata.absorbedInternal_le_m
        hdata.shiftSelected_le_preAbsorption
        hdata.cleanSelected_le_preAbsorption
        hdata.absorbedSelected_le_capacity hdata.absorbedDensity_lower
        hdata.shiftBand_lower hdata.shiftBand_upper hdata.selected_distance
  have hsingleNat :=
    supercriticalProfileMultiplicity_le_shiftedProfileAggregate
      D m (supercriticalOffDiagonal k gamma) P.delta u base hprofile
  have hsingle : (supercriticalProfileMultiplicity base : ℝ) ≤
      (supercriticalShiftedProfileAggregate D m
        (supercriticalOffDiagonal k gamma) P.delta u : ℝ) := by
    exact_mod_cast hsingleNat
  have hprofileBound : (supercriticalProfileMultiplicity base : ℝ) ≤
      (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-(P.cAbs * (D.sparse.card : ℝ) * n) +
          P.cShift * (u.natAbs : ℝ)) := by
    rw [P.cAbs_eq, P.cShift_eq]
    exact hsingle.trans haggregate
  have hshift : P.cShift * (u.natAbs : ℝ) ≤
      (P.cMed / 4) * (n : ℝ) ^ 2 := by
    calc
      P.cShift * (u.natAbs : ℝ) ≤
          P.cShift * (P.epsilon * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hu P.cShift_pos.le
      _ = (P.cShift * P.epsilon) * (n : ℝ) ^ 2 := by ring
      _ ≤ (P.cMed / 4) * (n : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_right P.medium_shift_small.le (by positivity)
  calc
    ((supercriticalMediumDegreeGraphFinset
      k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha m n tau hn D).card : ℝ) ≤
        (supercriticalProfileMultiplicity base : ℝ) *
          Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := hmedium
    _ ≤ ((supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
          Real.exp (-(P.cAbs * (D.sparse.card : ℝ) * n) +
            P.cShift * (u.natAbs : ℝ))) *
        Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hprofileBound (Real.exp_nonneg _)
    _ ≤ (supercriticalAbsorbedCoPartiteGraphFinset hk D m).card *
        Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2)) := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      have habs : 0 ≤ P.cAbs * (D.sparse.card : ℝ) * n := by
        exact mul_nonneg (mul_nonneg P.cAbs_pos.le (by positivity)) (by positivity)
      linarith

/-! ## Summing over every canonical division -/

/-- Global medium aggregation from the uniform signed-geometry consequence
of the parameter hierarchy.  The separate hypothesis is discharged below;
keeping this composition theorem explicit makes the finite source of every
factor visible. -/
theorem eventually_supercriticalMediumTotal_le_of_signedGeometry
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (hgeometry : ∀ᶠ n : ℕ in atTop,
      ∀ (D : SupercriticalDivision k (Fin n)) (u : ℤ),
        (∀ i : Fin (k - 1),
          |((D.parts i).card : ℝ) -
              (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
        (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
        (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 →
        SupercriticalSignedShiftGeometryHypotheses
          (gamma := gamma) hk P.delta D u) :
    ∀ m : ℕ → ℕ, ∀ᶠ n : ℕ in atTop,
      (supercriticalMediumTotal k hk gamma
        ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) ≤
      (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
        Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := by
  classical
  have hcore := supercriticalMediumDegreePenalty_of_closeStructure
    k hk ⟨hgamma.1.le, hgamma.2⟩ P.alpha_pos P.delta_pos
      P.medium_candidate_delta P.medium_janson_range
      P.medium_profile_lower P.medium_profile_upper P.epsilon_pos
      P.epsilon_pattern_small P.medium_candidate_epsilon
      P.medium_defect_rate P.medium_profile_rate
  let nClose := supercriticalCloseStructureVertexThreshold k hk gamma
    P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
      P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
        P.epsilon_pos
  have hpow := eventually_natPow_le_exp_quadratic k
    (show 0 < P.cMed / 4 by exact div_pos P.cMed_pos (by norm_num))
  intro m
  filter_upwards [hcore, hgeometry, hpow, eventually_ge_atTop nClose]
      with n hcoreN hgeometryN hpowN hnClose
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk gamma
      P.density_mem P.alpha P.alpha_mem_Ioo P.delta P.delta_pos
        P.delta_lt_alpha P.rho_three_lower P.rho_three_upper P.epsilon
          P.epsilon_pos).trans hnClose
  let C : ℝ := coMultipartiteGraphCountWithEdges (k - 1) n (m n)
  have hdivisionBound (D : SupercriticalDivision k (Fin n)) :
      ((supercriticalMediumDegreeGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
          (m n) n P.tau hn D).card : ℝ) ≤
        C * Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2)) := by
    by_cases hempty : (supercriticalMediumDegreeGraphFinset
        k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
          (m n) n P.tau hn D).Nonempty
    · obtain ⟨G, hG⟩ := hempty
      have hresult : ∀ H ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ (m n) n P.tau hn D,
          Nonempty (SupercriticalCloseStructureResult
            k hk gamma P.alpha P.delta P.epsilon
              ⟨hgamma.1.le, hgamma.2⟩ H hn) := by
        intro H hH
        have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hH).1
        have hfamily : H ∈
            inducedFreeGraphFinsetWithEdges (inducedStar k) n (m n) \
              supercriticalFarGraphFinset k hk gamma P.density_mem
                (m n) n P.tau := by
          rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
          exact hclose
        have hR := superCloseStructureK1k k hk gamma P.density_mem
          P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
            P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
              (m n) hnClose H (by simpa [P.tau_eq] using hfamily)
        simpa using hR
      have hdefect := (mem_supercriticalMediumDegreeGraphFinset.mp hG).1
      obtain ⟨R⟩ := hresult G hdefect
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
      let base := crossEdgeProfile G D
      have hedges : (finiteGraphEdges G).card = m n := by
        have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
        simpa [finiteGraphEdges] using
          (mem_supercriticalCloseGraphFinset.mp hclose).2.1
      have hwindow : SupercriticalProfileWindow D (m n)
          (supercriticalOffDiagonal k gamma) P.delta
          ⌊P.epsilon * (n : ℝ) ^ 2⌋₊ base := by
        have hw := canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
          hk ⟨hgamma.1.le, hgamma.2⟩ G hn R (m n) hedges
        dsimp [base]
        rw [← hdivision]
        exact hw
      obtain ⟨u, huFloor, hprofile⟩ := hwindow
      have hu : (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
        calc
          (u.natAbs : ℝ) ≤ (⌊P.epsilon * (n : ℝ) ^ 2⌋₊ : ℕ) := by
            exact_mod_cast huFloor
          _ ≤ P.epsilon * (n : ℝ) ^ 2 := by
            exact Nat.floor_le (mul_nonneg P.epsilon_pos.le (sq_nonneg _))
      have Hgeometry : SupercriticalSignedShiftGeometryHypotheses
          (gamma := gamma) hk P.delta D u :=
        hgeometryN D u hbalanced hsparse hu
      have hmediumRaw := hcoreN (m n) P.tau hn D base
        ⟨u, huFloor, hprofile⟩ hresult
      have hmedium :
          ((supercriticalMediumDegreeGraphFinset
            k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
              (m n) n P.tau hn D).card : ℝ) ≤
            (supercriticalProfileMultiplicity base : ℝ) *
              Real.exp (-(P.cMed * (n : ℝ) ^ 2)) := by
        simpa [P.cMed_eq] using hmediumRaw
      have habsorbed :=
        card_supercriticalMediumDegreeGraphFinset_le_absorbedCoPartite
          hk hgamma P hn D base u hprofile hbalanced hsparse hu
            Hgeometry hmedium
      have hfiberNat :
          (supercriticalAbsorbedCoPartiteGraphFinset hk D (m n)).card ≤
            coMultipartiteGraphCountWithEdges (k - 1) n (m n) := by
        rw [supercriticalAbsorbedCoPartiteGraphFinset_eq_fiber]
        exact Finset.card_le_card
          (supercriticalCoPartiteFiber_subset_global
            (supercriticalAbsorbSparseDivision hk D))
      have hfiber :
          ((supercriticalAbsorbedCoPartiteGraphFinset hk D (m n)).card : ℝ) ≤
            C := by
        dsimp [C]
        exact_mod_cast hfiberNat
      exact habsorbed.trans <| mul_le_mul_of_nonneg_right hfiber
        (Real.exp_nonneg _)
    · have hz : supercriticalMediumDegreeGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
            (m n) n P.tau hn D = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      rw [hz, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (by dsimp [C]; positivity) (Real.exp_nonneg _)
  simp only [supercriticalMediumTotal, dif_pos hn, Nat.cast_sum]
  calc
    ∑ D ∈ allSupercriticalDivisions k n,
        ((supercriticalMediumDegreeGraphFinset
          k hk gamma ⟨hgamma.1.le, hgamma.2⟩ P.alpha
            (m n) n P.tau hn D).card : ℝ) ≤
        ∑ _D ∈ allSupercriticalDivisions k n,
          C * Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2)) := by
      exact Finset.sum_le_sum fun D _hD ↦ hdivisionBound D
    _ = ((allSupercriticalDivisions k n).card : ℝ) *
        (C * Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2))) := by simp
    _ ≤ ((k ^ n : ℕ) : ℝ) *
        (C * Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2))) := by
      gcongr
      exact_mod_cast card_allSupercriticalDivisions_le
        (k := k) (n := n) (by omega : 1 ≤ k)
    _ ≤ Real.exp ((P.cMed / 4) * (n : ℝ) ^ 2) *
        (C * Real.exp (-((3 * P.cMed / 4) * (n : ℝ) ^ 2))) := by
      exact mul_le_mul_of_nonneg_right hpowN (by positivity)
    _ = C * Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := by
      rw [mul_left_comm, ← Real.exp_add]
      unfold SupercriticalAggregationParameters.mediumRate
      congr 2
      ring
    _ = (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
        Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := rfl

/-- The concrete global medium-degree estimate.  All scalar and geometric
hypotheses are supplied by the common aggregation package; the edge-density
hypothesis is retained in the paper-facing signature even though this branch
is uniform in the exact edge count. -/
theorem eventually_supercriticalMediumTotal_le
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ioo (gammaK k) 1)
    (P : SupercriticalAggregationParameters k gamma)
    (m : ℕ → ℕ) (_hm : HasAsymptoticEdgeDensity m gamma) :
    ∀ᶠ n : ℕ in atTop,
      (supercriticalMediumTotal k hk gamma
        ⟨hgamma.1.le, hgamma.2⟩ P.alpha (m n) n P.tau : ℝ) ≤
      (coMultipartiteGraphCountWithEdges (k - 1) n (m n) : ℝ) *
        Real.exp (-(P.mediumRate * (n : ℝ) ^ 2)) := by
  apply eventually_supercriticalMediumTotal_le_of_signedGeometry
    k hk gamma hgamma P ?_ m
  filter_upwards [] with n
  intro D u hbalanced hsparse hu
  apply supercriticalSignedShiftGeometryHypotheses_of_uniform_bound
    hk hgamma P.delta_pos.le P.joint_absorption_delta
  · linarith [P.support_signed_shift, P.alpha_pos, P.delta_pos]
  · exact P.epsilon_pos.le
  · exact P.signed_shift_epsilon
  · exact hbalanced
  · exact hsparse
  · exact hu

end InducedStars
