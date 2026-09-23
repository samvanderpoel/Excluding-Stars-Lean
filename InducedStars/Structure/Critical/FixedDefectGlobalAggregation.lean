import InducedStars.Structure.Critical.DivisionCounting
import InducedStars.Structure.Critical.ShiftedAggregate

/-!
# Global critical fixed-defect aggregation

This file completes the finite and asymptotic bookkeeping for the critical
fixed-defect branch, conditional only on the uniform shifted-profile
aggregate estimate isolated in `CriticalShiftedAggregateBoundAt`.

For one division, active support patterns are grouped by their matching
number.  The support-pattern count spends one eighth of the matching
penalty, and the remaining geometric series leaves a linear penalty.  The
global sum is then grouped by sparse-set size.  Division counting converts
the reference-fiber factor to the exact co-multipartite count, while the
full Gaussian sparse-size sum is subexponential and is absorbed by the
linear matching penalty.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalFixedGlobalGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) := Classical.decEq _

/-! ## The uniform shifted-aggregate input -/

/-- The precise pointwise shifted-aggregate estimate needed by the critical
fixed-defect aggregation at one vertex size.  Keeping this predicate
separate makes the combinatorial aggregation independent of the numerical
second-order binomial proof. -/
def CriticalShiftedAggregateBoundAt
    (k : ℕ) (P : CriticalAggregationParameters k) (n : ℕ) : Prop :=
  ∀ (_hn : k - 1 ≤ n) (D : SupercriticalDivision k (Fin n)),
    (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
    ∀ (T₀ : SimpleGraph (Fin n))
      (profile : SupercriticalEdgeProfile D) (t : ℕ),
      SupercriticalProfileAtShift D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalSupportDefectShift D T₀ + (t : ℤ)) profile →
      t ≤ Nat.choose D.sparse.card 2 →
      (supercriticalShiftedProfileAggregate D (criticalEdgeCount k n)
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalSupportDefectShift D T₀) : ℝ) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalShiftedAggregateExponent P n D.sparse.card
            (supercriticalSupportDefectShift D T₀))

/-! ## One-division aggregation -/

set_option maxHeartbeats 800000 in
-- The nested support-pattern regrouping is expensive to elaborate.
/-- Conditional on the uniform shifted-slice bound, the entire fixed-defect
contribution in one balanced small-sparse division is bounded by the
critical reference fiber, its Gaussian sparse-size weight, and a linear
matching penalty. -/
theorem eventually_criticalFixedDefectDivisionTotal_le_of_shiftedAggregate
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (haggregate : ∀ᶠ n : ℕ in atTop,
      CriticalShiftedAggregateBoundAt k P n) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : k - 1 ≤ n) (D : SupercriticalDivision k (Fin n)),
      (∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) →
      (D.sparse.card : ℝ) ≤ P.delta * n / 2 →
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T).card : ℕ) : ℝ)) ≤
        (criticalReferenceFiberCard k n : ℝ) *
          Real.exp (criticalSparseAggregateExponent P n D.sparse.card -
            (P.cMat / 2) * (n : ℝ)) := by
  classical
  have hpattern := eventually_criticalFixedPattern_le_profileMass k hk P
  have hsupport :=
    eventually_card_criticalLowSupportPatternFinset_le_exp k hk P
  have hseries :=
    eventually_sum_Icc_exp_neg_thirteen_sixteenths_le P.cMat_pos
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
      P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
        P.rho_three_upper P.epsilon P.epsilon_pos
  filter_upwards [hpattern, hsupport, hseries, haggregate,
      eventually_ge_atTop nClose]
      with n hpatternN hsupportN hseriesN haggregateN hnClose
  intro hn D hbalanced hsparse
  let active := supercriticalActiveSupportImage hk
    (gammaK_mem_supercritical_Ico k hk) P.alpha
      (criticalEdgeCount k n) n P.tau hn D
  let idx : SimpleGraph (Fin n) → ℕ :=
    fun T₀ ↦ supercriticalMatchingNumber D T₀
  let total : SimpleGraph (Fin n) → ℝ := fun T₀ ↦
    supercriticalFixedSupportTotal hk
      (gammaK_mem_supercritical_Ico k hk) P.alpha
        (criticalEdgeCount k n) n P.tau hn D T₀
  let A : ℝ := criticalReferenceFiberCard k n
  let E : ℝ := criticalSparseAggregateExponent P n D.sparse.card
  have hdata (T₀ : SimpleGraph (Fin n)) (hT₀ : T₀ ∈ active) :
      0 < idx T₀ ∧ idx T₀ ≤ n ∧
        T₀ ∈ supercriticalLowSupportPatternFinset D P.alpha (idx T₀) ∧
        total T₀ ≤ A * Real.exp
          (E - (15 * P.cMat / 16) * (idx T₀ : ℝ) * (n : ℝ)) := by
    have hpointwise : ∀ T : SimpleGraph (Fin n),
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
              (supercriticalMatchingNumber D T : ℝ) * (n : ℝ))) := by
      intro T hT
      exact hpatternN hn D T hT hbalanced
    have h := criticalActiveSupportTotal_le_referenceFiber hk P hnClose
      D hsparse T₀ (by simpa [active] using hT₀) hpointwise
        (fun profile t hprofile ht ↦
          haggregateN hn D hsparse T₀ profile t hprofile ht)
    simpa [idx, total, A, E] using h
  have horiginal :
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T).card : ℕ) : ℝ)) =
        ∑ T₀ ∈ active, total T₀ := by
    calc
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T).card : ℕ) : ℝ)) =
          ∑ T₀ ∈ supercriticalCombinedSupportImage hk
              (gammaK_mem_supercritical_Ico k hk)
                (criticalEdgeCount k n) n P.tau hn D,
            supercriticalFixedSupportTotal hk
              (gammaK_mem_supercritical_Ico k hk) P.alpha
                (criticalEdgeCount k n) n P.tau hn D T₀ :=
        sum_supercriticalFixedDefect_eq_sum_supportTotal
          hk (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D
      _ = ∑ T₀ ∈ supercriticalActiveSupportImage hk
              (gammaK_mem_supercritical_Ico k hk) P.alpha
                (criticalEdgeCount k n) n P.tau hn D,
            supercriticalFixedSupportTotal hk
              (gammaK_mem_supercritical_Ico k hk) P.alpha
                (criticalEdgeCount k n) n P.tau hn D T₀ :=
        sum_supportTotal_eq_sum_activeSupport
          hk (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D
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
        (A * Real.exp E) *
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
        total T₀ ≤ A * Real.exp
          (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) := by
      have hmem := Finset.mem_filter.mp hT₀
      have hb := (hdata T₀ hmem.1).2.2.2
      simpa only [hmem.2] using hb
    have hsupportCount := hsupportN D h hsparse
      (Finset.mem_Icc.mp hh).1
    calc
      (∑ T₀ ∈ fiber, total T₀) ≤
          ∑ _T₀ ∈ fiber, A * Real.exp
            (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) :=
        Finset.sum_le_sum fun T₀ hT₀ ↦ hbound T₀ hT₀
      _ = (fiber.card : ℝ) * (A * Real.exp
            (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by simp
      _ ≤ ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) *
            (A * Real.exp
              (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hcardReal (by positivity)
      _ ≤ Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) *
            (A * Real.exp
              (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) :=
        mul_le_mul_of_nonneg_right hsupportCount (by positivity)
      _ = (A * Real.exp E) *
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
        calc
          Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) *
              (A * Real.exp
                (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) =
              A * (Real.exp ((P.cMat / 8) * (h : ℝ) * (n : ℝ)) *
                Real.exp
                  (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
            ring
          _ = A * Real.exp
              ((P.cMat / 8) * (h : ℝ) * (n : ℝ) +
                (E - (15 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
            rw [Real.exp_add]
          _ = A * Real.exp
              (E - (13 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) := by
            congr 2
            ring
          _ = (A * Real.exp E) *
              Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) := by
            rw [show E - (13 * P.cMat / 16) * (h : ℝ) * (n : ℝ) =
                E + -((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ)) by ring,
              Real.exp_add]
            ring
  calc
    (∑ T₀ ∈ active, total T₀) ≤
        ∑ h ∈ Finset.Icc 1 n,
          ∑ T₀ ∈ active, if idx T₀ = h then total T₀ else 0 := hdouble
    _ ≤ ∑ h ∈ Finset.Icc 1 n,
        (A * Real.exp E) *
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ))) :=
      Finset.sum_le_sum fun h hh ↦ hfiber h hh
    _ = (A * Real.exp E) *
        (∑ h ∈ Finset.Icc 1 n,
          Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * (n : ℝ)))) := by
      rw [Finset.mul_sum]
    _ ≤ (A * Real.exp E) *
        Real.exp (-((P.cMat / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hseriesN (by positivity)
    _ = A * Real.exp (E - (P.cMat / 2) * (n : ℝ)) := by
      rw [show E - (P.cMat / 2) * (n : ℝ) =
          E + -((P.cMat / 2) * (n : ℝ)) by ring,
        Real.exp_add]
      ring

/-! ## Global grouping by sparse size -/

/-- Critical divisions with at least one nonempty fixed-defect fiber. -/
noncomputable def criticalFixedActiveDivisions
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (n : ℕ) (hn : k - 1 ≤ n) :
    Finset (SupercriticalDivision k (Fin n)) := by
  classical
  exact (allSupercriticalDivisions k n).filter fun D ↦
    ∃ T ∈ supercriticalCombinedDefectPatternFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
          (criticalEdgeCount k n) n P.tau hn D,
      (supercriticalFixedDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          (criticalEdgeCount k n) n P.tau hn D T).Nonempty

@[simp] theorem mem_criticalFixedActiveDivisions
    {k n : ℕ} {hk : 3 ≤ k} {P : CriticalAggregationParameters k}
    {hn : k - 1 ≤ n} {D : SupercriticalDivision k (Fin n)} :
    D ∈ criticalFixedActiveDivisions k hk P n hn ↔
      ∃ T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T).Nonempty := by
  classical
  simp [criticalFixedActiveDivisions]

set_option maxHeartbeats 800000 in
-- The division and sparse-size regroupings form a large elaboration term.
/-- The global critical fixed-defect contribution has a positive linear
exponential penalty relative to the exact co-multipartite count, conditional
on the uniform shifted-profile aggregate estimate. -/
theorem eventually_criticalFixedDefectTotal_le_of_shiftedAggregate
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    (haggregate : ∀ᶠ n : ℕ in atTop,
      CriticalShiftedAggregateBoundAt k P n) :
    ∀ᶠ n : ℕ in atTop,
      (criticalFixedDefectTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
            Real.exp (-((P.cMat / 8) * (n : ℝ))) := by
  classical
  have hdivision :=
    eventually_criticalFixedDefectDivisionTotal_le_of_shiftedAggregate
      k hk P haggregate
  have hdivisionCount :=
    eventually_card_supercriticalDivisionsWithSparseCard_mul_reference_le
      k hk
  have hsparseSum :=
    DenseGraph.eventually_subexponential_all_sparse_sum_le
      (k - 1) (c := P.cCrit) (C := P.cleanErrorConstant)
        (eta := P.cMat / 4) P.cCrit_pos P.cleanErrorConstant_nonneg
        (div_pos P.cMat_pos (by norm_num))
  have hconstant := eventually_natCast_mul_exp_neg_linear_le
    (c := P.cMat / 4) (2 * (k - 1).factorial)
      (div_pos P.cMat_pos (by norm_num))
  let nClose := supercriticalCloseStructureVertexThreshold k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
      P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
        P.rho_three_upper P.epsilon P.epsilon_pos
  filter_upwards [hdivision, hdivisionCount, hsparseSum, hconstant,
      eventually_ge_atTop nClose]
      with n hdivisionN hdivisionCountN hsparseSumN hconstantN hnClose
  let hn : k - 1 ≤ n :=
    (supercriticalCloseStructureVertexThreshold_large k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
        P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
          P.rho_three_upper P.epsilon P.epsilon_pos).trans hnClose
  let active := criticalFixedActiveDivisions k hk P n hn
  let weight : ℕ → ℝ := fun s ↦
    (criticalReferenceFiberCard k n : ℝ) *
      Real.exp (criticalSparseAggregateExponent P n s -
        (P.cMat / 2) * (n : ℝ))
  have hactiveBound (D : SupercriticalDivision k (Fin n))
      (hD : D ∈ active) :
      (((∑ T ∈ supercriticalCombinedDefectPatternFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
            (criticalEdgeCount k n) n P.tau hn D,
        (supercriticalFixedDefectGraphFinset
          k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
            (criticalEdgeCount k n) n P.tau hn D T).card : ℕ) : ℝ)) ≤
        weight D.sparse.card := by
    have hmem : D ∈ criticalFixedActiveDivisions k hk P n hn := by
      simpa [active] using hD
    obtain ⟨T, hT, G, hG⟩ :=
      mem_criticalFixedActiveDivisions.mp hmem
    have hdefect := (mem_supercriticalFixedDefectGraphFinset.mp hG).1
    have hclose := (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).1
    have hfamily : G ∈
        inducedFreeGraphFinsetWithEdges (inducedStar k) n
            (criticalEdgeCount k n) \
          supercriticalFarGraphFinset k hk (gammaK k)
            (gammaK_mem_supercritical_Ico k hk)
              (criticalEdgeCount k n) n P.tau := by
      rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
      exact hclose
    obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk)
        P.alpha P.alpha_mem_Ioo P.delta P.delta_pos P.delta_lt_alpha
          P.rho_three_lower P.rho_three_upper P.epsilon P.epsilon_pos
            (criticalEdgeCount k n) hnClose G
              (by simpa [P.tau_eq] using hfamily)
    have hcanonical :=
      (mem_supercriticalDivisionDefectGraphFinset.mp hdefect).2.1
    have hcastSub : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    have hbalanced : ∀ i : Fin (k - 1),
        |((D.parts i).card : ℝ) -
          (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n := by
      intro i
      simpa only [hcanonical, hcastSub] using R.part_card_close i
    have hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2 := by
      simpa only [hcanonical] using R.sparse_card_le
    simpa [weight] using hdivisionN hn D hbalanced hsparse
  have hfirst :
      (criticalFixedDefectTotal k hk P n : ℝ) ≤
        ∑ D ∈ active, weight D.sparse.card := by
    rw [criticalFixedDefectTotal, supercriticalFixedDefectTotal,
      dif_pos hn, Nat.cast_sum]
    calc
      ∑ D ∈ allSupercriticalDivisions k n,
          (((∑ T ∈ supercriticalCombinedDefectPatternFinset
              k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
                (criticalEdgeCount k n) n P.tau hn D,
            (supercriticalFixedDefectGraphFinset
              k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
                (criticalEdgeCount k n) n P.tau hn D T).card : ℕ) : ℝ)) ≤
        ∑ D ∈ allSupercriticalDivisions k n,
          if D ∈ active then weight D.sparse.card else 0 := by
        apply Finset.sum_le_sum
        intro D hDall
        by_cases hD : D ∈ active
        · rw [if_pos hD]
          exact hactiveBound D hD
        · rw [if_neg hD]
          have hempty (T : SimpleGraph (Fin n))
              (hT : T ∈ supercriticalCombinedDefectPatternFinset
                k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
                  (criticalEdgeCount k n) n P.tau hn D) :
              supercriticalFixedDefectGraphFinset
                k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
                  (criticalEdgeCount k n) n P.tau hn D T = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro hne
            apply hD
            rw [show active = criticalFixedActiveDivisions k hk P n hn by rfl,
              mem_criticalFixedActiveDivisions]
            exact ⟨T, hT, hne⟩
          have hzero :
              ∑ T ∈ supercriticalCombinedDefectPatternFinset
                  k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk)
                    (criticalEdgeCount k n) n P.tau hn D,
                (supercriticalFixedDefectGraphFinset
                  k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
                    (criticalEdgeCount k n) n P.tau hn D T).card = 0 := by
            apply Finset.sum_eq_zero
            intro T hT
            simp [hempty T hT]
          rw [hzero, Nat.cast_zero]
      _ = ∑ D ∈ active, weight D.sparse.card := by
        rw [← Finset.sum_filter]
        simp [active, criticalFixedActiveDivisions]
  have hmaps : ∀ D ∈ active, D.sparse.card ∈ Finset.Icc 0 n := by
    intro D _hD
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by
      simpa using Finset.card_le_univ D.sparse⟩
  have hregroup :
      (∑ D ∈ active, weight D.sparse.card) =
        ∑ s ∈ Finset.Icc 0 n,
          ∑ D ∈ active with D.sparse.card = s, weight s :=
    (Finset.sum_fiberwise_of_maps_to' hmaps weight).symm
  rw [hregroup] at hfirst
  let good : ℝ :=
    coMultipartiteGraphCountWithEdges (k - 1) n (criticalEdgeCount k n)
  let gaussian : ℕ → ℝ := fun s ↦
    DenseGraph.sparseGaussianWeight (k - 1) P.cCrit
      P.cleanErrorConstant n s
  have hsBound (s : ℕ) (hs : s ∈ Finset.Icc 0 n) :
      (∑ D ∈ active with D.sparse.card = s, weight s) ≤
        ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s *
          Real.exp (-((P.cMat / 2) * (n : ℝ))) := by
    let fiber := active.filter fun D ↦ D.sparse.card = s
    have hfiberSubset : fiber ⊆
        supercriticalDivisionsWithSparseCard k n s := by
      intro D hD
      have hmem := Finset.mem_filter.mp hD
      exact mem_supercriticalDivisionsWithSparseCard.mpr hmem.2
    have hcard : fiber.card ≤
        (supercriticalDivisionsWithSparseCard k n s).card :=
      Finset.card_le_card hfiberSubset
    have hcardReal : (fiber.card : ℝ) ≤
        (supercriticalDivisionsWithSparseCard k n s).card := by
      exact_mod_cast hcard
    have hrefNonneg : 0 ≤ (criticalReferenceFiberCard k n : ℝ) := by
      positivity
    have hlocalReference :
        (fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ) ≤
          ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good := by
      calc
        (fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ) ≤
            ((supercriticalDivisionsWithSparseCard k n s).card : ℝ) *
              (criticalReferenceFiberCard k n : ℝ) :=
          mul_le_mul_of_nonneg_right hcardReal hrefNonneg
        _ ≤ ((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good :=
          by simpa [good] using hdivisionCountN s (Finset.mem_Icc.mp hs).2
    have hsumEq :
        (∑ D ∈ active with D.sparse.card = s, weight s) =
          (fiber.card : ℝ) * weight s := by
      dsimp [fiber]
      simp
    rw [hsumEq]
    dsimp only [weight]
    rw [show criticalSparseAggregateExponent P n s -
        (P.cMat / 2) * (n : ℝ) =
          criticalSparseAggregateExponent P n s +
            -((P.cMat / 2) * (n : ℝ)) by ring,
      Real.exp_add]
    calc
      (fiber.card : ℝ) *
          ((criticalReferenceFiberCard k n : ℝ) *
            (Real.exp (criticalSparseAggregateExponent P n s) *
              Real.exp (-((P.cMat / 2) * (n : ℝ))))) =
          ((fiber.card : ℝ) * (criticalReferenceFiberCard k n : ℝ)) *
            Real.exp (criticalSparseAggregateExponent P n s) *
              Real.exp (-((P.cMat / 2) * (n : ℝ))) := by ring
      _ ≤ (((n + 1 : ℕ) : ℝ) ^ (k - 1) *
            (2 * (k - 1).factorial : ℕ) * (Nat.choose n s : ℝ) * good) *
            Real.exp (criticalSparseAggregateExponent P n s) *
              Real.exp (-((P.cMat / 2) * (n : ℝ))) := by
        gcongr
      _ = ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s *
          Real.exp (-((P.cMat / 2) * (n : ℝ))) := by
        dsimp [gaussian, DenseGraph.sparseGaussianWeight,
          criticalSparseAggregateExponent]
        ring
  calc
    (criticalFixedDefectTotal k hk P n : ℝ) ≤
        ∑ s ∈ Finset.Icc 0 n,
          ∑ D ∈ active with D.sparse.card = s, weight s := hfirst
    _ ≤ ∑ s ∈ Finset.Icc 0 n,
        ((2 * (k - 1).factorial : ℕ) : ℝ) * good * gaussian s *
          Real.exp (-((P.cMat / 2) * (n : ℝ))) :=
      Finset.sum_le_sum fun s hs ↦ hsBound s hs
    _ = (((2 * (k - 1).factorial : ℕ) : ℝ) * good *
          Real.exp (-((P.cMat / 2) * (n : ℝ)))) *
        (∑ s ∈ Finset.Icc 0 n, gaussian s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ ≤ (((2 * (k - 1).factorial : ℕ) : ℝ) * good *
          Real.exp (-((P.cMat / 2) * (n : ℝ)))) *
        Real.exp ((P.cMat / 4) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [gaussian] using hsparseSumN)
        (by positivity)
    _ = good *
        (((2 * (k - 1).factorial : ℕ) : ℝ) *
          Real.exp (-((P.cMat / 4) * (n : ℝ)))) := by
      calc
        ((2 * (k - 1).factorial : ℕ) : ℝ) * good *
            Real.exp (-((P.cMat / 2) * (n : ℝ))) *
              Real.exp ((P.cMat / 4) * (n : ℝ)) =
            good * (((2 * (k - 1).factorial : ℕ) : ℝ) *
              (Real.exp (-((P.cMat / 2) * (n : ℝ))) *
                Real.exp ((P.cMat / 4) * (n : ℝ)))) := by ring
        _ = good * (((2 * (k - 1).factorial : ℕ) : ℝ) *
              Real.exp (-((P.cMat / 2) * (n : ℝ)) +
                (P.cMat / 4) * (n : ℝ))) := by
            rw [Real.exp_add]
        _ = good * (((2 * (k - 1).factorial : ℕ) : ℝ) *
              Real.exp (-((P.cMat / 4) * (n : ℝ)))) := by
            congr 3
            ring
    _ ≤ good * Real.exp (-(((P.cMat / 4) / 2) * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hconstantN (by positivity)
    _ = (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
        Real.exp (-((P.cMat / 8) * (n : ℝ))) := by
      dsimp [good]
      ring_nf

/-! ## Discharging the shifted-aggregate hypothesis -/

/-- The unconditional critical fixed-defect estimate.  The numerical input
is exactly `criticalShiftedProfileAggregate_le_referenceFiber`; no
strict-supercritical absorption gap is used. -/
theorem eventually_criticalFixedDefectTotal_le
    (k : ℕ) (hk : 3 ≤ k) (P : CriticalAggregationParameters k) :
    ∀ᶠ n : ℕ in atTop,
      (criticalFixedDefectTotal k hk P n : ℝ) ≤
        (coMultipartiteGraphCountWithEdges (k - 1) n
          (criticalEdgeCount k n) : ℝ) *
            Real.exp (-((P.cMat / 8) * (n : ℝ))) := by
  apply eventually_criticalFixedDefectTotal_le_of_shiftedAggregate k hk P
  filter_upwards [criticalShiftedProfileAggregate_le_referenceFiber k hk P]
      with n hshift
  intro hn D hsparse T₀ profile t hprofile ht
  exact hshift D (supercriticalSupportDefectShift D T₀) profile t
    hsparse hprofile ht

end InducedStars
