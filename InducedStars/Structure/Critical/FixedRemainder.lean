import InducedStars.Structure.Critical.DefectAggregation
import InducedStars.Structure.Supercritical.FixedRemainderCounting

/-!
# Nonclean counts with a fixed sparse remainder

The endpoint matching and medium-degree penalties are uniform in the exact
edge count. Fixing the sparse graph before summing profiles leaves a single
cross-edge binomial, which is also the reference count for the logarithmic
critical window.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance criticalFixedRemainderGraphDecidableEq (W : Type*) :
    DecidableEq (SimpleGraph W) := Classical.decEq _

theorem CriticalAggregationParameters.delta_le_fixedRemainderRank
    {k : ℕ} (P : CriticalAggregationParameters k) :
    P.delta ≤ 1 / (2 * ((k - 1 : ℕ) : ℝ)) := by
  have hk := P.rank
  have hr : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (by omega : 0 < k - 1)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hrk : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  have ha : P.alpha * (100 * k) < 1 := by
    exact (lt_div_iff₀ (by positivity)).mp P.alpha_lt
  have hd : P.delta < P.alpha := by linarith [P.delta_lt_alpha, P.alpha_pos]
  rw [le_div_iff₀ (by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hrk P.delta_pos.le
  nlinarith

theorem CriticalAggregationParameters.fixedRemainderDensityMargins
    {k : ℕ} (P : CriticalAggregationParameters k) :
    2 * criticalDensityMargin k + P.delta ≤
        supercriticalOffDiagonal k (gammaK k) ∧
      supercriticalOffDiagonal k (gammaK k) + P.delta ≤
        1 - 2 * criticalDensityMargin k := by
  have hd : P.delta < criticalDensityMargin k / 16 :=
    P.critical_taylor_delta.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
  have hlo := criticalDensityMargin_le_pK_div_four k
  have hhi := criticalDensityMargin_le_one_sub_pK_div_four k
  have hp := criticalDensityMargin_pos P.rank
  rw [supercriticalOffDiagonal_at_gammaK k P.rank]
  constructor <;> linarith

theorem CriticalAggregationParameters.fixedRemainderShiftBudget
    {k n : ℕ} (P : CriticalAggregationParameters k)
    (D : SupercriticalDivision k (Fin n))
    (hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
        (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n) :
    2 * P.epsilon * (n : ℝ) ^ 2 ≤
      criticalDensityMargin k * (supercriticalTotalCrossCapacity D : ℝ) := by
  have hk := P.rank
  let r : ℝ := ((k - 1 : ℕ) : ℝ)
  have hr : 0 < r := by
    dsimp [r]; exact_mod_cast (by omega : 0 < k - 1)
  have hlam := criticalDensityMargin_pos P.rank
  have he : P.epsilon < criticalDensityMargin k / (100 * r ^ 2) :=
    P.signed_shift_epsilon
  have he' : P.epsilon * (100 * r ^ 2) < criticalDensityMargin k :=
    (lt_div_iff₀ (by positivity)).mp he
  have hscale : 2 * P.epsilon ≤ criticalDensityMargin k / (4 * r ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pos P.epsilon_pos (sq_pos_of_pos hr)]
  have hcap := supercriticalTotalCrossCapacity_lower_of_balanced
    P.rank P.delta_le_fixedRemainderRank D hbalanced
  calc
    _ ≤ (criticalDensityMargin k / (4 * r ^ 2)) * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hscale (sq_nonneg _)
    _ = criticalDensityMargin k * ((n : ℝ) ^ 2 / (4 * r ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcap hlam.le

/-- A close nonclean graph supplies its actual fixed-remainder reference
binomial with no asymptotic edge-density hypothesis. -/
theorem criticalFixedRemainderReferenceBand_of_close
    {k n m : ℕ} (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {hn : k - 1 ≤ n} (G : SimpleGraph (Fin n))
    (R : SupercriticalCloseStructureResult k hk (gammaK k)
      P.alpha P.delta P.epsilon (gammaK_mem_supercritical_Ico k hk) G hn)
    (D : SupercriticalDivision k (Fin n))
    (hD : canonicalSupercriticalDivision G (by simpa using hn) = D)
    (hedges : (finiteGraphEdges G).card = m) :
    divisionInternalCliqueCapacity D + (supercriticalSparseInducedEdges G D).card ≤ m ∧
      m - (divisionInternalCliqueCapacity D + (supercriticalSparseInducedEdges G D).card) ≤
        supercriticalTotalCrossCapacity D ∧
      criticalDensityMargin k * (supercriticalTotalCrossCapacity D : ℝ) ≤
        (m - (divisionInternalCliqueCapacity D +
          (supercriticalSparseInducedEdges G D).card) : ℕ) ∧
      ((m - (divisionInternalCliqueCapacity D +
        (supercriticalSparseInducedEdges G D).card) : ℕ) : ℝ) ≤
        (1 - criticalDensityMargin k) * (supercriticalTotalCrossCapacity D : ℝ) := by
  have hbalanced : ∀ i : Fin (k - 1),
      |((D.parts i).card : ℝ) -
        (n : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤ P.delta * n := by
    intro i
    simpa only [hD, Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
      using R.part_card_close i
  have hw := canonicalCrossEdgeProfile_mem_window_of_closeStructureResult
    hk (gammaK_mem_supercritical_Ico k hk) G hn R m hedges
  rw [hD] at hw
  obtain ⟨u, huFloor, hp⟩ := hw
  have hu : (u.natAbs : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
    exact (show (u.natAbs : ℝ) ≤
      (⌊P.epsilon * (n : ℝ) ^ 2⌋₊ : ℕ) by exact_mod_cast huFloor).trans
        (Nat.floor_le (by positivity [P.epsilon_pos]))
  let t := (supercriticalSparseInducedEdges G D).card
  have ht : (t : ℝ) ≤ P.epsilon * (n : ℝ) ^ 2 := by
    have hcost : (supercriticalDefectCost G D : ℝ) ≤
        P.epsilon * (n : ℝ) ^ 2 := by
      simpa [canonicalSupercriticalDefectCost, hD] using R.canonicalDefectCost_le
    have htCost : (t : ℝ) ≤ (supercriticalDefectCost G D : ℝ) := by
      exact_mod_cast card_supercriticalSparseInducedEdges_le_cost G D
    exact htCost.trans hcost
  have hshift : ((u - (t : ℤ)).natAbs : ℝ) ≤
      criticalDensityMargin k * (supercriticalTotalCrossCapacity D : ℝ) := by
    have hnabs : (u - (t : ℤ)).natAbs ≤ u.natAbs + t := by
      simpa using Int.natAbs_sub_le u (t : ℤ)
    have hR : ((u - (t : ℤ)).natAbs : ℝ) ≤ (u.natAbs : ℝ) + t := by
      exact_mod_cast hnabs
    exact (show ((u - (t : ℤ)).natAbs : ℝ) ≤
      2 * P.epsilon * (n : ℝ) ^ 2 by linarith).trans
        (P.fixedRemainderShiftBudget D hbalanced)
  apply supercriticalFixedRemainderReferenceBand_of_profile D
    (crossEdgeProfile G D) m t (u - (t : ℤ))
    (criticalDensityMargin_pos hk).le
    P.fixedRemainderDensityMargins.1 P.fixedRemainderDensityMargins.2
  · simpa only [sub_add_cancel] using hp
  · exact hshift


/-- A nonempty fixed-defect fiber gives a low-degree support pattern with
positive matching number. The matching and close-structure proofs are the
existing endpoint proofs, uniformly in the edge budget. -/
theorem criticalFixedDefectPattern_lowSupport
    {k n m : ℕ} (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {hn : k - 1 ≤ n}
    (hnClose : supercriticalCloseStructureVertexThreshold k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
        P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
          P.rho_three_upper P.epsilon P.epsilon_pos ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) m n P.tau hn D)
    (hne : (supercriticalFixedDefectGraphFinset
      k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
        m n P.tau hn D T).Nonempty) :
    0 < supercriticalMatchingNumber D T ∧
      supercriticalMatchingNumber D T ≤ n ∧
      supercriticalSupportIncidentGraph D T ∈
        supercriticalLowSupportPatternFinset D P.alpha
          (supercriticalMatchingNumber D T) := by
  obtain ⟨G, hG⟩ := hne
  have hm := mem_supercriticalFixedDefectGraphFinset.mp hG
  have hd := mem_supercriticalDivisionDefectGraphFinset.mp hm.1
  have hfamily : G ∈ inducedFreeGraphFinsetWithEdges (inducedStar k) n m \
      supercriticalFarGraphFinset k hk (gammaK k)
        (gammaK_mem_supercritical_Ico k hk) m n P.tau := by
    rw [← supercriticalCloseGraphFinset_eq_sdiff_far]
    exact hd.1
  obtain ⟨R⟩ := superCloseStructureK1k k hk (gammaK k)
    (gammaK_mem_supercritical_Ico k hk) P.alpha P.alpha_mem_Ioo
      P.delta P.delta_pos P.delta_lt_alpha P.rho_three_lower
        P.rho_three_upper P.epsilon P.epsilon_pos m hnClose G
          (by simpa [P.tau_eq] using hfamily)
  have hlow := low_degree_everywhere_of_mem_fixedDefect hG R
  have hcombined : combinedSupercriticalDefectGraph G D = T := by
    simpa [canonicalCombinedDefectGraph, hd.2.1] using hm.2.1
  have hlowCombined : ∀ v : Fin n, ∀ i : Fin (k - 1),
      HasLowDegreeInPart (combinedSupercriticalDefectGraph G D)
        P.alpha D v i := by simpa only [hcombined] using hlow
  have hsupport := supercriticalSupportIncidentGraph_mem_lowSupportPattern
    G D P.alpha hlowCombined
  rw [hcombined] at hsupport
  refine ⟨supercriticalMatchingNumber_pos_of_mem_pattern hT, ?_, hsupport⟩
  have hcard := Finset.card_le_univ (supercriticalCanonicalMatchingEndpoints D T)
  rw [card_supercriticalCanonicalMatchingEndpoints] at hcard
  have : 2 * supercriticalMatchingNumber D T ≤ n := by simpa using hcard
  omega

/-- Paying for the signed support shift consumes at most one sixteenth of
the matching exponent. This estimate does not charge for the fixed sparse
graph. -/
theorem CriticalAggregationParameters.fixedRemainderSupportShift
    {k n : ℕ} (P : CriticalAggregationParameters k)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (hlow : supercriticalSupportIncidentGraph D T ∈
      supercriticalLowSupportPatternFinset D P.alpha
        (supercriticalMatchingNumber D T)) :
    P.cShift *
        ((supercriticalSupportDefectShift D
          (supercriticalSupportIncidentGraph D T)).natAbs : ℝ) ≤
      (P.cMat / 16) * (supercriticalMatchingNumber D T : ℝ) * n := by
  have hshift := supercriticalSupportDefectShift_natAbs_le_edgeCount D T
  have hedge := supercriticalSupportPattern_edgeCount_le D
    P.alpha_pos.le P.delta_pos.le hsparse hlow
  have hshiftReal :
      ((supercriticalSupportDefectShift D
        (supercriticalSupportIncidentGraph D T)).natAbs : ℝ) ≤
      2 * (supercriticalMatchingNumber D T : ℝ) *
        (P.alpha + P.delta) * (n : ℝ) :=
    (show ((supercriticalSupportDefectShift D
        (supercriticalSupportIncidentGraph D T)).natAbs : ℝ) ≤
      ((finiteGraphEdges (supercriticalSupportIncidentGraph D T)).card : ℝ) by
        exact_mod_cast hshift).trans hedge
  have hkOne : (1 : ℝ) ≤ k := by
    exact_mod_cast ((show 1 ≤ 3 by omega).trans P.rank)
  have hsum0 : 0 ≤ P.alpha + P.delta := by positivity [P.alpha_pos, P.delta_pos]
  have hcoeff : 2 * P.cShift * (P.alpha + P.delta) ≤ P.cMat / 16 := by
    have hsmall := P.support_shift_small
    have hmono := mul_nonneg (sub_nonneg.mpr hkOne)
      (mul_nonneg P.cShift_pos.le hsum0)
    nlinarith
  calc
    _ ≤ P.cShift * (2 * (supercriticalMatchingNumber D T : ℝ) *
          (P.alpha + P.delta) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hshiftReal P.cShift_pos.le
    _ = (2 * P.cShift * (P.alpha + P.delta)) *
        ((supercriticalMatchingNumber D T : ℝ) * (n : ℝ)) := by ring
    _ ≤ (P.cMat / 16) * ((supercriticalMatchingNumber D T : ℝ) * (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = _ := by ring


/-- A fixed pattern with fixed remainder keeps fifteen sixteenths of its
matching exponent after the signed-binomial comparison. -/
theorem criticalFixedRemainderPattern_le_reference
    {k n m M : ℕ} (hk : 3 ≤ k) (P : CriticalAggregationParameters k)
    {hn : k - 1 ≤ n}
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n))
    (H : Finset (Sym2 (Fin n)))
    (hH : supercriticalSparseInducedEdges T D = H)
    (hbudget : M + divisionInternalCliqueCapacity D + H.card = m)
    (hMC : M ≤ supercriticalTotalCrossCapacity D)
    (hMlo : criticalDensityMargin k * (supercriticalTotalCrossCapacity D : ℝ) ≤ M)
    (hMhi : (M : ℝ) ≤ (1 - criticalDensityMargin k) *
      (supercriticalTotalCrossCapacity D : ℝ))
    (hsparse : (D.sparse.card : ℝ) ≤ P.delta * n / 2)
    (hlow : supercriticalSupportIncidentGraph D T ∈
      supercriticalLowSupportPatternFinset D P.alpha
        (supercriticalMatchingNumber D T))
    (hpattern :
      ((supercriticalFixedDefectGraphFinset
        k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
          m n P.tau hn D T).card : ℝ) ≤
        (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat * (supercriticalMatchingNumber D T : ℝ) * n))) :
    ((supercriticalFixedDefectGraphFinset
      k hk (gammaK k) (gammaK_mem_supercritical_Ico k hk) P.alpha
        m n P.tau hn D T).card : ℝ) ≤
      (Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (-(15 * P.cMat / 16) *
          (supercriticalMatchingNumber D T : ℝ) * n) := by
  have hshift := supercriticalDefectShift_eq_support_add_sparseEdges D T
  rw [hH] at hshift
  have hmass := supercriticalProfileMassAtShift_le_referenceCrossChoose
    D m M H.card (supercriticalOffDiagonal k (gammaK k)) P.delta
      (criticalDensityMargin k)
      (supercriticalSupportDefectShift D (supercriticalSupportIncidentGraph D T))
      hbudget hMC (criticalDensityMargin_pos hk) (criticalDensityMargin_lt_half hk)
        hMlo hMhi
  rw [← hshift] at hmass
  have hcost := P.fixedRemainderSupportShift D T hsparse hlow
  have hc : DenseGraph.binomialCompactBandShiftConstant (criticalDensityMargin k) =
      P.cShift := by
    rw [P.cShift_eq, criticalShiftErrorConstant]
  rw [hc] at hmass
  calc
    _ ≤ (supercriticalProfileMassAtShift D m
          (supercriticalOffDiagonal k (gammaK k)) P.delta
            (supercriticalDefectShift T D) : ℝ) *
          Real.exp (-(P.cMat * (supercriticalMatchingNumber D T : ℝ) * n)) := hpattern
    _ ≤ ((Nat.choose (supercriticalTotalCrossCapacity D) M : ℝ) *
        Real.exp (P.cShift *
          ((supercriticalSupportDefectShift D
            (supercriticalSupportIncidentGraph D T)).natAbs : ℝ))) *
          Real.exp (-(P.cMat * (supercriticalMatchingNumber D T : ℝ) * n)) :=
      mul_le_mul_of_nonneg_right hmass (Real.exp_nonneg _)
    _ ≤ _ := by
      rw [mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
      linarith

/-- Grouping fixed-remainder patterns by matching number costs only the
low-support count. Fixing the sparse graph makes the support encoding
injective, so there is no additional remainder multiplicity. -/
theorem criticalFixedRemainderPatternSum_le
    {k n : ℕ} (P : CriticalAggregationParameters k)
    (D : SupercriticalDivision k (Fin n))
    (S : Finset (SimpleGraph (Fin n))) (H : Finset (Sym2 (Fin n)))
    (w : SimpleGraph (Fin n) → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hH : ∀ T ∈ S, supercriticalSparseInducedEdges T D = H)
    (hdata : ∀ T ∈ S,
      0 < supercriticalMatchingNumber D T ∧
        supercriticalMatchingNumber D T ≤ n ∧
        supercriticalSupportIncidentGraph D T ∈
          supercriticalLowSupportPatternFinset D P.alpha
            (supercriticalMatchingNumber D T))
    (hw : ∀ T ∈ S, w T ≤ A * Real.exp
      (-(15 * P.cMat / 16) * (supercriticalMatchingNumber D T : ℝ) * n))
    (hcount : ∀ h ∈ Finset.Icc 1 n,
      ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) ≤
        Real.exp ((P.cMat / 8) * (h : ℝ) * n))
    (hseries : (∑ h ∈ Finset.Icc 1 n,
        Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * n))) ≤
      Real.exp (-((P.cMat / 2) * n))) :
    (∑ T ∈ S, w T) ≤ A * Real.exp (-((P.cMat / 2) * n)) := by
  classical
  let idx := supercriticalMatchingNumber D
  have heq : (∑ T ∈ S, w T) =
      ∑ h ∈ Finset.Icc 1 n, ∑ T ∈ S with idx T = h, w T := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T hT
    have hmem : idx T ∈ Finset.Icc 1 n :=
      Finset.mem_Icc.mpr ⟨(hdata T hT).1, (hdata T hT).2.1⟩
    simp [Finset.sum_filter, hmem]
  have hfiber (h : ℕ) (hh : h ∈ Finset.Icc 1 n) :
      (∑ T ∈ S with idx T = h, w T) ≤
        A * Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * n)) := by
    let F := S.filter fun T ↦ idx T = h
    have hmap : Set.MapsTo (supercriticalSupportIncidentGraph D) F
        (supercriticalLowSupportPatternFinset D P.alpha h) := by
      intro T hT
      have hm := Finset.mem_filter.mp hT
      have hl := (hdata T hm.1).2.2
      change supercriticalSupportIncidentGraph D T ∈
        supercriticalLowSupportPatternFinset D P.alpha h
      change supercriticalSupportIncidentGraph D T ∈
        supercriticalLowSupportPatternFinset D P.alpha (idx T) at hl
      rwa [hm.2] at hl
    have hinj : Set.InjOn (supercriticalSupportIncidentGraph D) F := by
      intro T hT U hU heq
      exact supercriticalSupportIncidentGraph_injectiveOn_fixedSparse D H
        (hH T (Finset.mem_filter.mp hT).1)
        (hH U (Finset.mem_filter.mp hU).1) heq
    have hcard : (F.card : ℝ) ≤
        (supercriticalLowSupportPatternFinset D P.alpha h).card := by
      exact_mod_cast Finset.card_le_card_of_injOn
        (supercriticalSupportIncidentGraph D) hmap hinj
    calc
      (∑ T ∈ F, w T) ≤
          ∑ _T ∈ F, A * Real.exp (-(15 * P.cMat / 16) * (h : ℝ) * n) := by
        apply Finset.sum_le_sum
        intro T hT
        have hm := Finset.mem_filter.mp hT
        have hbound := hw T hm.1
        simpa only [← hm.2] using hbound
      _ = (F.card : ℝ) *
          (A * Real.exp (-(15 * P.cMat / 16) * (h : ℝ) * n)) := by simp
      _ ≤ ((supercriticalLowSupportPatternFinset D P.alpha h).card : ℝ) *
          (A * Real.exp (-(15 * P.cMat / 16) * (h : ℝ) * n)) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hA (Real.exp_nonneg _))
      _ ≤ Real.exp ((P.cMat / 8) * (h : ℝ) * n) *
          (A * Real.exp (-(15 * P.cMat / 16) * (h : ℝ) * n)) :=
        mul_le_mul_of_nonneg_right (hcount h hh)
          (mul_nonneg hA (Real.exp_nonneg _))
      _ = A * Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * n)) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 1
        congr 1
        ring
  rw [heq]
  calc
    _ ≤ ∑ h ∈ Finset.Icc 1 n,
        A * Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * n)) :=
      Finset.sum_le_sum hfiber
    _ = A * (∑ h ∈ Finset.Icc 1 n,
        Real.exp (-((13 * P.cMat / 16) * (h : ℝ) * n))) := by
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hseries hA

end InducedStars
