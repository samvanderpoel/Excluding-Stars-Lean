import InducedStars.Structure.Subcritical.ProfileCounting
import InducedStars.Structure.Subcritical.ProfileHeadroom
import InducedStars.Structure.Subcritical.ProfileProbability
import InducedStars.Structure.Subcritical.ProfileRootEnergy
import InducedStars.Structure.Subcritical.ProfileErrorAbsorption

/-!
# Finite master profile counting

Paper: Lemma `lemma:profile-bound-K1k`. The remainder graph stays fixed
through the weighted leftover sum. Residual maxima are summed with their edge
weights in natural units before the matching exponent is used.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n : ℕ} {D : SubcriticalDivision k (Fin n)}
  {eta theta : ℝ} {R₀ : ℕ}

/-- The outside-root penalties vanish, so the local sum contains exactly
the retained-root probability cost and all rooted choice entropies. -/
theorem subcriticalProfileLocalExponent_sum
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ) :
    (∑ v ∈ p.roots, subcriticalProfileLocalExponent p m C alpha delta epsilon v) =
      (∑ v ∈ p.roots, subcriticalProfileRootEntropyNat p v) -
        ∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v := by
  simp only [subcriticalProfileLocalExponent, Finset.sum_sub_distrib]
  congr 1
  symm
  apply Finset.sum_subset (fun v hv ↦ Finset.mem_union_left _ hv)
  intro v _ hv
  simp [subcriticalProfileRootTailPenalty, hv]

/-- The signed exponential level cost splits into a root weight, the
weighted residual cost, and precisely the leftover/root-error weight. -/
theorem subcriticalCompatible_signedExponent_le
    {F : Finset (SimpleGraph (Fin n))} {alpha delta : ℝ}
    {p : SubcriticalProfile D eta R₀ theta} {TB R L : SimpleGraph (Fin n)}
    (hc : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1) :
    -subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ) +
      subcriticalActiveLevelConstant k * delta *
        |(subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ)| ≤
    -subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ TB : ℝ) +
      subcriticalResidualWeightConstant k * (finiteGraphEdges R).card +
        (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
          subcriticalActiveLevelConstant k * delta *
            |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
          subcriticalActiveLevelConstant k * delta *
            |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|) := by
  rw [hc.signedSize_eq]
  push_cast
  have habs := (abs_add_le
    ((subcriticalSignedDefectSize D eta R₀ TB : ℝ) +
      (subcriticalSignedDefectSize D eta R₀ R : ℝ))
    (subcriticalSignedDefectSize D eta R₀ L : ℝ)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  have hmul := mul_le_mul_of_nonneg_left habs
    (mul_nonneg (subcriticalActiveLevelConstant_pos k).le hd)
  have hres := subcriticalResidualSignedCost_le (D := D) (eta := eta) (R₀ := R₀) R hd hd1
  linarith

/-- One fixed compatible pattern, after summing the narrow quota vector.
The residual maximum is retained unchanged, ready for its weighted sum. -/
theorem subcriticalProfileLevelSum_le
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ)
    (hk : 3 ≤ k) (hn : 2 ≤ n) (hd : 0 ≤ delta)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n))
    (hH : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hedges : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (finiteGraphEdges G).card = m)
    (hwindow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (hdefect : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hheadroom : epsilon * (n : ℝ) ^ 2 ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4) :
    (∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
      (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
      (retainedEdgeCountMultiplicity mvec : ℝ) *
        subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
          (subcriticalProfileProbabilityEvent p alpha R)) ≤
      ((n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀))) ^ 2 *
        (retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) : ℝ) *
        Real.exp (-∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
        Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ TB : ℝ)) *
        (Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
          subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R) *
        Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
          subcriticalActiveLevelConstant k * delta *
            |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
          subcriticalActiveLevelConstant k * delta *
            |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|) := by
  let P := (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀))
  let J := ∑ v ∈ p.retainedRoots,
    subcriticalProfileRootTailPenalty p m C alpha delta epsilon v
  let Q := subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R
  let Z := (retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) : ℝ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := subcriticalResidualSafeMaximum_nonneg F p m C alpha delta epsilon TB R
  have hZ : 0 ≤ Z := Nat.cast_nonneg _
  have hc := (mem_subcriticalLeftoverDefectPatternFinset F alpha p TB R L).mp
    (subcriticalLeftoverDefectPatternFinsetWithRemainder_subset F alpha p H TB R hL)
  obtain ⟨G, hG, hsigned, hcard⟩ := hc.exists_signedSize_bound
  have habs : |(subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ)| ≤
      delta * retainedActiveTotalCapacity D eta R₀ / 4 := by
    have hs : |(subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ)| ≤
        (finiteGraphEdges (TB ⊔ R ⊔ L)).card := by
      rw [← hc.signedSize_eq] at hsigned
      exact_mod_cast hsigned
    exact hs.trans ((by exact_mod_cast hcard :
      ((finiteGraphEdges (TB ⊔ R ⊔ L)).card : ℝ) ≤ subcriticalDefectCost G D).trans
        ((hdefect G hG).trans hheadroom))
  have hlevel := subcriticalActiveLevelComparison_signed D eta R₀ m hk
    (by simpa using hn) hd hdp hdq hreserve (p.b : ℤ)
      (subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)) habs
  simp only [Fintype.card_fin] at hlevel
  have hexp := Real.exp_le_exp.mpr (subcriticalCompatible_signedExponent_le hc hd
    (by have hp := (pK_mem_Icc k).2; linarith : delta ≤ 1))
  have hsum : (∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
      (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
      (retainedEdgeCountMultiplicity mvec : ℝ) *
        subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
          (subcriticalProfileProbabilityEvent p alpha R)) ≤
      (retainedNarrowPartitionFunction D eta R₀ m delta
        (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)) : ℝ) *
          (P * (Real.exp (-J) * Q)) := by
    simp only [retainedNarrowPartitionFunction, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro mvec hmvec
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact subcriticalFixedProfileProbability_maximum hn F p m C alpha delta epsilon
      H TB R L mvec hH hL
        (subcriticalCompatible_narrowLevel_subset_window F p m C alpha delta epsilon
          H TB R L hL hedges hwindow hmvec)
  apply hsum.trans
  calc
    _ ≤ (P * Z * Real.exp
        (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ) +
          subcriticalActiveLevelConstant k * delta *
            |(subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L) : ℝ)|)) *
        (P * (Real.exp (-J) * Q)) :=
      mul_le_mul_of_nonneg_right hlevel (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le hQ))
    _ ≤ (P * Z * Real.exp
        (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ TB : ℝ) +
          subcriticalResidualWeightConstant k * (finiteGraphEdges R).card +
          (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
            subcriticalActiveLevelConstant k * delta *
              |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
            subcriticalActiveLevelConstant k * delta *
              |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|))) *
        (P * (Real.exp (-J) * Q)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (mul_nonneg hP hZ))
        (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le hQ))
    _ = _ := by simp only [Real.exp_add]; dsimp [P, J, Q, Z]; ring

section ProfileGeometry

variable
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (alpha delta epsilon : ℝ)
    (hk : 3 ≤ k) (hn : 2 ≤ n)
    (halpha : 0 ≤ alpha) (halpha_half : 5 * alpha ≤ 1 / 2)
    (htheta : 0 ≤ theta) (hdelta : 0 ≤ delta) (hepsilon : 0 ≤ epsilon)
    (hdp : 6 * delta ≤ pK k) (hdq : 6 * delta ≤ 1 - pK k)
    (hreserve : ∀ e, 2 ≤ delta * retainedActiveCapacity D eta R₀ e)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * (n : ℝ) / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * (n : ℝ))
    (hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2)
    (hfree : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (hsmall : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p, ∀ v,
      (degreeInFinset G v (D.nonretainedSmallVertices eta R₀ theta) : ℝ) ≤
        subcriticalSparseSideConstant k * theta * (n : ℝ))
    (hedges : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (finiteGraphEdges G).card = m)
    (hwindow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountWindow D eta R₀ m (subcriticalSparseSideConstant k) delta epsilon)
    (hdefect : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      (subcriticalDefectCost G D : ℝ) ≤ epsilon * (n : ℝ) ^ 2)
    (hheadroom : epsilon * (n : ℝ) ^ 2 ≤ delta * retainedActiveTotalCapacity D eta R₀ / 4)

include hk hn halpha halpha_half htheta hdelta hepsilon hdp hdq hreserve
  hret hpart hroot hrho hfree hsmall hedges hwindow hdefect hheadroom

set_option maxHeartbeats 800000 in
-- The nested quota sums use the allowance already needed by the fixed-H proof.
/-- Weighted profile sum for one fixed remainder and the unchanged ambient
family. Fixed-remainder and retained-key counting: apply the leftover estimate before summing over `H`,
and retain the same `F` in every residual probability maximum. -/
theorem subcriticalProfileFixedRemainderSum_le_of_geometry
    (H : SubcriticalRemainderGraph D eta R₀)
    (hH : H ∈ subcriticalProfileRemainderFinset p) :
    (∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
      ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
          ∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
            (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
            (retainedEdgeCountMultiplicity mvec : ℝ) *
              subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
                (subcriticalProfileProbabilityEvent p alpha R)) ≤
      (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
        (retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) : ℝ) *
        Real.exp ((∑ v ∈ p.roots,
          subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
            alpha delta epsilon v) +
          subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
            alpha delta epsilon + subcriticalProfileErrorBudget alpha delta epsilon p) := by
  let C := subcriticalSparseSideConstant k
  let P := (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀))
  let Z := (retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) : ℝ)
  let J := ∑ v ∈ p.retainedRoots,
    subcriticalProfileRootTailPenalty p m C alpha delta epsilon v
  let Ent := ∑ v ∈ p.roots, subcriticalProfileRootEntropyNat p v
  let Mat := subcriticalProfileMatchingExponent F p m C alpha delta epsilon
  let Err := subcriticalProfileErrorBudget alpha delta epsilon p
  let K := P ^ 2 * Z * Real.exp (-J)
  let wb := fun TB : SimpleGraph (Fin n) ↦
    Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ TB : ℝ))
  let wr := fun TB R : SimpleGraph (Fin n) ↦
    Real.exp (subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) *
      subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R
  let wl := fun TB L : SimpleGraph (Fin n) ↦
    Real.exp (-subcriticalLogOddsNat k * (subcriticalSignedDefectSize D eta R₀ L : ℝ) +
      subcriticalActiveLevelConstant k * delta *
        |(subcriticalSignedDefectSize D eta R₀ L : ℝ)| +
      subcriticalActiveLevelConstant k * delta *
        |(subcriticalSignedDefectSize D eta R₀ TB : ℝ)|)
  let f := fun (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n)) ↦
    ∑ mvec ∈ retainedNarrowEdgeCountLevel D eta R₀ m delta
      (p.b + subcriticalSignedDefectSize D eta R₀ (TB ⊔ R ⊔ L)),
      (retainedEdgeCountMultiplicity mvec : ℝ) *
        subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
          (subcriticalProfileProbabilityEvent p alpha R)
  have hK : 0 ≤ K := by dsimp [K, Z]; positivity
  have hwb : ∀ TB, 0 ≤ wb TB := fun TB ↦ (Real.exp_pos _).le
  have hwr : ∀ TB R, 0 ≤ wr TB R := fun TB R ↦
    mul_nonneg (Real.exp_pos _).le
      (subcriticalResidualSafeMaximum_nonneg F p m C alpha delta epsilon TB R)
  have hpoint : ∀ H ∈ subcriticalProfileRemainderFinset p, ∀ TB R,
      ∀ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
        f H TB R L ≤ K * wb TB * wr TB R * wl TB L := by
    intro H hH TB R L hL
    exact subcriticalProfileLevelSum_le F p m C alpha delta epsilon hk hn hdelta hdp hdq
      hreserve H TB R L (mem_subcriticalProfileRemainderFinset p H |>.mp hH).1
      hL hedges hwindow hdefect hheadroom
  have hleft : ∀ H TB R,
      (∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
        wl TB L) ≤ Real.exp Err := by
    intro H TB R
    exact subcriticalProfileLeftover_weightedSum_le_exp_errorBudget F H TB R hk
      (by simpa using hn) halpha halpha_half htheta hdelta hepsilon hdp hdq hret
      (by simpa using hpart) (by simpa using hroot) hrho hfree (by simpa using hsmall)
  have hLsum : ∀ H ∈ subcriticalProfileRemainderFinset p, ∀ TB R,
      (∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
        f H TB R L) ≤ K * wb TB * wr TB R * Real.exp Err := by
    intro H hH TB R
    calc
      _ ≤ ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
          K * wb TB * wr TB R * wl TB L := Finset.sum_le_sum (hpoint H hH TB R)
      _ = (K * wb TB * wr TB R) *
          ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
            wl TB L := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hleft H TB R)
        (mul_nonneg (mul_nonneg hK (hwb TB)) (hwr TB R))
  have hRsum : ∀ H ∈ subcriticalProfileRemainderFinset p,
      ∀ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
      (∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
        ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
          f H TB R L) ≤ K * wb TB * Real.exp Err * Real.exp Mat := by
    intro H hH TB hTB
    calc
      _ ≤ ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
          K * wb TB * wr TB R * Real.exp Err := Finset.sum_le_sum (fun R _ ↦ hLsum H hH TB R)
      _ = (K * wb TB * Real.exp Err) *
          ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB, wr TB R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (subcriticalResidualWeightedSum_le_exp_matching F p m C alpha delta epsilon hTB)
        (mul_nonneg (mul_nonneg hK (hwb TB)) (Real.exp_pos _).le)
  have hTBsum : ∀ H ∈ subcriticalProfileRemainderFinset p,
      (∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
        ∑ R ∈ subcriticalResidualDefectPatternFinset F alpha p TB,
          ∑ L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R,
            f H TB R L) ≤ K * Real.exp Err * Real.exp Mat * Real.exp Ent := by
    intro H hH
    calc
      _ ≤ ∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p,
          K * wb TB * Real.exp Err * Real.exp Mat := Finset.sum_le_sum (hRsum H hH)
      _ = (K * Real.exp Err * Real.exp Mat) *
          ∑ TB ∈ subcriticalRootedDefectPatternFinset F alpha p, wb TB := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro TB _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (subcriticalRootFreeEnergy_le F alpha p)
        (mul_nonneg (mul_nonneg hK (Real.exp_pos _).le) (Real.exp_pos _).le)
  have hP : P ^ 2 = (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) := by
    dsimp [P]
    rw [← pow_mul]
    congr 1
    omega
  have hexp : Real.exp (-J) * Real.exp Err * Real.exp Mat * Real.exp Ent =
      Real.exp ((∑ v ∈ p.roots,
        subcriticalProfileLocalExponent p m C alpha delta epsilon v) + Mat + Err) := by
    rw [subcriticalProfileLocalExponent_sum]
    simp only [← Real.exp_add]
    congr 1
    dsimp [J, Ent]
    ring
  calc
    _ ≤ K * Real.exp Err * Real.exp Mat * Real.exp Ent := hTBsum H hH
    _ = P ^ 2 * Z *
        Real.exp ((∑ v ∈ p.roots,
          subcriticalProfileLocalExponent p m C alpha delta epsilon v) + Mat + Err) := by
      rw [← hexp]
      dsimp [K]
      ring
    _ = _ := by rw [hP]

/-- Finite master profile bound. The hypotheses are the actual close-geometry
and finite density reserves, not assumed counting conclusions. The remainder
graph is summed only after the fixed-remainder weighted leftover estimate. -/
theorem subcriticalProfileBound_of_geometry
    (hb : (p.b : ℝ) ≤ subcriticalSparseSideConstant k * eta * (n : ℝ) ^ 2) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
        (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) *
        Real.exp ((∑ v ∈ p.roots,
          subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
            alpha delta epsilon v) +
          subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
            alpha delta epsilon + subcriticalProfileErrorBudget alpha delta epsilon p) := by
  let C := subcriticalSparseSideConstant k
  let P := (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀))
  let Z := (retainedPartitionFunction D eta R₀ m delta (p.b : ℤ) : ℝ)
  let E := Real.exp ((∑ v ∈ p.roots,
    subcriticalProfileLocalExponent p m C alpha delta epsilon v) +
    subcriticalProfileMatchingExponent F p m C alpha delta epsilon +
    subcriticalProfileErrorBudget alpha delta epsilon p)
  have htrim : ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
    exact subcriticalProfile_tailTrim_of_geometry p halpha hret
      (by simpa using hpart) (by simpa using hroot) hrho
  have hnarrow : ∀ G ∈ subcriticalProfileClassGraphFinset F alpha p,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedNarrowEdgeCountLevel D eta R₀ m delta (retainedEdgeShift G D eta R₀) := by
    intro G hG
    have h := (mem_retainedNarrowEdgeCountWindow.mp (hwindow G hG)).1
    rwa [subcriticalActualLevelShift_eq_of_edge_count G D eta R₀ m (hedges G hG)] at h
  have hcount := subcriticalProfileCountingDecomposition F p m alpha delta
    (subcriticalProfileProbabilityEvent p alpha) hfree hnarrow
    (fun G hG ↦ (mem_subcriticalProfileClassGraphFinset.mp hG).2.mem_probabilityEvent
      halpha htrim (hfree G hG) _)
  have hsum : ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      ∑ H ∈ subcriticalProfileRemainderFinset p, P * Z * E := by
    apply hcount.trans (Finset.sum_le_sum _)
    intro H hH
    exact subcriticalProfileFixedRemainderSum_le_of_geometry F p m alpha delta epsilon
      hk hn halpha halpha_half htheta hdelta hepsilon hdp hdq hreserve hret hpart
      hroot hrho hfree hsmall hedges hwindow hdefect hheadroom H hH
  have hclean : (subcriticalProfileRemainderFinset p).card * Z ≤
      (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) := by
    dsimp [Z]
    rw [card_subcriticalProfileRemainderFinset]
    exact_mod_cast subcriticalProfileRemainderTerm_le_cleanPartitionFunction p m delta
      (by simpa using hb)
  calc
    _ ≤ ∑ H ∈ subcriticalProfileRemainderFinset p, P * Z * E := hsum
    _ = P * ((subcriticalProfileRemainderFinset p).card * Z) * E := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ P * (cleanRetainedPartitionFunction D eta R₀ m delta : ℝ) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hclean (by dsimp [P]; positivity))
        (Real.exp_pos _).le

end ProfileGeometry

end InducedStars
