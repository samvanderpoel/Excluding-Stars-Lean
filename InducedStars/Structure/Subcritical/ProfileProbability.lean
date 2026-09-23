import InducedStars.Structure.Subcritical.ProfileEventSupport

/-!
# Fixed-profile probability bounds

Paper: Lemma `lemma:fixed-profile-probability-K1k`.
The exponent uses natural units, compatible leftover fibers retain the fixed remainder, and residual star witnesses are restricted
to the complement of every profile root. No Janson estimate occurs here.

The refined forms preserve the residual probability (or its admissible
maximum). These are needed before summing residual patterns: replacing
every summand by the whole matching sum would introduce an erroneous
extra factor counting those patterns.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped BigOperators Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- Compatibility supplies actual retained defects, hence never toggles an
active coordinate. The fixed-remainder restriction is preserved. -/
theorem subcriticalCompatiblePattern_valid
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R) :
    IsSubcriticalRetainedDefectPattern D eta R₀ (TB ⊔ R ⊔ L) := by
  have hc := (mem_subcriticalLeftoverDefectPatternFinset F alpha p TB R L).mp
    (subcriticalLeftoverDefectPatternFinsetWithRemainder_subset F alpha p H TB R hL)
  obtain ⟨G, _, hG⟩ := hc.decomposition.1
  rw [← hG]
  exact subcriticalRetainedIncidentDefectGraph_valid G D eta R₀

/-- Each individual narrow vector is bounded by the profile's root penalties;
the empty product is one, consistent with no retained roots. -/
theorem subcriticalProfileTailProduct_le_exp_penalty
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    (∏ v ∈ p.retainedRoots, subcriticalRootTailProbability p alpha v mvec) ≤
      Real.exp (-∑ v ∈ p.retainedRoots,
        subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) := by
  calc
    _ ≤ ∏ v ∈ p.retainedRoots,
        Real.exp (-subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) :=
      Finset.prod_le_prod
        (fun v _ ↦ (subcriticalRootTailProbability_mem_Icc p alpha v mvec).1)
        (fun v _ ↦ subcriticalRootTailProbability_le_exp_penalty
          p m C alpha delta epsilon v hm)
    _ = _ := by rw [← Real.exp_sum, Finset.sum_neg_distrib]

/-- Refined Bernoulli bound retaining the actual residual probability.
Valid defects are the only deterministic assumption needed. -/
theorem subcriticalProfileBernoulliProbability_refined
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ (TB ⊔ R ⊔ L))
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveBernoulliProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      Real.exp (-∑ v ∈ p.retainedRoots,
        subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
          subcriticalResidualSafeProbability p H TB R L mvec := by
  unfold subcriticalActiveBernoulliProbability
  rw [subcriticalProfileProbabilityEvent_pullback p alpha H (TB ⊔ R ⊔ L) R hT mvec,
    subcriticalTailResidual_probability_eq_prod]
  exact mul_le_mul_of_nonneg_right
    (subcriticalProfileTailProduct_le_exp_penalty p m C alpha delta epsilon mvec hm)
    (subcriticalResidualSafeProbability_mem_Icc p H TB R L mvec).1

/-- Refined bound retaining the admissible residual maximum for a particular
rooted/residual pair, ready for the weighted residual sum. -/
theorem subcriticalProfileBernoulliProbability_maximum
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveBernoulliProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      Real.exp (-∑ v ∈ p.retainedRoots,
        subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
          subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R :=
  (subcriticalProfileBernoulliProbability_refined p m C alpha delta epsilon H TB R L mvec
    (subcriticalCompatiblePattern_valid F p alpha H TB R L hL) hm).trans
      (mul_le_mul_of_nonneg_left
        (subcriticalResidualSafeProbability_le_maximum F p m C alpha delta epsilon
          H TB R L mvec hfree hL hm) (Real.exp_pos _).le)

/-- Bernoulli form of the fixed-profile estimate, retaining the compensating
negative residual-edge term from the matching weight. -/
theorem subcriticalProfileBernoulliProbability
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveBernoulliProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      Real.exp (-(∑ v ∈ p.retainedRoots,
        subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) +
          subcriticalProfileMatchingExponent F p m C alpha delta epsilon -
            subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) := by
  apply (subcriticalProfileBernoulliProbability_refined p m C alpha delta epsilon H TB R L mvec
    (subcriticalCompatiblePattern_valid F p alpha H TB R L hL) hm).trans
  calc
    _ ≤ Real.exp (-∑ v ∈ p.retainedRoots,
        subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
      Real.exp (subcriticalProfileMatchingExponent F p m C alpha delta epsilon -
        subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) :=
      mul_le_mul_of_nonneg_left
        (subcriticalResidualSafeProbability_le_exp_matching F p m C alpha delta epsilon
          H TB R L mvec hfree hL hm) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

section Fixed

variable {n : ℕ} {D : SubcriticalDivision k (Fin n)} {eta theta : ℝ} {R₀ : ℕ}

/-- Fixed-count refinement preserving the actual residual probability. -/
theorem subcriticalFixedProfileProbability_refined
    (hn : 2 ≤ n) (p : SubcriticalProfile D eta R₀ theta)
    (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n))
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ (TB ⊔ R ⊔ L))
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        (Real.exp (-∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
            subcriticalResidualSafeProbability p H TB R L mvec) :=
  (subcriticalFixedCountTransfer hn H (TB ⊔ R ⊔ L) mvec
    (subcriticalProfileProbabilityEvent p alpha R)).trans
      (mul_le_mul_of_nonneg_left
        (subcriticalProfileBernoulliProbability_refined p m C alpha delta epsilon
          H TB R L mvec hT hm) (by positivity))

/-- Fixed-count refinement preserving the admissible residual maximum. -/
theorem subcriticalFixedProfileProbability_maximum
    (hn : 2 ≤ n) (F : Finset (SimpleGraph (Fin n)))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n))
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        (Real.exp (-∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) *
            subcriticalResidualSafeMaximum F p m C alpha delta epsilon TB R) :=
  (subcriticalFixedCountTransfer hn H (TB ⊔ R ⊔ L) mvec
    (subcriticalProfileProbabilityEvent p alpha R)).trans
      (mul_le_mul_of_nonneg_left
        (subcriticalProfileBernoulliProbability_maximum F p m C alpha delta epsilon
          H TB R L mvec hfree hL hm) (by positivity))

/-- Paper: Lemma `lemma:fixed-profile-probability-K1k`.
The stronger weighted bound has the explicit transfer constant `3`.
Natural units. Fixed-remainder compatibility.
Residual induced stars avoid every profile root. -/
theorem subcriticalFixedProfileProbability
    (hn : 2 ≤ n) (F : Finset (SimpleGraph (Fin n)))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n))
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        Real.exp (-(∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) +
            subcriticalProfileMatchingExponent F p m C alpha delta epsilon -
              subcriticalResidualWeightConstant k * (finiteGraphEdges R).card) :=
  (subcriticalFixedCountTransfer hn H (TB ⊔ R ⊔ L) mvec
    (subcriticalProfileProbabilityEvent p alpha R)).trans
      (mul_le_mul_of_nonneg_left
        (subcriticalProfileBernoulliProbability F p m C alpha delta epsilon
          H TB R L mvec hfree hL hm) (by positivity))

/-- The source-shaped weaker corollary, with the nonpositive weighted
residual correction dropped. Root-avoiding residual safety remains explicit. -/
theorem subcriticalFixedProfileProbability_weak
    (hn : 2 ≤ n) (F : Finset (SimpleGraph (Fin n)))
    (p : SubcriticalProfile D eta R₀ theta) (m : ℕ) (C alpha delta epsilon : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph (Fin n))
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) H)
    (hL : L ∈ subcriticalLeftoverDefectPatternFinsetWithRemainder F alpha p H TB R)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon) :
    subcriticalActiveFixedProbability H (TB ⊔ R ⊔ L) mvec
        (subcriticalProfileProbabilityEvent p alpha R) ≤
      (n : ℝ) ^ (3 * Fintype.card (RetainedActivePair D eta R₀)) *
        Real.exp (-(∑ v ∈ p.retainedRoots,
          subcriticalProfileRootTailPenalty p m C alpha delta epsilon v) +
            subcriticalProfileMatchingExponent F p m C alpha delta epsilon) := by
  apply (subcriticalFixedProfileProbability hn F p m C alpha delta epsilon
    H TB R L mvec hfree hL hm).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (mul_nonneg (subcriticalResidualWeightConstant_pos k).le
    (Nat.cast_nonneg _))

end Fixed
end InducedStars
