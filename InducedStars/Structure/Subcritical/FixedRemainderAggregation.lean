import InducedStars.Structure.Subcritical.FixedRemainderProfileBound
import InducedStars.Structure.Subcritical.ProfileAggregation
import InducedStars.Structure.Subcritical.CleanCanonical

/-!
# Aggregation with a fixed induced remainder

These inequalities are obtained before the sum over actual remainder
graphs. The same ambient family supplies all profile probabilities, and no
canonicality of constructed model graphs is assumed.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n R₀ m : ℕ} {gamma omega eta theta alpha delta epsilon : ℝ}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}

/-- Fixed-remainder refinement of the finite penalty, with the original
family in all maxima and logarithms. -/
theorem subcriticalProfilePenaltyCore_fixedRemainder
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n))) (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ)^2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hfixed : ∀ G ∈ F, subcriticalRemainderGraph G D eta R₀ = H) :
    ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
      (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) *
        (retainedPartitionFunction D eta R₀ m delta
          ((finiteGraphEdges H).card : ℤ) : ℝ) *
        Real.exp (-(48 * subcriticalAggregationConstant k eta R₀) *
          subcriticalProfileComplexity p * n) := by
  by_cases hne : (subcriticalProfileClassGraphFinset F alpha p).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G₀, hG₀⟩ := hne
  obtain ⟨hG₀F, hp⟩ := mem_subcriticalProfileClassGraphFinset.mp hG₀
  let R := (A.close G₀ hG₀F).some
  have hR := P.localConditions.retained_order
  have heta := P.localConditions.eta_pos
  have htheta := P.localConditions.theta_pos
  have halpha := P.localConditions.alpha_pos
  have hdelta := P.residual.delta_pos
  have hepsilon := P.residual.epsilon_pos
  have hcutoff := P.localConditions.retained_visible
  have hret := D.retainedPartIndices_subset_visiblePartIndices hR htheta.le hcutoff
  have hthetaEta : theta ≤ eta := by
    have hRreal : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR
    exact hcutoff.trans (div_le_self heta.le (by linarith))
  have hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * n / 2 ≤ ((D.part a).card : ℝ) :=
    fun a ha ↦ R.visible_part_card_ge_half homega a ha
  have hroot : (p.roots.card : ℝ) ≤
      subcriticalProfileRootFraction alpha theta epsilon * n := by
    rw [hp.roots_eq]
    exact R.badRoots_card_le halpha htheta (by have := P.profile_order; omega)
      hR homega hcutoff
  have hsparse G (hG : G ∈ F) :=
    (A.close G hG).some.sparseSideControls heta.le hR P.retained_inverse homega hthetaEta
      (P.epsilon_cap.trans (min_le_left _ _))
      (P.epsilon_cap.trans (min_le_right _ _)) P.residual.sparse_scale (A.free G hG)
  have hhead := (R.profileActiveCapacityHeadroom hR htheta.le homega hcutoff
    (A.edges G₀ hG₀F) (hsparse G₀ hG₀F).1 hdensity P.density_headroom
    hdelta.le P.shift_headroom).2
  have hround := R.profileActiveRoundingReserve hR heta.le htheta hdelta hcutoff
    P.active_rounding
  have hrho : subcriticalProfileRootFraction alpha theta epsilon ≤ alpha * theta / 2 :=
    P.localConditions.root_fraction.trans (by nlinarith [mul_pos halpha htheta])
  have hbound := subcriticalProfileBound_fixedRemainder_of_geometry F p m alpha delta epsilon H hk
    P.profile_order halpha.le P.localConditions.alpha_small htheta.le hdelta.le hepsilon.le
    P.localConditions.density_lower P.localConditions.density_upper hround hret hpart hroot hrho
    (fun G hG ↦ A.free G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
    (fun G hG ↦ (hsparse G (mem_subcriticalProfileClassGraphFinset.mp hG).1).2.2)
    (fun G hG ↦ A.edges G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
    (fun G hG ↦ (A.close G (mem_subcriticalProfileClassGraphFinset.mp hG).1).some.actualRetainedEdgeCountVector_mem_narrowWindow hR heta.le htheta.le
        P.retained_inverse homega hcutoff (by have := P.localConditions.alpha_small; linarith)
        P.epsilon_cap P.residual.sparse_scale
        (A.free G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
        (A.edges G (mem_subcriticalProfileClassGraphFinset.mp hG).1))
    (fun G hG ↦ (A.close G (mem_subcriticalProfileClassGraphFinset.mp hG).1).some.defect_cost_le)
    hhead (fun G hG ↦ hfixed G (mem_subcriticalProfileClassGraphFinset.mp hG).1)
  have hlocal : (∑ v ∈ p.roots,
      subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
        alpha delta epsilon v) ≤
      -subcriticalAggregationRootRate k eta R₀ * n * p.roots.card := by
    have hh := Finset.sum_le_sum (fun v hv ↦ subcriticalLocalCompensation_of_geometry
      hk P.localConditions R homega (A.free G₀ hG₀F) (A.minimal G₀ hG₀F) hp hroot
      m (subcriticalSparseSideConstant k) v hv)
    simpa only [Finset.sum_const, nsmul_eq_mul, subcriticalAggregationRootRate,
      div_eq_mul_inv, neg_mul, mul_neg, mul_assoc, mul_left_comm, mul_comm] using hh
  have hmatching := subcriticalResidualMatchingEstimateCore_all_ell hk J F p m
    (subcriticalSparseSideConstant k) heta hetaOne hR P.residual
    (fun a ha ↦ R.retainedPart_card_lower_bound hR heta.le ha) hpart A.free
    (fun G hG ↦ (A.close G hG).some.defect_cost_le)
  have herr := P.profile_error_le p
  have hrootRate := mul_le_mul_of_nonneg_right
    (subcriticalAggregationConstant_le_root k eta R₀)
    (show (0 : ℝ) ≤ n * p.roots.card by positivity)
  have hmatchingRate := mul_le_mul_of_nonneg_right
    (subcriticalAggregationConstant_le_matching k eta R₀)
    (show (0 : ℝ) ≤ p.ell * n by positivity)
  have hexp : (∑ v ∈ p.roots,
      subcriticalProfileLocalExponent p m (subcriticalSparseSideConstant k)
        alpha delta epsilon v) +
      subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
        alpha delta epsilon + subcriticalProfileErrorBudget alpha delta epsilon p ≤
      -(48 * subcriticalAggregationConstant k eta R₀) * subcriticalProfileComplexity p * n := by
    change _ ≤ -(48 * subcriticalAggregationConstant k eta R₀) *
      ((p.roots.card + p.ell : ℕ) : ℝ) * n
    simp only [Nat.cast_add]
    change subcriticalProfileMatchingExponent F p m (subcriticalSparseSideConstant k)
      alpha delta epsilon ≤ -subcriticalAggregationMatchingRate k eta R₀ * p.ell * n at hmatching
    have hc := subcriticalAggregationConstant_pos hk heta hR
    nlinarith [show 0 ≤ subcriticalAggregationConstant k eta R₀ * p.ell * n by positivity]
  exact hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))

/-- The nonclean family with a single actual remainder has only one
wide-level partition-function factor. -/
theorem subcriticalNoncleanDivision_card_le_fixedRemainder
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n)))
    (H : SubcriticalRemainderGraph D eta R₀)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hfixed : ∀ G ∈ F, subcriticalRemainderGraph G D eta R₀ = H)
    (hpoly : ((n : ℝ) + 1) ^
        (2 * subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) +
          6 * subcriticalActiveIndexBound eta R₀ + 2) ≤
      Real.exp (subcriticalAggregationConstant k eta R₀ * n)) :
    ((subcriticalNoncleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      Real.exp (-subcriticalAggregationConstant k eta R₀ * n) *
        (retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) : ℝ) := by
  by_cases hF : F.Nonempty
  swap
  · have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [hzero, subcriticalNoncleanDivisionGraphFinset, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨G₀, hG₀⟩ := hF
  let R := (A.close G₀ hG₀).some
  let c := subcriticalAggregationConstant k eta R₀
  let Qvis := subcriticalVisibleIndexBound theta
  let Qact := subcriticalActiveIndexBound eta R₀
  let Cprof := subcriticalProfileEnumerationConstant Qvis
  let Z : ℝ := retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hc : 0 < c := subcriticalAggregationConstant_pos hk
    P.localConditions.eta_pos P.localConditions.retained_order
  have hbase : (1 : ℝ) ≤ n + 1 := by exact_mod_cast (show 1 ≤ n + 1 by omega)
  have hvisible : ∀ a ∈ D.visiblePartIndices theta,
      theta * Fintype.card (Fin n) / 2 ≤ ((D.part a).card : ℝ) := by
    intro a ha
    simpa only [Fintype.card_fin] using R.visible_part_card_ge_half homega a ha
  have hvis := subcriticalVisiblePartIndices_card_le D P.localConditions.theta_pos hvisible
  have hret := D.retainedPartIndices_subset_visiblePartIndices
    P.localConditions.retained_order P.localConditions.theta_pos.le
    P.localConditions.retained_visible
  have hact := subcriticalRetainedActivePair_card_le D R₀ P.localConditions.eta_pos
  have hpolyAct : (n : ℝ) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) ≤
      ((n : ℝ) + 1) ^ (6 * Qact) := by
    calc
      _ ≤ ((n : ℝ) + 1) ^ (6 * Fintype.card (RetainedActivePair D eta R₀)) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ _ := pow_le_pow_right₀ hbase (Nat.mul_le_mul_left 6 hact)
  have hprofile (r : ℕ) (p : SubcriticalProfile D eta R₀ theta)
      (hp : p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r) :
      ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) ≤
        ((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n) := by
    have hcount := subcriticalProfilePenaltyCore_fixedRemainder hk J F p H P hetaOne homega hdensity A hfixed
    have hr := (mem_subcriticalProfilesOfComplexity D eta R₀ theta r p).mp hp
    rw [hr] at hcount
    have hexp : Real.exp (-(48 * c) * r * n) ≤ Real.exp (-(32 * c) * r * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [show 0 ≤ c * r * n by positivity]
    exact hcount.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hpolyAct hZ) hexp
      (Real.exp_pos _).le (by positivity))
  have hlevel (r : ℕ) :
      (∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
        ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ)) ≤
      Z * (((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
        Real.exp (-(32 * c) * r * n)) := by
    have hcount : ((subcriticalProfilesOfComplexity D eta R₀ theta r).card : ℝ) ≤
        ((n : ℝ) + 1) ^ (Cprof * (r + 1)) := by
      have hh := subcriticalProfilesOfComplexity_card_le D eta R₀ theta r Qvis hret hvis
      simp only [Fintype.card_fin] at hh
      exact_mod_cast hh
    calc
      _ ≤ ∑ _p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          ((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n) :=
        Finset.sum_le_sum (hprofile r)
      _ = ((subcriticalProfilesOfComplexity D eta R₀ theta r).card : ℝ) *
          (((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n)) := by simp
      _ ≤ ((n : ℝ) + 1) ^ (Cprof * (r + 1)) *
          (((n : ℝ) + 1) ^ (6 * Qact) * Z * Real.exp (-(32 * c) * r * n)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hcover : ((subcriticalNoncleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      ∑ r ∈ Finset.Icc 1 (2 * n),
        ∑ p ∈ subcriticalProfilesOfComplexity D eta R₀ theta r,
          ((subcriticalProfileClassGraphFinset F alpha p).card : ℝ) := by
    have hh := subcriticalNonclean_card_le_sum_profiles F D eta R₀ theta alpha
      P.localConditions.alpha_pos (by have := P.localConditions.alpha_small; linarith)
    simp only [Fintype.card_fin] at hh
    exact_mod_cast hh
  have hsum := DenseGraph.sum_profileComplexity_pow_mul_exp_le Cprof (6 * Qact) n hc.le hpoly
  calc
    _ ≤ _ := hcover
    _ ≤ ∑ r ∈ Finset.Icc 1 (2 * n),
        Z * (((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
          Real.exp (-(32 * c) * r * n)) := Finset.sum_le_sum fun r _ ↦ hlevel r
    _ = Z * ∑ r ∈ Finset.Icc 1 (2 * n),
        ((n : ℝ) + 1) ^ (Cprof * (r + 1) + 6 * Qact) *
          Real.exp (-(32 * c) * r * n) := (Finset.mul_sum _ _ _).symm
    _ ≤ Z * Real.exp (-c * n) := mul_le_mul_of_nonneg_left hsum hZ
    _ = _ := mul_comm _ _

/-- Wide-level choices with the entire induced remainder graph fixed.
No edge-count choice or remainder-graph multiplicity is stored. -/
abbrev SubcriticalFixedRemainderCleanData
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) :=
  Σ v : ↥(retainedEdgeCountLevel D eta R₀ m delta ((finiteGraphEdges H).card : ℤ)),
    RetainedEdgeChoices v.val

def SubcriticalFixedRemainderCleanData.graph
    (H : SubcriticalRemainderGraph D eta R₀)
    (d : SubcriticalFixedRemainderCleanData D eta R₀ m delta H) :
    SimpleGraph (Fin n) :=
  subcriticalCleanGraph H d.2

theorem SubcriticalFixedRemainderCleanData.graph_injective
    (H : SubcriticalRemainderGraph D eta R₀) :
    Function.Injective (SubcriticalFixedRemainderCleanData.graph
      (m := m) (delta := delta) H) := by
  rintro ⟨⟨v, hv⟩, S⟩ ⟨⟨w, hw⟩, U⟩ h
  change subcriticalCleanGraph H S = subcriticalCleanGraph H U at h
  have hvw := congrArg (fun G ↦ actualRetainedEdgeCountVector G D eta R₀) h
  simp only [subcriticalCleanGraph_active_vector] at hvw
  subst w
  have hSU := subcriticalActiveGraphFromOutcome_injective H ⊥
    (isSubcriticalRetainedDefectPattern_bot D eta R₀) v h
  subst U
  rfl

theorem card_subcriticalFixedRemainderCleanData
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) :
    Fintype.card (SubcriticalFixedRemainderCleanData D eta R₀ m delta H) =
      retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) := by
  simp only [SubcriticalFixedRemainderCleanData, Fintype.card_sigma,
    retainedEdgeChoices_card, retainedPartitionFunction, Finset.sum_coe_sort]

/-- The actual clean graphs represented by one exact remainder fiber. -/
def subcriticalFixedRemainderCleanGraphFinset
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) : Finset (SimpleGraph (Fin n)) :=
  Finset.univ.image (SubcriticalFixedRemainderCleanData.graph
    (m := m) (delta := delta) H)

theorem card_subcriticalFixedRemainderCleanGraphFinset
    (D : SubcriticalDivision k (Fin n)) (eta : ℝ) (R₀ m : ℕ) (delta : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) :
    (subcriticalFixedRemainderCleanGraphFinset D eta R₀ m delta H).card =
      retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) := by
  rw [subcriticalFixedRemainderCleanGraphFinset,
    Finset.card_image_of_injective _ (SubcriticalFixedRemainderCleanData.graph_injective H),
    Finset.card_univ, card_subcriticalFixedRemainderCleanData]

theorem mem_subcriticalFixedRemainderCleanGraphFinset_of_clean
    (G : SimpleGraph (Fin n)) (H : SubcriticalRemainderGraph D eta R₀)
    (hclean : subcriticalRetainedIncidentDefectGraph G D eta R₀ = ⊥)
    (hfixed : subcriticalRemainderGraph G D eta R₀ = H)
    (hv : actualRetainedEdgeCountVector G D eta R₀ ∈
      retainedEdgeCountLevel D eta R₀ m delta ((finiteGraphEdges H).card : ℤ)) :
    G ∈ subcriticalFixedRemainderCleanGraphFinset D eta R₀ m delta H := by
  let d : SubcriticalFixedRemainderCleanData D eta R₀ m delta H :=
    ⟨⟨actualRetainedEdgeCountVector G D eta R₀, hv⟩,
      subcriticalActualActiveSample G D eta R₀⟩
  apply Finset.mem_image.mpr
  refine ⟨d, Finset.mem_univ _, ?_⟩
  change subcriticalActiveGraphFromOutcome H ⊥
    (subcriticalActualActiveSample G D eta R₀) = G
  rw [← hfixed, ← hclean]
  exact subcriticalActiveGraphFromOutcome_actual G D eta R₀

/-- A fixed-remainder clean fiber is bounded by its one wide-level count.
No induced-freeness, cutoff, or nonemptiness is needed for this injection. -/
theorem subcriticalCleanDivision_card_le_fixedRemainder_of_wideLevel
    (F : Finset (SimpleGraph (Fin n))) (H : SubcriticalRemainderGraph D eta R₀)
    (hfixed : ∀ G ∈ F, subcriticalRemainderGraph G D eta R₀ = H)
    (hwide : ∀ G ∈ subcriticalCleanDivisionGraphFinset F D eta R₀,
      actualRetainedEdgeCountVector G D eta R₀ ∈
        retainedEdgeCountLevel D eta R₀ m delta ((finiteGraphEdges H).card : ℤ)) :
    (subcriticalCleanDivisionGraphFinset F D eta R₀).card ≤
      retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) := by
  rw [← card_subcriticalFixedRemainderCleanGraphFinset]
  apply Finset.card_le_card
  intro G hG
  obtain ⟨hGF, hclean⟩ := (mem_subcriticalCleanDivisionGraphFinset F G).mp hG
  exact mem_subcriticalFixedRemainderCleanGraphFinset_of_clean G H hclean
    (hfixed G hGF) (hwide G hG)

/-- The wide-level hypothesis follows from the actual common close geometry.
The graph family need not have a particular canonical division. -/
theorem subcriticalCleanDivision_card_le_fixedRemainder
    (hk : 3 ≤ k) (F : Finset (SimpleGraph (Fin n)))
    (H : SubcriticalRemainderGraph D eta R₀)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hfixed : ∀ G ∈ F, subcriticalRemainderGraph G D eta R₀ = H) :
    (subcriticalCleanDivisionGraphFinset F D eta R₀).card ≤
      retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) := by
  apply subcriticalCleanDivision_card_le_fixedRemainder_of_wideLevel F H hfixed
  intro G hG
  obtain ⟨hGF, hclean⟩ := (mem_subcriticalCleanDivisionGraphFinset F G).mp hG
  let R := (A.close G hGF).some
  have hv := R.actualRetainedEdgeCountVector_mem_narrowLevel
    P.localConditions.retained_order P.localConditions.eta_pos.le
    P.localConditions.theta_pos.le P.localConditions.retained_visible
    (by have := P.localConditions.alpha_small; linarith) (A.edges G hGF)
  rw [retainedEdgeShift_eq_remainder_of_clean G hclean, hfixed G hGF] at hv
  exact retainedNarrowEdgeCountLevel_subset D eta R₀ m P.residual.delta_pos.le _ hv

/-- Fixed-(division,remainder) total bound. The remainder multiplicity
is one, including an empty family or an infeasible wide level. -/
theorem subcriticalDivision_card_le_fixedRemainder
    (hk : 3 ≤ k) (J : DenseGraph.PrincipalJansonInput.{0, 0})
    (F : Finset (SimpleGraph (Fin n)))
    (H : SubcriticalRemainderGraph D eta R₀)
    (P : SubcriticalAggregationParameters k gamma eta R₀ theta alpha delta epsilon n)
    (hetaOne : eta ≤ 1) (homega : omega ≤ 1)
    (hdensity : gamma / 8 * (n : ℝ) ^ 2 ≤ m)
    (A : SubcriticalAggregationGeometry hk F D L R₀ m omega eta theta alpha delta epsilon)
    (hfixed : ∀ G ∈ F, subcriticalRemainderGraph G D eta R₀ = H)
    (hpoly : ((n : ℝ) + 1) ^
        (2 * subcriticalProfileEnumerationConstant (subcriticalVisibleIndexBound theta) +
          6 * subcriticalActiveIndexBound eta R₀ + 2) ≤
      Real.exp (subcriticalAggregationConstant k eta R₀ * n)) :
    (F.card : ℝ) ≤
      (1 + Real.exp (-subcriticalAggregationConstant k eta R₀ * n)) *
        (retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) : ℝ) := by
  have hclean : ((subcriticalCleanDivisionGraphFinset F D eta R₀).card : ℝ) ≤
      (retainedPartitionFunction D eta R₀ m delta ((finiteGraphEdges H).card : ℤ) : ℝ) := by
    exact_mod_cast subcriticalCleanDivision_card_le_fixedRemainder hk F H P A hfixed
  have hnon := subcriticalNoncleanDivision_card_le_fixedRemainder
    hk J F H P hetaOne homega hdensity A hfixed hpoly
  have hcard : (F.card : ℝ) =
      (subcriticalCleanDivisionGraphFinset F D eta R₀).card +
        (subcriticalNoncleanDivisionGraphFinset F D eta R₀).card := by
    exact_mod_cast (card_subcriticalClean_add_nonclean F).symm
  rw [hcard]
  calc
    _ ≤ _ := add_le_add hclean hnon
    _ = _ := by ring

end InducedStars
