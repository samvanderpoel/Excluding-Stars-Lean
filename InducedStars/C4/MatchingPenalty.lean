import InducedStars.C4.MatchingCoordinates

/-!
# Independent matching-pattern penalty

Paper: the probability step in Lemma `lemma:c4-matching`. Independence is
proved from pairwise disjoint four-coordinate supports, not from disjointness
of candidate vertex sets. The finite fixed-count comparison loses only the
explicit factor `crossCapacity + 1` supplied by the existing binomial mode
theorem. No unpublished probability input is used.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {D : C4Division V} {q ell : ℕ} (W : C4MatchingSides D q ell)

theorem c4MatchingPattern_probability_ge (P : DenseGraph.FiniteBernoulliProduct (C4CrossCoordinate D))
    (present : Bool) (ij : Fin q × Fin ell) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ e, beta ≤ P.probability e ∧ P.probability e ≤ 1 - beta) :
    beta ^ 4 ≤ P.eventProbability (W.event present ij) := by
  rw [C4MatchingSides.event, P.eventProbability_cylinderEvent (W.pattern_subset_support present ij)]
  calc
    beta ^ 4 = ∏ _e ∈ W.support ij, beta := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ ↦ hbeta) (fun e he ↦ by
      split_ifs
      · exact (hband e).1
      · linarith [(hband e).2])

/-- The independent avoidance estimate handles both matching polarities
with the same compact-band constant. -/
theorem c4Matching_bernoulli_avoidance_le
    (T : SimpleGraph V) (present : Bool) (hstatus : W.InternalStatus T present)
    (P : DenseGraph.FiniteBernoulliProduct (C4CrossCoordinate D))
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : ∀ e, beta ≤ P.probability e ∧ P.probability e ≤ 1 - beta) :
    P.eventProbability (c4DefectFreeOutcomeEvent D T) ≤
      Real.exp (-(beta ^ 4) * (q : ℝ) * ell) := by
  have hcomp (ij : Fin q × Fin ell) :
      P.eventProbability (W.event present ij)ᶜ ≤ Real.exp (-(beta ^ 4)) := by
    have hsum := P.eventProbability_union
      (Finset.disjoint_left.mpr (fun _ he hc ↦ (Finset.mem_compl.mp hc) he) :
        Disjoint (W.event present ij) (W.event present ij)ᶜ)
    rw [Finset.union_compl, P.eventProbability_univ] at hsum
    have hmass := c4MatchingPattern_probability_ge W P present ij hbeta hband
    have hexp := Real.add_one_le_exp (-(beta ^ 4))
    linarith
  calc
    P.eventProbability (c4DefectFreeOutcomeEvent D T) ≤
        P.eventProbability (DenseGraph.FiniteBernoulliProduct.eventIntersection univ
          (fun ij : Fin q × Fin ell ↦ (W.event present ij)ᶜ)) :=
      P.eventProbability_mono (W.freeEvent_subset_avoidance T present hstatus)
    _ = ∏ ij : Fin q × Fin ell, P.eventProbability (W.event present ij)ᶜ := by
      apply P.eventProbability_intersection_eq_prod _ _ W.support
      · intro ij hij
        exact (DenseGraph.FiniteBernoulliProduct.cylinderEvent_supportedOn _ _).compl
      · simpa only [Finset.coe_univ] using W.supports_pairwiseDisjoint
    _ ≤ ∏ _ij : Fin q × Fin ell, Real.exp (-(beta ^ 4)) :=
      Finset.prod_le_prod (fun _ _ ↦ P.eventProbability_nonneg _) (fun ij _ ↦ hcomp ij)
    _ = Real.exp (-(beta ^ 4) * (q : ℝ) * ell) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Fixed-cardinality avoidance with its explicit polynomial conditioning
loss. Quota feasibility is an input, never inferred from real division. -/
theorem c4Matching_fixedProbability_le
    (T : SimpleGraph V) (present : Bool) (hstatus : W.InternalStatus T present)
    (quota : ℕ) (hquota : quota ≤ (c4CrossPotentialEdges D).card)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card quota ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card quota ≤ 1 - beta) :
    (c4FixedCrossModel D quota hquota).outcomeEventProbability (c4DefectFreeOutcomeEvent D T) ≤
      ((c4CrossPotentialEdges D).card + 1) * Real.exp (-(beta ^ 4) * (q : ℝ) * ell) := by
  let M := c4FixedCrossModel D quota hquota
  have hprob := c4Matching_bernoulli_avoidance_le W T present hstatus M.associatedBernoulli
    hbeta (fun e ↦ hband)
  calc
    M.outcomeEventProbability (c4DefectFreeOutcomeEvent D T) ≤
        M.conditioningFactor * M.associatedBernoulli.eventProbability (c4DefectFreeOutcomeEvent D T) :=
      M.fixedCardinality_eventProbability_le_conditioningFactor_mul _
    _ ≤ M.conditioningFactor * Real.exp (-(beta ^ 4) * (q : ℝ) * ell) :=
      mul_le_mul_of_nonneg_left hprob M.conditioningFactor_pos.le
    _ = _ := by rw [c4FixedCrossModel_conditioningFactor]

/-- Cardinality form in the actual fixed sample space. Each sample chooses
exactly `quota` cross coordinates, so its total size is one binomial slice. -/
theorem c4Matching_fixedSampleCard_le
    (T : SimpleGraph V) (present : Bool) (hstatus : W.InternalStatus T present)
    (quota : ℕ) (hquota : quota ≤ (c4CrossPotentialEdges D).card)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card quota ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card quota ≤ 1 - beta) :
    (((c4FixedCrossModel D quota hquota).sampleEvent (c4DefectFreeOutcomeEvent D T)).card : ℝ) ≤
      (Nat.choose (c4CrossPotentialEdges D).card quota : ℝ) *
        ((c4CrossPotentialEdges D).card + 1) * Real.exp (-(beta ^ 4) * (q : ℝ) * ell) := by
  let M := c4FixedCrossModel D quota hquota
  have h := c4Matching_fixedProbability_le W T present hstatus quota hquota hbeta hband
  change M.eventProbability (M.sampleEvent (c4DefectFreeOutcomeEvent D T)) ≤ _ at h
  rw [M.eventProbability_eq_card_div] at h
  have hpos : (0 : ℝ) < M.sampleSpaceCard := Nat.cast_pos.mpr M.sampleSpaceCard_pos
  have hc := (div_le_iff₀ hpos).mp h
  simpa only [M, c4FixedCrossModel_sampleSpaceCard, mul_comm, mul_left_comm, mul_assoc] using hc

/-- Finite actual-graph form of the matching penalty, before substituting a
linear-size companion matching and absorbing the polynomial factor. -/
theorem c4Matching_fixedDefectFiber_le {n q ell : ℕ} {D : C4Division (Fin n)}
    (W : C4MatchingSides D q ell) (T : SimpleGraph (Fin n)) (present : Bool)
    (hstatus : W.InternalStatus T present) (m : ℕ)
    (hquota : c4FixedDefectQuota D T m ≤ (c4CrossPotentialEdges D).card)
    {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ∧
      DenseGraph.FixedCardinalityBlockModel.quotaParameter
        (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) ≤ 1 - beta) :
    ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
      (Nat.choose (c4CrossPotentialEdges D).card (c4FixedDefectQuota D T m) : ℝ) *
        ((c4CrossPotentialEdges D).card + 1) * Real.exp (-(beta ^ 4) * (q : ℝ) * ell) := by
  have hcard : ((c4FixedDefectFreeFiber D T m).card : ℝ) ≤
      (((c4FixedCrossModel D (c4FixedDefectQuota D T m) hquota).sampleEvent
        (c4DefectFreeOutcomeEvent D T)).card : ℝ) := by
    exact_mod_cast card_c4FixedDefectFreeFiber_le_sampleEvent D T m hquota
  exact hcard.trans (c4Matching_fixedSampleCard_le W T present hstatus
    (c4FixedDefectQuota D T m) hquota hbeta hband)

end InducedStars
