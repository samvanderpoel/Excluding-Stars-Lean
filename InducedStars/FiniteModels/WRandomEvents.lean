import InducedStars.FiniteModels.ConditionalSupport
import InducedStars.FiniteModels.Shannon
import Mathlib.Tactic

/-!
# Event algebra for graphon sampling

This file adds the complement and intersection operations needed to combine
the graph-only, latent-only, and genuinely joint estimates in the exact-edge
transfer.  All identities are proved directly from the finite conditional
law.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace InducedStars

namespace WRandomJointEvent

/-- Complement of a measurable joint sampling event. -/
def compl {n : ℕ} (P : WRandomJointEvent n) : WRandomJointEvent n where
  Holds := fun x G ↦ ¬P.Holds x G
  measurableSet_holds G := (P.measurableSet_holds G).compl

/-- Intersection of two measurable joint sampling events. -/
def inter {n : ℕ} (P Q : WRandomJointEvent n) : WRandomJointEvent n where
  Holds := fun x G ↦ P.Holds x G ∧ Q.Holds x G
  measurableSet_holds G :=
    (P.measurableSet_holds G).inter (Q.measurableSet_holds G)

/-- The event that the conditionally sampled graph has positive weight. -/
def positiveConditionalWeight {n : ℕ} (W : Graphon) : WRandomJointEvent n where
  Holds := fun x G ↦ 0 < wRandomConditionalWeight W x G
  measurableSet_holds G :=
    measurableSet_lt measurable_const (measurable_wRandomConditionalWeight W G)

/-- The latent configuration has induced-`H`-free positive conditional
support.  The sampled graph argument is intentionally ignored. -/
def conditionalSupportInducedFree {h n : ℕ}
    (H : SimpleGraph (Fin h)) (W : Graphon) : WRandomJointEvent n where
  Holds := fun x _G ↦ ∀ K : SimpleGraph (Fin n),
    0 < wRandomConditionalWeight W x K →
      ¬Regularity.InducedEmbeds H K
  measurableSet_holds _G := by
    rw [show {x : Fin n → UnitInterval | ∀ K : SimpleGraph (Fin n),
        0 < wRandomConditionalWeight W x K →
          ¬Regularity.InducedEmbeds H K} =
        ⋂ K : SimpleGraph (Fin n),
          {x | 0 < wRandomConditionalWeight W x K →
            ¬Regularity.InducedEmbeds H K} by
      ext x
      simp]
    apply MeasurableSet.iInter
    intro K
    by_cases hK : ¬Regularity.InducedEmbeds H K
    · convert MeasurableSet.univ using 1
      ext x
      simp [hK]
    · have hK' : Regularity.InducedEmbeds H K := Classical.not_not.mp hK
      convert measurableSet_le (measurable_wRandomConditionalWeight W K)
        (measurable_const : Measurable
          (fun _ : Fin n → UnitInterval ↦ (0 : ℝ))) using 1
      ext x
      simp [hK', not_lt]

end WRandomJointEvent

theorem wRandomGraphEventProbability_compl {n : ℕ} (W : Graphon)
    (A : Set (SimpleGraph (Fin n))) :
    wRandomGraphEventProbability W Aᶜ =
      1 - wRandomGraphEventProbability W A := by
  classical
  rw [← sum_wRandomGraphMass (n := n) W]
  unfold wRandomGraphEventProbability
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro G _hG
  by_cases hA : G ∈ A
  · simp [hA]
  · simp [hA]

theorem wRandomJointEventIntegrand_compl {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) (x : Fin n → UnitInterval) :
    wRandomJointEventIntegrand W P.compl x =
      1 - wRandomJointEventIntegrand W P x := by
  classical
  rw [← sum_wRandomConditionalWeight W x]
  unfold wRandomJointEventIntegrand WRandomJointEvent.compl
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro G _hG
  by_cases hP : P.Holds x G
  · simp [hP]
  · simp [hP]

theorem wRandomJointEventProbability_compl {n : ℕ} (W : Graphon)
    (P : WRandomJointEvent n) :
    wRandomJointEventProbability W P.compl =
      1 - wRandomJointEventProbability W P := by
  unfold wRandomJointEventProbability
  rw [integral_congr_ae (ae_of_all _
    (wRandomJointEventIntegrand_compl W P))]
  rw [integral_sub (integrable_const 1)
    (integrable_wRandomJointEventIntegrand W P)]
  simp

theorem wRandomJointEventProbability_inter_compl_le {n : ℕ}
    (W : Graphon) (P Q : WRandomJointEvent n) :
    1 - wRandomJointEventProbability W (P.inter Q) ≤
      (1 - wRandomJointEventProbability W P) +
        (1 - wRandomJointEventProbability W Q) := by
  rw [← wRandomJointEventProbability_compl W (P.inter Q),
    ← wRandomJointEventProbability_compl W P,
    ← wRandomJointEventProbability_compl W Q]
  calc
    wRandomJointEventProbability W (P.inter Q).compl ≤
        wRandomJointEventProbability W (P.compl.union Q.compl) := by
      apply wRandomJointEventProbability_mono W
      intro x G h
      by_cases hP : P.Holds x G
      · exact Or.inr (fun hQ ↦ h ⟨hP, hQ⟩)
      · exact Or.inl hP
    _ ≤ wRandomJointEventProbability W P.compl +
          wRandomJointEventProbability W Q.compl :=
      wRandomJointEventProbability_union_le W P.compl Q.compl

/-- A finite graph-event mass is the corresponding marginal event
probability. -/
theorem finiteEventMass_wRandomGraphMass_eq_eventProbability {n : ℕ}
    (W : Graphon) (A : Finset (SimpleGraph (Fin n))) :
    finiteEventMass A (wRandomGraphMass W) =
      wRandomGraphEventProbability W {G | G ∈ A} := by
  classical
  unfold finiteEventMass wRandomGraphEventProbability
  simp only [Set.mem_setOf_eq]
  rw [← Finset.sum_filter]
  simp

/-- A sequence of finite events whose probability tends to one is eventually
nonempty. -/
theorem eventually_nonempty_of_finiteEventMass_tendsto_one
    (W : Graphon)
    (A : (n : ℕ) → Finset (SimpleGraph (Fin n)))
    (hA : Tendsto
      (fun n ↦ finiteEventMass (A n) (wRandomGraphMass W))
      atTop (nhds 1)) :
    ∀ᶠ n in atTop, (A n).Nonempty := by
  have hpos : ∀ᶠ n in atTop,
      0 < finiteEventMass (A n) (wRandomGraphMass W) :=
    (tendsto_order.1 hA).1 0 (by norm_num)
  filter_upwards [hpos] with n hn
  by_contra hne
  have hempty : A n = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
  simp [hempty, finiteEventMass] at hn

/-- A conditionally sampled graph has positive conditional mass with joint
probability one.  Zero-weight outcomes contribute zero to the finite sum. -/
@[simp] theorem wRandomJointEventProbability_positiveConditionalWeight
    {n : ℕ} (W : Graphon) :
    wRandomJointEventProbability (n := n) W
      (WRandomJointEvent.positiveConditionalWeight (n := n) W) = 1 := by
  have hpoint : ∀ x : Fin n → UnitInterval,
      wRandomJointEventIntegrand W
        (WRandomJointEvent.positiveConditionalWeight (n := n) W) x = 1 := by
    intro x
    classical
    unfold wRandomJointEventIntegrand
      WRandomJointEvent.positiveConditionalWeight
    rw [← sum_wRandomConditionalWeight W x]
    apply Finset.sum_congr rfl
    intro G _hG
    by_cases hpos : 0 < wRandomConditionalWeight W x G
    · simp [hpos]
    · have hzero : wRandomConditionalWeight W x G = 0 :=
        le_antisymm (not_lt.mp hpos)
          (wRandomConditionalWeight_nonneg W x G)
      simp [hpos, hzero]
  unfold wRandomJointEventProbability
  rw [integral_congr_ae (ae_of_all _ hpoint)]
  simp

/-- Zero induced density makes the induced-free conditional-support event
hold with joint probability one. -/
@[simp] theorem wRandomJointEventProbability_conditionalSupportInducedFree
    {h n : ℕ} (H : SimpleGraph (Fin h)) (W : Graphon)
    (hfree : graphonInducedDensity H W = 0) :
    wRandomJointEventProbability W
      (WRandomJointEvent.conditionalSupportInducedFree
        (n := n) H W) = 1 := by
  have hpoint : ∀ᵐ x : Fin n → UnitInterval ∂volume,
      wRandomJointEventIntegrand W
        (WRandomJointEvent.conditionalSupportInducedFree H W) x = 1 := by
    filter_upwards [ae_conditionalSupport_inducedFree H W hfree] with x hx
    classical
    unfold wRandomJointEventIntegrand
      WRandomJointEvent.conditionalSupportInducedFree
    simp_rw [if_pos hx]
    exact sum_wRandomConditionalWeight W x
  unfold wRandomJointEventProbability
  rw [integral_congr_ae hpoint]
  simp

end InducedStars
