import InducedStars.Structure.Subcritical.ResidualCandidateEvents
import InducedStars.Structure.Subcritical.ResidualJansonBounds

/-!
# Residual witness probabilities in the actual retained active model

All candidate events use one globally fixed coordinate polarity. Their
deterministic realization is proved in `ResidualCandidateEvents`; only the
published principal-event Janson capability is passed to the finite bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped Classical
open DenseGraph.FiniteBernoulliProduct
namespace InducedStars
universe u
variable {k : ℕ} {V : Type u} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {F : Finset (SimpleGraph V)} {p : SubcriticalProfile D eta R₀ theta}
  {TB R L : SimpleGraph V}

/-- The narrow window gives the same symmetric compact band for every
individual Bernoulli coordinate. -/
theorem subcriticalResidualActiveProbability_band
    {m : ℕ} {C delta epsilon : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (hd : delta ≤ subcriticalPaletteGap k / 2)
    (e : SubcriticalActiveCoordinate D eta R₀) :
    (subcriticalActiveBernoulliModel mvec).probability e ∈
      Icc (subcriticalPaletteGap k / 2) (1 - subcriticalPaletteGap k / 2) := by
  have hb := (mem_retainedNarrowEdgeCountLevel.mp
    (mem_retainedNarrowEdgeCountWindow.mp hm).1).2 e.1
  have hp := min_le_left (pK k) (1 - pK k)
  have hq := min_le_right (pK k) (1 - pK k)
  change subcriticalPaletteGap k ≤ pK k at hp
  change subcriticalPaletteGap k ≤ 1 - pK k at hq
  rw [subcriticalActiveBernoulliModel_probability]
  change subcriticalPaletteGap k / 2 ≤ retainedEdgeCountDensity mvec e.1 ∧
    retainedEdgeCountDensity mvec e.1 ≤ 1 - subcriticalPaletteGap k / 2
  constructor <;> linarith

/-- A positive floor depending only on the forbidden star size. -/
def subcriticalResidualCandidateAtomFloor (k : ℕ) : ℝ :=
  (subcriticalPaletteGap k / 2) ^ ((k + 1).choose 2)

theorem subcriticalResidualCandidateAtomFloor_pos (hk : 3 ≤ k) :
    0 < subcriticalResidualCandidateAtomFloor k := by
  unfold subcriticalResidualCandidateAtomFloor
  exact pow_pos (div_pos (subcriticalPaletteGap_pos hk) (by norm_num)) _

theorem subcriticalResidualCandidate_atom_lower
    {I : Type*} [Fintype I] [DecidableEq I] {center : I}
    (K : SubcriticalResidualStarWitness p R I center)
    (hcard : Fintype.card I = k + 1) (hk : 3 ≤ k)
    {m : ℕ} {C delta epsilon : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (hd : delta ≤ subcriticalPaletteGap k / 2)
    (flip : Finset (SubcriticalActiveCoordinate D eta R₀)) :
    subcriticalResidualCandidateAtomFloor k ≤
      ((subcriticalActiveBernoulliModel mvec).complementCoordinates flip).eventProbability
        (principalSuccessEvent (K.present ∪ K.absent)) := by
  have hp := subcriticalPaletteGap_pos hk
  have hu : subcriticalPaletteGap k / 2 ≤ 1 := by
    have hm := min_le_left (pK k) (1 - pK k)
    change subcriticalPaletteGap k ≤ pK k at hm
    have hk1 := (pK_mem_Icc k).2
    linarith
  exact subcriticalResidualPolarizedPrincipalProbability_lower
    (subcriticalActiveBernoulliModel mvec) flip (K.present ∪ K.absent)
    (by positivity) hu (subcriticalResidualActiveProbability_band mvec hm hd)
    (by simpa only [hcard] using K.required_card_le mvec)

/-- Roots-away residual safety forbids every one of the actual signed
candidate events, before any change of coordinates. -/
theorem subcriticalResidualSafeEvent_subset_mixedAvoidance
    {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    {center : I} (K : A → SubcriticalResidualStarWitness p R I center)
    (hcard : Fintype.card I = k + 1)
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalActiveGraphEvent H (TB ⊔ R ⊔ L) mvec
        (subcriticalResidualSafeAwayFromRootsEvent p R) ⊆
      mixedAvoidanceEvent (fun a ↦ (K a).present) (fun a ↦ (K a).absent) := by
  intro S hS
  apply (mem_mixedAvoidanceEvent _ _ S).mpr
  intro a ha
  exact (K a).mixedSuccess_not_safe hcard h H mvec S ha
    (Finset.mem_filter.mp hS).2

set_option maxHeartbeats 600000 in
-- The composed model and witness supports have several dependent finite indices.
/-- Capability-parametric probability bound for a finite family of actual
residual witnesses. Abundance and overlap are explicit geometric inputs at
this intermediate interface, discharged by the matching construction. -/
theorem subcriticalResidualWitnessFamily_probability_le
    {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A]
    {center : I} (K : A → SubcriticalResidualStarWitness p R I center)
    (hcard : Fintype.card I = k + 1) (hk : 3 ≤ k)
    (J : DenseGraph.PrincipalJansonInput.{u, 0})
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    {m : ℕ} {C delta epsilon : ℝ}
    (mvec : RetainedEdgeCountVector D eta R₀)
    (hm : mvec ∈ retainedNarrowEdgeCountWindow D eta R₀ m C delta epsilon)
    (hd : delta ≤ subcriticalPaletteGap k / 2)
    (flip : Finset (SubcriticalActiveCoordinate D eta R₀))
    (hpresent : ∀ a, Disjoint (K a).present flip)
    (habsent : ∀ a, (K a).absent ⊆ flip)
    {n t : ℕ} {cCand cDelta : ℝ} (hcCand : 0 < cCand) (hcDelta : 0 < cDelta)
    (habundance : cCand * (t : ℝ) * (n : ℝ)^(k-1) ≤ Fintype.card A)
    (hoverlap : ((unorderedOverlappingPairs
      (fun a ↦ (K a).present ∪ (K a).absent)).card : ℝ) ≤
        cDelta * (t : ℝ) * (n : ℝ)^(2*k-3)) :
    subcriticalResidualSafeProbability p H TB R L mvec ≤
      Real.exp (-(subcriticalResidualJansonLinearConstant
        (cCand * subcriticalResidualCandidateAtomFloor k) cDelta * t * n)) := by
  let P := subcriticalActiveBernoulliModel mvec
  let required := fun a ↦ (K a).present ∪ (K a).absent
  have hfloor := subcriticalResidualCandidateAtomFloor_pos hk
  have hmu := subcriticalResidualCandidateMu_lower (P.complementCoordinates flip)
    required (k := k) (n := n) (t := t) hfloor.le
    (fun a ↦ subcriticalResidualCandidate_atom_lower (K a) hcard hk mvec hm hd flip)
    habundance
  have hdelta := subcriticalResidualCandidateDelta_upper
    (P.complementCoordinates flip) required (k := k) (n := n) (t := t) hoverlap
  calc
    _ ≤ P.eventProbability (mixedAvoidanceEvent
        (fun a ↦ (K a).present) (fun a ↦ (K a).absent)) :=
      P.eventProbability_mono
        (subcriticalResidualSafeEvent_subset_mixedAvoidance K hcard h H mvec)
    _ = (P.complementCoordinates flip).eventProbability
        (principalAvoidanceEvent required) :=
      P.eventProbability_mixedAvoidanceEvent _ _ flip hpresent habsent
    _ ≤ _ := subcriticalResidualCandidateAvoidanceProbability_le J
      (P.complementCoordinates flip) required
      (k := k) (n := n) (t := t) hk
      (mul_pos hcCand hfloor) hcDelta hmu hdelta

end InducedStars
