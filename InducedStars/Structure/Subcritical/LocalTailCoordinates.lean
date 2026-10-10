import InducedStars.Structure.Subcritical.ProfileEventSupport
import InducedStars.Structure.Subcritical.LocalRowData
import DenseGraph.FiniteModels.BernoulliTail

/-!
# Exact local-tail coordinate counts

Each trimmed target is identified with its actual tagged active coordinates.
Distinct targets at a root are disjoint. Consequently the simultaneous tail
probability is the product of the individual labeled-tail probabilities.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped BigOperators Classical
open DenseGraph.FiniteBernoulliProduct

namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

private theorem sym2_root_injective (v : V) : Function.Injective (fun y : V ↦ s(v, y)) := by
  intro x y h
  have he := (Sym2.mk_eq_mk_iff (p := (v, x)) (q := (v, y))).mp h
  simp only [Prod.mk.injEq, Prod.swap_prod_mk] at he
  rcases he with ⟨_, hxy⟩ | ⟨hvy, hxv⟩
  · exact hxy
  · exact hxv.trans hvy

/-- The sampled degree is exactly the number of selected tail coordinates.
This equality itself does not require a tail label. -/
theorem subcriticalTailDegree_eq_coordinate_count
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : Finset (SubcriticalActiveCoordinate D eta R₀)) :
    subcriticalTailDegree p v a S = (S ∩ subcriticalTailCoordinates p v a).card := by
  have heq :
      (((D.part a \ p.roots).filter fun y ↦ s(v, y) ∈ S.image (fun e ↦ e.2.1)).image
        (fun y ↦ s(v, y))) =
      (S ∩ subcriticalTailCoordinates p v a).image (fun e ↦ e.2.1) := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hyt, he⟩ := Finset.mem_filter.mp hy
      obtain ⟨e, heS, heq⟩ := Finset.mem_image.mp he
      exact Finset.mem_image.mpr ⟨e, Finset.mem_inter.mpr
        ⟨heS, Finset.mem_filter.mpr ⟨Finset.mem_univ e, y, hyt, heq⟩⟩, heq⟩
    · intro hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨heS, heA⟩ := Finset.mem_inter.mp he
      obtain ⟨y, hy, heq⟩ := (Finset.mem_filter.mp heA).2
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr
        ⟨hy, Finset.mem_image.mpr ⟨e, heS, heq⟩⟩, heq.symm⟩
  have hc := congrArg Finset.card heq
  have hinj : Function.Injective (fun e : SubcriticalActiveCoordinate D eta R₀ ↦ e.2.1) :=
    subcriticalActiveCoordinate_val_injective mvec
  rw [Finset.card_image_of_injective _ (sym2_root_injective v),
    Finset.card_image_of_injective _ hinj] at hc
  exact hc

/-- Every vertex in a valid trimmed target gives exactly one active
coordinate, so the support cardinality has no hidden loss. -/
theorem subcriticalTailCoordinates_card
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex)
    (mvec : RetainedEdgeCountVector D eta R₀)
    {t : SubcriticalTailDirection} (ht : p.tails v a = some t) :
    (subcriticalTailCoordinates p v a).card = (D.part a \ p.roots).card := by
  obtain ⟨hv, hactive⟩ := p.tails_valid v a t ht
  have heq : (subcriticalTailCoordinates p v a).image (fun e ↦ e.2.1) =
      (D.part a \ p.roots).image (fun y ↦ s(v, y)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨y, hy, heq⟩ := (Finset.mem_filter.mp he).2
      exact Finset.mem_image.mpr ⟨y, hy, heq.symm⟩
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      have hA : s(v, y) ∈ retainedActiveEdgeUniverse D eta R₀ :=
        (mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ v y).mpr
          ⟨(D.activePair_iff_of_mem_parts
            (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
            (Finset.mem_sdiff.mp hy).1).mpr hactive, p.retainedRoots_subset hv⟩
      obtain ⟨e, he⟩ := (mem_retainedActiveEdgeUniverse D eta R₀ s(v, y)).mp hA
      exact Finset.mem_image.mpr ⟨⟨e, ⟨s(v, y), he⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, y, hy, rfl⟩, rfl⟩
  have hc := congrArg Finset.card heq
  have hinj : Function.Injective (fun e : SubcriticalActiveCoordinate D eta R₀ ↦ e.2.1) :=
    subcriticalActiveCoordinate_val_injective mvec
  rw [Finset.card_image_of_injective _ hinj,
    Finset.card_image_of_injective _ (sym2_root_injective v)] at hc
  exact hc

theorem subcriticalTailCoordinates_disjoint
    (p : SubcriticalProfile D eta R₀ theta) (v : V)
    {a b : D.PartIndex} (hne : a ≠ b) :
    Disjoint (subcriticalTailCoordinates p v a) (subcriticalTailCoordinates p v b) := by
  rw [Finset.disjoint_left]
  intro e he hf
  obtain ⟨x, hx, hex⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨y, hy, hey⟩ := (Finset.mem_filter.mp hf).2
  have hxy := sym2_root_injective v (hex.symm.trans hey)
  exact Finset.disjoint_left.mp (D.part_disjoint hne)
    (Finset.mem_sdiff.mp hx).1 (hxy ▸ (Finset.mem_sdiff.mp hy).1)

theorem subcriticalTailEvent_upper_eq_count
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V) (a : D.PartIndex)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalTailEvent p alpha v a .upper = successCountAtLeast
      (subcriticalTailCoordinates p v a) ((1 - 2 * alpha) * (D.part a).card) := by
  ext S
  simp only [subcriticalTailEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_successCountAtLeast, subcriticalTailDegree_eq_coordinate_count p v a mvec S]

theorem subcriticalTailEvent_lower_eq_count
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V) (a : D.PartIndex)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalTailEvent p alpha v a .lower = successCountAtMost
      (subcriticalTailCoordinates p v a) (2 * alpha * (D.part a).card) := by
  ext S
  simp only [subcriticalTailEvent, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_successCountAtMost, subcriticalTailDegree_eq_coordinate_count p v a mvec S]

/-- A missing tail label imposes no random restriction. -/
def subcriticalLabeledTailEvent (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (v : V) (a : D.PartIndex) : Finset (Finset (SubcriticalActiveCoordinate D eta R₀)) :=
  match p.tails v a with
  | none => Finset.univ
  | some t => subcriticalTailEvent p alpha v a t

theorem subcriticalLabeledTailEvent_supportedOn
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V) (a : D.PartIndex) :
    EventSupportedOn (subcriticalLabeledTailEvent p alpha v a)
      (subcriticalTailCoordinates p v a) := by
  unfold subcriticalLabeledTailEvent
  split
  · exact EventSupportedOn.universal _
  · exact subcriticalTailEvent_supportedOn p alpha v a _

theorem subcriticalRootTailEvent_eq_targetIntersection
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V) :
    subcriticalRootTailEvent p alpha v =
      eventIntersection Finset.univ (subcriticalLabeledTailEvent p alpha v) := by
  ext S
  simp only [subcriticalRootTailEvent, eventIntersection, Finset.mem_filter,
    Finset.mem_univ, true_and, forall_const]
  apply forall_congr'
  intro a
  cases ht : p.tails v a with
  | none => simp [subcriticalLabeledTailEvent, ht]
  | some t => simp [subcriticalLabeledTailEvent, ht]

theorem subcriticalUpperNeighborIndices_mem_iff_tail
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) :
    a ∈ subcriticalUpperNeighborIndices p v hv ↔ p.tails v a = some .upper := by
  rw [mem_subcriticalUpperNeighborIndices]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨(p.tails_valid v a .upper h).2, h⟩⟩

theorem subcriticalLowerNeighborIndices_mem_iff_tail
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) :
    a ∈ subcriticalLowerNeighborIndices p v hv ↔ p.tails v a = some .lower := by
  rw [mem_subcriticalLowerNeighborIndices]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨(p.tails_valid v a .lower h).2, h⟩⟩

/-- Full tail-event independence into distinct trimmed targets at one root.
The identity concerns the literal profile events, not just principal events. -/
theorem subcriticalRootTailProbability_eq_target_product
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V)
    (hv : v ∈ p.retainedRoots) (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalRootTailProbability p alpha v mvec =
      (∏ a ∈ subcriticalUpperNeighborIndices p v hv,
        (subcriticalActiveBernoulliModel mvec).eventProbability (subcriticalTailEvent p alpha v a .upper)) *
      (∏ a ∈ subcriticalLowerNeighborIndices p v hv,
        (subcriticalActiveBernoulliModel mvec).eventProbability (subcriticalTailEvent p alpha v a .lower)) := by
  let P := subcriticalActiveBernoulliModel mvec
  change P.eventProbability _ = _
  rw [subcriticalRootTailEvent_eq_targetIntersection,
    P.eventProbability_intersection_eq_prod Finset.univ
      (subcriticalLabeledTailEvent p alpha v) (subcriticalTailCoordinates p v)
      (fun a _ ↦ subcriticalLabeledTailEvent_supportedOn p alpha v a)
      (fun a _ b _ hne ↦ subcriticalTailCoordinates_disjoint p v hne)]
  calc
    _ = ∏ a : D.PartIndex,
        (if a ∈ subcriticalUpperNeighborIndices p v hv then
          P.eventProbability (subcriticalTailEvent p alpha v a .upper) else 1) *
        (if a ∈ subcriticalLowerNeighborIndices p v hv then
          P.eventProbability (subcriticalTailEvent p alpha v a .lower) else 1) := by
      apply Finset.prod_congr rfl
      intro a _
      simp only [subcriticalUpperNeighborIndices_mem_iff_tail,
        subcriticalLowerNeighborIndices_mem_iff_tail]
      cases ht : p.tails v a with
      | none => simp [subcriticalLabeledTailEvent, ht, P.eventProbability_univ]
      | some t => cases t <;> simp [subcriticalLabeledTailEvent, ht]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_ite_mem_eq]
      rfl

end InducedStars
