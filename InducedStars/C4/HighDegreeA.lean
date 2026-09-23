import InducedStars.C4.HighDegreeAJanson
import InducedStars.C4.FrozenCrossModels
import InducedStars.C4.MatchingCoordinates

/-!
# Actual induced-C4 candidates for a high independent-side defect degree

Paper: Lemma `lemma:FPi1`, Case 2. The center-to-opposite-set nonedges
are frozen before defining the probability space. All remaining candidate
requirements are principal events with exactly two successful coordinates.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars
open Regularity

universe v u z
variable {V : Type v} {U : Type u} {Z : Type z} [Fintype V] [DecidableEq V]
  [Fintype U] [DecidableEq U] [Fintype Z] [DecidableEq Z]

structure C4HighAConfiguration {D : C4Division V} (W : C4FrozenCrossData D)
    (T : SimpleGraph V) (H : SimpleGraph U) (Z : Type*) where
  vertex : V
  vertex_mem : vertex ∈ D.independentPart
  neighbor : U ↪ V
  neighbor_mem : ∀ x, neighbor x ∈ D.independentPart
  neighbor_defect : ∀ x, T.Adj vertex (neighbor x)
  opposite : Z ↪ V
  opposite_mem : ∀ z, opposite z ∈ D.cliquePart
  nonedges : ∀ x y, H.Adj x y → ¬T.Adj (neighbor x) (neighbor y)
  frozen : ∀ z, s(vertex, opposite z) ∈ W.frozen
  absent : ∀ z, s(vertex, opposite z) ∉ W.present
  optional : ∀ x z, s(neighbor x, opposite z) ∈ W.optional

namespace C4HighAConfiguration

variable {D : C4Division V} {W : C4FrozenCrossData D}
  {T : SimpleGraph V} {H : SimpleGraph U} (K : C4HighAConfiguration W T H Z)

theorem independent_ne_opposite {x : V} (hx : x ∈ D.independentPart) (z : Z) :
    x ≠ K.opposite z := by
  intro h
  exact Finset.disjoint_left.mp D.disjoint (h ▸ hx) (K.opposite_mem z)

def coordinate (xz : U × Z) : W.Coordinate :=
  ⟨(), ⟨s(K.neighbor xz.1, K.opposite xz.2), K.optional xz.1 xz.2⟩⟩

theorem coordinate_injective : Function.Injective K.coordinate := by
  intro p q h
  have he := congrArg (fun c : W.Coordinate ↦ c.2.val) h
  change s(K.neighbor p.1, K.opposite p.2) = s(K.neighbor q.1, K.opposite q.2) at he
  rcases Sym2.eq_iff.mp he with ⟨hl, hr⟩ | ⟨hcross, _⟩
  · exact Prod.ext (K.neighbor.injective hl) (K.opposite.injective hr)
  · exact False.elim (K.independent_ne_opposite (K.neighbor_mem p.1) q.2 hcross)

def coordinateEmbedding : (U × Z) ↪ W.Coordinate := ⟨K.coordinate, K.coordinate_injective⟩

def cycleMap (i : C4StarCandidate H Z) : Fin 4 → V :=
  ![K.vertex, K.neighbor i.1.val.out.1, K.opposite i.2, K.neighbor i.1.val.out.2]

theorem edge_adj (i : C4StarCandidate H Z) : H.Adj i.1.val.out.1 i.1.val.out.2 := by
  have he := (mem_finiteGraphEdges _ _).mp i.1.prop
  rw [← i.1.val.out_eq] at he
  exact he

theorem cycleMap_injective (i : C4StarCandidate H Z) : Function.Injective (K.cycleMap i) := by
  have h01 := (K.neighbor_defect i.1.val.out.1).ne
  have h03 := (K.neighbor_defect i.1.val.out.2).ne
  have h02 := K.independent_ne_opposite K.vertex_mem i.2
  have h12 := K.independent_ne_opposite (K.neighbor_mem i.1.val.out.1) i.2
  have h23 := K.independent_ne_opposite (K.neighbor_mem i.1.val.out.2) i.2
  have h13 := K.neighbor.injective.ne (edge_adj (H := H) i).ne
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cycleMap, ne_comm]

theorem principalEvent_forces_inducedC4 (i : C4StarCandidate H Z)
    {outcome : Finset W.Coordinate}
    (he : C4StarCandidate.required H K.coordinateEmbedding i ⊆ outcome) :
    InducedEmbeds inducedC4 (W.outcomeGraph T outcome) := by
  let G := W.outcomeGraph T outcome
  have hfixed (x : U) : G.Adj K.vertex (K.neighbor x) :=
    (W.outcomeGraph_adj_independent T outcome K.vertex_mem (K.neighbor_mem x)).mpr
      (K.neighbor_defect x)
  have hcross (x : U) (hx : x ∈ i.1.val) : G.Adj (K.neighbor x) (K.opposite i.2) := by
    apply (W.outcomeGraph_adj_cross T outcome (K.neighbor_mem x) (K.opposite_mem i.2)).mpr
    right
    apply (W.coordinate_mem_choice (K.coordinate (x, i.2)) outcome).mpr
    apply he
    exact (C4StarCandidate.mem_required H K.coordinateEmbedding i _).mpr ⟨x, hx, rfl⟩
  have heq : s(i.1.val.out.1, i.1.val.out.2) = i.1.val := i.1.val.out_eq
  have hx : i.1.val.out.1 ∈ i.1.val := by
    have h := Sym2.mem_mk_left i.1.val.out.1 i.1.val.out.2
    rwa [heq] at h
  have hy : i.1.val.out.2 ∈ i.1.val := by
    have h := Sym2.mem_mk_right i.1.val.out.1 i.1.val.out.2
    rwa [heq] at h
  have hnonA : ¬G.Adj (K.neighbor i.1.val.out.1) (K.neighbor i.1.val.out.2) := by
    intro hadj
    exact K.nonedges _ _ (edge_adj (H := H) i)
      ((W.outcomeGraph_adj_independent T outcome (K.neighbor_mem _) (K.neighbor_mem _)).mp hadj)
  have hnonCross : ¬G.Adj K.vertex (K.opposite i.2) := by
    intro hadj
    rcases (W.outcomeGraph_adj_cross T outcome K.vertex_mem (K.opposite_mem i.2)).mp hadj with hp | hp
    · exact K.absent i.2 hp
    · exact (Finset.mem_sdiff.mp (W.choiceOfOutcome_subset outcome hp)).2 (K.frozen i.2)
  exact c4_inducedEmbeds_of_sixPairs G ⟨K.cycleMap i, K.cycleMap_injective i⟩
    (hfixed _) (hcross _ hx) (hcross _ hy).symm (hfixed _).symm hnonCross hnonA

theorem freeEvent_subset_principalAvoidance [LinearOrder (C4StarCandidate H Z)] : W.freeEvent T ⊆
    DenseGraph.FiniteBernoulliProduct.principalAvoidanceEvent
      (C4StarCandidate.required H K.coordinateEmbedding) := by
  intro outcome houtcome
  apply (DenseGraph.FiniteBernoulliProduct.mem_principalAvoidanceEvent _ outcome).mpr
  intro i he
  exact (W.mem_freeEvent T outcome).mp houtcome (K.principalEvent_forces_inducedC4 i he)

include K in
theorem bernoulli_avoidance_le [LinearOrder (C4StarCandidate H Z)]
    (J : DenseGraph.PrincipalJansonInput.{v, max u z})
    (P : DenseGraph.FiniteBernoulliProduct W.Coordinate) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hband : ∀ c, beta ≤ P.probability c)
    (hU : 1 ≤ Fintype.card U) (hZ : 0 < Fintype.card Z)
    (hdense : (Fintype.card U : ℝ) ^ 2 / 8 ≤ (finiteGraphEdges H).card) :
    P.eventProbability (W.freeEvent T) ≤
      Real.exp (-(beta ^ 4 / 64) * Fintype.card U * Fintype.card Z) :=
  (P.eventProbability_mono K.freeEvent_subset_principalAvoidance).trans
    (C4StarCandidate.avoidance_le H K.coordinateEmbedding J P hbeta hbeta1 hband hU hZ hdense)

theorem fixedFiber_le {n : ℕ} {D : C4Division (Fin n)} {W : C4FrozenCrossData D}
    {T : SimpleGraph (Fin n)} (K : C4HighAConfiguration W T H Z)
    [LinearOrder (C4StarCandidate H Z)] (J : DenseGraph.PrincipalJansonInput.{0, max u z})
    (m : ℕ) (hq : W.quota T m ≤ W.optional.card) {beta : ℝ}
    (hbeta : 0 < beta) (hbeta1 : beta ≤ 1)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter W.optional.card (W.quota T m))
    (hU : 1 ≤ Fintype.card U) (hZ : 0 < Fintype.card Z)
    (hdense : (Fintype.card U : ℝ) ^ 2 / 8 ≤ (finiteGraphEdges H).card) :
    ((W.freeFiber T m).card : ℝ) ≤
      (W.optional.card.choose (W.quota T m) : ℝ) * (W.optional.card + 1) *
        Real.exp (-(beta ^ 4 / 64) * Fintype.card U * Fintype.card Z) := by
  apply W.card_freeFiber_le_of_bernoulli T m hq
  exact K.bernoulli_avoidance_le J _ hbeta hbeta1 (fun _ ↦ hband) hU hZ hdense

end C4HighAConfiguration
end InducedStars
