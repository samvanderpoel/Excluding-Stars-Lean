import InducedStars.C4.FrozenCrossModels
import InducedStars.C4.CompanionMatching

/-!
# Independent two-coordinate penalty for a high clique-side defect degree

Paper: the probability argument of Lemma `lemma:FPi2`. A fixed vertex in
the clique side has prescribed missing neighbors there and forced neighbors
in the independent side. Pair the latter by an actual matching of nonedges.
Each candidate then needs precisely two optional cross successes.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars
open Regularity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Actual vertices and statuses for the high-degree-B candidates. Optional
membership explicitly excludes every frozen pair from the random support. -/
structure C4HighBConfiguration {D : C4Division V} (W : C4FrozenCrossData D)
    (T : SimpleGraph V) (ell a : ℕ) where
  vertex : V
  vertex_mem : vertex ∈ D.cliquePart
  neighbor : Fin a ↪ V
  neighbor_mem : ∀ x, neighbor x ∈ D.cliquePart
  neighbor_defect : ∀ x, T.Adj vertex (neighbor x)
  matching : (Fin ell × Fin 2) ↪ V
  matching_mem : ∀ i b, matching (i,b) ∈ D.independentPart
  matching_nonedge : ∀ i, ¬T.Adj (matching (i,0)) (matching (i,1))
  forced : ∀ i b, s(matching (i,b), vertex) ∈ W.present
  optional : ∀ i b x, s(matching (i,b), neighbor x) ∈ W.optional

namespace C4HighBConfiguration

variable {D : C4Division V} {W : C4FrozenCrossData D} {T : SimpleGraph V} {ell a : ℕ}
    (K : C4HighBConfiguration W T ell a)

theorem matching_ne_clique (i : Fin ell) (b : Fin 2) {v : V} (hv : v ∈ D.cliquePart) :
    K.matching (i,b) ≠ v := by
  intro h
  exact Finset.disjoint_left.mp D.disjoint (h ▸ K.matching_mem i b) hv

def coordinate (ib : Fin ell × Fin 2) (x : Fin a) : W.Coordinate :=
  ⟨(), ⟨s(K.matching ib, K.neighbor x), K.optional ib.1 ib.2 x⟩⟩

theorem coordinate_injective :
    Function.Injective (fun p : (Fin ell × Fin 2) × Fin a => K.coordinate p.1 p.2) := by
  intro p r h
  have he := congrArg (fun e : W.Coordinate => e.2.val) h
  change s(K.matching p.1, K.neighbor p.2) = s(K.matching r.1, K.neighbor r.2) at he
  rcases Sym2.eq_iff.mp he with ⟨hl, hr⟩ | ⟨hcross, _⟩
  · exact Prod.ext (K.matching.injective hl) (K.neighbor.injective hr)
  · exact False.elim (K.matching_ne_clique p.1.1 p.1.2 (K.neighbor_mem r.2) hcross)

def support (ix : Fin ell × Fin a) : Finset W.Coordinate :=
  univ.image fun b : Fin 2 => K.coordinate (ix.1,b) ix.2

theorem coordinate_mem_support (ix : Fin ell × Fin a) (b : Fin 2) :
    K.coordinate (ix.1,b) ix.2 ∈ K.support ix := Finset.mem_image.mpr ⟨b, mem_univ _, rfl⟩

@[simp] theorem card_support (ix : Fin ell × Fin a) : (K.support ix).card = 2 := by
  rw [support, Finset.card_image_iff.mpr]
  · simp
  · intro b hb c hc he
    have hh : ((ix.1,b),ix.2) = ((ix.1,c),ix.2) := K.coordinate_injective he
    exact congrArg (fun x => x.1.2) hh

theorem supports_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin ell × Fin a)) K.support := by
  intro ix _ jy _ hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨c, hc, heq⟩ := Finset.mem_image.mp hf
  have hh : ((jy.1,c),jy.2) = ((ix.1,b),ix.2) := K.coordinate_injective heq
  exact hne (Prod.ext (congrArg (fun x => x.1.1) hh).symm (congrArg Prod.snd hh).symm)

/-- This is a principal two-success event, represented as its exact cylinder. -/
def event (ix : Fin ell × Fin a) : Finset (Finset W.Coordinate) :=
  DenseGraph.FiniteBernoulliProduct.cylinderEvent (K.support ix) (K.support ix)

theorem event_iff (ix : Fin ell × Fin a) (outcome : Finset W.Coordinate) :
    outcome ∈ K.event ix ↔ K.support ix ⊆ outcome := by
  rw [event, DenseGraph.FiniteBernoulliProduct.mem_cylinderEvent]
  exact Finset.inter_eq_right

def cycleMap (ix : Fin ell × Fin a) : Fin 4 → V :=
  ![K.vertex, K.matching (ix.1,0), K.neighbor ix.2, K.matching (ix.1,1)]

theorem cycleMap_injective (ix : Fin ell × Fin a) : Function.Injective (K.cycleMap ix) := by
  have h01 := K.matching_ne_clique ix.1 0 K.vertex_mem
  have h03 := K.matching_ne_clique ix.1 1 K.vertex_mem
  have h12 := K.matching_ne_clique ix.1 0 (K.neighbor_mem ix.2)
  have h23 := K.matching_ne_clique ix.1 1 (K.neighbor_mem ix.2)
  have h02 := (K.neighbor_defect ix.2).ne
  have h13 : K.matching (ix.1,0) ≠ K.matching (ix.1,1) :=
    K.matching.injective.ne (by simp)
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cycleMap, ne_comm]

theorem event_forces_inducedC4 (ix : Fin ell × Fin a) {outcome : Finset W.Coordinate}
    (he : outcome ∈ K.event ix) : InducedEmbeds inducedC4 (W.outcomeGraph T outcome) := by
  let G := W.outcomeGraph T outcome
  have hfixed (b : Fin 2) : G.Adj (K.matching (ix.1,b)) K.vertex :=
    (W.outcomeGraph_adj_cross T outcome (K.matching_mem ix.1 b) K.vertex_mem).mpr
      (Or.inl (K.forced ix.1 b))
  have hcross (b : Fin 2) : G.Adj (K.matching (ix.1,b)) (K.neighbor ix.2) := by
    apply (W.outcomeGraph_adj_cross T outcome (K.matching_mem ix.1 b)
      (K.neighbor_mem ix.2)).mpr
    right
    apply (W.coordinate_mem_choice (K.coordinate (ix.1,b) ix.2) outcome).mpr
    exact (K.event_iff ix outcome).mp he (K.coordinate_mem_support ix b)
  have hnonB : ¬G.Adj K.vertex (K.neighbor ix.2) := by
    intro hh
    exact ((W.outcomeGraph_adj_clique T outcome K.vertex_mem (K.neighbor_mem ix.2)).mp hh).2
      (K.neighbor_defect ix.2)
  have hnonA : ¬G.Adj (K.matching (ix.1,0)) (K.matching (ix.1,1)) := by
    intro hh
    exact K.matching_nonedge ix.1
      ((W.outcomeGraph_adj_independent T outcome (K.matching_mem ix.1 0)
        (K.matching_mem ix.1 1)).mp hh)
  exact c4_inducedEmbeds_of_sixPairs G ⟨K.cycleMap ix, K.cycleMap_injective ix⟩
    (hfixed 0).symm (hcross 0) (hcross 1).symm (hfixed 1) hnonB hnonA

theorem freeEvent_subset_avoidance : W.freeEvent T ⊆
    DenseGraph.FiniteBernoulliProduct.eventIntersection univ
      (fun ix : Fin ell × Fin a => (K.event ix)ᶜ) := by
  intro outcome houtcome
  rw [DenseGraph.FiniteBernoulliProduct.mem_eventIntersection]
  intro ix hix
  rw [Finset.mem_compl]
  intro hevent
  exact (W.mem_freeEvent T outcome).mp houtcome (K.event_forces_inducedC4 ix hevent)

theorem event_probability_ge (P : DenseGraph.FiniteBernoulliProduct W.Coordinate)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hband : ∀ e, beta ≤ P.probability e)
    (ix : Fin ell × Fin a) : beta^2 ≤ P.eventProbability (K.event ix) := by
  rw [event, P.eventProbability_cylinderEvent (Finset.Subset.refl _)]
  calc
    beta^2 = ∏ _e ∈ K.support ix, beta := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => hbeta) (fun e he => by simpa [he] using hband e)

include K in
/-- Candidate copies can share the fixed center or matching endpoints, but
their two random-coordinate supports are pairwise disjoint. -/
theorem bernoulli_avoidance_le (P : DenseGraph.FiniteBernoulliProduct W.Coordinate)
    {beta : ℝ} (hbeta : 0 ≤ beta) (hband : ∀ e, beta ≤ P.probability e) :
    P.eventProbability (W.freeEvent T) ≤ Real.exp (-(beta^2)*(ell : ℝ)*a) := by
  have hcomp (ix : Fin ell × Fin a) :
      P.eventProbability (K.event ix)ᶜ ≤ Real.exp (-(beta^2)) := by
    have hsum := P.eventProbability_union
      (Finset.disjoint_left.mpr (fun _ he hc => (Finset.mem_compl.mp hc) he) :
        Disjoint (K.event ix) (K.event ix)ᶜ)
    rw [Finset.union_compl, P.eventProbability_univ] at hsum
    have hmass := K.event_probability_ge P hbeta hband ix
    have hexp := Real.add_one_le_exp (-(beta^2))
    linarith
  calc
    P.eventProbability (W.freeEvent T) ≤
        P.eventProbability (DenseGraph.FiniteBernoulliProduct.eventIntersection univ
          (fun ix : Fin ell × Fin a => (K.event ix)ᶜ)) :=
      P.eventProbability_mono K.freeEvent_subset_avoidance
    _ = ∏ ix : Fin ell × Fin a, P.eventProbability (K.event ix)ᶜ := by
      apply P.eventProbability_intersection_eq_prod _ _ K.support
      · intro ix hix
        exact (DenseGraph.FiniteBernoulliProduct.cylinderEvent_supportedOn _ _).compl
      · simpa only [Finset.coe_univ] using K.supports_pairwiseDisjoint
    _ ≤ ∏ _ix : Fin ell × Fin a, Real.exp (-(beta^2)) :=
      Finset.prod_le_prod (fun _ _ => P.eventProbability_nonneg _) (fun ix _ => hcomp ix)
    _ = Real.exp (-(beta^2)*(ell : ℝ)*a) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring

/-- Finite actual-graph penalty with the reduced quota, reduced capacity,
and exact polynomial conditioning loss. -/
theorem frozenFiber_le {n : ℕ} {D : C4Division (Fin n)} {W : C4FrozenCrossData D}
    {T : SimpleGraph (Fin n)} {ell a : ℕ} (K : C4HighBConfiguration W T ell a)
    (m : ℕ) (hq : W.quota T m ≤ W.optional.card) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
      W.optional.card (W.quota T m)) :
    ((W.freeFiber T m).card : ℝ) ≤
      (W.optional.card.choose (W.quota T m) : ℝ)*((W.optional.card : ℝ)+1)*
        Real.exp (-(beta^2)*(ell : ℝ)*a) := by
  exact W.card_freeFiber_le_of_bernoulli T m hq
    (K.bernoulli_avoidance_le (W.model (W.quota T m) hq).associatedBernoulli hbeta
      (fun e => hband))

end C4HighBConfiguration

/-- Actual cross coordinates from a clique vertex to an independent-side set. -/
theorem c4HighB_star_cross {D : C4Division V} {v : V} (hv : v ∈ D.cliquePart)
    {Z : Finset V} (hZ : Z ⊆ D.independentPart) :
    ∀ z ∈ Z, s(v,z) ∈ c4CrossPotentialEdges D := by
  intro z hz
  exact (mk_mem_c4CrossPotentialEdges D v z).mpr (Or.inr ⟨hZ hz,hv⟩)

/-- The source matching can be constructed from the actual complementary
graph on the forced-neighbor set, rather than supplied as a counting premise. -/
def c4HighBConfigurationOfSets {D : C4Division V} (T : SimpleGraph V)
    (v : V) (hv : v ∈ D.cliquePart) (N Z : Finset V)
    (hN : N ⊆ D.cliquePart) (hNT : ∀ x ∈ N, T.Adj v x)
    (hZ : Z ⊆ D.independentPart) :
    C4HighBConfiguration (c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true) T
      (DenseGraph.matchingNumber (c4WithinGraph Tᶜ Z)) N.card := by
  classical
  let e : Fin N.card ≃ ↥N := (Fintype.equivFinOfCardEq (by simp)).symm
  let f : Fin N.card ↪ V := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hf (x : Fin N.card) : f x ∈ N := (e x).prop
  let hex := c4_exists_orientedMaximumWithinMatching Tᶜ Z
  let g := Classical.choose hex
  have hg := (Classical.choose_spec hex).1
  have hgT := (Classical.choose_spec hex).2
  refine ⟨v, hv, f, fun x => hN (hf x), fun x => hNT _ (hf x), g,
    fun i b => hZ (hg i b), fun i => (hgT i).2, ?_, ?_⟩
  · intro i b
    change s(g (i,b),v) ∈ c4CrossStar v Z
    exact (mk_mem_c4CrossStar v Z _ _).mpr (Or.inr ⟨rfl,hg i b⟩)
  · intro i b x
    change s(g (i,b),f x) ∈ c4CrossPotentialEdges D \ c4CrossStar v Z
    refine Finset.mem_sdiff.mpr ⟨(mk_mem_c4CrossPotentialEdges D _ _).mpr
      (Or.inl ⟨hZ (hg i b), hN (hf x)⟩), ?_⟩
    intro he
    rcases (mk_mem_c4CrossStar v Z _ _).mp he with ⟨hgv,_⟩ | ⟨hfv,_⟩
    · exact Finset.disjoint_left.mp D.disjoint (hgv ▸ hZ (hg i b)) hv
    · exact (hNT _ (hf x)).ne hfv.symm

/-- Finite high-degree-B estimate after constructing the complementary
matching. Here `nu` is the linear lower bound on both the missing-neighbor
and forced-neighbor sets; later it is a fixed multiple of `alpha`.
The exponent is quadratic in `n` and cubic in `nu`, exactly as in the paper. -/
theorem c4HighB_starFiber_le {n : ℕ} (D : C4Division (Fin n))
    (T : SimpleGraph (Fin n)) (v : Fin n) (hv : v ∈ D.cliquePart)
    (N Z : Finset (Fin n)) (hN : N ⊆ D.cliquePart) (hNT : ∀ x ∈ N, T.Adj v x)
    (hZ : Z ⊆ D.independentPart) (m : ℕ) {nu beta : ℝ}
    (hnu : 0 < nu) (hbeta : 0 ≤ beta) (hn : 4 ≤ nu*n)
    (hNsize : nu*n ≤ (N.card : ℝ)) (hZsize : nu*n ≤ (Z.card : ℝ))
    (hsmall : ((finiteGraphEdges T).card : ℝ) ≤ nu^2*(n : ℝ)^2/8)
    (hq : (c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true).quota T m ≤
      (c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true).optional.card)
    (hband : beta ≤ DenseGraph.FixedCardinalityBlockModel.quotaParameter
      (c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true).optional.card
      ((c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true).quota T m)) :
    let W := c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true
    ((W.freeFiber T m).card : ℝ) ≤
      (W.optional.card.choose (W.quota T m) : ℝ)*((W.optional.card : ℝ)+1)*
        Real.exp (-(beta^2*nu^3/16)*(n : ℝ)^2) := by
  let W := c4FrozenCrossStar D v Z (c4HighB_star_cross hv hZ) true
  let K := c4HighBConfigurationOfSets T v hv N Z hN hNT hZ
  have h := K.frozenFiber_le m hq hbeta hband
  have hmatching := c4Within_complement_matchingNumber_ge T Z hnu hn hZsize hsmall
  have hprod := mul_le_mul hmatching hNsize (by positivity : 0 ≤ nu*(n : ℝ))
    (by positivity : 0 ≤ (DenseGraph.matchingNumber (c4WithinGraph Tᶜ Z) : ℝ))
  have hscaled := mul_le_mul_of_nonneg_left hprod (sq_nonneg beta)
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  nlinarith only [hscaled]

end InducedStars
