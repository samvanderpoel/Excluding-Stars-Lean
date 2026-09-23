import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# Finite maximality, matchings, and neighborhood covers

Mathlib represents a matching in `G` as a subgraph `M : G.Subgraph`
satisfying `M.IsMatching`.  This file supplies the finite extremal layer that
is intentionally absent from Mathlib's basic matching API: maximum matchings,
a fixed noncomputable selector, the matching number, and the standard vertex
cover and endpoint-cardinality consequences.

The selector is canonical only in the usual formal sense that it is a fixed
function of `G`; no equivariance under relabeling is asserted.

The final section gives the parallel finite maximal-independent-set
argument: subsets of bounded independence number have small closed-
neighborhood covers. Its counting theorem explicitly fixes the ambient
graph; it does not count neighborhoods while that graph varies.
-/

noncomputable section

open Set

namespace DenseGraph

variable {V : Type*} {G : SimpleGraph V} {M N : G.Subgraph}

/-- A matching with at least as many edges as every other matching in the
same finite graph. -/
def IsMaximumMatching [Finite V] (M : G.Subgraph) : Prop :=
  M.IsMatching ∧
    ∀ N : G.Subgraph, N.IsMatching → N.edgeSet.ncard ≤ M.edgeSet.ncard

namespace IsMaximumMatching

variable [Finite V]

/-- A maximum matching is a matching. -/
theorem isMatching (hM : IsMaximumMatching M) : M.IsMatching :=
  hM.1

/-- The edge-cardinality comparison supplied by maximumity. -/
theorem maximal_card (hM : IsMaximumMatching M) (hN : N.IsMatching) :
    N.edgeSet.ncard ≤ M.edgeSet.ncard :=
  hM.2 N hN

end IsMaximumMatching

/-- Every finite simple graph has a maximum matching. -/
theorem exists_isMaximumMatching [Finite V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, IsMaximumMatching M := by
  classical
  let matchings : Set G.Subgraph := {M | M.IsMatching}
  have hnonempty : matchings.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [matchings, SimpleGraph.Subgraph.IsMatching]
  obtain ⟨M, hM, hmax⟩ :=
    Set.exists_max_image matchings (fun N : G.Subgraph ↦ N.edgeSet.ncard)
      (Set.toFinite matchings) hnonempty
  exact ⟨M, hM, fun N hN ↦ hmax N hN⟩

/-- A fixed maximum matching in a finite graph. -/
def canonicalMaximumMatching [Finite V] (G : SimpleGraph V) : G.Subgraph :=
  Classical.choose (exists_isMaximumMatching G)

/-- The fixed selector is maximum. -/
theorem canonicalMaximumMatching_isMaximum [Finite V] (G : SimpleGraph V) :
    IsMaximumMatching (canonicalMaximumMatching G) :=
  Classical.choose_spec (exists_isMaximumMatching G)

/-- The fixed selector is a matching. -/
theorem canonicalMaximumMatching_isMatching [Finite V] (G : SimpleGraph V) :
    (canonicalMaximumMatching G).IsMatching :=
  (canonicalMaximumMatching_isMaximum G).isMatching

/-- Every matching has at most as many edges as the fixed maximum matching. -/
theorem canonicalMaximumMatching_maximal_card [Finite V] (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ (canonicalMaximumMatching G).edgeSet.ncard :=
  (canonicalMaximumMatching_isMaximum G).maximal_card hM

/-- The matching number of a finite graph. -/
def matchingNumber [Finite V] (G : SimpleGraph V) : ℕ :=
  (canonicalMaximumMatching G).edgeSet.ncard

/-- The fixed maximum matching realizes the matching number. -/
@[simp] theorem canonicalMaximumMatching_card [Finite V] (G : SimpleGraph V) :
    (canonicalMaximumMatching G).edgeSet.ncard = matchingNumber G :=
  rfl

/-- Every matching has cardinality at most the matching number. -/
theorem matching_card_le_matchingNumber [Finite V] (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ matchingNumber G :=
  canonicalMaximumMatching_maximal_card G M hM

noncomputable local instance matchingEdgeSetFintype [Finite V]
    (M : G.Subgraph) : Fintype M.edgeSet :=
  Fintype.ofFinite M.edgeSet

noncomputable local instance matchingAmbientEdgeSetFintype [Finite V]
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- The ambient unordered edges of a subgraph, packaged as a stable finset.
For a matching this is its usual finite edge family. -/
def matchingEdgeFinset [Finite V] (M : G.Subgraph) : Finset (Sym2 V) :=
  M.edgeSet.toFinset

@[simp] theorem mem_matchingEdgeFinset [Finite V] (M : G.Subgraph)
    (e : Sym2 V) :
    e ∈ matchingEdgeFinset M ↔ e ∈ M.edgeSet := by
  classical
  simp [matchingEdgeFinset]

@[simp] theorem card_matchingEdgeFinset [Finite V] (M : G.Subgraph) :
    (matchingEdgeFinset M).card = M.edgeSet.ncard := by
  classical
  unfold matchingEdgeFinset
  exact (Set.ncard_eq_toFinset_card' M.edgeSet).symm

/-- The finite edge family of a subgraph is contained in the ambient graph's
finite edge family.  For a matching this is the usual ambient-edge
containment statement. -/
theorem matching_subset_edgeFinset [Finite V] (M : G.Subgraph) :
    matchingEdgeFinset M ⊆ G.edgeFinset := by
  classical
  intro e he
  rw [mem_matchingEdgeFinset] at he
  rw [SimpleGraph.mem_edgeFinset]
  exact M.edgeSet_subset he

/-- The canonical maximum matching uses only edges of the ambient graph. -/
theorem canonicalMaximumMatching_subset_edgeFinset [Finite V]
    (G : SimpleGraph V) :
    matchingEdgeFinset (canonicalMaximumMatching G) ⊆ G.edgeFinset :=
  matching_subset_edgeFinset (canonicalMaximumMatching G)

/-- Two distinct edges of a matching have disjoint endpoint sets. -/
theorem matching_edges_endpoint_disjoint (hM : M.IsMatching)
    {e f : Sym2 V} (he : e ∈ M.edgeSet) (hf : f ∈ M.edgeSet)
    (hef : e ≠ f) :
    Disjoint (e : Set V) (f : Set V) := by
  rw [Set.disjoint_left]
  intro x hxe hxf
  apply hef
  induction e using Sym2.ind with
  | _ u v =>
      induction f using Sym2.ind with
      | _ w z =>
          rw [SimpleGraph.Subgraph.mem_edgeSet] at he hf
          have hxe' : x = u ∨ x = v := Sym2.mem_iff.mp hxe
          have hxf' : x = w ∨ x = z := Sym2.mem_iff.mp hxf
          rcases hxe' with rfl | rfl <;> rcases hxf' with rfl | rfl
          · simp [hM.eq_of_adj_left he hf]
          · have huv := hM.eq_of_adj_left he hf.symm
            simp [huv, Sym2.eq_swap]
          · have huv := hM.eq_of_adj_left he.symm hf
            simp [huv, Sym2.eq_swap]
          · simp [hM.eq_of_adj_left he.symm hf.symm]

/-! ## Finite edge-family view -/

/-- A finite family of ambient edges whose distinct members have disjoint
endpoint sets.  This is the finite-edge-set view of Mathlib's matching
subgraph predicate. -/
def IsEdgeMatching (G : SimpleGraph V) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, e ∈ G.edgeSet) ∧
    ∀ ⦃e⦄, e ∈ E → ∀ ⦃f⦄, f ∈ E → e ≠ f →
      Disjoint (e : Set V) (f : Set V)

namespace IsEdgeMatching

/-- Every finite subfamily of an edge matching is again an edge matching. -/
theorem mono {E F : Finset (Sym2 V)} (hE : IsEdgeMatching G E)
    (hFE : F ⊆ E) : IsEdgeMatching G F := by
  constructor
  · intro e he
    exact hE.1 e (hFE he)
  · intro e he f hf hef
    exact hE.2 (hFE he) (hFE hf) hef

end IsEdgeMatching

/-- The finite edge family of a Mathlib matching subgraph is an edge
matching in the ambient graph. -/
theorem matchingEdgeFinset_isEdgeMatching [Finite V]
    (hM : M.IsMatching) : IsEdgeMatching G (matchingEdgeFinset M) := by
  constructor
  · intro e he
    exact M.edgeSet_subset ((mem_matchingEdgeFinset M e).mp he)
  · intro e he f hf hef
    exact matching_edges_endpoint_disjoint hM
      ((mem_matchingEdgeFinset M e).mp he)
      ((mem_matchingEdgeFinset M f).mp hf) hef

/-- The endpoints used by a finite edge family. -/
def matchingEndpoints [DecidableEq V] (E : Finset (Sym2 V)) : Finset V :=
  E.biUnion Sym2.toFinset

@[simp] theorem mem_matchingEndpoints [DecidableEq V]
    (E : Finset (Sym2 V)) (v : V) :
    v ∈ matchingEndpoints E ↔ ∃ e ∈ E, v ∈ e := by
  simp [matchingEndpoints, Sym2.mem_toFinset]

/-- A finite edge matching has exactly two endpoints per edge. -/
theorem IsEdgeMatching.matchingEndpoints_card [DecidableEq V]
    {E : Finset (Sym2 V)} (hE : IsEdgeMatching G E) :
    (matchingEndpoints E).card = 2 * E.card := by
  have hpairwise : (E : Set (Sym2 V)).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hef
    change Disjoint e.toFinset f.toFinset
    rw [Finset.disjoint_left]
    intro v hve hvf
    exact Set.disjoint_left.mp (hE.2 he hf hef)
      (by simpa [Sym2.mem_toFinset] using hve)
      (by simpa [Sym2.mem_toFinset] using hvf)
  rw [matchingEndpoints, Finset.card_biUnion hpairwise]
  calc
    (∑ e ∈ E, e.toFinset.card) = ∑ _e ∈ E, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact Sym2.card_toFinset_of_not_isDiag e
        (G.not_isDiag_of_mem_edgeSet (hE.1 e he))
    _ = 2 * E.card := by simp [Nat.mul_comm]

/-- A finite matching has exactly two endpoints per edge. -/
theorem matching_endpoint_ncard (hM : M.IsMatching) [Finite V] :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have hedgeEndpoints :
      ∀ e ∈ M.edgeSet, (e : Set V).ncard = 2 := by
    intro e he
    let hefinite : (e : Set V).Finite := Set.toFinite (e : Set V)
    rw [Set.ncard_eq_toFinset_card _ hefinite]
    have htoFinset : hefinite.toFinset = e.toFinset := by
      ext x
      simp [Sym2.mem_toFinset]
    rw [htoFinset]
    exact Sym2.card_toFinset_of_not_isDiag e
      (G.not_isDiag_of_mem_edgeSet (M.edgeSet_subset he))
  have hpairwise :
      M.edgeSet.PairwiseDisjoint (fun e : Sym2 V ↦ (e : Set V)) := by
    intro e he f hf hef
    exact matching_edges_endpoint_disjoint hM he hf hef
  rw [hM.verts_eq_biUnion_edgeSet]
  rw [M.edgeSet.toFinite.ncard_biUnion
    (fun e _ ↦ Set.toFinite (e : Set V)) hpairwise]
  calc
    ∑ᶠ e ∈ M.edgeSet, (e : Set V).ncard =
        ∑ᶠ _e ∈ M.edgeSet, 2 :=
      finsum_mem_congr rfl hedgeEndpoints
    _ = 2 * M.edgeSet.ncard := by
      rw [finsum_mem_eq_finite_toFinset_sum _ M.edgeSet.toFinite,
        Set.ncard_eq_toFinset_card _ M.edgeSet.toFinite]
      simp [Nat.mul_comm]

/-- The endpoints of a maximum matching form a vertex cover. -/
theorem IsMaximumMatching.endpoints_vertexCover [Finite V]
    (hM : IsMaximumMatching M) :
    G.IsVertexCover M.verts := by
  intro u v huv
  by_contra hcover
  simp only [not_or] at hcover
  have hedge_not_mem : s(u, v) ∉ M.edgeSet := by
    intro hedge
    exact hcover.1 (M.edge_vert hedge)
  have hdisjoint :
      Disjoint M.support (G.subgraphOfAdj huv).support := by
    rw [hM.isMatching.support_eq_verts,
      SimpleGraph.support_subgraphOfAdj]
    rw [Set.disjoint_left]
    intro a ha ha'
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
    exact ha'.elim (fun hau ↦ hcover.1 (hau ▸ ha))
      (fun hav ↦ hcover.2 (hav ▸ ha))
  have haugmented : (M ⊔ G.subgraphOfAdj huv).IsMatching :=
    hM.isMatching.sup
      (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj huv) hdisjoint
  have hcard := hM.maximal_card haugmented
  rw [SimpleGraph.Subgraph.edgeSet_sup,
    SimpleGraph.edgeSet_subgraphOfAdj,
    Set.union_singleton,
    Set.ncard_insert_of_notMem hedge_not_mem] at hcard
  omega

/-- The endpoints of the fixed maximum matching form a vertex cover. -/
theorem canonicalMaximumMatching_endpoints_vertexCover [Finite V]
    (G : SimpleGraph V) :
    G.IsVertexCover (canonicalMaximumMatching G).verts :=
  (canonicalMaximumMatching_isMaximum G).endpoints_vertexCover

/-- The fixed maximum matching has twice its matching number many endpoints. -/
@[simp] theorem canonicalMaximumMatching_endpoint_ncard [Finite V]
    (G : SimpleGraph V) :
    (canonicalMaximumMatching G).verts.ncard = 2 * matchingNumber G := by
  rw [matching_endpoint_ncard (canonicalMaximumMatching_isMatching G)]
  rfl

/-! ## Small independent witnesses and fixed-graph neighborhood counting -/

section NeighborhoodCovers

variable [DecidableEq V]

/-- All subsets with at most `r` vertices. -/
def smallSubsetFinset (S : Finset V) (r : ℕ) : Finset (Finset V) :=
  S.powerset.filter (fun A ↦ A.card ≤ r)

@[simp] theorem mem_smallSubsetFinset (S : Finset V) (r : ℕ) (A : Finset V) :
    A ∈ smallSubsetFinset S r ↔ A ⊆ S ∧ A.card ≤ r := by
  simp [smallSubsetFinset]

/-- At most `(N+1)^r` subsets have size at most `r`. The recursive proof
encodes a nonempty set by one vertex and its smaller remainder. -/
theorem card_smallSubsetFinset_le_pow (S : Finset V) (r : ℕ) :
    (smallSubsetFinset S r).card ≤ (S.card + 1)^r := by
  classical
  induction r with
  | zero =>
      have heq : smallSubsetFinset S 0 = {∅} := by
        ext A
        simp only [mem_smallSubsetFinset, nonpos_iff_eq_zero, Finset.card_eq_zero,
          Finset.mem_singleton, and_iff_right_iff_imp]
        rintro rfl
        exact Finset.empty_subset S
      simp [heq]
  | succ r ih =>
      let F := smallSubsetFinset S r
      let f : V × Finset V → Finset V := fun p ↦ insert p.1 p.2
      have hsub : smallSubsetFinset S (r + 1) ⊆ {∅} ∪ (S ×ˢ F).image f := by
        intro A hA
        obtain ⟨hAS, hcard⟩ := (mem_smallSubsetFinset S (r + 1) A).mp hA
        by_cases hempty : A = ∅
        · simp [hempty]
        · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_image.mpr
          refine ⟨(v, A.erase v), Finset.mem_product.mpr ⟨hAS hv, ?_⟩, ?_⟩
          · exact (mem_smallSubsetFinset S r (A.erase v)).mpr
              ⟨(Finset.erase_subset _ _).trans hAS,
                by have := Finset.card_erase_lt_of_mem hv; omega⟩
          · exact Finset.insert_erase hv
      have hc : (smallSubsetFinset S (r + 1)).card ≤ 1 + S.card * F.card := by
        calc
          _ ≤ ({∅} ∪ (S ×ˢ F).image f).card := Finset.card_le_card hsub
          _ ≤ ({∅} : Finset (Finset V)).card + ((S ×ˢ F).image f).card :=
            Finset.card_union_le _ _
          _ ≤ 1 + S.card * F.card := by
            simpa only [Finset.card_singleton, Finset.card_product] using
              Nat.add_le_add_left (Finset.card_image_le (s := S ×ˢ F) (f := f)) 1
      have hpow : 1 ≤ (S.card + 1)^r := Nat.one_le_pow r _ (by omega)
      calc
        (smallSubsetFinset S (r + 1)).card ≤ 1 + S.card * F.card := hc
        _ ≤ 1 + S.card * (S.card + 1)^r := Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) _
        _ ≤ (S.card + 1)^(r + 1) := by rw [pow_succ]; nlinarith

/-- A maximum independent subset supplies a closed-neighborhood cover of
the given finite set. The independence bound need only hold inside `A`. -/
theorem exists_small_independent_closedNeighborhood_cover
    (H : SimpleGraph V) (A : Finset V) (r : ℕ)
    (hbounded : ∀ I ⊆ A, H.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ I : Finset V, I ⊆ A ∧ H.IsIndepSet (I : Set V) ∧ I.card ≤ r ∧
      ∀ x ∈ A, ∃ y ∈ I, x = y ∨ H.Adj y x := by
  classical
  let F := A.powerset.filter (fun I : Finset V ↦ H.IsIndepSet (I : Set V))
  have hF : F.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [F, SimpleGraph.isIndepSet_iff]
  obtain ⟨I, hI, hmax⟩ := Finset.exists_max_image F Finset.card hF
  have hIA : I ⊆ A := Finset.mem_powerset.mp (Finset.mem_filter.mp hI).1
  have hind : H.IsIndepSet (I : Set V) := (Finset.mem_filter.mp hI).2
  refine ⟨I, hIA, hind, hbounded I hIA hind, ?_⟩
  intro x hx
  by_contra hcover
  have hxI : x ∉ I := by
    intro hxi
    exact hcover ⟨x, hxi, Or.inl rfl⟩
  have hnon : ∀ y ∈ I, ¬ H.Adj x y := by
    intro y hy hxy
    exact hcover ⟨y, hy, Or.inr hxy.symm⟩
  have hnew : H.IsIndepSet (insert x I : Finset V) := by
    rw [← SimpleGraph.isClique_compl]
    simp only [Finset.coe_insert, SimpleGraph.isClique_insert]
    refine ⟨(SimpleGraph.isClique_compl H).mpr hind, ?_⟩
    intro y hy hxy
    exact ⟨hxy, hnon y hy⟩
  have hmem : insert x I ∈ F :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hx hIA), hnew⟩
  have hcard := hmax (insert x I) hmem
  rw [Finset.card_insert_of_notMem hxI] at hcard
  omega

/-- Closed neighborhood restricted to a fixed finite vertex domain. -/
def closedNeighborhoodWithin (H : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (fun x ↦ x = v ∨ H.Adj v x)

@[simp] theorem mem_closedNeighborhoodWithin
    (H : SimpleGraph V) (S : Finset V) (v x : V) :
    x ∈ closedNeighborhoodWithin H S v ↔ x ∈ S ∧ (x = v ∨ H.Adj v x) := by
  classical
  simp [closedNeighborhoodWithin]

/-- Union of the restricted closed neighborhoods of a finite witness set. -/
def closedNeighborhoodUnionWithin (H : SimpleGraph V) (S I : Finset V) : Finset V :=
  I.biUnion (closedNeighborhoodWithin H S)

@[simp] theorem mem_closedNeighborhoodUnionWithin
    (H : SimpleGraph V) (S I : Finset V) (x : V) :
    x ∈ closedNeighborhoodUnionWithin H S I ↔
      x ∈ S ∧ ∃ y ∈ I, x = y ∨ H.Adj y x := by
  simp only [closedNeighborhoodUnionWithin, Finset.mem_biUnion, mem_closedNeighborhoodWithin]
  aesop

theorem card_closedNeighborhoodWithin_le (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V)
    (v : V) (d : ℕ) (hdeg : (S.filter (H.Adj v)).card ≤ d) :
    (closedNeighborhoodWithin H S v).card ≤ d + 1 := by
  classical
  have hsub : closedNeighborhoodWithin H S v ⊆ insert v (S.filter (H.Adj v)) := by
    intro x hx
    obtain ⟨hxs, h⟩ := (mem_closedNeighborhoodWithin H S v x).mp hx
    rcases h with rfl | h
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hxs, h⟩)
  exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by omega))

theorem card_closedNeighborhoodUnionWithin_le
    (H : SimpleGraph V) [DecidableRel H.Adj] (S I : Finset V) (r d : ℕ)
    (hIS : I ⊆ S) (hIr : I.card ≤ r)
    (hdeg : ∀ v ∈ S, (S.filter (H.Adj v)).card ≤ d) :
    (closedNeighborhoodUnionWithin H S I).card ≤ r * (d + 1) := by
  classical
  calc
    _ ≤ ∑ v ∈ I, (closedNeighborhoodWithin H S v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ I, (d + 1) := Finset.sum_le_sum
      (fun v hv ↦ card_closedNeighborhoodWithin_le H S v d (hdeg v (hIS hv)))
    _ = I.card * (d + 1) := by simp
    _ ≤ r * (d + 1) := Nat.mul_le_mul_right _ hIr

/-- All subsets of `S` with independence number at most `r` in the one
fixed graph `H`. This family does not range over varying ambient graphs. -/
def boundedIndependenceSubsetFinset (H : SimpleGraph V) (S : Finset V)
    (r : ℕ) : Finset (Finset V) := by
  classical
  exact S.powerset.filter (fun A ↦
    ∀ I ⊆ A, H.IsIndepSet (I : Set V) → I.card ≤ r)

@[simp] theorem mem_boundedIndependenceSubsetFinset
    (H : SimpleGraph V) (S : Finset V) (r : ℕ) (A : Finset V) :
    A ∈ boundedIndependenceSubsetFinset H S r ↔
      A ⊆ S ∧ ∀ I ⊆ A, H.IsIndepSet (I : Set V) → I.card ≤ r := by
  classical
  simp [boundedIndependenceSubsetFinset]

/-- For a fixed graph with maximum degree at most `d` on `S`, its subsets
of independence number at most `r` have at most
`(S.card+1)^r * 2^(r*(d+1))` possibilities. The witnesses are small maximal
independent sets; each subset is encoded inside their closed neighborhoods. -/
theorem card_boundedIndependenceSubsetFinset_le
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) (r d : ℕ)
    (hdeg : ∀ v ∈ S, (S.filter (H.Adj v)).card ≤ d) :
    (boundedIndependenceSubsetFinset H S r).card ≤
      (S.card + 1)^r * 2^(r * (d + 1)) := by
  classical
  let W := smallSubsetFinset S r
  let U := fun I ↦ (closedNeighborhoodUnionWithin H S I).powerset
  have hcover : boundedIndependenceSubsetFinset H S r ⊆ W.biUnion U := by
    intro A hA
    obtain ⟨hAS, hbound⟩ := (mem_boundedIndependenceSubsetFinset H S r A).mp hA
    obtain ⟨I, hIA, _, hIr, hcover⟩ :=
      exists_small_independent_closedNeighborhood_cover H A r hbound
    apply Finset.mem_biUnion.mpr
    refine ⟨I, (mem_smallSubsetFinset S r I).mpr ⟨hIA.trans hAS, hIr⟩, ?_⟩
    apply Finset.mem_powerset.mpr
    intro x hx
    exact (mem_closedNeighborhoodUnionWithin H S I x).mpr ⟨hAS hx, hcover x hx⟩
  calc
    _ ≤ (W.biUnion U).card := Finset.card_le_card hcover
    _ ≤ ∑ I ∈ W, (U I).card := Finset.card_biUnion_le
    _ ≤ ∑ _I ∈ W, 2^(r * (d + 1)) := by
      apply Finset.sum_le_sum
      intro I hI
      obtain ⟨hIS, hIr⟩ := (mem_smallSubsetFinset S r I).mp hI
      simp only [U, Finset.card_powerset]
      exact Nat.pow_le_pow_right (by norm_num)
        (card_closedNeighborhoodUnionWithin_le H S I r d hIS hIr hdeg)
    _ = W.card * 2^(r * (d + 1)) := by simp
    _ ≤ (S.card + 1)^r * 2^(r * (d + 1)) :=
      Nat.mul_le_mul_right _ (card_smallSubsetFinset_le_pow S r)

end NeighborhoodCovers

end DenseGraph
