import DenseGraph.FiniteModels.GraphEdit
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic

/-!
# Finite co-multipartite witnesses

A co-`r`-partite witness here is the complementary convention appropriate
for the induced-star problem: the vertex set is partitioned into `r` parts,
each of which is a clique.  Edges between different parts are unrestricted.
The explicit witness is useful when a later argument must retain its actual
parts rather than merely know that some partition exists.
-/

noncomputable section

namespace DenseGraph

universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Explicit evidence that `G` has a covering partition into `r` cliques. -/
structure CoMultipartiteWitness (G : SimpleGraph V) (r : ℕ) where
  parts : Fin r → Finset V
  cover : Finset.univ.biUnion parts = Finset.univ
  pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts
  isClique : ∀ i, G.IsClique (parts i : Set V)

/-- A graph is co-`r`-partite when it admits an explicit covering partition
into `r` cliques. -/
def IsCoMultipartite (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CoMultipartiteWitness G r)

namespace CoMultipartiteWitness

variable {G : SimpleGraph V} {r : ℕ}

/-- Every vertex belongs to one of the witness parts. -/
theorem exists_mem_part (C : CoMultipartiteWitness G r) (v : V) :
    ∃ i : Fin r, v ∈ C.parts i := by
  have hv : v ∈ Finset.univ.biUnion C.parts := by
    rw [C.cover]
    exact Finset.mem_univ v
  simpa using Finset.mem_biUnion.mp hv

/-- A deterministic part containing a given vertex. -/
noncomputable def partIndex (C : CoMultipartiteWitness G r) (v : V) : Fin r :=
  Classical.choose (C.exists_mem_part v)

@[simp] theorem mem_partIndex (C : CoMultipartiteWitness G r) (v : V) :
    v ∈ C.parts (C.partIndex v) :=
  Classical.choose_spec (C.exists_mem_part v)

/-- Pairwise disjointness makes the part containing a vertex unique. -/
theorem mem_part_unique (C : CoMultipartiteWitness G r) {v : V}
    {i j : Fin r} (hvi : v ∈ C.parts i) (hvj : v ∈ C.parts j) : i = j := by
  by_contra hij
  exact (Finset.disjoint_left.mp
    (C.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)) hvi hvj

/-- Any covering co-multipartite witness can be refined to one with the same
number of parts and no empty part, provided the ambient vertex set has at
least that many vertices.

The construction first chooses one representative from every nonempty old
part, extends those representatives to `r` seed vertices, and then makes each
seed its own new label.  Every non-seed vertex is assigned to the distinguished
representative of its old part.  Thus every new part is nonempty and refines
an old clique. -/
theorem exists_nonempty_refinement (C : CoMultipartiteWitness G r)
    (hcard : r ≤ Fintype.card V) :
    ∃ C' : CoMultipartiteWitness G r, ∀ i, (C'.parts i).Nonempty := by
  classical
  let active : Finset (Fin r) :=
    Finset.univ.filter fun i ↦ (C.parts i).Nonempty
  let representative : ↥active → V := fun i ↦
    Classical.choose (show (C.parts i.1).Nonempty from
      (Finset.mem_filter.mp i.2).2)
  have hrepresentative_mem (i : ↥active) :
      representative i ∈ C.parts i.1 := by
    exact Classical.choose_spec (show (C.parts i.1).Nonempty from
      (Finset.mem_filter.mp i.2).2)
  let representatives : Finset V := active.attach.image representative
  have hrepresentatives_card : representatives.card ≤ r := by
    calc
      representatives.card ≤ active.attach.card := Finset.card_image_le
      _ = active.card := Finset.card_attach
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ active)
      _ = r := Fintype.card_fin r
  obtain ⟨seeds, hrepresentatives_seeds, hseeds_card⟩ :=
    Finset.exists_superset_card_eq hrepresentatives_card hcard
  let seedEquiv : Fin r ≃ ↥seeds := Fintype.equivOfCardEq (by
    simpa [hseeds_card])
  let seed (i : Fin r) : V := (seedEquiv i).1
  have hseed_mem (i : Fin r) : seed i ∈ seeds := (seedEquiv i).2
  have hpartIndex_active (v : V) : C.partIndex v ∈ active := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, ⟨v, C.mem_partIndex v⟩⟩
  let activePart (v : V) : ↥active :=
    ⟨C.partIndex v, hpartIndex_active v⟩
  let preferred (v : V) : V := representative (activePart v)
  have hpreferred_mem_part (v : V) :
      preferred v ∈ C.parts (C.partIndex v) := by
    exact hrepresentative_mem (activePart v)
  have hpreferred_mem_representatives (v : V) :
      preferred v ∈ representatives := by
    apply Finset.mem_image.mpr
    exact ⟨activePart v, Finset.mem_attach _ _, rfl⟩
  have hpreferred_mem_seeds (v : V) : preferred v ∈ seeds :=
    hrepresentatives_seeds (hpreferred_mem_representatives v)
  let label (v : V) : Fin r :=
    if hv : v ∈ seeds then seedEquiv.symm ⟨v, hv⟩
    else seedEquiv.symm ⟨preferred v, hpreferred_mem_seeds v⟩
  have hlabel_seed (i : Fin r) : label (seed i) = i := by
    simp only [label, hseed_mem, dite_true, seed]
    exact seedEquiv.symm_apply_apply i
  have hpartIndex_eq_of_label_eq {x y : V} (hxy : x ≠ y)
      (hlabel : label x = label y) : C.partIndex x = C.partIndex y := by
    by_cases hx : x ∈ seeds <;> by_cases hy : y ∈ seeds
    · have hsub : (⟨x, hx⟩ : ↥seeds) = ⟨y, hy⟩ := by
        apply seedEquiv.symm.injective
        simpa [label, hx, hy] using hlabel
      exact False.elim (hxy (congrArg Subtype.val hsub))
    · have hsub : (⟨x, hx⟩ : ↥seeds) =
          ⟨preferred y, hpreferred_mem_seeds y⟩ := by
        apply seedEquiv.symm.injective
        simpa [label, hx, hy] using hlabel
      have hxmem : x ∈ C.parts (C.partIndex y) := by
        rw [show x = preferred y from congrArg Subtype.val hsub]
        exact hpreferred_mem_part y
      exact C.mem_part_unique (C.mem_partIndex x) hxmem
    · have hsub : (⟨preferred x, hpreferred_mem_seeds x⟩ : ↥seeds) =
          ⟨y, hy⟩ := by
        apply seedEquiv.symm.injective
        simpa [label, hx, hy] using hlabel
      have hymem : y ∈ C.parts (C.partIndex x) := by
        rw [← show preferred x = y from congrArg Subtype.val hsub]
        exact hpreferred_mem_part x
      exact (C.mem_part_unique (C.mem_partIndex y) hymem).symm
    · have hsub :
          (⟨preferred x, hpreferred_mem_seeds x⟩ : ↥seeds) =
            ⟨preferred y, hpreferred_mem_seeds y⟩ := by
        apply seedEquiv.symm.injective
        simpa [label, hx, hy] using hlabel
      exact C.mem_part_unique (hpreferred_mem_part x) (by
        rw [show preferred x = preferred y from congrArg Subtype.val hsub]
        exact hpreferred_mem_part y)
  let parts : Fin r → Finset V := fun i ↦
    Finset.univ.filter fun v ↦ label v = i
  have hparts_nonempty (i : Fin r) : (parts i).Nonempty := by
    refine ⟨seed i, ?_⟩
    simp [parts, hlabel_seed]
  refine ⟨{
    parts := parts
    cover := ?_
    pairwiseDisjoint := ?_
    isClique := ?_
  }, hparts_nonempty⟩
  · ext v
    simp [parts]
  · intro i _hi j _hj hij
    change Disjoint (parts i) (parts j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [parts, Finset.mem_filter, Finset.mem_univ, true_and] at hvi hvj
    exact hij (hvi.symm.trans hvj)
  · intro i
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    simp only [parts, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_ofPred_eq] at hx hy
    have hindex : C.partIndex x = C.partIndex y :=
      hpartIndex_eq_of_label_eq hxy (hx.trans hy.symm)
    exact C.isClique (C.partIndex x) (C.mem_partIndex x)
      (by simpa [hindex] using C.mem_partIndex y) hxy

variable {W : Type v} [Fintype W] [DecidableEq W]

/-- Pull a co-multipartite witness back along a vertex equivalence. -/
noncomputable def comapEquiv (C : CoMultipartiteWitness G r)
    (e : W ≃ V) : CoMultipartiteWitness (G.comap e) r where
  parts i := (C.parts i).map e.symm.toEmbedding
  cover := by
    apply Finset.eq_univ_of_forall
    intro w
    obtain ⟨i, hi⟩ := C.exists_mem_part (e w)
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [Finset.mem_map_equiv]
    simpa using hi
  pairwiseDisjoint := by
    intro i _hi j _hj hij
    change Disjoint ((C.parts i).map e.symm.toEmbedding)
      ((C.parts j).map e.symm.toEmbedding)
    rw [Finset.disjoint_left]
    intro w hwi hwj
    rw [Finset.mem_map_equiv] at hwi hwj
    exact Finset.disjoint_left.mp
      (C.pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hwi hwj
  isClique := by
    intro i
    rw [SimpleGraph.isClique_iff]
    intro w hw w' hw' hww'
    rw [Finset.coe_map] at hw hw'
    obtain ⟨v, hv, hvw⟩ := hw
    obtain ⟨v', hv', hvw'⟩ := hw'
    subst w
    subst w'
    have hvv' : v ≠ v' := by
      intro hvv'
      exact hww' (congrArg e.symm hvv')
    change G.Adj (e (e.symm v)) (e (e.symm v'))
    simpa using C.isClique i hv hv' hvv'

end CoMultipartiteWitness

/-- Co-multipartiteness is invariant under a simultaneous relabeling of
the vertex type. -/
theorem isCoMultipartite_comap_equiv_iff
    {W : Type v} [Fintype W] [DecidableEq W]
    (e : V ≃ W) (G : SimpleGraph W) (r : ℕ) :
    IsCoMultipartite (G.comap e) r ↔ IsCoMultipartite G r := by
  constructor
  · rintro ⟨C⟩
    have C' := C.comapEquiv e.symm
    have hC' : IsCoMultipartite ((G.comap e).comap e.symm) r := ⟨C'⟩
    have hgraph : (G.comap e).comap e.symm = G := by
      ext x y
      simp
    rw [hgraph] at hC'
    exact hC'
  · rintro ⟨C⟩
    exact ⟨C.comapEquiv e⟩

/-- In particular, a permutation of a fixed vertex type preserves
co-multipartiteness. -/
theorem isCoMultipartite_comap_perm_iff
    (e : Equiv.Perm V) (G : SimpleGraph V) (r : ℕ) :
    IsCoMultipartite (G.comap e) r ↔ IsCoMultipartite G r :=
  isCoMultipartite_comap_equiv_iff e G r

/-- Graph isomorphism preserves co-multipartiteness. -/
theorem isCoMultipartite_iff_of_iso
    {W : Type v} [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (r : ℕ) :
    IsCoMultipartite G r ↔ IsCoMultipartite H r := by
  have hG : G = H.comap e.toEquiv := by
    ext i j
    exact e.map_rel_iff.symm
  rw [hG, isCoMultipartite_comap_equiv_iff]

/-! ## Completing a prescribed partition -/

/-- The graph containing exactly the pairs of distinct vertices that lie in
a common prescribed part. -/
def partitionCliqueGraph (parts : Fin r → Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ i, u ∈ parts i ∧ v ∈ parts i
  symm.symm := by
    intro u v huv
    exact ⟨huv.1.symm, by
      obtain ⟨i, hu, hv⟩ := huv.2
      exact ⟨i, hv, hu⟩⟩
  loopless.irrefl := by
    intro u huu
    exact huu.1 rfl

@[simp] theorem partitionCliqueGraph_adj
    (parts : Fin r → Finset V) (u v : V) :
    (partitionCliqueGraph parts).Adj u v ↔
      u ≠ v ∧ ∃ i, u ∈ parts i ∧ v ∈ parts i :=
  Iff.rfl

/-- Add every missing within-part edge while retaining all existing edges. -/
def completeWithinParts (G : SimpleGraph V) (parts : Fin r → Finset V) :
    SimpleGraph V :=
  G ⊔ partitionCliqueGraph parts

@[simp] theorem completeWithinParts_adj
    (G : SimpleGraph V) (parts : Fin r → Finset V) (u v : V) :
    (completeWithinParts G parts).Adj u v ↔
      G.Adj u v ∨ (u ≠ v ∧ ∃ i, u ∈ parts i ∧ v ∈ parts i) :=
  Iff.rfl

/-- The graph of precisely those nonedges of `G` whose endpoints lie in a
common prescribed part.  These are exactly the edges added by
`completeWithinParts`. -/
def missingWithinPartsGraph (G : SimpleGraph V) (parts : Fin r → Finset V) :
    SimpleGraph V :=
  Gᶜ ⊓ partitionCliqueGraph parts

@[simp] theorem missingWithinPartsGraph_adj
    (G : SimpleGraph V) (parts : Fin r → Finset V) (u v : V) :
    (missingWithinPartsGraph G parts).Adj u v ↔
      ¬G.Adj u v ∧ u ≠ v ∧ ∃ i, u ∈ parts i ∧ v ∈ parts i := by
  rw [missingWithinPartsGraph, SimpleGraph.inf_adj,
    SimpleGraph.compl_adj, partitionCliqueGraph_adj]
  tauto

/-- Completing prescribed parts changes exactly the missing internal
unordered pairs. -/
theorem simpleGraphEditFinset_completeWithinParts
    (G : SimpleGraph V) (parts : Fin r → Finset V) :
    simpleGraphEditFinset G (completeWithinParts G parts) =
      InducedStars.finiteGraphEdges (missingWithinPartsGraph G parts) := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [mem_simpleGraphEditFinset,
        SimpleGraph.mem_edgeSet, InducedStars.mk_mem_finiteGraphEdges,
        completeWithinParts_adj, missingWithinPartsGraph_adj]
      tauto

/-- Exact unordered-edge count for completing prescribed parts. -/
theorem simpleGraphEditDistance_completeWithinParts
    (G : SimpleGraph V) (parts : Fin r → Finset V) :
    simpleGraphEditDistance G (completeWithinParts G parts) =
      (InducedStars.finiteGraphEdges
        (missingWithinPartsGraph G parts)).card := by
  rw [simpleGraphEditDistance,
    simpleGraphEditFinset_completeWithinParts]

/-- For pairwise-disjoint parts, the ordered missing internal pairs count
each edge added by `completeWithinParts` exactly twice. -/
theorem two_mul_simpleGraphEditDistance_completeWithinParts
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (parts : Fin r → Finset V)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts) :
    2 * simpleGraphEditDistance G (completeWithinParts G parts) =
      ∑ i, ((Gᶜ).interedges (parts i) (parts i)).card := by
  classical
  let D : SimpleGraph V := missingWithinPartsGraph G parts
  letI : DecidableRel D.Adj := Classical.decRel _
  have hedge : D.edgeFinset = InducedStars.finiteGraphEdges D := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset,
      InducedStars.mem_finiteGraphEdges]
  have hordered :
      2 * (InducedStars.finiteGraphEdges D).card =
        (Finset.univ.filter fun p : V × V ↦ D.Adj p.1 p.2).card := by
    rw [← hedge]
    exact D.two_mul_card_edgeFinset
  have hpairwise :
      (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint
        (fun i ↦ (Gᶜ).interedges (parts i) (parts i)) := by
    intro i _hi j _hj hij
    change Disjoint ((Gᶜ).interedges (parts i) (parts i))
      ((Gᶜ).interedges (parts j) (parts j))
    rw [Finset.disjoint_left]
    intro p hpi hpj
    rw [SimpleGraph.mem_interedges_iff] at hpi hpj
    exact Finset.disjoint_left.mp
      (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hpi.1 hpj.1
  have hunion :
      Finset.univ.biUnion
          (fun i ↦ (Gᶜ).interedges (parts i) (parts i)) =
        Finset.univ.filter fun p : V × V ↦ D.Adj p.1 p.2 := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      SimpleGraph.mem_interedges_iff, Finset.mem_filter]
    change
      (∃ i, p.1 ∈ parts i ∧ p.2 ∈ parts i ∧ (Gᶜ).Adj p.1 p.2) ↔
        (missingWithinPartsGraph G parts).Adj p.1 p.2
    rw [missingWithinPartsGraph_adj]
    constructor
    · rintro ⟨i, hi, hi', hcomp⟩
      have hc : p.1 ≠ p.2 ∧ ¬G.Adj p.1 p.2 := by
        simpa using hcomp
      exact ⟨hc.2, hc.1, i, hi, hi'⟩
    · rintro ⟨hnot, hne, i, hi, hi'⟩
      refine ⟨i, hi, hi', ?_⟩
      simpa using And.intro hne hnot
  calc
    2 * simpleGraphEditDistance G (completeWithinParts G parts) =
        2 * (InducedStars.finiteGraphEdges D).card := by
      rw [simpleGraphEditDistance_completeWithinParts]
    _ = (Finset.univ.filter fun p : V × V ↦ D.Adj p.1 p.2).card :=
      hordered
    _ = (Finset.univ.biUnion
        (fun i ↦ (Gᶜ).interedges (parts i) (parts i))).card := by
      rw [hunion]
    _ = ∑ i, ((Gᶜ).interedges (parts i) (parts i)).card := by
      simpa using Finset.card_biUnion hpairwise

theorem completeWithinParts_isClique
    (G : SimpleGraph V) (parts : Fin r → Finset V) (i : Fin r) :
    (completeWithinParts G parts).IsClique (parts i : Set V) := by
  rw [SimpleGraph.isClique_iff]
  intro u hu v hv huv
  exact Or.inr ⟨huv, i, hu, hv⟩

/-- Completing every part of a covering disjoint partition produces an
explicitly co-multipartite graph. -/
def completeWithinPartsWitness
    (G : SimpleGraph V) (parts : Fin r → Finset V)
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts) :
    CoMultipartiteWitness (completeWithinParts G parts) r where
  parts := parts
  cover := hcover
  pairwiseDisjoint := hdisjoint
  isClique := completeWithinParts_isClique G parts

theorem completeWithinParts_isCoMultipartite
    (G : SimpleGraph V) (parts : Fin r → Finset V)
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts) :
    IsCoMultipartite (completeWithinParts G parts) r :=
  ⟨completeWithinPartsWitness G parts hcover hdisjoint⟩

theorem partitionCliqueGraph_isCoMultipartite
    (parts : Fin r → Finset V)
    (hcover : Finset.univ.biUnion parts = Finset.univ)
    (hdisjoint : Set.PairwiseDisjoint (Set.univ : Set (Fin r)) parts) :
    IsCoMultipartite (partitionCliqueGraph parts) r := by
  have hbot : completeWithinParts (⊥ : SimpleGraph V) parts =
      partitionCliqueGraph parts := by
    simp [completeWithinParts]
  rw [← hbot]
  exact completeWithinParts_isCoMultipartite ⊥ parts hcover hdisjoint

end DenseGraph
