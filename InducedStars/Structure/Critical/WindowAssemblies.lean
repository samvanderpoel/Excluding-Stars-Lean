import InducedStars.Structure.Critical.Basic
import InducedStars.Structure.Critical.FixedSparseCoverMultiplicity

/-!
# Exact clean assemblies for the critical window

The exceptional set is a labeled set of exactly the specified size.  The
families below retain the literal disjoint-union witness and the exact total
edge count; their counting bounds do not identify distinct decompositions.
-/

noncomputable section

open Finset
namespace InducedStars

noncomputable local instance assemblyGraphDecidableEq (V : Type*) :
    DecidableEq (SimpleGraph V) := Classical.decEq _
noncomputable local instance assemblyEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet
noncomputable local instance assemblyAdjDecidable
    {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

/-- Literal critical structure with an exceptional set of exactly `s` vertices. -/
def HasExactCriticalStructure (k s : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ W : CriticalStructureWitness k n G, W.exceptionalVertices.card = s

theorem hasExactCriticalStructure_iff_vertexSet
    {k s n : ℕ} {G : SimpleGraph (Fin n)} :
    HasExactCriticalStructure k s G ↔
      ∃ S : Finset (Fin n), S.card = s ∧
        (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
        DenseGraph.IsCoMultipartite
          (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1) := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W.exceptionalVertices, hW,
      fun _ hx _ hy ↦ W.not_adj_of_mem_exceptional_of_not_mem hx hy, ?_⟩
    rw [W.induce_complement_eq_core]
    exact W.coreCoMultipartite
  · rintro ⟨S, hS, hcross, hcore⟩
    exact ⟨{
      exceptionalVertices := S
      core := G.induce ({v : Fin n | v ∉ S} : Set (Fin n))
      remainder := G.induce (S : Set (Fin n))
      coreCoMultipartite := hcore
      decomposition :=
        graph_eq_complement_induce_sup_induce_of_noCross G S hcross
    }, hS⟩

/-- Exact-edge induced-star-free graphs admitting an exact-size clean assembly. -/
def exactCriticalAssemblyFinset (k n m s : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (inducedStarFreeGraphFinsetWithEdges k n m).filter
    (HasExactCriticalStructure k s)

@[simp] theorem mem_exactCriticalAssemblyFinset
    {k n m s : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ exactCriticalAssemblyFinset k n m s ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧
        HasExactCriticalStructure k s G := by
  classical
  simp [exactCriticalAssemblyFinset]

theorem isCoMultipartite_map_equiv_iff
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) (r : ℕ) :
    DenseGraph.IsCoMultipartite (G.map e.toEmbedding) r ↔
      DenseGraph.IsCoMultipartite G r := by
  have hmap : G.map e.toEmbedding = G.comap e.symm := by
    ext x y
    exact map_equiv_adj_iff G e x y
  rw [hmap, DenseGraph.isCoMultipartite_comap_equiv_iff]

theorem hasExactCriticalStructure_zero_iff
    {k n : ℕ} {G : SimpleGraph (Fin n)} :
    HasExactCriticalStructure k 0 G ↔ DenseGraph.IsCoMultipartite G (k - 1) := by
  let e : ({v : Fin n | v ∉ (∅ : Finset (Fin n))} : Set (Fin n)) ≃ Fin n :=
    { toFun := Subtype.val
      invFun := fun v ↦ ⟨v, by simp⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hgraph : G.induce ({v : Fin n | v ∉ (∅ : Finset (Fin n))} : Set (Fin n))
      = G.comap e := rfl
  rw [hasExactCriticalStructure_iff_vertexSet]
  constructor
  · rintro ⟨S, hS, _, hcore⟩
    have hS' : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    rw [hgraph, DenseGraph.isCoMultipartite_comap_equiv_iff] at hcore
    exact hcore
  · intro hco
    refine ⟨∅, by simp, by simp, ?_⟩
    rw [hgraph, DenseGraph.isCoMultipartite_comap_equiv_iff]
    exact hco

@[simp] theorem exactCriticalAssemblyFinset_zero
    {k : ℕ} (hk : 1 ≤ k) (n m : ℕ) :
    exactCriticalAssemblyFinset k n m 0 =
      coMultipartiteGraphFinsetWithEdges (k - 1) n m := by
  ext G
  simp only [mem_exactCriticalAssemblyFinset,
    mem_inducedStarFreeGraphFinsetWithEdges, hasExactCriticalStructure_zero_iff,
    mem_coMultipartiteGraphFinsetWithEdges]
  constructor
  · rintro ⟨⟨_, hm⟩, hco⟩
    exact ⟨hco, hm⟩
  · rintro ⟨hco, hm⟩
    exact ⟨⟨coMultipartite_not_inducedEmbeds_inducedStar hk hco, hm⟩, hco⟩

/-- Standard labels for the exceptional induced graph. -/
def assemblyRemainderEquiv {n : ℕ} (S : Finset (Fin n)) :
    ({v : Fin n | v ∈ S} : Set (Fin n)) ≃ Fin S.card :=
  (Fintype.equivFin _).trans (finCongr (by simp))

def assemblyRemainderGraph {n : ℕ} (S : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : SimpleGraph (Fin S.card) :=
  (G.induce (S : Set (Fin n))).map (assemblyRemainderEquiv S).toEmbedding

theorem not_inducedEmbeds_induce_map
    {k n : ℕ} {G : SimpleGraph (Fin n)}
    (hfree : ¬Regularity.InducedEmbeds (inducedStar k) G)
    (S : Finset (Fin n)) :
    ¬Regularity.InducedEmbeds (inducedStar k) (assemblyRemainderGraph S G) := by
  rintro ⟨f⟩
  apply hfree
  let e := assemblyRemainderEquiv S
  refine ⟨{
    toFun := fun v ↦ (e.symm (f v)).1
    inj' := ?_
    map_rel_iff' := ?_ }⟩
  · intro v w h
    exact f.injective (e.symm.injective (Subtype.ext h))
  · intro v w
    exact (map_equiv_adj_iff (G.induce (S : Set (Fin n))) e (f v) (f w)).symm.trans
      f.map_rel_iff

theorem card_core_add_remainder_eq_of_noCross
    {n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    (hcross : ∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) :
    (finiteGraphEdges (fixedSparseCoreGraph S G)).card +
        (finiteGraphEdges (assemblyRemainderGraph S G)).card =
      (finiteGraphEdges G).card := by
  let C := G.induce ({v : Fin n | v ∉ S} : Set (Fin n))
  let R := G.induce (S : Set (Fin n))
  have hdecomp : G = C.spanningCoe ⊔ R.spanningCoe :=
    graph_eq_complement_induce_sup_induce_of_noCross G S hcross
  have hfin : finiteGraphEdges G =
      finiteGraphEdges C.spanningCoe ∪ finiteGraphEdges R.spanningCoe := by
    simpa only [C, R, finiteGraphEdges_sup, Finset.mem_coe] using congrArg finiteGraphEdges hdecomp
  have hdisjoint : Disjoint (finiteGraphEdges C.spanningCoe)
      (finiteGraphEdges R.spanningCoe) := by
    rw [Finset.disjoint_left]
    intro e heC heR
    induction e using Sym2.inductionOn with
    | _ x y =>
      rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at heC heR
      obtain ⟨a, _, _, hax, _⟩ := heC
      obtain ⟨c, _, _, hcx, _⟩ := heR
      have hax' : a.1 = x := hax
      have hcx' : c.1 = x := hcx
      exact a.2 (hax' ▸ hcx'.symm ▸ c.2)
  unfold fixedSparseCoreGraph assemblyRemainderGraph
  rw [card_finiteGraphEdges_map_embedding, card_finiteGraphEdges_map_embedding]
  calc
    (finiteGraphEdges C).card + (finiteGraphEdges R).card =
        (finiteGraphEdges C.spanningCoe).card +
          (finiteGraphEdges R.spanningCoe).card := by
      rw [card_finiteGraphEdges_map_embedding, card_finiteGraphEdges_map_embedding]
    _ = (finiteGraphEdges G).card := by
      rw [← Finset.card_union_of_disjoint hdisjoint, ← hfin]

theorem graph_eq_of_assembly_coordinates_eq
    {n : ℕ} {S : Finset (Fin n)} {G H : SimpleGraph (Fin n)}
    (hG : ∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y)
    (hH : ∀ x, x ∈ S → ∀ y, y ∉ S → ¬H.Adj x y)
    (hcore : fixedSparseCoreGraph S G = fixedSparseCoreGraph S H)
    (hremainder : assemblyRemainderGraph S G = assemblyRemainderGraph S H) :
    G = H := by
  have hc := SimpleGraph.map_injective (fixedSparseCoreEquiv S).toEmbedding hcore
  have hr := SimpleGraph.map_injective (assemblyRemainderEquiv S).toEmbedding hremainder
  rw [graph_eq_complement_induce_sup_induce_of_noCross G S hG,
    graph_eq_complement_induce_sup_induce_of_noCross H S hH]
  change (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))).spanningCoe ⊔
    (G.induce (S : Set (Fin n))).spanningCoe =
    (H.induce ({v : Fin n | v ∉ S} : Set (Fin n))).spanningCoe ⊔
    (H.induce (S : Set (Fin n))).spanningCoe
  rw [hc, hr]

/-- The finite family with the exceptional set prescribed. -/
def fixedSetCriticalAssemblyFinset (k n m : ℕ) (S : Finset (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (inducedStarFreeGraphFinsetWithEdges k n m).filter fun G ↦
    (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
      DenseGraph.IsCoMultipartite
        (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1)

@[simp] theorem mem_fixedSetCriticalAssemblyFinset
    {k n m : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ fixedSetCriticalAssemblyFinset k n m S ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧
        (∀ x, x ∈ S → ∀ y, y ∉ S → ¬G.Adj x y) ∧
        DenseGraph.IsCoMultipartite
          (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) (k - 1) := by
  classical
  simp [fixedSetCriticalAssemblyFinset]

/-- A prescribed exceptional set gives the exact convolution upper bound.
The sum is truncated at `m`, so natural subtraction cannot create spurious
negative core edge counts. -/
theorem card_fixedSetCriticalAssemblyFinset_le
    (k n m : ℕ) (S : Finset (Fin n)) :
    (fixedSetCriticalAssemblyFinset k n m S).card ≤
      ∑ t ∈ Finset.range (m + 1),
        coMultipartiteGraphCountWithEdges (k - 1) (n - S.card) (m - t) *
          inducedStarFreeGraphCountWithEdges k S.card t := by
  classical
  let source := fixedSetCriticalAssemblyFinset k n m S
  let target := Σ t : Fin (m + 1),
    ↑(coMultipartiteGraphFinsetWithEdges (k - 1) (fixedSparseCoreCard S) (m - t.1)) ×
      ↑(inducedStarFreeGraphFinsetWithEdges k S.card t.1)
  have hsplit (G : ↑source) :
      (finiteGraphEdges (fixedSparseCoreGraph S G.1)).card +
          (finiteGraphEdges (assemblyRemainderGraph S G.1)).card = m := by
    obtain ⟨hfree, hcross, _⟩ := mem_fixedSetCriticalAssemblyFinset.mp G.2
    rw [card_core_add_remainder_eq_of_noCross hcross,
      finiteGraphEdges_card_eq_edgeFinset_card,
      (mem_inducedStarFreeGraphFinsetWithEdges.mp hfree).2]
  let f : ↑source → target := fun G ↦
    ⟨⟨(finiteGraphEdges (assemblyRemainderGraph S G.1)).card, by
        have := hsplit G
        omega⟩,
      ⟨⟨fixedSparseCoreGraph S G.1, by
          rw [mem_coMultipartiteGraphFinsetWithEdges]
          refine ⟨?_, ?_⟩
          · exact (isCoMultipartite_map_equiv_iff _ (fixedSparseCoreEquiv S)
              (k - 1)).mpr (mem_fixedSetCriticalAssemblyFinset.mp G.2).2.2
          · rw [← finiteGraphEdges_card_eq_edgeFinset_card]
            change (finiteGraphEdges (fixedSparseCoreGraph S G.1)).card =
              m - (finiteGraphEdges (assemblyRemainderGraph S G.1)).card
            have := hsplit G
            omega⟩,
        ⟨assemblyRemainderGraph S G.1, by
          rw [mem_inducedStarFreeGraphFinsetWithEdges]
          refine ⟨not_inducedEmbeds_induce_map
            (mem_inducedStarFreeGraphFinsetWithEdges.mp
              (mem_fixedSetCriticalAssemblyFinset.mp G.2).1).1 S, ?_⟩
          exact (finiteGraphEdges_card_eq_edgeFinset_card _).symm⟩⟩⟩
  have hf : Function.Injective f := by
    intro G H h
    apply Subtype.ext
    apply graph_eq_of_assembly_coordinates_eq
      (mem_fixedSetCriticalAssemblyFinset.mp G.2).2.1
      (mem_fixedSetCriticalAssemblyFinset.mp H.2).2.1
    · exact congrArg (fun p : target ↦ p.2.1.1) h
    · exact congrArg (fun p : target ↦ p.2.2.1) h
  calc
    source.card = Fintype.card ↑source := by simp
    _ ≤ Fintype.card target := Fintype.card_le_of_injective f hf
    _ = ∑ t ∈ Finset.range (m + 1),
          coMultipartiteGraphCountWithEdges (k - 1) (n - S.card) (m - t) *
            inducedStarFreeGraphCountWithEdges k S.card t := by
      simp only [target, Fintype.card_sigma, Fintype.card_prod, Fintype.card_coe]
      change (∑ t : Fin (m + 1),
        coMultipartiteGraphCountWithEdges (k - 1) (n - S.card) (m - t.1) *
          inducedStarFreeGraphCountWithEdges k S.card t.1) = _
      exact Fin.sum_univ_eq_sum_range
        (fun t ↦ coMultipartiteGraphCountWithEdges (k - 1) (n - S.card) (m - t) *
          inducedStarFreeGraphCountWithEdges k S.card t) (m + 1)

/-- Choosing the exceptional labels and the two component graphs bounds the
number of actual graphs, regardless of decomposition multiplicity. -/
theorem card_exactCriticalAssemblyFinset_le
    (k n m s : ℕ) :
    (exactCriticalAssemblyFinset k n m s).card ≤
      n.choose s * ∑ t ∈ Finset.range (m + 1),
        coMultipartiteGraphCountWithEdges (k - 1) (n - s) (m - t) *
          inducedStarFreeGraphCountWithEdges k s t := by
  classical
  let sets := (Finset.univ : Finset (Fin n)).powersetCard s
  have hsub : exactCriticalAssemblyFinset k n m s ⊆
      sets.biUnion (fixedSetCriticalAssemblyFinset k n m) := by
    intro G hG
    obtain ⟨hfree, hstructure⟩ := mem_exactCriticalAssemblyFinset.mp hG
    obtain ⟨S, hS, hcross, hcore⟩ :=
      hasExactCriticalStructure_iff_vertexSet.mp hstructure
    exact Finset.mem_biUnion.mpr ⟨S, by simp [sets, hS],
      mem_fixedSetCriticalAssemblyFinset.mpr ⟨hfree, hcross, hcore⟩⟩
  calc
    (exactCriticalAssemblyFinset k n m s).card ≤
        (sets.biUnion (fixedSetCriticalAssemblyFinset k n m)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ S ∈ sets, (fixedSetCriticalAssemblyFinset k n m S).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ S ∈ sets, ∑ t ∈ Finset.range (m + 1),
          coMultipartiteGraphCountWithEdges (k - 1) (n - s) (m - t) *
            inducedStarFreeGraphCountWithEdges k s t := by
      apply Finset.sum_le_sum
      intro S hS
      have hcard : S.card = s := (Finset.mem_powersetCard.mp hS).2
      simpa [hcard] using card_fixedSetCriticalAssemblyFinset_le k n m S
    _ = _ := by simp [sets, Finset.card_powersetCard]


/-- Vertices incident with no edge of the graph. -/
def assemblyIsolatedVertices {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset V := by
  classical
  exact Finset.univ.filter fun x ↦ ∀ y, ¬G.Adj x y

@[simp] theorem mem_assemblyIsolatedVertices
    {V : Type*} [Fintype V] {G : SimpleGraph V} {x : V} :
    x ∈ assemblyIsolatedVertices G ↔ ∀ y, ¬G.Adj x y := by
  classical
  simp [assemblyIsolatedVertices]

/-- A co-`r`-partite graph has at most `r` isolated vertices.  More generally,
a co-`r`-partite complement leaves at most `|S|+r` isolated vertices. -/
theorem card_assemblyIsolatedVertices_le
    {n r : ℕ} {G : SimpleGraph (Fin n)} (S : Finset (Fin n))
    (hco : DenseGraph.IsCoMultipartite
      (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) r) :
    (assemblyIsolatedVertices G).card ≤ S.card + r := by
  classical
  obtain ⟨C⟩ := hco
  let f : ↑(assemblyIsolatedVertices G) → (↑S ⊕ Fin r) := fun x ↦
    if hx : x.1 ∈ S then Sum.inl ⟨x.1, hx⟩
    else Sum.inr (C.partIndex ⟨x.1, hx⟩)
  have hf : Function.Injective f := by
    intro x y h
    by_cases hx : x.1 ∈ S <;> by_cases hy : y.1 ∈ S
    · simp only [f, dite_eq_left hx, dite_eq_left hy, Sum.inl.injEq] at h
      exact Subtype.ext (congrArg (fun z : ↑S ↦ (z : Fin n)) h)
    · simp [f, hx, hy] at h
    · simp [f, hx, hy] at h
    · simp only [f, dite_eq_right hx, dite_eq_right hy, Sum.inr.injEq] at h
      apply Subtype.ext
      by_contra hxy
      have hadj := C.isClique (C.partIndex ⟨x.1, hx⟩)
        (C.mem_partIndex ⟨x.1, hx⟩)
        (by rw [h]; exact C.mem_partIndex ⟨y.1, hy⟩)
        (fun heq ↦ hxy (congrArg
          (fun z : ({v : Fin n | v ∉ S} : Set (Fin n)) ↦ z.1) heq))
      exact (mem_assemblyIsolatedVertices.mp x.2) y.1 hadj
  simpa only [Fintype.card_coe, Fintype.card_sum, Fintype.card_fin] using
    Fintype.card_le_of_injective f hf

/-- Assemble a co-partite core with an empty exceptional graph. -/
def emptyCriticalAssembly {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S))) : SimpleGraph (Fin n) :=
  fixedSparseAssembledGraph S J ⊥

theorem emptyCriticalAssembly_not_adj_of_mem
    {n : ℕ} {S : Finset (Fin n)}
    (J : SimpleGraph (Fin (fixedSparseCoreCard S))) {x : Fin n}
    (hx : x ∈ S) (y : Fin n) :
    ¬(emptyCriticalAssembly S J).Adj x y := by
  intro h
  rcases (SimpleGraph.sup_adj _ _ x y).mp h with hc | hr
  · rw [SimpleGraph.map_adj] at hc
    obtain ⟨a, _, _, ha, _⟩ := hc
    have ha' : a.1 = x := ha
    exact a.2 (ha'.symm ▸ hx)
  · rw [SimpleGraph.map_adj] at hr
    obtain ⟨a, b, hab, _, _⟩ := hr
    exact hab

theorem emptyCriticalAssembly_noCross
    {n : ℕ} {S : Finset (Fin n)}
    (J : SimpleGraph (Fin (fixedSparseCoreCard S))) :
    ∀ x, x ∈ S → ∀ y, y ∉ S → ¬(emptyCriticalAssembly S J).Adj x y :=
  fun _ hx y _ ↦ emptyCriticalAssembly_not_adj_of_mem J hx y

@[simp] theorem assemblyRemainderGraph_emptyCriticalAssembly
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S))) :
    assemblyRemainderGraph S (emptyCriticalAssembly S J) = ⊥ := by
  unfold assemblyRemainderGraph
  have hR : (emptyCriticalAssembly S J).induce (S : Set (Fin n)) = ⊥ :=
    fixedSparseRemainderGraph_assembled S J ⊥
  rw [hR]
  ext x y
  constructor
  · intro h
    obtain ⟨a, b, hab, _, _⟩ :=
      (SimpleGraph.map_adj (assemblyRemainderEquiv S).toEmbedding ⊥ x y).mp h
    exact hab
  · intro h
    exact False.elim h

@[simp] theorem card_emptyCriticalAssembly
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S))) :
    (finiteGraphEdges (emptyCriticalAssembly S J)).card =
      (finiteGraphEdges J).card := by
  have hsplit := card_core_add_remainder_eq_of_noCross
    (emptyCriticalAssembly_noCross J)
  rw [assemblyRemainderGraph_emptyCriticalAssembly] at hsplit
  have hbot : (finiteGraphEdges (⊥ : SimpleGraph (Fin S.card))).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rw [mem_finiteGraphEdges, SimpleGraph.edgeSet_bot] at he
    exact he
  rw [hbot, Nat.add_zero] at hsplit
  simpa only [emptyCriticalAssembly, fixedSparseCoreGraph_assembled] using hsplit.symm

theorem emptyCriticalAssembly_core_coMultipartite
    {n r : ℕ} {S : Finset (Fin n)}
    {J : SimpleGraph (Fin (fixedSparseCoreCard S))}
    (hco : DenseGraph.IsCoMultipartite J r) :
    DenseGraph.IsCoMultipartite
      ((emptyCriticalAssembly S J).induce
        ({v : Fin n | v ∉ S} : Set (Fin n))) r := by
  apply (isCoMultipartite_map_equiv_iff _ (fixedSparseCoreEquiv S) r).mp
  change DenseGraph.IsCoMultipartite
    (fixedSparseCoreGraph S (fixedSparseAssembledGraph S J ⊥)) r
  simpa using hco

theorem emptyCriticalAssembly_inducedStarFree
    {k n : ℕ} (hk : 1 ≤ k) {S : Finset (Fin n)}
    {J : SimpleGraph (Fin (fixedSparseCoreCard S))}
    (hco : DenseGraph.IsCoMultipartite J (k - 1)) :
    ¬Regularity.InducedEmbeds (inducedStar k) (emptyCriticalAssembly S J) := by
  rintro ⟨f⟩
  have hvertices : ∀ v : Fin (k + 1), f v ∉ S := by
    intro v hv
    have hneighbor : ∃ w, (inducedStar k).Adj v w := by
      by_cases hv0 : v = 0
      · subst v
        exact ⟨⟨1, by omega⟩, inducedStar_center_adj_of_ne (by simp)⟩
      · exact ⟨0, (inducedStar_center_adj_of_ne hv0).symm⟩
    obtain ⟨w, hw⟩ := hneighbor
    exact emptyCriticalAssembly_not_adj_of_mem J hv (f w) (f.map_rel_iff.mpr hw)
  apply coMultipartite_not_inducedEmbeds_inducedStar hk
    (emptyCriticalAssembly_core_coMultipartite hco)
  refine ⟨{
    toFun := fun v ↦ ⟨f v, hvertices v⟩
    inj' := fun _ _ h ↦ f.injective (congrArg Subtype.val h)
    map_rel_iff' := by intro v w; exact f.map_rel_iff }⟩

theorem emptyCriticalAssembly_mem_exact
    {k n m : ℕ} (hk : 1 ≤ k) (S : Finset (Fin n))
    {J : SimpleGraph (Fin (fixedSparseCoreCard S))}
    (hJ : J ∈ coMultipartiteGraphFinsetWithEdges (k - 1) (fixedSparseCoreCard S) m) :
    emptyCriticalAssembly S J ∈ exactCriticalAssemblyFinset k n m S.card := by
  obtain ⟨hco, hm⟩ := mem_coMultipartiteGraphFinsetWithEdges.mp hJ
  rw [mem_exactCriticalAssemblyFinset, mem_inducedStarFreeGraphFinsetWithEdges,
    hasExactCriticalStructure_iff_vertexSet]
  refine ⟨⟨emptyCriticalAssembly_inducedStarFree hk hco, ?_⟩,
    S, rfl, emptyCriticalAssembly_noCross J, emptyCriticalAssembly_core_coMultipartite hco⟩
  rw [← finiteGraphEdges_card_eq_edgeFinset_card, card_emptyCriticalAssembly,
    finiteGraphEdges_card_eq_edgeFinset_card, hm]


/-- Displayed empty-remainder assemblies: the exceptional labels and an
ordinary labeled co-partite core. -/
abbrev EmptyCriticalAssemblySource (k n m s : ℕ) :=
  Σ S : ↑((Finset.univ : Finset (Fin n)).powersetCard s),
    ↑(coMultipartiteGraphFinsetWithEdges (k - 1) (fixedSparseCoreCard S.1) m)

def emptyCriticalAssemblySourceGraph {k n m s : ℕ}
    (p : EmptyCriticalAssemblySource k n m s) : SimpleGraph (Fin n) :=
  emptyCriticalAssembly p.1.1 p.2.1

theorem emptyCriticalAssemblySource_eq_of_set_eq_of_graph_eq
    {k n m s : ℕ} {p q : EmptyCriticalAssemblySource k n m s}
    (hS : p.1.1 = q.1.1)
    (hG : emptyCriticalAssemblySourceGraph p = emptyCriticalAssemblySourceGraph q) :
    p = q := by
  rcases p with ⟨⟨S, hSp⟩, ⟨J, hJ⟩⟩
  rcases q with ⟨⟨T, hT⟩, ⟨K, hK⟩⟩
  dsimp only at hS
  subst T
  have hJK : J = K := by
    have h := congrArg (fixedSparseCoreGraph S) hG
    simpa [emptyCriticalAssemblySourceGraph, emptyCriticalAssembly] using h
  subst K
  rfl

theorem card_emptyCriticalAssemblySource (k n m s : ℕ) :
    Fintype.card (EmptyCriticalAssemblySource k n m s) =
      n.choose s * coMultipartiteGraphCountWithEdges (k - 1) (n - s) m := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ S : ↑((Finset.univ : Finset (Fin n)).powersetCard s),
        Fintype.card ↑(coMultipartiteGraphFinsetWithEdges
          (k - 1) (fixedSparseCoreCard S.1) m)) =
        ∑ _S : ↑((Finset.univ : Finset (Fin n)).powersetCard s),
          coMultipartiteGraphCountWithEdges (k - 1) (n - s) m := by
      apply Finset.sum_congr rfl
      intro S _
      have hS : S.1.card = s := (Finset.mem_powersetCard.mp S.2).2
      simp only [Fintype.card_coe]
      change coMultipartiteGraphCountWithEdges (k - 1) (n - S.1.card) m = _
      rw [hS]
    _ = _ := by simp [Finset.card_powersetCard]

/-- Forgetting the displayed exceptional set has multiplicity at most
`choose(s+k-1,k-1)`.  This factor is independent of the ambient order. -/
theorem card_emptyCriticalAssemblySource_fiber_le
    {k n m s : ℕ} (G : SimpleGraph (Fin n)) :
    ((Finset.univ : Finset (EmptyCriticalAssemblySource k n m s)).filter
      fun p ↦ emptyCriticalAssemblySourceGraph p = G).card ≤
        (s + (k - 1)).choose (k - 1) := by
  classical
  let fiber := (Finset.univ : Finset (EmptyCriticalAssemblySource k n m s)).filter
    fun p ↦ emptyCriticalAssemblySourceGraph p = G
  change fiber.card ≤ _
  by_cases hempty : fiber = ∅
  · simp only [hempty, Finset.card_empty, Nat.zero_le]
  obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hp₀G : emptyCriticalAssemblySourceGraph p₀ = G :=
    (Finset.mem_filter.mp hp₀).2
  have hp₀card : p₀.1.1.card = s := (Finset.mem_powersetCard.mp p₀.1.2).2
  have hisolates : (assemblyIsolatedVertices G).card ≤ s + (k - 1) := by
    rw [← hp₀G]
    have h := card_assemblyIsolatedVertices_le p₀.1.1
      (emptyCriticalAssembly_core_coMultipartite
        (mem_coMultipartiteGraphFinsetWithEdges.mp p₀.2.2).1)
    simpa only [emptyCriticalAssemblySourceGraph, hp₀card] using h
  have hencode : fiber.card ≤ ((assemblyIsolatedVertices G).powersetCard s).card := by
    apply Finset.card_le_card_of_injOn (fun p ↦ p.1.1)
    · intro p hp
      change p.1.1 ∈ (assemblyIsolatedVertices G).powersetCard s
      rw [Finset.mem_powersetCard]
      refine ⟨?_, (Finset.mem_powersetCard.mp p.1.2).2⟩
      intro x hx
      apply mem_assemblyIsolatedVertices.mpr
      intro y
      have hpG : emptyCriticalAssemblySourceGraph p = G := (Finset.mem_filter.mp hp).2
      rw [← hpG]
      exact emptyCriticalAssembly_not_adj_of_mem p.2.1 hx y
    · intro p hp q hq hS
      apply emptyCriticalAssemblySource_eq_of_set_eq_of_graph_eq hS
      exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
  calc
    fiber.card ≤ ((assemblyIsolatedVertices G).powersetCard s).card := hencode
    _ = ((assemblyIsolatedVertices G).card).choose s := Finset.card_powersetCard _ _
    _ ≤ (s + (k - 1)).choose s := Nat.choose_le_choose s hisolates
    _ = (s + (k - 1)).choose (k - 1) := by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.choose_symm (by omega : s ≤ s + (k - 1))).symm

/-- Empty exceptional graphs provide a lower bound for the actual exact-size
family, with only a fixed-degree polynomial in the exceptional size lost to
decomposition multiplicity. -/
theorem choose_mul_coPartiteCount_le_card_exactCriticalAssembly_mul
    {k : ℕ} (hk : 1 ≤ k) (n m s : ℕ) :
    n.choose s * coMultipartiteGraphCountWithEdges (k - 1) (n - s) m ≤
      (s + (k - 1)).choose (k - 1) *
        (exactCriticalAssemblyFinset k n m s).card := by
  classical
  let source := (Finset.univ : Finset (EmptyCriticalAssemblySource k n m s))
  let image := source.image emptyCriticalAssemblySourceGraph
  have himage : image ⊆ exactCriticalAssemblyFinset k n m s := by
    intro G hG
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hG
    have hp := emptyCriticalAssembly_mem_exact hk p.1.1 p.2.2
    have hcard : p.1.1.card = s := (Finset.mem_powersetCard.mp p.1.2).2
    simpa only [emptyCriticalAssemblySourceGraph, hcard] using hp
  calc
    n.choose s * coMultipartiteGraphCountWithEdges (k - 1) (n - s) m =
        source.card := by
      change _ = Fintype.card (EmptyCriticalAssemblySource k n m s)
      exact (card_emptyCriticalAssemblySource k n m s).symm
    _ = ∑ G ∈ image, (source.filter
          fun p ↦ emptyCriticalAssemblySourceGraph p = G).card :=
      Finset.card_eq_sum_card_image _ _
    _ ≤ ∑ _G ∈ image, (s + (k - 1)).choose (k - 1) :=
      Finset.sum_le_sum fun G _ ↦ card_emptyCriticalAssemblySource_fiber_le G
    _ = (s + (k - 1)).choose (k - 1) * image.card := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.card_le_card himage)


end InducedStars
