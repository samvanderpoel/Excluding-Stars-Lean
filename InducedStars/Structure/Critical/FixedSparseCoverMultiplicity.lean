import InducedStars.Structure.Critical.CanonicalSparse
import InducedStars.Structure.Critical.CapacityBookkeeping
import InducedStars.Structure.Supercritical.CoverMultiplicity
import InducedStars.Structure.Supercritical.CoverReindexing
import Mathlib.Tactic

/-!
# Cover multiplicity with a prescribed sparse set

The critical fine-balance argument first counts *displayed* ordered clean
divisions and then has to return to graphs whose division is selected
canonically.  This file supplies the exact finite bridge.  With the sparse
set fixed, a zero-defect division is simply an ordered clique cover of the
complement.  Covers which are unique up to relabeling occur at most
`(k - 1)!` times; all remaining multiplicity is isolated in an explicit
nonunique-cover pair family.

No probabilistic estimate is used here.  In particular, the final inequality
is valid for an arbitrary finite graph family and is the deterministic input
to which the cover-uniqueness estimates can be applied.
-/

noncomputable section

open Finset Set

namespace InducedStars

noncomputable local instance fixedSparseCoverGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

noncomputable local instance fixedSparseCoverDivisionDecidableEq
    (k n : ℕ) : DecidableEq (SupercriticalDivision k (Fin n)) :=
  Classical.decEq _

noncomputable local instance fixedSparseCoverEdgeSetFintype
    {V : Type*} [Fintype V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

noncomputable local instance fixedSparseCoverAdjDecidable
    {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Divisions and uniqueness at one sparse set -/

/-- All ordered divisions whose sparse set is exactly `S`. -/
noncomputable def criticalFixedSparseCoverDivisions
    (k n : ℕ) (S : Finset (Fin n)) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (allSupercriticalDivisions k n).filter fun D ↦ D.sparse = S

@[simp] theorem mem_criticalFixedSparseCoverDivisions
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ criticalFixedSparseCoverDivisions k n S ↔ D.sparse = S := by
  classical
  simp [criticalFixedSparseCoverDivisions]

/-- Zero-defect ordered covers of `G` having prescribed sparse set `S`. -/
noncomputable def fixedSparseCleanCoverDivisionFinset
    {k n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    Finset (SupercriticalDivision k (Fin n)) :=
  (criticalFixedSparseCoverDivisions k n S).filter fun D ↦
    supercriticalDefectGraph G D = ⊥

@[simp] theorem mem_fixedSparseCleanCoverDivisionFinset
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)} :
    D ∈ fixedSparseCleanCoverDivisionFinset S G ↔
      D.sparse = S ∧ supercriticalDefectGraph G D = ⊥ := by
  classical
  simp [fixedSparseCleanCoverDivisionFinset]

/-- Uniqueness, modulo a permutation of the main-part labels, of a clean
ordered cover with one prescribed sparse set. -/
def HasUniqueFixedSparseCleanCover
    (k : ℕ) {n : ℕ} (S : Finset (Fin n))
    (G : SimpleGraph (Fin n)) : Prop :=
  ∃ D : SupercriticalDivision k (Fin n),
    D.sparse = S ∧ supercriticalDefectGraph G D = ⊥ ∧
      ∀ E : SupercriticalDivision k (Fin n),
        E.sparse = S → supercriticalDefectGraph G E = ⊥ →
          FullDivisionsEquivalent D E

instance {k n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    Decidable (HasUniqueFixedSparseCleanCover k S G) :=
  Classical.propDecidable _

/-- A graph with a unique fixed-sparse clean cover has at most the factorial
number of ordered relabelings of that cover. -/
theorem card_fixedSparseCleanCoverDivisionFinset_le_factorial_of_unique
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    (hunique : HasUniqueFixedSparseCleanCover k S G) :
    (fixedSparseCleanCoverDivisionFinset (k := k) S G).card ≤
      (k - 1).factorial := by
  classical
  obtain ⟨D₀, hD₀sparse, hD₀clean, hunique⟩ := hunique
  let choosePerm :
      {D // D ∈ fixedSparseCleanCoverDivisionFinset (k := k) S G} →
        Equiv.Perm (Fin (k - 1)) := fun D ↦
    Classical.choose (hunique D.1
      (mem_fixedSparseCleanCoverDivisionFinset.mp D.2).1
      (mem_fixedSparseCleanCoverDivisionFinset.mp D.2).2)
  have hchoose :
      ∀ D : {D // D ∈ fixedSparseCleanCoverDivisionFinset (k := k) S G},
        D.1 = D₀.reindexParts (choosePerm D) := fun D ↦
    Classical.choose_spec (hunique D.1
      (mem_fixedSparseCleanCoverDivisionFinset.mp D.2).1
      (mem_fixedSparseCleanCoverDivisionFinset.mp D.2).2)
  have hinj : Function.Injective choosePerm := by
    intro D E hperm
    apply Subtype.ext
    rw [hchoose D, hchoose E, hperm]
  calc
    (fixedSparseCleanCoverDivisionFinset (k := k) S G).card =
        Fintype.card
          {D // D ∈ fixedSparseCleanCoverDivisionFinset (k := k) S G} := by
          exact (Fintype.card_coe _).symm
    _ ≤ Fintype.card (Equiv.Perm (Fin (k - 1))) :=
      Fintype.card_le_of_injective choosePerm hinj
    _ = (k - 1).factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]

/-! ## Restriction to the complementary full cover -/

/-- Restrict a division with sparse set `S` to the complementary vertex
subtype.  The result is a full ordered division on that subtype. -/
def fixedSparseCoreDivision
    {k n : ℕ} (S : Finset (Fin n))
    (D : SupercriticalDivision k (Fin n)) (hD : D.sparse = S) :
    SupercriticalDivision k ({v : Fin n | v ∉ S} : Set (Fin n)) where
  parts i := Finset.univ.filter fun v ↦ v.1 ∈ D.parts i
  parts_nonempty i := by
    obtain ⟨v, hv⟩ := D.parts_nonempty i
    have hvSupport : v ∈ D.support := D.part_subset_support i hv
    have hvNotSparse : v ∉ D.sparse := by simpa using hvSupport
    refine ⟨⟨v, ?_⟩, by simp [hv]⟩
    simpa [← hD] using hvNotSparse
  parts_pairwiseDisjoint := by
    intro i _hi j _hj hij
    change Disjoint
      (Finset.univ.filter fun v : {v : Fin n | v ∉ S} ↦
        v.1 ∈ D.parts i)
      (Finset.univ.filter fun v : {v : Fin n | v ∉ S} ↦
        v.1 ∈ D.parts j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    have hvi' : v.1 ∈ D.parts i := by
      simpa using hvi
    have hvj' : v.1 ∈ D.parts j := by
      simpa using hvj
    exact (Finset.disjoint_left.mp
      (D.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij))
        hvi' hvj'

@[simp] theorem mem_fixedSparseCoreDivision_part
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} (hD : D.sparse = S)
    (i : Fin (k - 1)) (v : {v : Fin n | v ∉ S}) :
    v ∈ (fixedSparseCoreDivision S D hD).parts i ↔ v.1 ∈ D.parts i := by
  simp [fixedSparseCoreDivision]

@[simp] theorem fixedSparseCoreDivision_isFull
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} (hD : D.sparse = S) :
    (fixedSparseCoreDivision S D hD).IsFull := by
  rw [SupercriticalDivision.isFull_iff_support_eq_univ]
  apply Finset.eq_univ_of_forall
  intro v
  have hvNotSparseD : v.1 ∉ D.sparse := by
    rw [hD]
    exact v.2
  have hvSupport : v.1 ∈ D.support := by simpa using hvNotSparseD
  obtain ⟨i, hi⟩ := SupercriticalDivision.mem_support.mp hvSupport
  exact SupercriticalDivision.mem_support.mpr
    ⟨i, (mem_fixedSparseCoreDivision_part hD i v).2 hi⟩

/-- A zero-defect displayed division restricts to a full clique cover of the
induced graph on the complement of its sparse set. -/
theorem fixedSparseCoreDivision_isClique_of_clean
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)} (hD : D.sparse = S)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (i : Fin (k - 1)) :
    (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))).IsClique
      ((fixedSparseCoreDivision S D hD).parts i :
        Set ({v : Fin n | v ∉ S} : Set (Fin n))) := by
  rw [SimpleGraph.isClique_iff]
  intro x hx y hy hxy
  have hxPart : x.1 ∈ D.parts i := by
    exact (mem_fixedSparseCoreDivision_part hD i x).1 hx
  have hyPart : y.1 ∈ D.parts i := by
    exact (mem_fixedSparseCoreDivision_part hD i y).1 hy
  exact mainParts_clique_of_supercriticalDefectGraph_eq_bot
    G D hclean i hxPart hyPart (fun h ↦ hxy (Subtype.ext h))

/-- Equivalence of the restricted full covers implies equivalence of the
original ordered divisions when their sparse sets agree. -/
theorem fullDivisionsEquivalent_of_fixedSparseCoreDivision
    {k n : ℕ} {S : Finset (Fin n)}
    {D E : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S) (hE : E.sparse = S)
    (hcore : FullDivisionsEquivalent
      (fixedSparseCoreDivision S D hD)
      (fixedSparseCoreDivision S E hE)) :
    FullDivisionsEquivalent D E := by
  classical
  obtain ⟨sigma, hcore⟩ := hcore
  refine ⟨sigma, SupercriticalDivision.ext_parts ?_⟩
  funext i
  ext v
  constructor
  · intro hvE
    have hvNotSparse : v ∉ S := by
      rw [← hE]
      intro hvSparse
      exact Finset.disjoint_left.mp (E.part_disjoint_sparse i) hvE hvSparse
    let x : {v : Fin n | v ∉ S} := ⟨v, hvNotSparse⟩
    have hx : x ∈ (fixedSparseCoreDivision S E hE).parts i :=
      (mem_fixedSparseCoreDivision_part hE i x).2 hvE
    rw [hcore] at hx
    simpa [x, fixedSparseCoreDivision] using hx
  · intro hvD
    have hvNotSparse : v ∉ S := by
      rw [← hD]
      have hvPart : v ∈ D.parts (sigma.symm i) := by
        simpa using hvD
      intro hvSparse
      exact Finset.disjoint_left.mp
        (D.part_disjoint_sparse (sigma.symm i)) hvPart hvSparse
    let x : {v : Fin n | v ∉ S} := ⟨v, hvNotSparse⟩
    have hx :
        x ∈ ((fixedSparseCoreDivision S D hD).reindexParts sigma).parts i := by
      simpa [x, fixedSparseCoreDivision] using hvD
    rw [← hcore] at hx
    exact (mem_fixedSparseCoreDivision_part hE i x).1 hx

/-- Uniqueness of the ordinary full clique cover on the induced core implies
uniqueness of the clean cover with the prescribed sparse set. -/
theorem hasUniqueFixedSparseCleanCover_of_core
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S) (hclean : supercriticalDefectGraph G D = ⊥)
    (huniqueCore : HasUniqueCoMultipartiteCover k
      (G.induce ({v : Fin n | v ∉ S} : Set (Fin n)))) :
    HasUniqueFixedSparseCleanCover k S G := by
  refine ⟨D, hD, hclean, ?_⟩
  intro E hE hEclean
  obtain ⟨C, hCfull, hCclique, hCunique⟩ := huniqueCore
  have hDcore := hCunique (fixedSparseCoreDivision S D hD)
    (fixedSparseCoreDivision_isFull hD)
    (fixedSparseCoreDivision_isClique_of_clean hD hclean)
  have hEcore := hCunique (fixedSparseCoreDivision S E hE)
    (fixedSparseCoreDivision_isFull hE)
    (fixedSparseCoreDivision_isClique_of_clean hE hEclean)
  exact fullDivisionsEquivalent_of_fixedSparseCoreDivision hD hE
    (fullDivisionsEquivalent_trans
      (fullDivisionsEquivalent_symm hDcore) hEcore)

/-! ## Relabeling the complementary core onto a standard finite type -/

/-- The cardinality of the complement of a prescribed sparse set. -/
def fixedSparseCoreCard {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  n - S.card

/-- The complementary vertex subtype has the expected cardinality. -/
@[simp] theorem card_fixedSparseCore
    {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card ({v : Fin n | v ∉ S} : Set (Fin n)) =
      fixedSparseCoreCard S := by
  classical
  calc
    Fintype.card ({v : Fin n | v ∉ S} : Set (Fin n)) =
        Fintype.card (Fin n) - Fintype.card {v : Fin n // v ∈ S} :=
      Fintype.card_subtype_compl (fun v : Fin n ↦ v ∈ S)
    _ = fixedSparseCoreCard S := by simp [fixedSparseCoreCard]

/-- A fixed, proof-independent relabeling of the complement of `S` by
`Fin (n - |S|)`. -/
noncomputable def fixedSparseCoreEquiv
    {n : ℕ} (S : Finset (Fin n)) :
    ({v : Fin n | v ∉ S} : Set (Fin n)) ≃ Fin (fixedSparseCoreCard S) :=
  Fintype.equivFinOfCardEq (card_fixedSparseCore S)

/-- Relabel the graph induced on the complement of `S` onto the standard
finite type of the same cardinality. -/
noncomputable def fixedSparseCoreGraph
    {n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    SimpleGraph (Fin (fixedSparseCoreCard S)) :=
  (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))).map
    (fixedSparseCoreEquiv S).toEmbedding

/-- The neutral finite edge set commutes with mapping a graph along an
embedding. -/
theorem finiteGraphEdges_map_embedding
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (f : V ↪ W) :
    finiteGraphEdges (G.map f) =
      (finiteGraphEdges G).map f.sym2Map := by
  classical
  ext z
  simp [mem_finiteGraphEdges, SimpleGraph.edgeSet_map]

/-- The neutral finite edge set sends a graph supremum to union. -/
theorem finiteGraphEdges_sup
    {V : Type*} [Finite V] [DecidableEq (Sym2 V)] (G H : SimpleGraph V) :
    finiteGraphEdges (G ⊔ H) = finiteGraphEdges G ∪ finiteGraphEdges H := by
  classical
  ext z
  simp [mem_finiteGraphEdges, SimpleGraph.edgeSet_sup]

/-- Mapping a finite graph along an embedding preserves its edge count. -/
theorem card_finiteGraphEdges_map_embedding
    {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (f : V ↪ W) :
    (finiteGraphEdges (G.map f)).card = (finiteGraphEdges G).card := by
  rw [finiteGraphEdges_map_embedding, Finset.card_map]

/-- Relabel a displayed fixed-sparse division onto the standard core. -/
noncomputable def fixedSparseCoreFinDivision
    {k n : ℕ} (S : Finset (Fin n))
    (D : SupercriticalDivision k (Fin n)) (hD : D.sparse = S) :
    SupercriticalDivision k (Fin (fixedSparseCoreCard S)) :=
  (fixedSparseCoreDivision S D hD).relabel (fixedSparseCoreEquiv S)

@[simp] theorem card_fixedSparseCoreFinDivision_part
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} (hD : D.sparse = S)
    (i : Fin (k - 1)) :
    ((fixedSparseCoreFinDivision S D hD).parts i).card =
      (D.parts i).card := by
  change (((fixedSparseCoreDivision S D hD).parts i).map
    (fixedSparseCoreEquiv S).toEmbedding).card = (D.parts i).card
  rw [Finset.card_map]
  let f :
      {x // x ∈ (fixedSparseCoreDivision S D hD).parts i} →
        {v // v ∈ D.parts i} := fun x ↦
    ⟨x.1.1, (mem_fixedSparseCoreDivision_part hD i x.1).1 x.2⟩
  let g :
      {v // v ∈ D.parts i} →
        {x // x ∈ (fixedSparseCoreDivision S D hD).parts i} := fun v ↦
    ⟨⟨v.1, by
        rw [← hD]
        intro hvSparse
        exact Finset.disjoint_left.mp (D.part_disjoint_sparse i)
          v.2 hvSparse⟩,
      (mem_fixedSparseCoreDivision_part hD i _).2 v.2⟩
  let e :
      {x // x ∈ (fixedSparseCoreDivision S D hD).parts i} ≃
        {v // v ∈ D.parts i} := {
    toFun := f
    invFun := g
    left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
    right_inv v := by apply Subtype.ext; rfl
  }
  calc
    ((fixedSparseCoreDivision S D hD).parts i).card =
        Fintype.card
          {x // x ∈ (fixedSparseCoreDivision S D hD).parts i} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {v // v ∈ D.parts i} := Fintype.card_congr e
    _ = (D.parts i).card := by simp

@[simp] theorem fixedSparseCoreFinDivision_isFull
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} (hD : D.sparse = S) :
    (fixedSparseCoreFinDivision S D hD).IsFull := by
  unfold fixedSparseCoreFinDivision
  rw [SupercriticalDivision.isFull_iff_support_eq_univ]
  apply Finset.eq_univ_of_forall
  intro w
  rw [SupercriticalDivision.mem_relabel_support]
  have hfull := fixedSparseCoreDivision_isFull hD
  rw [SupercriticalDivision.isFull_iff_support_eq_univ] at hfull
  rw [hfull]
  simp

/-- Fixed-sparse balance is exactly ordinary balance after restriction and
standard relabeling. -/
def IsBalancedFixedSparseDivision
    {k n : ℕ} (S : Finset (Fin n))
    (D : SupercriticalDivision k (Fin n)) (beta : ℝ) : Prop :=
  D.sparse = S ∧ ∀ i,
    |((D.parts i).card : ℝ) -
        (fixedSparseCoreCard S : ℝ) / ((k - 1 : ℕ) : ℝ)| ≤
      beta * fixedSparseCoreCard S

instance {k n : ℕ} (S : Finset (Fin n))
    (D : SupercriticalDivision k (Fin n)) (beta : ℝ) :
    Decidable (IsBalancedFixedSparseDivision S D beta) :=
  Classical.propDecidable _

theorem isBalancedFullDivision_fixedSparseCoreFinDivision
    {k n : ℕ} {S : Finset (Fin n)}
    {D : SupercriticalDivision k (Fin n)} {beta : ℝ}
    (hbalanced : IsBalancedFixedSparseDivision S D beta) :
    IsBalancedFullDivision
      (fixedSparseCoreFinDivision S D hbalanced.1) beta := by
  refine ⟨fixedSparseCoreFinDivision_isFull hbalanced.1, ?_⟩
  intro i
  simpa using hbalanced.2 i

/-- Standard relabeling preserves the number of core edges. -/
@[simp] theorem card_finiteGraphEdges_fixedSparseCoreGraph
    {n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    (finiteGraphEdges (fixedSparseCoreGraph S G)).card =
      (finiteGraphEdges
        (G.induce ({v : Fin n | v ∉ S} : Set (Fin n)))).card := by
  let H := G.induce ({v : Fin n | v ∉ S} : Set (Fin n))
  let e := fixedSparseCoreEquiv S
  have hedge : finiteGraphEdges (H.map e.toEmbedding) =
      (finiteGraphEdges H).map (DenseGraph.sym2Equiv e).toEmbedding := by
    classical
    ext z
    rw [Finset.mem_map_equiv]
    induction z using Sym2.inductionOn with
    | _ x y =>
        simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet,
          DenseGraph.sym2Equiv, Equiv.coe_fn_mk, Sym2.map_pair_eq,
          Equiv.toEmbedding_apply]
        rw [SimpleGraph.map_adj]
        constructor
        · rintro ⟨a, b, hab, hax, hby⟩
          have ha : a = e.symm x := by
            apply e.injective
            simpa using hax
          have hb : b = e.symm y := by
            apply e.injective
            simpa using hby
          simpa [ha, hb] using hab
        · intro h
          exact ⟨e.symm x, e.symm y, h,
            e.apply_symm_apply x, e.apply_symm_apply y⟩
  change (finiteGraphEdges (H.map e.toEmbedding)).card =
    (finiteGraphEdges H).card
  rw [hedge, Finset.card_map]

/-- A clean displayed fixed-sparse cover becomes a member of the ordinary
full co-multipartite fiber of its relabeled core. -/
theorem fixedSparseCoreGraph_mem_supercriticalCoPartiteFiber
    {k n m : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S)
    (hclean : supercriticalDefectGraph G D = ⊥)
    (hcard : (finiteGraphEdges
      (G.induce ({v : Fin n | v ∉ S} : Set (Fin n)))).card = m) :
    fixedSparseCoreGraph S G ∈
      supercriticalCoPartiteFiber (fixedSparseCoreFinDivision S D hD) m := by
  rw [mem_supercriticalCoPartiteFiber_iff_isFull_card_isClique]
  refine ⟨fixedSparseCoreFinDivision_isFull hD, ?_, ?_⟩
  · simpa using hcard
  · intro i
    rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    unfold fixedSparseCoreGraph
    rw [SimpleGraph.map_adj]
    let e := fixedSparseCoreEquiv S
    let x' : ({v : Fin n | v ∉ S} : Set (Fin n)) := e.symm x
    let y' : ({v : Fin n | v ∉ S} : Set (Fin n)) := e.symm y
    refine ⟨x', y', ?_, e.apply_symm_apply x, e.apply_symm_apply y⟩
    apply fixedSparseCoreDivision_isClique_of_clean hD hclean i
    · simpa [fixedSparseCoreFinDivision, x', e] using hx
    · simpa [fixedSparseCoreFinDivision, y', e] using hy
    · intro h
      exact hxy (e.symm.injective h)

namespace SupercriticalDivision

@[simp] theorem relabel_symm_relabel
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W) :
    (D.relabel e).relabel e.symm = D := by
  apply SupercriticalDivision.ext_parts
  funext i
  ext v
  simp

@[simp] theorem relabel_reindexParts
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).relabel e =
      (D.relabel e).reindexParts sigma := by
  apply SupercriticalDivision.ext_parts
  funext i
  ext w
  simp

theorem isFull_relabel_iff
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (D : SupercriticalDivision k V) (e : V ≃ W) :
    (D.relabel e).IsFull ↔ D.IsFull := by
  simp only [SupercriticalDivision.isFull_iff_support_eq_univ]
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro v
    have : e v ∈ (D.relabel e).support := by rw [h]; simp
    simpa using this
  · intro h
    apply Finset.eq_univ_of_forall
    intro w
    rw [SupercriticalDivision.mem_relabel_support, h]
    simp

end SupercriticalDivision

/-- Relabeling both a graph and a division through a vertex equivalence
preserves the clique condition on every displayed part. -/
theorem isClique_map_relabel_iff
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (e : V ≃ W) (i : Fin (k - 1)) :
    (G.map e.toEmbedding).IsClique
        ((D.relabel e).parts i : Set W) ↔
      G.IsClique (D.parts i : Set V) := by
  rw [SimpleGraph.isClique_iff, SimpleGraph.isClique_iff]
  constructor
  · intro h x hx y hy hxy
    have hadj := h (by simpa using hx) (by simpa using hy)
      (fun heq ↦ hxy (e.injective heq))
    rw [SimpleGraph.map_adj] at hadj
    obtain ⟨a, b, hab, ha, hb⟩ := hadj
    have hax : a = x := e.injective ha
    have hby : b = y := e.injective hb
    simpa [hax, hby] using hab
  · intro h x hx y hy hxy
    rw [SimpleGraph.map_adj]
    refine ⟨e.symm x, e.symm y, ?_, e.apply_symm_apply x,
      e.apply_symm_apply y⟩
    apply h
    · simpa using hx
    · simpa using hy
    · intro heq
      exact hxy (e.symm.injective heq)

/-- Adjacency in a graph mapped along an equivalence can be read by applying
the inverse equivalence to both endpoints. -/
theorem map_equiv_adj_iff
    {V W : Type*} (G : SimpleGraph V) (e : V ≃ W) (x y : W) :
    (G.map e.toEmbedding).Adj x y ↔ G.Adj (e.symm x) (e.symm y) := by
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    have ha : a = e.symm x := by apply e.injective; simpa using hax
    have hb : b = e.symm y := by apply e.injective; simpa using hby
    simpa [ha, hb] using hab
  · intro h
    exact ⟨e.symm x, e.symm y, h,
      e.apply_symm_apply x, e.apply_symm_apply y⟩

/-- Vertex relabeling preserves equivalence of ordered full divisions. -/
theorem fullDivisionsEquivalent_relabel
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    {D E : SupercriticalDivision k V} (e : V ≃ W)
    (h : FullDivisionsEquivalent D E) :
    FullDivisionsEquivalent (D.relabel e) (E.relabel e) := by
  obtain ⟨sigma, rfl⟩ := h
  exact ⟨sigma, (SupercriticalDivision.relabel_reindexParts D e sigma).symm⟩

/-- Uniqueness of a full clique cover is preserved by a bijective relabeling
of the vertex type. -/
theorem hasUniqueCoMultipartiteCover_map_equiv
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W)
    (hunique : HasUniqueCoMultipartiteCover k G) :
    HasUniqueCoMultipartiteCover k (G.map e.toEmbedding) := by
  rcases hunique with ⟨D, hDfull, hDclique, hDunique⟩
  refine ⟨D.relabel e,
    (SupercriticalDivision.isFull_relabel_iff D e).2 hDfull,
    fun i ↦ (isClique_map_relabel_iff G D e i).2 (hDclique i), ?_⟩
  intro E hEfull hEclique
  let Eback := E.relabel e.symm
  have hEbackFull : Eback.IsFull := by
    rw [SupercriticalDivision.isFull_relabel_iff]
    exact hEfull
  have hEbackClique : ∀ i, G.IsClique (Eback.parts i : Set V) := by
    intro i
    rw [← isClique_map_relabel_iff G Eback e i]
    have hcancel : Eback.relabel e = E := by
      dsimp [Eback]
      simpa using SupercriticalDivision.relabel_symm_relabel E e.symm
    rw [hcancel]
    exact hEclique i
  have hequiv := hDunique Eback hEbackFull hEbackClique
  have hrelabel := fullDivisionsEquivalent_relabel e hequiv
  have hcancel : Eback.relabel e = E := by
    dsimp [Eback]
    simpa using SupercriticalDivision.relabel_symm_relabel E e.symm
  rw [hcancel] at hrelabel
  exact hrelabel

/-- Uniqueness of a full clique cover is invariant under a bijective
relabeling of the vertex type. -/
theorem hasUniqueCoMultipartiteCover_map_equiv_iff
    {k : ℕ} {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (e : V ≃ W) :
    HasUniqueCoMultipartiteCover k (G.map e.toEmbedding) ↔
      HasUniqueCoMultipartiteCover k G := by
  constructor
  · intro hmap
    have hback := hasUniqueCoMultipartiteCover_map_equiv
      (G.map e.toEmbedding) e.symm hmap
    simpa using hback
  · exact hasUniqueCoMultipartiteCover_map_equiv G e

/-- Nonuniqueness of a fixed-sparse clean cover transfers to the relabeled
ordinary core graph. -/
theorem not_unique_fixedSparseCoreGraph_of_not_unique_fixedSparseCover
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S) (hclean : supercriticalDefectGraph G D = ⊥)
    (hnot : ¬ HasUniqueFixedSparseCleanCover k S G) :
    ¬ HasUniqueCoMultipartiteCover k (fixedSparseCoreGraph S G) := by
  intro hunique
  have huniqueCore : HasUniqueCoMultipartiteCover k
      (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))) :=
    (hasUniqueCoMultipartiteCover_map_equiv_iff _
      (fixedSparseCoreEquiv S)).1 hunique
  exact hnot (hasUniqueFixedSparseCleanCover_of_core
    hD hclean huniqueCore)

/-! ## A density-form cover-uniqueness estimate on the relabeled core -/

/-- The geometric cover-uniqueness theorem only needs an upper bound on the
selected cross-coordinate density.  This density-form wrapper is uniform in
the core edge count and is therefore suitable for every fixed sparse set and
every fixed sparse induced graph. -/
theorem eventually_balancedCoreFiber_nonuniqueCover_card_le_of_density
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ m : ℕ,
      ∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c) →
        ((supercriticalCoPartiteFiberNonuniqueCover D m).card : ℝ) ≤
          ((supercriticalCoPartiteFiber D m).card : ℝ) *
            Real.exp (-(supercriticalCoverUniquenessRate k c * (q : ℝ))) :=
  eventually_balancedCoPartiteFiber_nonuniqueCover_card_le_of_density hk hc

/-! ## Fixed-remainder displayed pairs and restriction to the core -/

/-- The graph induced on a prescribed sparse set, retained on its vertex
subtype.  Fixing this graph (rather than only its edge count) makes core
restriction injective. -/
def fixedSparseRemainderGraph
    {n : ℕ} (S : Finset (Fin n)) (G : SimpleGraph (Fin n)) :
    SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)) :=
  G.induce (S : Set (Fin n))

/-- Relabeled restrictions determine the ambient division once its sparse
set is fixed. -/
theorem fixedSparseCoreFinDivision_injective
    {k n : ℕ} {S : Finset (Fin n)}
    {D E : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S) (hE : E.sparse = S)
    (hcore : fixedSparseCoreFinDivision S D hD =
      fixedSparseCoreFinDivision S E hE) :
    D = E := by
  apply SupercriticalDivision.ext_parts
  funext i
  ext v
  constructor
  · intro hv
    have hvNot : v ∉ S := by
      rw [← hD]
      intro hvSparse
      exact Finset.disjoint_left.mp (D.part_disjoint_sparse i) hv hvSparse
    let x : ({v : Fin n | v ∉ S} : Set (Fin n)) := ⟨v, hvNot⟩
    have hx : fixedSparseCoreEquiv S x ∈
        (fixedSparseCoreFinDivision S D hD).parts i := by
      simp [fixedSparseCoreFinDivision, x, hv]
    rw [hcore] at hx
    simpa [fixedSparseCoreFinDivision, x] using hx
  · intro hv
    have hvNot : v ∉ S := by
      rw [← hE]
      intro hvSparse
      exact Finset.disjoint_left.mp (E.part_disjoint_sparse i) hv hvSparse
    let x : ({v : Fin n | v ∉ S} : Set (Fin n)) := ⟨v, hvNot⟩
    have hx : fixedSparseCoreEquiv S x ∈
        (fixedSparseCoreFinDivision S E hE).parts i := by
      simp [fixedSparseCoreFinDivision, x, hv]
    rw [← hcore] at hx
    simpa [fixedSparseCoreFinDivision, x] using hx

/-- For zero-defect graphs with the same prescribed sparse set, the
relabeled core and the sparse induced graph determine the whole graph. -/
theorem fixedSparseGraph_eq_of_core_eq_of_remainder_eq
    {k n : ℕ} {S : Finset (Fin n)}
    {G H : SimpleGraph (Fin n)}
    {D E : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S) (hE : E.sparse = S)
    (hGclean : supercriticalDefectGraph G D = ⊥)
    (hHclean : supercriticalDefectGraph H E = ⊥)
    (hcore : fixedSparseCoreGraph S G = fixedSparseCoreGraph S H)
    (hremainder : fixedSparseRemainderGraph S G =
      fixedSparseRemainderGraph S H) :
    G = H := by
  have hcoreInduced :
      G.induce ({v : Fin n | v ∉ S} : Set (Fin n)) =
        H.induce ({v : Fin n | v ∉ S} : Set (Fin n)) := by
    exact SimpleGraph.map_injective (fixedSparseCoreEquiv S).toEmbedding hcore
  have hGdecomp :=
    graph_eq_core_induce_sup_sparse_induce_of_defectGraph_eq_bot G D hGclean
  have hHdecomp :=
    graph_eq_core_induce_sup_sparse_induce_of_defectGraph_eq_bot H E hHclean
  rw [hD] at hGdecomp
  rw [hE] at hHdecomp
  calc
    G = (G.induce ({v : Fin n | v ∉ S} : Set (Fin n))).spanningCoe ⊔
        (fixedSparseRemainderGraph S G).spanningCoe := by
      simpa [fixedSparseRemainderGraph] using hGdecomp
    _ = (H.induce ({v : Fin n | v ∉ S} : Set (Fin n))).spanningCoe ⊔
        (fixedSparseRemainderGraph S H).spanningCoe := by
      rw [hcoreInduced, hremainder]
    _ = H := by
      simpa [fixedSparseRemainderGraph] using hHdecomp.symm

/-- Exact edge-count decomposition for a zero-defect graph with prescribed
sparse set.  The core is standardly relabeled, while the sparse induced
graph is kept on its natural subtype. -/
theorem card_core_add_remainder_eq_of_fixedSparse_clean
    {k n : ℕ} {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hD : D.sparse = S)
    (hclean : supercriticalDefectGraph G D = ⊥) :
    (finiteGraphEdges (fixedSparseCoreGraph S G)).card +
        (fixedSparseRemainderGraph S G).edgeFinset.card =
      (finiteGraphEdges G).card := by
  let C := G.induce ({v : Fin n | v ∉ S} : Set (Fin n))
  let R := fixedSparseRemainderGraph S G
  have hdecomp :=
    graph_eq_core_induce_sup_sparse_induce_of_defectGraph_eq_bot G D hclean
  rw [hD] at hdecomp
  have hfin : finiteGraphEdges G =
      finiteGraphEdges C.spanningCoe ∪ finiteGraphEdges R.spanningCoe := by
    have hfin' := congrArg finiteGraphEdges hdecomp
    rw [finiteGraphEdges_sup] at hfin'
    simpa [C, R, fixedSparseRemainderGraph] using hfin'
  have hdisjoint : Disjoint (finiteGraphEdges C.spanningCoe)
      (finiteGraphEdges R.spanningCoe) := by
    rw [Finset.disjoint_left]
    intro e heC heR
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet] at heC heR
        rw [SimpleGraph.map_adj] at heC heR
        obtain ⟨a, _b, _hab, hax, _hby⟩ := heC
        obtain ⟨c, _d, _hcd, hcx, _hdy⟩ := heR
        have hax' : a.1 = x := hax
        have hcx' : c.1 = x := hcx
        exact a.2 (hax' ▸ hcx'.symm ▸ c.2)
  have hRcard : (finiteGraphEdges R).card = R.edgeFinset.card := by
    congr 1
  calc
    (finiteGraphEdges (fixedSparseCoreGraph S G)).card +
        R.edgeFinset.card =
        (finiteGraphEdges C).card + (finiteGraphEdges R).card := by
      rw [card_finiteGraphEdges_fixedSparseCoreGraph]
      exact congrArg ((finiteGraphEdges C).card + ·) hRcard.symm
    _ = (finiteGraphEdges C.spanningCoe).card +
          (finiteGraphEdges R.spanningCoe).card := by
      rw [card_finiteGraphEdges_map_embedding,
        card_finiteGraphEdges_map_embedding]
    _ = (finiteGraphEdges C.spanningCoe ∪
          finiteGraphEdges R.spanningCoe).card := by
      rw [Finset.card_union_of_disjoint hdisjoint]
    _ = (finiteGraphEdges G).card := by rw [hfin]

/-- Balanced displayed clean covers with fixed sparse set, fixed relabeled
core edge count, and fixed sparse induced graph. -/
noncomputable def fixedSparseBalancedCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) := by
  classical
  exact ((criticalFixedSparseCoverDivisions k n S).product
    (Finset.univ : Finset (SimpleGraph (Fin n)))).filter fun p ↦
      supercriticalDefectGraph p.2 p.1 = ⊥ ∧
        IsBalancedFixedSparseDivision S p.1 beta ∧
        (finiteGraphEdges
          (p.2.induce ({v : Fin n | v ∉ S} : Set (Fin n)))).card = m ∧
        fixedSparseRemainderGraph S p.2 = R

@[simp] theorem mem_fixedSparseBalancedCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)} {beta : ℝ} {m : ℕ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseBalancedCleanCoverPairFinset k n S beta m R ↔
      p.1.sparse = S ∧ supercriticalDefectGraph p.2 p.1 = ⊥ ∧
        IsBalancedFixedSparseDivision S p.1 beta ∧
        (finiteGraphEdges
          (p.2.induce ({v : Fin n | v ∉ S} : Set (Fin n)))).card = m ∧
        fixedSparseRemainderGraph S p.2 = R := by
  simp [fixedSparseBalancedCleanCoverPairFinset, and_assoc]

/-- The subfamily of fixed-remainder displayed pairs whose fixed-sparse
clean cover is not unique. -/
noncomputable def fixedSparseBalancedNonuniqueCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :=
  (fixedSparseBalancedCleanCoverPairFinset k n S beta m R).filter fun p ↦
    ¬ HasUniqueFixedSparseCleanCover k S p.2

@[simp] theorem mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)} {beta : ℝ} {m : ℕ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseBalancedNonuniqueCleanCoverPairFinset
        k n S beta m R ↔
      p ∈ fixedSparseBalancedCleanCoverPairFinset k n S beta m R ∧
        ¬ HasUniqueFixedSparseCleanCover k S p.2 := by
  simp [fixedSparseBalancedNonuniqueCleanCoverPairFinset]

/-- Restrict a displayed pair to its standardly relabeled core. -/
noncomputable def fixedSparseCoverPairCore
    {k n : ℕ} (S : Finset (Fin n))
    (p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n))
    (hp : p.1.sparse = S) :
    SupercriticalDivision k (Fin (fixedSparseCoreCard S)) ×
      SimpleGraph (Fin (fixedSparseCoreCard S)) :=
  (fixedSparseCoreFinDivision S p.1 hp, fixedSparseCoreGraph S p.2)

/-- The relabeled core of a nonunique fixed-remainder pair lies in the
ordinary balanced nonunique-cover pair family. -/
theorem fixedSparseCoverPairCore_mem_balancedNonunique
    {k n : ℕ} {S : Finset (Fin n)} {beta : ℝ} {m : ℕ}
    {R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseBalancedNonuniqueCleanCoverPairFinset
      k n S beta m R) :
    fixedSparseCoverPairCore S p
        (mem_fixedSparseBalancedCleanCoverPairFinset.mp
          (mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mp hp).1).1 ∈
      balancedCoMultipartiteNonuniqueCoverPairFinset
        k (fixedSparseCoreCard S) m beta := by
  obtain ⟨hraw, hnotUnique⟩ :=
    mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mp hp
  obtain ⟨hD, hclean, hbalanced, hcard, _hR⟩ :=
    mem_fixedSparseBalancedCleanCoverPairFinset.mp hraw
  rw [mem_balancedCoMultipartiteNonuniqueCoverPairFinset]
  refine ⟨?_, ?_⟩
  · rw [mem_balancedCoMultipartiteCoverPairFinset]
    exact ⟨isBalancedFullDivision_fixedSparseCoreFinDivision hbalanced,
      fixedSparseCoreGraph_mem_supercriticalCoPartiteFiber hD hclean hcard⟩
  · exact not_unique_fixedSparseCoreGraph_of_not_unique_fixedSparseCover
      hD hclean hnotUnique

/-- Restriction to the standardly relabeled core injects a fixed-sparse,
fixed-remainder displayed pair family into the ordinary balanced core-pair
family.  Fixing the sparse remainder is what makes this map injective. -/
theorem card_fixedSparseBalancedCleanCoverPairFinset_le_core
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    (fixedSparseBalancedCleanCoverPairFinset k n S beta m R).card ≤
      (balancedCoMultipartiteCoverPairFinset
        k (fixedSparseCoreCard S) m beta).card := by
  classical
  let source := fixedSparseBalancedCleanCoverPairFinset k n S beta m R
  let target := balancedCoMultipartiteCoverPairFinset
    k (fixedSparseCoreCard S) m beta
  let f : ↑source → ↑target := fun p ↦
    ⟨fixedSparseCoverPairCore S p.1
        (mem_fixedSparseBalancedCleanCoverPairFinset.mp p.2).1,
      by
        obtain ⟨hD, hclean, hbalanced, hcard, _hR⟩ :=
          mem_fixedSparseBalancedCleanCoverPairFinset.mp p.2
        exact mem_balancedCoMultipartiteCoverPairFinset.mpr
          ⟨isBalancedFullDivision_fixedSparseCoreFinDivision hbalanced,
            fixedSparseCoreGraph_mem_supercriticalCoPartiteFiber
              hD hclean hcard⟩⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hcore := congrArg Subtype.val hpq
    obtain ⟨hpD, hpclean, _hpbalanced, _hpcard, hpR⟩ :=
      mem_fixedSparseBalancedCleanCoverPairFinset.mp p.2
    obtain ⟨hqD, hqclean, _hqbalanced, _hqcard, hqR⟩ :=
      mem_fixedSparseBalancedCleanCoverPairFinset.mp q.2
    have hdivision : p.1.1 = q.1.1 :=
      fixedSparseCoreFinDivision_injective hpD hqD
        (congrArg Prod.fst hcore)
    have hgraph : p.1.2 = q.1.2 :=
      fixedSparseGraph_eq_of_core_eq_of_remainder_eq
        hpD hqD hpclean hqclean (congrArg Prod.snd hcore)
          (hpR.trans hqR.symm)
    apply Subtype.ext
    exact Prod.ext hdivision hgraph
  calc
    source.card = Fintype.card ↑source := by simp
    _ ≤ Fintype.card ↑target := Fintype.card_le_of_injective f hf
    _ = target.card := by simp

/-- Uniform support-restriction bound: for every fixed sparse induced graph,
the nonunique displayed pair mass is at most the standard relabeled-core
nonunique pair mass.  There is no factor depending on `S` or on the sparse
graph. -/
theorem card_fixedSparseBalancedNonuniqueCleanCoverPairFinset_le_core
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    (fixedSparseBalancedNonuniqueCleanCoverPairFinset
      k n S beta m R).card ≤
      (balancedCoMultipartiteNonuniqueCoverPairFinset
        k (fixedSparseCoreCard S) m beta).card := by
  classical
  let source := fixedSparseBalancedNonuniqueCleanCoverPairFinset
    k n S beta m R
  let target := balancedCoMultipartiteNonuniqueCoverPairFinset
    k (fixedSparseCoreCard S) m beta
  let f : ↑source → ↑target := fun p ↦
    ⟨fixedSparseCoverPairCore S p.1
        (mem_fixedSparseBalancedCleanCoverPairFinset.mp
          (mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mp p.2).1).1,
      fixedSparseCoverPairCore_mem_balancedNonunique p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hcore := congrArg Subtype.val hpq
    obtain ⟨hpRaw, _hpNot⟩ :=
      mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mp p.2
    obtain ⟨hqRaw, _hqNot⟩ :=
      mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mp q.2
    obtain ⟨hpD, hpclean, _hpbalanced, _hpcard, hpR⟩ :=
      mem_fixedSparseBalancedCleanCoverPairFinset.mp hpRaw
    obtain ⟨hqD, hqclean, _hqbalanced, _hqcard, hqR⟩ :=
      mem_fixedSparseBalancedCleanCoverPairFinset.mp hqRaw
    have hdivision : p.1.1 = q.1.1 :=
      fixedSparseCoreFinDivision_injective hpD hqD
        (congrArg Prod.fst hcore)
    have hgraph : p.1.2 = q.1.2 :=
      fixedSparseGraph_eq_of_core_eq_of_remainder_eq
        hpD hqD hpclean hqclean (congrArg Prod.snd hcore)
          (hpR.trans hqR.symm)
    apply Subtype.ext
    exact Prod.ext hdivision hgraph
  calc
    source.card = Fintype.card ↑source := by simp
    _ ≤ Fintype.card ↑target := Fintype.card_le_of_injective f hf
    _ = target.card := by simp

/-- Aggregate density-form uniqueness bound for all balanced ordered core
fibers.  The density hypothesis is pointwise in the displayed division,
which is exactly what the fixed-density critical arithmetic supplies. -/
theorem eventually_card_balancedCoreNonuniqueCoverPairFinset_le_of_density
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ m : ℕ,
      (∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c)) →
      ((balancedCoMultipartiteNonuniqueCoverPairFinset k q m
        (supercriticalCoverBalanceRadius k)).card : ℝ) ≤
        ((balancedCoMultipartiteCoverPairFinset k q m
          (supercriticalCoverBalanceRadius k)).card : ℝ) *
          Real.exp (-(supercriticalCoverUniquenessRate k c * (q : ℝ))) := by
  filter_upwards
      [eventually_balancedCoreFiber_nonuniqueCover_card_le_of_density hk hc]
      with q hfiber m hdensity
  exact card_balancedCoMultipartiteNonuniqueCoverPairFinset_le_mul_of_fiber
    k q m (supercriticalCoverBalanceRadius k) _
    (fun D hD ↦ hfiber m D hD (hdensity D hD))

/-- Uniform fixed-sparse-set specialization.  The quantifier over `n`, `S`,
and the sparse induced graph `R` comes *after* the eventual core-size
threshold, so the estimate is genuinely uniform over all sparse sets of a
given complementary size. -/
theorem eventually_card_fixedSparseBalancedNonunique_le_corePair
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ n : ℕ, ∀ S : Finset (Fin n), fixedSparseCoreCard S = q →
      ∀ m : ℕ,
      (∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c)) →
      ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
      ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k) m R).card : ℝ) ≤
        ((balancedCoMultipartiteCoverPairFinset k q m
          (supercriticalCoverBalanceRadius k)).card : ℝ) *
          Real.exp (-(supercriticalCoverUniquenessRate k c * (q : ℝ))) := by
  filter_upwards
      [eventually_card_balancedCoreNonuniqueCoverPairFinset_le_of_density
        hk hc] with q hcore n S hSq m hdensity R
  have hrestrict :=
    card_fixedSparseBalancedNonuniqueCleanCoverPairFinset_le_core
      k n S (supercriticalCoverBalanceRadius k) m R
  have hrestrictReal :
      ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k) m R).card : ℝ) ≤
      ((balancedCoMultipartiteNonuniqueCoverPairFinset k
        (fixedSparseCoreCard S) m
          (supercriticalCoverBalanceRadius k)).card : ℝ) := by
    exact_mod_cast hrestrict
  rw [hSq] at hrestrictReal
  exact hrestrictReal.trans (hcore m hdensity)

/-! ## Reverse assembly: every standard core pair gives a fixed-sparse pair -/

/-- Embed the standardly labeled core back into the ambient vertex type. -/
noncomputable def fixedSparseCoreEmbedding
    {n : ℕ} (S : Finset (Fin n)) :
    Fin (fixedSparseCoreCard S) ↪ Fin n :=
  (fixedSparseCoreEquiv S).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

/-- Extend a full ordered division of the standard core by declaring `S` to
be sparse. -/
noncomputable def extendFixedSparseCoreDivision
    {k n : ℕ} (S : Finset (Fin n))
    (C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))) :
    SupercriticalDivision k (Fin n) where
  parts i := (C.parts i).map (fixedSparseCoreEmbedding S)
  parts_nonempty i := by
    obtain ⟨v, hv⟩ := C.parts_nonempty i
    exact ⟨fixedSparseCoreEmbedding S v, by simp [hv]⟩
  parts_pairwiseDisjoint := by
    intro i _hi j _hj hij
    change Disjoint
      ((C.parts i).map (fixedSparseCoreEmbedding S))
      ((C.parts j).map (fixedSparseCoreEmbedding S))
    rw [Finset.disjoint_left]
    intro v hvi hvj
    simp only [Finset.mem_map] at hvi hvj
    obtain ⟨x, hxi, rfl⟩ := hvi
    obtain ⟨y, hyj, hxy⟩ := hvj
    have : x = y := (fixedSparseCoreEmbedding S).injective hxy.symm
    subst y
    exact (Finset.disjoint_left.mp
      (C.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij))
        hxi hyj

theorem mem_extendFixedSparseCoreDivision_support_iff
    {k n : ℕ} {S : Finset (Fin n)}
    {C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    (hC : C.IsFull) (v : Fin n) :
    v ∈ (extendFixedSparseCoreDivision S C).support ↔ v ∉ S := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := SupercriticalDivision.mem_support.mp hv
    simp only [extendFixedSparseCoreDivision, Finset.mem_map] at hi
    obtain ⟨w, _hw, hwv⟩ := hi
    rw [← hwv]
    exact (fixedSparseCoreEquiv S).symm w |>.2
  · intro hv
    let x : ({v : Fin n | v ∉ S} : Set (Fin n)) := ⟨v, hv⟩
    let w : Fin (fixedSparseCoreCard S) := fixedSparseCoreEquiv S x
    have hwSupport : w ∈ C.support := by
      rw [SupercriticalDivision.isFull_iff_support_eq_univ] at hC
      rw [hC]
      simp
    obtain ⟨i, hi⟩ := SupercriticalDivision.mem_support.mp hwSupport
    apply SupercriticalDivision.mem_support.mpr
    refine ⟨i, Finset.mem_map.mpr ⟨w, hi, ?_⟩⟩
    change ((fixedSparseCoreEquiv S).symm w).1 = v
    dsimp [w, x]
    simp

@[simp] theorem extendFixedSparseCoreDivision_sparse
    {k n : ℕ} {S : Finset (Fin n)}
    {C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    (hC : C.IsFull) :
    (extendFixedSparseCoreDivision S C).sparse = S := by
  ext v
  rw [SupercriticalDivision.mem_sparse]
  simp [mem_extendFixedSparseCoreDivision_support_iff hC]

@[simp] theorem fixedSparseCoreFinDivision_extend
    {k n : ℕ} {S : Finset (Fin n)}
    (C : SupercriticalDivision k (Fin (fixedSparseCoreCard S)))
    (hC : C.IsFull) :
    fixedSparseCoreFinDivision S (extendFixedSparseCoreDivision S C)
      (extendFixedSparseCoreDivision_sparse hC) = C := by
  apply SupercriticalDivision.ext_parts
  funext i
  ext w
  unfold fixedSparseCoreFinDivision
  rw [SupercriticalDivision.mem_relabel_part]
  rw [mem_fixedSparseCoreDivision_part]
  change ((fixedSparseCoreEquiv S).symm w).1 ∈
      (extendFixedSparseCoreDivision S C).parts i ↔ w ∈ C.parts i
  simp only [extendFixedSparseCoreDivision, Finset.mem_map]
  change (∃ a ∈ C.parts i,
      ((fixedSparseCoreEquiv S).symm a).1 =
        ((fixedSparseCoreEquiv S).symm w).1) ↔ w ∈ C.parts i
  constructor
  · rintro ⟨a, ha, haw⟩
    have : a = w := by
      apply (fixedSparseCoreEquiv S).symm.injective
      apply Subtype.ext
      exact haw
    simpa [this] using ha
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- Assemble a graph on the standard core and a graph on the prescribed
sparse set, with no edges between the two vertex sets. -/
noncomputable def fixedSparseAssembledGraph
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    SimpleGraph (Fin n) :=
  ((J.map (fixedSparseCoreEquiv S).symm.toEmbedding).spanningCoe) ⊔
    R.spanningCoe

theorem fixedSparseAssembledGraph_adj_core
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (x y : ({v : Fin n | v ∉ S} : Set (Fin n))) :
    (fixedSparseAssembledGraph S J R).Adj x.1 y.1 ↔
      J.Adj (fixedSparseCoreEquiv S x) (fixedSparseCoreEquiv S y) := by
  unfold fixedSparseAssembledGraph
  rw [SimpleGraph.sup_adj]
  constructor
  · rintro (hcore | hR)
    · rw [SimpleGraph.map_adj] at hcore
      obtain ⟨a, b, hab, hax, hby⟩ := hcore
      have ha : a = x := Subtype.ext hax
      have hb : b = y := Subtype.ext hby
      subst a
      subst b
      exact (map_equiv_adj_iff J (fixedSparseCoreEquiv S).symm x y).mp hab
    · rw [SimpleGraph.map_adj] at hR
      obtain ⟨a, _b, _hab, hax, _hby⟩ := hR
      exact (x.2 (hax ▸ a.2)).elim
  · intro h
    left
    rw [SimpleGraph.map_adj]
    refine ⟨x, y, ?_, rfl, rfl⟩
    exact (map_equiv_adj_iff J (fixedSparseCoreEquiv S).symm x y).mpr h

theorem fixedSparseAssembledGraph_adj_sparse
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (x y : ({v : Fin n | v ∈ S} : Set (Fin n))) :
    (fixedSparseAssembledGraph S J R).Adj x.1 y.1 ↔ R.Adj x y := by
  unfold fixedSparseAssembledGraph
  rw [SimpleGraph.sup_adj]
  constructor
  · rintro (hcore | hR)
    · rw [SimpleGraph.map_adj] at hcore
      obtain ⟨a, _b, _hab, hax, _hby⟩ := hcore
      have hax' : a.1 = x.1 := hax
      exact (a.2 (hax' ▸ x.2)).elim
    · rw [SimpleGraph.map_adj] at hR
      obtain ⟨a, b, hab, hax, hby⟩ := hR
      have ha : a = x := Subtype.ext hax
      have hb : b = y := Subtype.ext hby
      simpa [ha, hb] using hab
  · intro h
    right
    rw [SimpleGraph.map_adj]
    exact ⟨x, y, h, rfl, rfl⟩

@[simp] theorem fixedSparseCoreGraph_assembled
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    fixedSparseCoreGraph S (fixedSparseAssembledGraph S J R) = J := by
  ext x y
  unfold fixedSparseCoreGraph
  rw [map_equiv_adj_iff]
  change (fixedSparseAssembledGraph S J R).Adj
      ((fixedSparseCoreEquiv S).symm x).1
      ((fixedSparseCoreEquiv S).symm y).1 ↔ J.Adj x y
  simpa using fixedSparseAssembledGraph_adj_core S J R
    ((fixedSparseCoreEquiv S).symm x)
    ((fixedSparseCoreEquiv S).symm y)

@[simp] theorem fixedSparseRemainderGraph_assembled
    {n : ℕ} (S : Finset (Fin n))
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    fixedSparseRemainderGraph S (fixedSparseAssembledGraph S J R) = R := by
  ext x y
  exact fixedSparseAssembledGraph_adj_sparse S J R x y

theorem fixedSparseAssembledGraph_not_adj_core_sparse
    {n : ℕ} {S : Finset (Fin n)}
    (J : SimpleGraph (Fin (fixedSparseCoreCard S)))
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    {x y : Fin n} (hx : x ∉ S) (hy : y ∈ S) :
    ¬ (fixedSparseAssembledGraph S J R).Adj x y := by
  unfold fixedSparseAssembledGraph
  rw [SimpleGraph.sup_adj]
  rintro (hcore | hR)
  · rw [SimpleGraph.map_adj] at hcore
    obtain ⟨_a, b, _hab, _hax, hby⟩ := hcore
    have hby' : b.1 = y := hby
    exact b.2 (hby' ▸ hy)
  · rw [SimpleGraph.map_adj] at hR
    obtain ⟨a, _b, _hab, hax, _hby⟩ := hR
    have hax' : a.1 = x := hax
    exact hx (hax'.symm ▸ a.2)

/-- Clique parts together with an empty support--sparse cut are exactly what
is needed for the ordinary defect graph to vanish. -/
theorem supercriticalDefectGraph_eq_bot_of_cliques_of_noCross
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (hclique : ∀ i, G.IsClique (D.parts i : Set V))
    (hcross : ∀ x, x ∈ D.support → ∀ y, y ∈ D.sparse →
      ¬ G.Adj x y) :
    supercriticalDefectGraph G D = ⊥ := by
  ext x y
  simp only [SimpleGraph.bot_adj, iff_false]
  intro hdef
  by_cases hxs : x ∈ D.sparse
  · by_cases hys : y ∈ D.sparse
    · exact supercriticalDefectGraph_not_adj_of_mem_sparse
        G D hxs hys hdef
    · have hySupport : y ∈ D.support := by
        simpa [SupercriticalDivision.mem_sparse] using hys
      have hadj : G.Adj y x :=
        (supercriticalDefectGraph_adj_support_sparse
          G D hySupport hxs).mp hdef.symm
      exact hcross y hySupport x hxs hadj
  · have hxSupport : x ∈ D.support := by
      simpa [SupercriticalDivision.mem_sparse] using hxs
    by_cases hys : y ∈ D.sparse
    · have hadj : G.Adj x y :=
        (supercriticalDefectGraph_adj_support_sparse
          G D hxSupport hys).mp hdef
      exact hcross x hxSupport y hys hadj
    · have hySupport : y ∈ D.support := by
        simpa [SupercriticalDivision.mem_sparse] using hys
      obtain ⟨i, hxi⟩ := SupercriticalDivision.mem_support.mp hxSupport
      obtain ⟨j, hyj⟩ := SupercriticalDivision.mem_support.mp hySupport
      by_cases hij : i = j
      · subst j
        have hmissing :=
          (supercriticalDefectGraph_adj_of_mem_same_part
            G D i hxi hyj).mp hdef
        exact hmissing.2 (hclique i hxi hyj hmissing.1)
      · exact supercriticalDefectGraph_not_adj_of_mem_distinct_parts
          G D hij hxi hyj hdef

/-- Each extended core part remains a clique in the assembled graph. -/
theorem fixedSparseAssembledGraph_isClique_extend
    {k n : ℕ} {S : Finset (Fin n)}
    {C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    {J : SimpleGraph (Fin (fixedSparseCoreCard S))}
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hclique : ∀ i, J.IsClique (C.parts i : Set (Fin (fixedSparseCoreCard S))))
    (i : Fin (k - 1)) :
    (fixedSparseAssembledGraph S J R).IsClique
      ((extendFixedSparseCoreDivision S C).parts i : Set (Fin n)) := by
  rw [SimpleGraph.isClique_iff]
  intro x hx y hy hxy
  change x ∈ (extendFixedSparseCoreDivision S C).parts i at hx
  change y ∈ (extendFixedSparseCoreDivision S C).parts i at hy
  simp only [extendFixedSparseCoreDivision, Finset.mem_map] at hx hy
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  let a' := (fixedSparseCoreEquiv S).symm a
  let b' := (fixedSparseCoreEquiv S).symm b
  apply (fixedSparseAssembledGraph_adj_core S J R a' b').mpr
  simpa [a', b'] using hclique i ha hb
    (fun hab ↦ hxy (congrArg (fixedSparseCoreEmbedding S) hab))

/-- Assembly has zero ordinary defect for the extended displayed cover. -/
theorem fixedSparseAssembledGraph_clean
    {k n : ℕ} {S : Finset (Fin n)}
    {C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    {J : SimpleGraph (Fin (fixedSparseCoreCard S))}
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hC : C.IsFull)
    (hclique : ∀ i, J.IsClique (C.parts i : Set (Fin (fixedSparseCoreCard S)))) :
    supercriticalDefectGraph (fixedSparseAssembledGraph S J R)
      (extendFixedSparseCoreDivision S C) = ⊥ := by
  apply supercriticalDefectGraph_eq_bot_of_cliques_of_noCross
  · exact fixedSparseAssembledGraph_isClique_extend R hclique
  · intro x hx y hy
    have hxS : x ∉ S :=
      (mem_extendFixedSparseCoreDivision_support_iff hC x).mp hx
    have hyS : y ∈ S := by
      rw [extendFixedSparseCoreDivision_sparse hC] at hy
      exact hy
    exact fixedSparseAssembledGraph_not_adj_core_sparse J R hxS hyS

/-- Balance is preserved exactly by extending a standard core division with
the prescribed sparse set. -/
theorem isBalancedFixedSparseDivision_extend
    {k n : ℕ} {S : Finset (Fin n)}
    {C : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    {beta : ℝ} (hbalanced : IsBalancedFullDivision C beta) :
    IsBalancedFixedSparseDivision S
      (extendFixedSparseCoreDivision S C) beta := by
  refine ⟨extendFixedSparseCoreDivision_sparse hbalanced.1, ?_⟩
  intro i
  simpa [extendFixedSparseCoreDivision] using hbalanced.2 i

/-- Extending a full core division by a fixed sparse set is injective. -/
theorem extendFixedSparseCoreDivision_injective_of_full
    {k n : ℕ} {S : Finset (Fin n)}
    {C E : SupercriticalDivision k (Fin (fixedSparseCoreCard S))}
    (hC : C.IsFull) (hE : E.IsFull)
    (h : extendFixedSparseCoreDivision S C =
      extendFixedSparseCoreDivision S E) :
    C = E := by
  apply SupercriticalDivision.ext_parts
  funext i
  apply Finset.map_injective (fixedSparseCoreEmbedding S)
  exact congrArg (fun D ↦ D.parts i) h

/-- Every balanced standard core pair assembles to a member of the literal
fixed-sparse, fixed-remainder displayed pair family. -/
theorem fixedSparseAssembledPair_mem
    {k n m : ℕ} {S : Finset (Fin n)} {beta : ℝ}
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    {p : SupercriticalDivision k (Fin (fixedSparseCoreCard S)) ×
      SimpleGraph (Fin (fixedSparseCoreCard S))}
    (hp : p ∈ balancedCoMultipartiteCoverPairFinset
      k (fixedSparseCoreCard S) m beta) :
    (extendFixedSparseCoreDivision S p.1,
        fixedSparseAssembledGraph S p.2 R) ∈
      fixedSparseBalancedCleanCoverPairFinset k n S beta m R := by
  obtain ⟨hbalanced, hfiber⟩ :=
    mem_balancedCoMultipartiteCoverPairFinset.mp hp
  rw [mem_fixedSparseBalancedCleanCoverPairFinset]
  refine ⟨extendFixedSparseCoreDivision_sparse hbalanced.1,
    fixedSparseAssembledGraph_clean R hbalanced.1
      (fun i ↦ supercriticalCoPartiteFiber_isClique hfiber i),
    isBalancedFixedSparseDivision_extend hbalanced, ?_,
    fixedSparseRemainderGraph_assembled S p.2 R⟩
  rw [← card_finiteGraphEdges_fixedSparseCoreGraph S
    (fixedSparseAssembledGraph S p.2 R), fixedSparseCoreGraph_assembled]
  exact card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber hfiber

/-- The standard balanced core-pair mass injects into every fixed-remainder
displayed pair family. -/
theorem card_balancedCoreCoverPairFinset_le_fixedSparse
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n))) :
    (balancedCoMultipartiteCoverPairFinset
      k (fixedSparseCoreCard S) m beta).card ≤
      (fixedSparseBalancedCleanCoverPairFinset k n S beta m R).card := by
  classical
  let source := balancedCoMultipartiteCoverPairFinset
    k (fixedSparseCoreCard S) m beta
  let target := fixedSparseBalancedCleanCoverPairFinset k n S beta m R
  let f : ↑source → ↑target := fun p ↦
    ⟨(extendFixedSparseCoreDivision S p.1.1,
      fixedSparseAssembledGraph S p.1.2 R),
      fixedSparseAssembledPair_mem R p.2⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have hp := mem_balancedCoMultipartiteCoverPairFinset.mp p.2
    have hq := mem_balancedCoMultipartiteCoverPairFinset.mp q.2
    have hval := congrArg Subtype.val hpq
    have hdivision : p.1.1 = q.1.1 := by
      have h := congrArg Prod.fst hval
      change extendFixedSparseCoreDivision S p.1.1 =
        extendFixedSparseCoreDivision S q.1.1 at h
      exact extendFixedSparseCoreDivision_injective_of_full
        hp.1.1 hq.1.1 h
    have hgraph : p.1.2 = q.1.2 := by
      have h := congrArg Prod.snd hval
      change fixedSparseAssembledGraph S p.1.2 R =
        fixedSparseAssembledGraph S q.1.2 R at h
      have h' := congrArg (fixedSparseCoreGraph S) h
      simpa using h'
    apply Subtype.ext
    exact Prod.ext hdivision hgraph
  calc
    source.card = Fintype.card ↑source := by simp
    _ ≤ Fintype.card ↑target := Fintype.card_le_of_injective f hf
    _ = target.card := by simp

/-- The fixed-sparse nonunique error is exponentially small relative to the
literal fixed-sparse, fixed-remainder displayed pair mass.  The estimate is
uniform in the ambient size, sparse set, retained core edge count, and
sparse induced graph once the complementary core size is large. -/
theorem eventually_card_fixedSparseBalancedNonunique_le_raw_of_density
    {k : ℕ} (hk : 3 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ n : ℕ, ∀ S : Finset (Fin n), fixedSparseCoreCard S = q →
      ∀ m : ℕ,
      (∀ D : SupercriticalDivision k (Fin q),
        IsBalancedFullDivision D (supercriticalCoverBalanceRadius k) →
        ((m - divisionInternalCliqueCapacity D : ℕ) : ℝ) /
            (supercriticalTotalCrossCapacity D : ℝ) ≤ Real.exp (-c)) →
      ∀ R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)),
      ((fixedSparseBalancedNonuniqueCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k) m R).card : ℝ) ≤
        ((fixedSparseBalancedCleanCoverPairFinset k n S
          (supercriticalCoverBalanceRadius k) m R).card : ℝ) *
          Real.exp (-(supercriticalCoverUniquenessRate k c * (q : ℝ))) := by
  filter_upwards
      [eventually_card_fixedSparseBalancedNonunique_le_corePair hk hc]
      with q hnonunique n S hSq m hdensity R
  have hcore := card_balancedCoreCoverPairFinset_le_fixedSparse
    k n S (supercriticalCoverBalanceRadius k) m R
  have hcoreReal :
      ((balancedCoMultipartiteCoverPairFinset k (fixedSparseCoreCard S) m
        (supercriticalCoverBalanceRadius k)).card : ℝ) ≤
      ((fixedSparseBalancedCleanCoverPairFinset k n S
        (supercriticalCoverBalanceRadius k) m R).card : ℝ) := by
    exact_mod_cast hcore
  rw [hSq] at hcoreReal
  exact (hnonunique n S hSq m hdensity R).trans
    (mul_le_mul_of_nonneg_right hcoreReal (Real.exp_nonneg _))

/-! ## Coarse balanced mass versus one exactly balanced size vector -/

/-- There are at most `(k-1)^q` ordered full divisions, hence also at most
that many divisions in any coarse balance window. -/
theorem card_balancedFullSupercriticalDivisions_le_pow
    (k q : ℕ) (beta : ℝ) :
    (balancedFullSupercriticalDivisions k q beta).card ≤ (k - 1) ^ q := by
  classical
  let label :
      {D // D ∈ balancedFullSupercriticalDivisions k q beta} →
        (Fin q → Fin (k - 1)) := fun D ↦
    D.1.fullAssignment
      (mem_balancedFullSupercriticalDivisions.mp D.2).1
  have hlabel : Function.Injective label := by
    intro D E hDE
    apply Subtype.ext
    apply SupercriticalDivision.assignment_injective
    funext v
    rw [D.1.assignment_eq_some_fullAssignment
      (mem_balancedFullSupercriticalDivisions.mp D.2).1,
      E.1.assignment_eq_some_fullAssignment
        (mem_balancedFullSupercriticalDivisions.mp E.2).1]
    exact congrArg some (congrFun hDE v)
  calc
    (balancedFullSupercriticalDivisions k q beta).card =
        Fintype.card
          {D // D ∈ balancedFullSupercriticalDivisions k q beta} := by simp
    _ ≤ Fintype.card (Fin q → Fin (k - 1)) :=
      Fintype.card_le_of_injective label hlabel
    _ = (k - 1) ^ q := by simp

/-- Every full co-multipartite fiber is bounded by the balanced-capacity
binomial slice with the division-independent number of missing edges. -/
theorem card_supercriticalCoPartiteFiber_le_balanced_choose_missing
    {k q m : ℕ} (D : SupercriticalDivision k (Fin q))
    (hfull : D.IsFull) (hm : m ≤ Nat.choose q 2) :
    (supercriticalCoPartiteFiber D m).card ≤
      (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
        (Nat.choose q 2 - m) := by
  have hparts : ∑ i, (D.parts i).card = q := by
    rw [← D.card_support, D.support_eq_univ hfull]
    simp
  have hcross : supercriticalTotalCrossCapacity D ≤
      DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q := by
    rw [supercriticalTotalCrossCapacity_eq_multipartiteCrossCapacity]
    exact DenseGraph.balancedMultipartiteCrossCapacity_max
      (fun i : Fin (k - 1) ↦ (D.parts i).card) hparts
  have htotal := supercriticalTotalCrossCapacity_add_internal D
  rw [D.support_eq_univ hfull] at htotal
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  by_cases hinter : divisionInternalCliqueCapacity D ≤ m
  · rw [card_supercriticalCoPartiteFiber D hfull, if_pos hinter]
    have hselected : m - divisionInternalCliqueCapacity D ≤
        supercriticalTotalCrossCapacity D := by omega
    have hmissing :
        supercriticalTotalCrossCapacity D -
            (m - divisionInternalCliqueCapacity D) =
          Nat.choose q 2 - m := by omega
    rw [← Nat.choose_symm hselected, hmissing]
    exact Nat.choose_le_choose _ hcross
  · rw [card_supercriticalCoPartiteFiber D hfull, if_neg hinter]
    exact Nat.zero_le _

/-- The whole coarse-balanced ordered core-pair mass costs only the number of
full assignments times the single maximal missing-edge slice. -/
theorem card_balancedCoMultipartiteCoverPairFinset_le_pow_mul_choose_missing
    (k q m : ℕ) (beta : ℝ) (hm : m ≤ Nat.choose q 2) :
    (balancedCoMultipartiteCoverPairFinset k q m beta).card ≤
      (k - 1) ^ q *
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
          (Nat.choose q 2 - m) := by
  rw [card_balancedCoMultipartiteCoverPairFinset]
  calc
    (∑ D ∈ balancedFullSupercriticalDivisions k q beta,
        (supercriticalCoPartiteFiber D m).card) ≤
        ∑ _D ∈ balancedFullSupercriticalDivisions k q beta,
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (Nat.choose q 2 - m) := by
      apply Finset.sum_le_sum
      intro D hD
      exact card_supercriticalCoPartiteFiber_le_balanced_choose_missing
        D (mem_balancedFullSupercriticalDivisions.mp hD).1 hm
    _ = (balancedFullSupercriticalDivisions k q beta).card *
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
          (Nat.choose q 2 - m) := by simp
    _ ≤ (k - 1) ^ q *
        (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
          (Nat.choose q 2 - m) :=
      Nat.mul_le_mul_right _
        (card_balancedFullSupercriticalDivisions_le_pow k q beta)

/-- No-Stirling comparison between the coarse core-pair mass and the mass of
one exactly balanced size vector, expressed using the common missing count. -/
theorem card_balancedCoMultipartiteCoverPairFinset_le_succ_pow_mul_multinomial_mul_choose_missing
    {k q m : ℕ} (hk : 3 ≤ k) (beta : ℝ)
    (hm : m ≤ Nat.choose q 2) :
    (balancedCoMultipartiteCoverPairFinset k q m beta).card ≤
      (q + 1) ^ (k - 1) *
        (Nat.multinomial Finset.univ
          (DenseGraph.balancedPartSize (k - 1) q) *
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (Nat.choose q 2 - m)) := by
  have hpow := DenseGraph.pow_le_succ_pow_mul_multinomial_balancedPartSize
    (q := q) (by omega : 0 < k - 1)
  have hslice := card_balancedCoMultipartiteCoverPairFinset_le_pow_mul_choose_missing
    k q m beta hm
  calc
    (balancedCoMultipartiteCoverPairFinset k q m beta).card ≤
        (k - 1) ^ q *
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (Nat.choose q 2 - m) := hslice
    _ ≤ ((q + 1) ^ (k - 1) *
          Nat.multinomial Finset.univ
            (DenseGraph.balancedPartSize (k - 1) q)) *
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (Nat.choose q 2 - m) :=
      Nat.mul_le_mul_right _ hpow
    _ = (q + 1) ^ (k - 1) *
        (Nat.multinomial Finset.univ
          (DenseGraph.balancedPartSize (k - 1) q) *
          (DenseGraph.balancedMultipartiteCrossCapacity (k - 1) q).choose
            (Nat.choose q 2 - m)) := by rw [Nat.mul_assoc]

/-- For a feasible retained edge count, the balanced fiber may equivalently
be written using selected or missing cross coordinates. -/
theorem balanced_choose_missing_eq_selected
    {r q m : ℕ}
    (hlower : DenseGraph.balancedMultipartiteInternalCapacity r q ≤ m)
    (hupper : m ≤ Nat.choose q 2) :
    (DenseGraph.balancedMultipartiteCrossCapacity r q).choose
        (Nat.choose q 2 - m) =
      (DenseGraph.balancedMultipartiteCrossCapacity r q).choose
        (m - DenseGraph.balancedMultipartiteInternalCapacity r q) := by
  have htotal := DenseGraph.balancedCross_add_internal r q
  have hselected :
      m - DenseGraph.balancedMultipartiteInternalCapacity r q ≤
        DenseGraph.balancedMultipartiteCrossCapacity r q := by omega
  have hmissing :
      DenseGraph.balancedMultipartiteCrossCapacity r q -
          (m - DenseGraph.balancedMultipartiteInternalCapacity r q) =
        Nat.choose q 2 - m := by omega
  rw [← hmissing, Nat.choose_symm hselected]

/-- Fixed-support version of the coarse-to-balanced-multinomial comparison.
It is uniform in the prescribed sparse graph and loses only the polynomial
factor `(q+1)^(k-1)`. -/
theorem card_fixedSparseBalancedCleanCoverPairFinset_le_succ_pow_mul_multinomial_mul_choose_missing
    {k n m : ℕ} (hk : 3 ≤ k) (S : Finset (Fin n)) (beta : ℝ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (hm : m ≤ Nat.choose (fixedSparseCoreCard S) 2) :
    (fixedSparseBalancedCleanCoverPairFinset k n S beta m R).card ≤
      (fixedSparseCoreCard S + 1) ^ (k - 1) *
        (Nat.multinomial Finset.univ
          (DenseGraph.balancedPartSize (k - 1) (fixedSparseCoreCard S)) *
          (DenseGraph.balancedMultipartiteCrossCapacity
            (k - 1) (fixedSparseCoreCard S)).choose
              (Nat.choose (fixedSparseCoreCard S) 2 - m)) := by
  exact (card_fixedSparseBalancedCleanCoverPairFinset_le_core
    k n S beta m R).trans
      (card_balancedCoMultipartiteCoverPairFinset_le_succ_pow_mul_multinomial_mul_choose_missing
        hk beta hm)

/-! ## Displayed cover pairs over an arbitrary graph family -/

/-- Pairs `(D,G)` in which `G` belongs to `graphs` and `D` is a zero-defect
ordered division with sparse set exactly `S`. -/
noncomputable def fixedSparseCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) :=
  (criticalFixedSparseCoverDivisions k n S).biUnion fun D ↦
    (graphs.filter fun G ↦ supercriticalDefectGraph G D = ⊥).image
      fun G ↦ (D, G)

@[simp] theorem mem_fixedSparseCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)}
    {graphs : Finset (SimpleGraph (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseCleanCoverPairFinset k n S graphs ↔
      p.1.sparse = S ∧ p.2 ∈ graphs ∧
        supercriticalDefectGraph p.2 p.1 = ⊥ := by
  classical
  constructor
  · intro hp
    rw [fixedSparseCleanCoverPairFinset, Finset.mem_biUnion] at hp
    obtain ⟨D, hD, hp⟩ := hp
    obtain ⟨G, hG, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨mem_criticalFixedSparseCoverDivisions.mp hD,
      (Finset.mem_filter.mp hG).1, (Finset.mem_filter.mp hG).2⟩
  · rintro ⟨hD, hG, hclean⟩
    rw [fixedSparseCleanCoverPairFinset, Finset.mem_biUnion]
    refine ⟨p.1, mem_criticalFixedSparseCoverDivisions.mpr hD, ?_⟩
    exact Finset.mem_image.mpr
      ⟨p.2, Finset.mem_filter.mpr ⟨hG, hclean⟩, Prod.eta p⟩

/-- Exact dependent-sum formula for fixed-sparse clean cover pairs. -/
theorem card_fixedSparseCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :
    (fixedSparseCleanCoverPairFinset k n S graphs).card =
      ∑ D ∈ criticalFixedSparseCoverDivisions k n S,
        (graphs.filter fun G ↦ supercriticalDefectGraph G D = ⊥).card := by
  classical
  rw [fixedSparseCleanCoverPairFinset, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro D _hD
    rw [Finset.card_image_iff.mpr]
    intro G _ H _ h
    exact Prod.mk.inj h |>.2
  · intro D _hD E _hE hDE
    change Disjoint
      ((graphs.filter fun G ↦ supercriticalDefectGraph G D = ⊥).image
        fun G ↦ (D, G))
      ((graphs.filter fun G ↦ supercriticalDefectGraph G E = ⊥).image
        fun G ↦ (E, G))
    rw [Finset.disjoint_left]
    rintro p hpD hpE
    obtain ⟨G, _, rfl⟩ := Finset.mem_image.mp hpD
    obtain ⟨H, _, heq⟩ := Finset.mem_image.mp hpE
    exact hDE (Prod.mk.inj heq.symm).1

/-- Fixed-sparse pairs whose graph has a unique clean cover. -/
noncomputable def fixedSparseUniqueCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :=
  (fixedSparseCleanCoverPairFinset k n S graphs).filter fun p ↦
    HasUniqueFixedSparseCleanCover k S p.2

/-- Fixed-sparse pairs whose graph has more than one unordered clean cover. -/
noncomputable def fixedSparseNonuniqueCleanCoverPairFinset
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :=
  (fixedSparseCleanCoverPairFinset k n S graphs).filter fun p ↦
    ¬ HasUniqueFixedSparseCleanCover k S p.2

@[simp] theorem mem_fixedSparseUniqueCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)}
    {graphs : Finset (SimpleGraph (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseUniqueCleanCoverPairFinset k n S graphs ↔
      p ∈ fixedSparseCleanCoverPairFinset k n S graphs ∧
        HasUniqueFixedSparseCleanCover k S p.2 := by
  simp [fixedSparseUniqueCleanCoverPairFinset]

@[simp] theorem mem_fixedSparseNonuniqueCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)}
    {graphs : Finset (SimpleGraph (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparseNonuniqueCleanCoverPairFinset k n S graphs ↔
      p ∈ fixedSparseCleanCoverPairFinset k n S graphs ∧
        ¬ HasUniqueFixedSparseCleanCover k S p.2 := by
  simp [fixedSparseNonuniqueCleanCoverPairFinset]

/-- Every nonunique fixed-sparse displayed pair has a core graph with a
genuinely nonunique full clique cover. -/
theorem not_uniqueCore_of_mem_fixedSparseNonuniqueCleanCoverPairFinset
    {k n : ℕ} {S : Finset (Fin n)}
    {graphs : Finset (SimpleGraph (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)}
    (hp : p ∈ fixedSparseNonuniqueCleanCoverPairFinset k n S graphs) :
    ¬ HasUniqueCoMultipartiteCover k
      (p.2.induce ({v : Fin n | v ∉ S} : Set (Fin n))) := by
  intro hunique
  obtain ⟨hpair, hnotUnique⟩ :=
    mem_fixedSparseNonuniqueCleanCoverPairFinset.mp hp
  obtain ⟨hsparse, _hgraph, hclean⟩ :=
    mem_fixedSparseCleanCoverPairFinset.mp hpair
  exact hnotUnique
    (hasUniqueFixedSparseCleanCover_of_core hsparse hclean hunique)

/-- Exact unique/nonunique decomposition of the displayed pair mass. -/
theorem card_fixedSparseCleanCoverPairFinset_eq_unique_add_nonunique
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :
    (fixedSparseCleanCoverPairFinset k n S graphs).card =
      (fixedSparseUniqueCleanCoverPairFinset k n S graphs).card +
        (fixedSparseNonuniqueCleanCoverPairFinset k n S graphs).card := by
  classical
  simpa [fixedSparseUniqueCleanCoverPairFinset,
    fixedSparseNonuniqueCleanCoverPairFinset] using
      (Finset.card_filter_add_card_filter_not
        (s := fixedSparseCleanCoverPairFinset k n S graphs)
        (p := fun p ↦ HasUniqueFixedSparseCleanCover k S p.2)).symm

/-- Unique fixed-sparse pairs contribute at most one factorial of ordered
part relabelings per underlying graph. -/
theorem card_fixedSparseUniqueCleanCoverPairFinset_le
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :
    (fixedSparseUniqueCleanCoverPairFinset k n S graphs).card ≤
      (k - 1).factorial * graphs.card := by
  classical
  let uniqueGraphs := graphs.filter (HasUniqueFixedSparseCleanCover k S)
  let target :
      Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) :=
    uniqueGraphs.biUnion fun G ↦
      (fixedSparseCleanCoverDivisionFinset (k := k) S G).image
        fun D ↦ (D, G)
  have hsubset : fixedSparseUniqueCleanCoverPairFinset k n S graphs ⊆
      target := by
    rintro ⟨D, G⟩ hp
    obtain ⟨hpair, hunique⟩ :=
      mem_fixedSparseUniqueCleanCoverPairFinset.mp hp
    obtain ⟨hDsparse, hG, hDclean⟩ :=
      mem_fixedSparseCleanCoverPairFinset.mp hpair
    apply Finset.mem_biUnion.mpr
    refine ⟨G, Finset.mem_filter.mpr ⟨hG, hunique⟩, ?_⟩
    exact Finset.mem_image.mpr
      ⟨D, mem_fixedSparseCleanCoverDivisionFinset.mpr
        ⟨hDsparse, hDclean⟩, rfl⟩
  calc
    (fixedSparseUniqueCleanCoverPairFinset k n S graphs).card ≤
        target.card := Finset.card_le_card hsubset
    _ ≤ ∑ G ∈ uniqueGraphs,
          (fixedSparseCleanCoverDivisionFinset (k := k) S G).card := by
      exact Finset.card_biUnion_le.trans
        (Finset.sum_le_sum fun G _hG ↦ Finset.card_image_le)
    _ ≤ ∑ _G ∈ uniqueGraphs, (k - 1).factorial := by
      apply Finset.sum_le_sum
      intro G hG
      exact card_fixedSparseCleanCoverDivisionFinset_le_factorial_of_unique
        (Finset.mem_filter.mp hG).2
    _ = uniqueGraphs.card * (k - 1).factorial := by simp
    _ ≤ graphs.card * (k - 1).factorial := by
      exact Nat.mul_le_mul_right _
        (Finset.card_le_card (Finset.filter_subset _ _))
    _ = (k - 1).factorial * graphs.card := Nat.mul_comm _ _

/-- Deterministic cover-multiplicity bridge: displayed fixed-sparse pair
mass is bounded by the factorial graph mass plus the explicit nonunique
pair error. -/
theorem card_fixedSparseCleanCoverPairFinset_le_factorial_mul_add_nonunique
    (k n : ℕ) (S : Finset (Fin n))
    (graphs : Finset (SimpleGraph (Fin n))) :
    (fixedSparseCleanCoverPairFinset k n S graphs).card ≤
      (k - 1).factorial * graphs.card +
        (fixedSparseNonuniqueCleanCoverPairFinset k n S graphs).card := by
  rw [card_fixedSparseCleanCoverPairFinset_eq_unique_add_nonunique]
  exact Nat.add_le_add_right
    (card_fixedSparseUniqueCleanCoverPairFinset_le k n S graphs) _

/-! ## Canonical critical clean graphs with fixed sparse set -/

/-- The full canonical clean critical family with prescribed sparse set.
Unlike the fine-balance numerator, no condition is imposed on the main-part
size vector. -/
noncomputable def criticalCanonicalCleanFixedSparseGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  (criticalFixedSparseCoverDivisions k n S).biUnion fun D ↦
    criticalCleanDivisionGraphFinset k hk n tau hn D

@[simp] theorem mem_criticalCanonicalCleanFixedSparseGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {S : Finset (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S ↔
      G ∈ supercriticalCloseGraphFinset k hk (gammaK k)
          (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau ∧
      (canonicalSupercriticalDivision G (by simpa using hn)).sparse = S ∧
      (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0 := by
  classical
  constructor
  · intro hG
    rw [criticalCanonicalCleanFixedSparseGraphFinset,
      Finset.mem_biUnion] at hG
    obtain ⟨D, hD, hG⟩ := hG
    obtain ⟨hclose, hcanonical, hzero⟩ :=
      mem_supercriticalCleanDivisionGraphFinset.mp hG
    exact ⟨hclose, hcanonical ▸
      mem_criticalFixedSparseCoverDivisions.mp hD, hzero⟩
  · rintro ⟨hclose, hsparse, hzero⟩
    rw [criticalCanonicalCleanFixedSparseGraphFinset,
      Finset.mem_biUnion]
    let D := canonicalSupercriticalDivision G (by simpa using hn)
    refine ⟨D, mem_criticalFixedSparseCoverDivisions.mpr hsparse, ?_⟩
    rw [mem_supercriticalCleanDivisionGraphFinset]
    exact ⟨hclose, rfl, hzero⟩

/-- Every graph in the canonical fixed-sparse clean family supplies its
canonical division as a displayed zero-defect cover. -/
theorem criticalCanonicalCleanFixedSparseGraphFinset_card_le_coverPairs
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    (criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S).card ≤
      (fixedSparseCleanCoverPairFinset k n S
        (criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S)).card := by
  classical
  let graphs := criticalCanonicalCleanFixedSparseGraphFinset
    k hk n tau hn S
  let toPair : ↑graphs →
      SupercriticalDivision k (Fin n) × SimpleGraph (Fin n) := fun G ↦
    (canonicalSupercriticalDivision G.1 (by simpa using hn), G.1)
  have hmem : ∀ G : ↑graphs,
      toPair G ∈ fixedSparseCleanCoverPairFinset k n S graphs := by
    intro G
    have hG := mem_criticalCanonicalCleanFixedSparseGraphFinset.mp G.2
    rw [mem_fixedSparseCleanCoverPairFinset]
    refine ⟨hG.2.1, G.2, ?_⟩
    apply simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero
    simpa [canonicalSupercriticalDefectGraph] using hG.2.2
  have hinj : Function.Injective toPair := by
    intro G H h
    apply Subtype.ext
    exact congrArg Prod.snd h
  calc
    graphs.card = Fintype.card ↑graphs := by simp
    _ ≤ Fintype.card
        {p // p ∈ fixedSparseCleanCoverPairFinset k n S graphs} :=
      Fintype.card_le_of_injective
        (fun G ↦ ⟨toPair G, hmem G⟩)
        (fun _ _ h ↦ hinj (congrArg Subtype.val h))
    _ = (fixedSparseCleanCoverPairFinset k n S graphs).card := by simp

/-- Exact canonical-family version of the multiplicity sandwich used in
the critical fine-balance calculation. -/
theorem criticalFixedSparseCanonicalCoverPair_card_le
    (k : ℕ) (hk : 3 ≤ k) (n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (S : Finset (Fin n)) :
    (fixedSparseCleanCoverPairFinset k n S
        (criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S)).card ≤
      (k - 1).factorial *
          (criticalCanonicalCleanFixedSparseGraphFinset
            k hk n tau hn S).card +
        (fixedSparseNonuniqueCleanCoverPairFinset k n S
          (criticalCanonicalCleanFixedSparseGraphFinset
            k hk n tau hn S)).card :=
  card_fixedSparseCleanCoverPairFinset_le_factorial_mul_add_nonunique
    k n S _

/-! ## Canonical sparse-set transfer -/

/-- Convenient fixed-sparse specialization of the deterministic canonical
sparse-set theorem.  This is the support-restriction step needed before the
factorial multiplicity bridge can be applied to a displayed balanced cover. -/
theorem canonical_sparse_eq_of_mem_fixedSparseCover_of_geometry
    {k n : ℕ} (hk : 3 ≤ k) (hn : k - 1 ≤ n)
    {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hD : D ∈ fixedSparseCleanCoverDivisionFinset (k := k) S G)
    (hcanonicalParts : ∀ i : Fin (k - 1),
      2 * S.card <
        ((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card)
    (hdisplayedParts : ∀ i : Fin (k - 1),
      n < k * ((D.parts i).card -
        ((canonicalSupercriticalDivision G (by simpa using hn)).sparse.card + 1))) :
    (canonicalSupercriticalDivision G (by simpa using hn)).sparse = S := by
  obtain ⟨hDsparse, hclean⟩ :=
    mem_fixedSparseCleanCoverDivisionFinset.mp hD
  rw [← hDsparse]
  exact canonicalSupercriticalDivision_sparse_eq_of_clean
    G D hk (by simpa using hn) hclean
      (by simpa [hDsparse] using hcanonicalParts)
      (by simpa only [Fintype.card_fin] using hdisplayedParts)

/-- The graph induced by the sparse set depends only on that set, not on the
main-part labels of the division. -/
theorem sparseInducedGraph_eq_of_sparse_eq
    {k n : ℕ} (G : SimpleGraph (Fin n))
    {D E : SupercriticalDivision k (Fin n)} (h : D.sparse = E.sparse) :
    sparseInducedGraph G D = sparseInducedGraph G E := by
  ext x y
  simp [h]

/-- If a zero-defect displayed division and the canonical minimizer have the
same sparse set, canonical minimality forces the canonical ordinary defect
graph to be empty as well.  Sparse-induced edges cancel from the two costs. -/
theorem canonicalSupercriticalDefectGraph_eq_bot_of_clean_of_sparse_eq
    {k n : ℕ} (G : SimpleGraph (Fin n))
    (hn : k - 1 ≤ n) (D : SupercriticalDivision k (Fin n))
    (hclean : supercriticalDefectGraph G D = ⊥)
    (hsparse :
      (canonicalSupercriticalDivision G (by simpa using hn)).sparse =
        D.sparse) :
    canonicalSupercriticalDefectGraph G (by simpa using hn) = ⊥ := by
  let E := canonicalSupercriticalDivision G (by simpa using hn)
  have hmin := canonicalSupercriticalDivision_minimal G
    (by simpa using hn) D
  have hsparseGraph : sparseInducedGraph G E = sparseInducedGraph G D :=
    sparseInducedGraph_eq_of_sparse_eq G hsparse
  have hzeroDisplayed :
      (finiteGraphEdges (supercriticalDefectGraph G D)).card = 0 := by
    rw [hclean, finiteGraphEdges_card_eq_edgeFinset_card]
    simp
  have hzero : (finiteGraphEdges (supercriticalDefectGraph G E)).card = 0 := by
    have hmin' :
        (finiteGraphEdges (supercriticalDefectGraph G E)).card +
            (finiteGraphEdges (sparseInducedGraph G D)).card ≤
          0 + (finiteGraphEdges (sparseInducedGraph G D)).card := by
      calc
        (finiteGraphEdges (supercriticalDefectGraph G E)).card +
            (finiteGraphEdges (sparseInducedGraph G D)).card =
            supercriticalDefectCost G E := by
              simp only [supercriticalDefectCost]
              rw [hsparseGraph]
        _ ≤ supercriticalDefectCost G D := hmin
        _ = 0 + (finiteGraphEdges (sparseInducedGraph G D)).card := by
          simp only [supercriticalDefectCost, hzeroDisplayed, zero_add]
    exact Nat.eq_zero_of_le_zero
      ((add_le_add_iff_right
        (finiteGraphEdges (sparseInducedGraph G D)).card).mp hmin')
  apply simpleGraph_eq_bot_of_finiteGraphEdges_card_eq_zero
  simpa [canonicalSupercriticalDefectGraph, E] using hzero

/-- A close displayed zero-defect graph satisfying the explicit canonical
sparse-set geometry belongs to the literal canonical fixed-sparse clean
family.  Thus the cover-pair bridge loses neither the close-family condition
nor the canonicality condition. -/
theorem mem_criticalCanonicalCleanFixedSparseGraphFinset_of_displayed
    {k n : ℕ} (hk : 3 ≤ k) (tau : ℝ) (hn : k - 1 ≤ n)
    {S : Finset (Fin n)} {G : SimpleGraph (Fin n)}
    {D : SupercriticalDivision k (Fin n)}
    (hclose : G ∈ supercriticalCloseGraphFinset k hk (gammaK k)
      (gammaK_mem_supercritical_Ico k hk) (criticalEdgeCount k n) n tau)
    (hD : D ∈ fixedSparseCleanCoverDivisionFinset S G)
    (hcanonicalParts : ∀ i : Fin (k - 1),
      2 * S.card <
        ((canonicalSupercriticalDivision G (by simpa using hn)).parts i).card)
    (hdisplayedParts : ∀ i : Fin (k - 1),
      n < k * ((D.parts i).card -
        ((canonicalSupercriticalDivision G (by simpa using hn)).sparse.card + 1))) :
    G ∈ criticalCanonicalCleanFixedSparseGraphFinset k hk n tau hn S := by
  have hsparse := canonical_sparse_eq_of_mem_fixedSparseCover_of_geometry
    hk hn hD hcanonicalParts hdisplayedParts
  have hclean := (mem_fixedSparseCleanCoverDivisionFinset.mp hD).2
  have hcanonicalClean :=
    canonicalSupercriticalDefectGraph_eq_bot_of_clean_of_sparse_eq
      G hn D hclean (by
        simpa [mem_fixedSparseCleanCoverDivisionFinset.mp hD |>.1] using hsparse)
  rw [mem_criticalCanonicalCleanFixedSparseGraphFinset]
  refine ⟨hclose, hsparse, ?_⟩
  rw [hcanonicalClean]
  rw [finiteGraphEdges_card_eq_edgeFinset_card]
  simp

/-! ## Finite subfamily split for the fine-balance transfer -/

/-- Pairs in a displayed subfamily whose underlying graph lies outside a
specified target graph family.  In the critical application the displayed
subfamily is the exactly balanced reference family and the target is the
canonical close, fixed-sparse family; the geometry theorem then sends this
explicit exceptional set into the genuine far family. -/
noncomputable def fixedSparsePairOutsideGraphFamilyFinset
    {k n : ℕ}
    (pairs : Finset
      (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)))
    (graphs : Finset (SimpleGraph (Fin n))) :
    Finset (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)) :=
  pairs.filter fun p ↦ p.2 ∉ graphs

@[simp] theorem mem_fixedSparsePairOutsideGraphFamilyFinset
    {k n : ℕ}
    {pairs : Finset
      (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n))}
    {graphs : Finset (SimpleGraph (Fin n))}
    {p : SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)} :
    p ∈ fixedSparsePairOutsideGraphFamilyFinset pairs graphs ↔
      p ∈ pairs ∧ p.2 ∉ graphs := by
  simp [fixedSparsePairOutsideGraphFamilyFinset]

/-- Exact finite multiplicity split for an arbitrary subfamily of a balanced
fixed-sparse, fixed-remainder displayed-pair family.  This formulation is
deliberately relative to a subfamily: the critical proof applies it to the
exactly balanced reference pairs, while the nonunique error may safely be
bounded by the larger coarse-balanced family. -/
theorem card_fixedSparseBalancedPairSubfamily_le_factorial_mul_add_nonunique_add_outside
    (k n : ℕ) (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (pairs : Finset
      (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)))
    (graphs : Finset (SimpleGraph (Fin n)))
    (hpairs : pairs ⊆
      fixedSparseBalancedCleanCoverPairFinset k n S beta m R) :
    pairs.card ≤
      (k - 1).factorial * graphs.card +
        (fixedSparseBalancedNonuniqueCleanCoverPairFinset
          k n S beta m R).card +
        (fixedSparsePairOutsideGraphFamilyFinset pairs graphs).card := by
  classical
  let uniqueGood := pairs.filter fun p ↦
    HasUniqueFixedSparseCleanCover k S p.2 ∧ p.2 ∈ graphs
  let nonunique := pairs.filter fun p ↦
    ¬ HasUniqueFixedSparseCleanCover k S p.2
  let outside := fixedSparsePairOutsideGraphFamilyFinset pairs graphs
  have hcover : pairs ⊆ uniqueGood ∪ nonunique ∪ outside := by
    intro p hp
    by_cases hu : HasUniqueFixedSparseCleanCover k S p.2
    · by_cases hg : p.2 ∈ graphs
      · exact Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨hp, hu, hg⟩))
      · exact Finset.mem_union_right _
          (mem_fixedSparsePairOutsideGraphFamilyFinset.mpr ⟨hp, hg⟩)
    · exact Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hu⟩))
  have hgoodSubset : uniqueGood ⊆
      fixedSparseUniqueCleanCoverPairFinset k n S graphs := by
    intro p hp
    obtain ⟨hpA, hu, hgraph⟩ := Finset.mem_filter.mp hp
    obtain ⟨hsparse, hclean, _hbalanced, _hcard, _hR⟩ :=
      mem_fixedSparseBalancedCleanCoverPairFinset.mp (hpairs hpA)
    exact mem_fixedSparseUniqueCleanCoverPairFinset.mpr
      ⟨mem_fixedSparseCleanCoverPairFinset.mpr
        ⟨hsparse, hgraph, hclean⟩, hu⟩
  have hnonuniqueSubset : nonunique ⊆
      fixedSparseBalancedNonuniqueCleanCoverPairFinset
        k n S beta m R := by
    intro p hp
    obtain ⟨hpA, hnotUnique⟩ := Finset.mem_filter.mp hp
    exact mem_fixedSparseBalancedNonuniqueCleanCoverPairFinset.mpr
      ⟨hpairs hpA, hnotUnique⟩
  have hcoverCard : pairs.card ≤
      (uniqueGood ∪ nonunique ∪ outside).card :=
    Finset.card_le_card hcover
  have hunionOne := Finset.card_union_le uniqueGood nonunique
  have hunionTwo := Finset.card_union_le (uniqueGood ∪ nonunique) outside
  have hgoodCard : uniqueGood.card ≤ (k - 1).factorial * graphs.card :=
    (Finset.card_le_card hgoodSubset).trans
      (card_fixedSparseUniqueCleanCoverPairFinset_le k n S graphs)
  have hnonuniqueCard : nonunique.card ≤
      (fixedSparseBalancedNonuniqueCleanCoverPairFinset
        k n S beta m R).card :=
    Finset.card_le_card hnonuniqueSubset
  change pairs.card ≤
    (k - 1).factorial * graphs.card +
      (fixedSparseBalancedNonuniqueCleanCoverPairFinset
        k n S beta m R).card + outside.card
  omega

/-- If every outside pair in the selected subfamily has its graph in a
specified exceptional graph family, its pair count costs at most the number
of all ordered divisions, hence at most `k^n`, per exceptional graph. -/
theorem card_fixedSparsePairOutsideGraphFamilyFinset_le_pow_mul
    {k n : ℕ} (hk : 1 ≤ k)
    {pairs : Finset
      (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n))}
    {graphs exceptional : Finset (SimpleGraph (Fin n))}
    (houtside : ∀ p ∈ pairs, p.2 ∉ graphs → p.2 ∈ exceptional) :
    (fixedSparsePairOutsideGraphFamilyFinset pairs graphs).card ≤
      k ^ n * exceptional.card := by
  classical
  have hsubset : fixedSparsePairOutsideGraphFamilyFinset pairs graphs ⊆
      (allSupercriticalDivisions k n).product exceptional := by
    intro p hp
    obtain ⟨hpairs, hnotGraph⟩ :=
      mem_fixedSparsePairOutsideGraphFamilyFinset.mp hp
    exact Finset.mem_product.mpr
      ⟨mem_allSupercriticalDivisions p.1,
        houtside p hpairs hnotGraph⟩
  calc
    (fixedSparsePairOutsideGraphFamilyFinset pairs graphs).card ≤
        ((allSupercriticalDivisions k n).product exceptional).card :=
      Finset.card_le_card hsubset
    _ = (allSupercriticalDivisions k n).card * exceptional.card := by
      exact Finset.card_product _ _
    _ ≤ k ^ n * exceptional.card :=
      Nat.mul_le_mul_right _ (card_allSupercriticalDivisions_le hk)

/-- Finite fixed-support transfer in the form used by the critical proof:
the chosen displayed reference mass is paid for by canonical graphs, the
coarse-balanced nonunique-cover error, and a `k^n` multiple of a certified
exceptional (in practice, far) graph family. -/
theorem card_fixedSparseBalancedPairSubfamily_le_factorial_mul_add_nonunique_add_pow_mul
    (k n : ℕ) (hk : 1 ≤ k)
    (S : Finset (Fin n)) (beta : ℝ) (m : ℕ)
    (R : SimpleGraph ({v : Fin n | v ∈ S} : Set (Fin n)))
    (pairs : Finset
      (SupercriticalDivision k (Fin n) × SimpleGraph (Fin n)))
    (graphs exceptional : Finset (SimpleGraph (Fin n)))
    (hpairs : pairs ⊆
      fixedSparseBalancedCleanCoverPairFinset k n S beta m R)
    (houtside : ∀ p ∈ pairs, p.2 ∉ graphs → p.2 ∈ exceptional) :
    pairs.card ≤
      (k - 1).factorial * graphs.card +
        (fixedSparseBalancedNonuniqueCleanCoverPairFinset
          k n S beta m R).card +
        k ^ n * exceptional.card := by
  exact (card_fixedSparseBalancedPairSubfamily_le_factorial_mul_add_nonunique_add_outside
    k n S beta m R pairs graphs hpairs).trans
      (Nat.add_le_add_left
        (card_fixedSparsePairOutsideGraphFamilyFinset_le_pow_mul hk houtside)
        ((k - 1).factorial * graphs.card +
          (fixedSparseBalancedNonuniqueCleanCoverPairFinset
            k n S beta m R).card))

end InducedStars
