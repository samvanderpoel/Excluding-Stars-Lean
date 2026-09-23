import InducedStars.EdgeColoring.CoreExtraction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Dist
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Colored extremal stability

This file contains the exact extremal family and the unordered-edge Hamming
distance used by the colored stability theorem.
-/

open Finset
open scoped Classical

namespace InducedStars

namespace ColoredGraph

/-! ## Raw unordered-edge Hamming distance -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The color assigned by `C` to an unordered pair.  On diagonal pairs this
uses the project's harmless blue convention; Hamming support below filters
those pairs out. -/
def unorderedPairColor (C : ColoredGraph V) : Sym2 V → EdgeColor :=
  Sym2.lift ⟨fun x y ↦ C.color x y, C.color_comm⟩

omit [Fintype V] in
@[simp]
theorem unorderedPairColor_pair (C : ColoredGraph V) (x y : V) :
    C.unorderedPairColor s(x, y) = C.color x y := by
  simp [unorderedPairColor, Sym2.lift_mk]

/-- The unordered, loop-free edges on which two colorings differ. -/
def coloringHammingSupport (C C' : ColoredGraph V) : Finset (Sym2 V) :=
  (SimpleGraph.edgeFinset (⊤ : SimpleGraph V)).filter fun e ↦
    C.unorderedPairColor e ≠ C'.unorderedPairColor e

/-- The paper's raw edge-Hamming distance.  It is an unnormalized count of
unordered edges, so every edge is counted exactly once. -/
def coloringHammingDistance (C C' : ColoredGraph V) : ℕ :=
  (coloringHammingSupport C C').card

@[simp]
theorem pair_mem_coloringHammingSupport (C C' : ColoredGraph V) (x y : V) :
    s(x, y) ∈ coloringHammingSupport C C' ↔
      x ≠ y ∧ C.color x y ≠ C'.color x y := by
  simp [coloringHammingSupport]

theorem coloringHammingSupport_comm (C C' : ColoredGraph V) :
    coloringHammingSupport C C' = coloringHammingSupport C' C := by
  ext e
  simp only [coloringHammingSupport, Finset.mem_filter]
  exact and_congr_right fun _ ↦ ne_comm

/-- Hamming distance is symmetric. -/
theorem coloringHammingDistance_comm (C C' : ColoredGraph V) :
    coloringHammingDistance C C' = coloringHammingDistance C' C := by
  rw [coloringHammingDistance, coloringHammingDistance,
    coloringHammingSupport_comm]

@[simp]
theorem coloringHammingSupport_self (C : ColoredGraph V) :
    coloringHammingSupport C C = ∅ := by
  simp [coloringHammingSupport]

/-- Equal colorings have Hamming distance zero. -/
@[simp]
theorem coloringHammingDistance_self (C : ColoredGraph V) :
    coloringHammingDistance C C = 0 := by
  simp [coloringHammingDistance]

theorem coloringHammingDistance_eq_zero_of_eq {C C' : ColoredGraph V}
    (h : C = C') : coloringHammingDistance C C' = 0 := by
  subst C'
  exact coloringHammingDistance_self C

/-- Hamming support satisfies the set-theoretic triangle inclusion. -/
theorem coloringHammingSupport_subset_union (C C' C'' : ColoredGraph V) :
    coloringHammingSupport C C'' ⊆
      coloringHammingSupport C C' ∪ coloringHammingSupport C' C'' := by
  intro e he
  have he' : C.unorderedPairColor e ≠ C''.unorderedPairColor e :=
    (Finset.mem_filter.mp he).2
  by_cases h : C.unorderedPairColor e = C'.unorderedPairColor e
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp he).1, by simpa [h] using he'⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, h⟩

/-- Triangle inequality for the raw edge-Hamming distance. -/
theorem coloringHammingDistance_triangle (C C' C'' : ColoredGraph V) :
    coloringHammingDistance C C'' ≤
      coloringHammingDistance C C' + coloringHammingDistance C' C'' := by
  unfold coloringHammingDistance
  exact (Finset.card_le_card (coloringHammingSupport_subset_union C C' C'')).trans
    (Finset.card_union_le _ _)

/-- A specified finite set of unordered edges bounds the Hamming distance
when it contains every edge on which the colorings differ. -/
theorem coloringHammingDistance_le_card_of_support_subset
    (C C' : ColoredGraph V) (S : Finset (Sym2 V))
    (h : coloringHammingSupport C C' ⊆ S) :
    coloringHammingDistance C C' ≤ S.card := by
  exact Finset.card_le_card h

/-- Recoloring only edges from `S` changes the coloring by at most `|S|`.
This is the support-upper-bound form used by the stability proof. -/
theorem coloringHammingDistance_le_card_of_eq_outside
    (C C' : ColoredGraph V) (S : Finset (Sym2 V))
    (h : ∀ e ∈ (SimpleGraph.edgeFinset (⊤ : SimpleGraph V)),
      e ∉ S → C.unorderedPairColor e = C'.unorderedPairColor e) :
    coloringHammingDistance C C' ≤ S.card := by
  apply coloringHammingDistance_le_card_of_support_subset C C' S
  intro e he
  have hedge := (Finset.mem_filter.mp he).1
  by_contra heS
  exact (Finset.mem_filter.mp he).2 (h e hedge heS)

/-- The edges changed when making a coloring all green are exactly its red
and blue edges. -/
theorem coloringHammingSupport_allGreen (C : ColoredGraph V) :
    coloringHammingSupport C (allGreen : ColoredGraph V) =
      C.edgeFinset .red ∪ C.edgeFinset .blue := by
  ext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [pair_mem_coloringHammingSupport, Finset.mem_union,
        C.pair_mem_edgeFinset, C.pair_mem_edgeFinset]
      by_cases hxy : x = y
      · subst y
        simp
      · rw [color_allGreen]
        simp only [hxy, ↓reduceIte]
        cases C.color x y <;> simp

/-- Exact edit count for recoloring all non-green edges green. -/
theorem coloringHammingDistance_allGreen (C : ColoredGraph V) :
    coloringHammingDistance C (allGreen : ColoredGraph V) =
      C.redEdgeCount + C.blueEdgeCount := by
  have hgraph : Disjoint (C.colorGraph .red) (C.colorGraph .blue) :=
    SimpleGraph.EdgeLabeling.pairwise_disjoint_labelGraph (by decide)
  have hedge : Disjoint (C.edgeFinset .red) (C.edgeFinset .blue) :=
    SimpleGraph.disjoint_edgeFinset.mpr hgraph
  rw [coloringHammingDistance, coloringHammingSupport_allGreen,
    Finset.card_union_of_disjoint hedge]
  rfl

/-! ## Exact `Δ`-regular cores -/

/-- A witness that a coloring of `K_n` is one of the paper's exact
`Δ = k - 2` regular cores.

The field `clusterEquitable` is stated for every ordered pair, so its single
inequality also supplies the swapped inequality and is equivalent to the
absolute size difference being at most one.

Paper: Definition `dfn:d-regular-cores`.
-/
structure RegularCoreWitness (k n : ℕ) (C : ColoredGraph (Fin n)) where
  three_le_k : 3 ≤ k
  k_le_n : k ≤ n
  clusterCount : ℕ
  clusterCount_lower : k - 1 ≤ clusterCount
  clusterCount_upper : clusterCount ≤ n
  clusters : Fin clusterCount → Finset (Fin n)
  clusters_nonempty : ∀ i, (clusters i).Nonempty
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  clusters_cover : clusterUnion clusters = Finset.univ
  reducedGraph : SimpleGraph (Fin clusterCount)
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  reducedGraph_connected : reducedGraph.Connected
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  clusterEquitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1
  internalBlue : ∀ i x y,
    x ∈ clusters i → y ∈ clusters i → x ≠ y → C.color x y = .blue
  redBetween : ∀ i j,
    reducedGraph.Adj i j →
      ∀ x ∈ clusters i, ∀ y ∈ clusters j, C.color x y = .red
  greenBetween : ∀ i j,
    i ≠ j → ¬ reducedGraph.Adj i j →
      ∀ x ∈ clusters i, ∀ y ∈ clusters j, C.color x y = .green

/-- Predicate form of an exact `Δ`-regular core. -/
def IsRegularCore (k n : ℕ) (C : ColoredGraph (Fin n)) : Prop :=
  Nonempty (RegularCoreWitness k n C)

/-- The paper's family `ℛ_k(n)` of exact `Δ`-regular cores. -/
def regularCores (k n : ℕ) : Set (ColoredGraph (Fin n)) :=
  {C | IsRegularCore k n C}

@[simp]
theorem mem_regularCores_iff {k n : ℕ} {C : ColoredGraph (Fin n)} :
    C ∈ regularCores k n ↔ IsRegularCore k n C :=
  Iff.rfl

/-! ## The exact global extremal family -/

/-- A witness that an ambient coloring is a vertex-disjoint union of exact
regular cores, with every edge not contained in one core green.  Restriction
to an ambient vertex set uses the canonical injection
`restrictionEmbedding`; this is equivalent to the paper's choice of an
arbitrary injective embedding.

Paper: Definition `dfn:k1k-extremal-fam`.
-/
structure ExtremalFamilyWitness (k n : ℕ) (C : ColoredGraph (Fin n)) where
  coreCount : ℕ
  coreVertices : Fin coreCount → Finset (Fin n)
  coreVertices_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin coreCount)) coreVertices
  coreSize_lower : ∀ i, k ≤ (coreVertices i).card
  coreRegular : ∀ i,
    RegularCoreWitness k (coreVertices i).card
      (C.restrictToFin (coreVertices i))
  offCoreGreen : ∀ x y,
    x ≠ y →
      (∀ i, ¬ (x ∈ coreVertices i ∧ y ∈ coreVertices i)) →
      C.color x y = .green

namespace ExtremalFamilyWitness

/-- The sum of the pairwise-disjoint core sizes is automatically at most the
ambient size, matching the numerical condition in the paper's definition. -/
theorem sum_coreSize_le {k n : ℕ} {C : ColoredGraph (Fin n)}
    (W : ExtremalFamilyWitness k n C) :
    ∑ i, (W.coreVertices i).card ≤ n := by
  simpa using sum_cluster_card_le_card W.coreVertices W.coreVertices_pairwiseDisjoint

end ExtremalFamilyWitness

/-- Predicate form of membership in the exact extremal family. -/
def IsExtremalColoring (k n : ℕ) (C : ColoredGraph (Fin n)) : Prop :=
  Nonempty (ExtremalFamilyWitness k n C)

/-- The paper's extremal family `ℰ_k(n)`. -/
def extremalFamily (k n : ℕ) : Set (ColoredGraph (Fin n)) :=
  {C | IsExtremalColoring k n C}

@[simp]
theorem mem_extremalFamily_iff {k n : ℕ} {C : ColoredGraph (Fin n)} :
    C ∈ extremalFamily k n ↔ IsExtremalColoring k n C :=
  Iff.rfl

/-- The empty collection of cores realizes the all-green coloring.

Paper: the observation immediately following Definition
`dfn:k1k-extremal-fam`.
-/
theorem allGreen_mem_extremalFamily (k n : ℕ) :
    (allGreen : ColoredGraph (Fin n)) ∈ extremalFamily k n := by
  refine ⟨{
    coreCount := 0
    coreVertices := fun i ↦ Fin.elim0 i
    coreVertices_pairwiseDisjoint := ?_
    coreSize_lower := fun i ↦ Fin.elim0 i
    coreRegular := fun i ↦ Fin.elim0 i
    offCoreGreen := ?_ }⟩
  · intro i
    exact Fin.elim0 i
  · intro x y hxy _
    simp [hxy]

/-! ## Labeled equitable repartitioning -/

@[simp]
theorem mem_clusterUnion_iff {V I : Type*} [DecidableEq V]
    [Fintype I] [DecidableEq I] {clusters : I → Finset V} {x : V} :
    x ∈ clusterUnion clusters ↔ ∃ i, x ∈ clusters i := by
  simp [clusterUnion]

/-- A finite set can be partitioned into labeled, pairwise-disjoint pieces
of any prescribed cardinalities whose sum is the cardinality of the set.

The construction uses an equivalence with the finite type of labeled slots.
It is kept private because the stability proof only needs the equitable
specialization below. -/
private theorem exists_labeledPartition_of_sum_card
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (S : Finset V)
    (sizes : Fin q → ℕ) (hsizes : ∑ i, sizes i = S.card) :
    ∃ pieces : Fin q → Finset V,
      Set.PairwiseDisjoint (Set.univ : Set (Fin q)) pieces ∧
      clusterUnion pieces = S ∧
      ∀ i, (pieces i).card = sizes i := by
  classical
  have hcard : Fintype.card S = Fintype.card (Σ i : Fin q, Fin (sizes i)) := by
    simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin]
    exact hsizes.symm
  let allocation : S ≃ (Σ i : Fin q, Fin (sizes i)) :=
    Fintype.equivOfCardEq hcard
  let slot (i : Fin q) : Fin (sizes i) ↪ (Σ i : Fin q, Fin (sizes i)) :=
    @Function.Embedding.sigmaMk (Fin q) (fun j ↦ Fin (sizes j)) i
  let intoS (i : Fin q) : Fin (sizes i) ↪ S :=
    (slot i).trans allocation.symm.toEmbedding
  let intoV (i : Fin q) : Fin (sizes i) ↪ V :=
    (intoS i).trans (Function.Embedding.subtype _)
  let pieces : Fin q → Finset V := fun i ↦
    (Finset.univ : Finset (Fin (sizes i))).map (intoV i)
  refine ⟨pieces, ?_, ?_, ?_⟩
  · intro i _ j _ hij
    change Disjoint (pieces i) (pieces j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_map] at hxi hxj
    obtain ⟨a, _, ha⟩ := hxi
    obtain ⟨b, _, hb⟩ := hxj
    have habV : intoV i a = intoV j b := ha.trans hb.symm
    have habS : intoS i a = intoS j b := by
      apply Subtype.ext
      exact habV
    have habSigma : slot i a = slot j b := allocation.symm.injective habS
    exact hij (congrArg Sigma.fst habSigma)
  · ext x
    constructor
    · intro hx
      rw [clusterUnion, Finset.mem_biUnion] at hx
      obtain ⟨i, _, hi⟩ := hx
      rw [Finset.mem_map] at hi
      obtain ⟨a, _, rfl⟩ := hi
      exact (intoS i a).property
    · intro hx
      let xS : S := ⟨x, hx⟩
      rw [clusterUnion, Finset.mem_biUnion]
      refine ⟨(allocation xS).1, Finset.mem_univ _,
        Finset.mem_map.mpr ⟨(allocation xS).2,
          Finset.mem_univ (allocation xS).2, ?_⟩⟩
      have hback : allocation.symm (allocation xS) = xS :=
        allocation.symm_apply_apply xS
      change ((allocation.symm (allocation xS) : S) : V) = x
      exact congrArg Subtype.val hback
  · intro i
    simp [pieces]

/-- Repartition nonempty labeled parts into equitable labeled parts without
changing their union.  If every two old part sizes have natural distance at
most `e`, then at most `q * e` vertices change their label.

The moved set records a vertex once, under its old label.  The construction
keeps `min |A_i| target_i` vertices in every old part and redistributes only
the remaining surplus. -/
theorem exists_equitableRepartition
    {V : Type*} [Fintype V] [DecidableEq V] {q e : ℕ} (hq : 0 < q)
    (parts : Fin q → Finset V)
    (hnonempty : ∀ i, (parts i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) parts)
    (hclose : ∀ i j, Nat.dist (parts i).card (parts j).card ≤ e) :
    ∃ balanced : Fin q → Finset V,
      (∀ i, (balanced i).Nonempty) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin q)) balanced ∧
      clusterUnion balanced = clusterUnion parts ∧
      Set.EquitableOn (Set.univ : Set (Fin q))
        (fun i ↦ (balanced i).card) ∧
      (clusterUnion fun i ↦ parts i \ balanced i).card ≤ q * e := by
  classical
  let S : Finset V := clusterUnion parts
  let base : ℕ := S.card / q
  let extra : ℕ := S.card % q
  have hextra : extra < q := by
    dsimp only [extra]
    exact Nat.mod_lt _ hq
  let large : Finset (Fin q) := Finset.Iio ⟨extra, hextra⟩
  let target : Fin q → ℕ := fun i ↦ if i ∈ large then base + 1 else base
  have hlargeCard : large.card = extra := by
    simp [large]
  have htargetSum : ∑ i, target i = S.card := by
    calc
      ∑ i, target i = ∑ i, (base + if i ∈ large then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ large <;> simp [target, hi]
      _ = q * base + large.card := by simp [Finset.sum_add_distrib]
      _ = S.card := by
        rw [hlargeCard]
        dsimp only [base, extra]
        simpa [Nat.add_comm] using (Nat.mod_add_div S.card q)
  have hpartsCard : S.card = ∑ i, (parts i).card := by
    simpa only [S] using (card_clusterUnion parts hdisj)
  have hunivNonempty : (Finset.univ : Finset (Fin q)).Nonempty := by
    exact ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  obtain ⟨imin, _, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin q))
      (fun i ↦ (parts i).card) hunivNonempty
  have hminBase : (parts imin).card ≤ base := by
    apply (Nat.le_div_iff_mul_le hq).2
    rw [hpartsCard]
    calc
      (parts imin).card * q = ∑ _i : Fin q, (parts imin).card := by
        simp [mul_comm]
      _ ≤ ∑ i : Fin q, (parts i).card := by
        exact Finset.sum_le_sum fun i _ ↦ hmin i (Finset.mem_univ i)
  have htargetMin (i : Fin q) : (parts imin).card ≤ target i := by
    dsimp only [target]
    split <;> omega
  have hpartMinusMin (i : Fin q) :
      (parts i).card - (parts imin).card ≤ e := by
    have hle := hmin i (Finset.mem_univ i)
    simpa [Nat.dist_eq_sub_of_le hle] using hclose imin i
  let keepSize : Fin q → ℕ := fun i ↦ min (parts i).card (target i)
  have hkeepSizePart (i : Fin q) : keepSize i ≤ (parts i).card := by
    exact Nat.min_le_left _ _
  choose kept hkeptSubset hkeptCard using fun i ↦
    Finset.exists_subset_card_eq (hkeepSizePart i)
  have hkeptDisj :
      Set.PairwiseDisjoint (Set.univ : Set (Fin q)) kept := by
    intro i _ j _ hij
    exact (hdisj (Set.mem_univ i) (Set.mem_univ j) hij).mono
      (hkeptSubset i) (hkeptSubset j)
  let keptUnion : Finset V := clusterUnion kept
  have hkeptUnionSubset : keptUnion ⊆ S := by
    intro x hx
    change x ∈ clusterUnion kept at hx
    rw [mem_clusterUnion_iff] at hx
    change x ∈ clusterUnion parts
    rw [mem_clusterUnion_iff]
    obtain ⟨i, hxi⟩ := hx
    exact ⟨i, hkeptSubset i hxi⟩
  have hkeptUnionCard : keptUnion.card = ∑ i, keepSize i := by
    rw [card_clusterUnion kept hkeptDisj]
    exact Finset.sum_congr rfl fun i _ ↦ hkeptCard i
  let pool : Finset V := S \ keptUnion
  let deficit : Fin q → ℕ := fun i ↦ target i - keepSize i
  have hkeepSizeTarget (i : Fin q) : keepSize i ≤ target i := by
    exact Nat.min_le_right _ _
  have hdeficitSum : ∑ i, deficit i = pool.card := by
    rw [show (∑ i, deficit i) =
        (∑ i, target i) - ∑ i, keepSize i by
      exact Finset.sum_tsub_distrib Finset.univ
        (fun i _ ↦ hkeepSizeTarget i)]
    rw [htargetSum, ← hkeptUnionCard]
    simpa only [pool] using
      (Finset.card_sdiff_of_subset hkeptUnionSubset).symm
  obtain ⟨added, haddDisj, haddUnion, haddCard⟩ :=
    exists_labeledPartition_of_sum_card pool deficit hdeficitSum
  have haddSubsetPool (i : Fin q) : added i ⊆ pool := by
    intro x hx
    rw [← haddUnion, clusterUnion, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ _, hx⟩
  have hkeptAdded (i j : Fin q) : Disjoint (kept i) (added j) := by
    rw [Finset.disjoint_left]
    intro x hxK hxA
    have hxKU : x ∈ keptUnion := by
      change x ∈ clusterUnion kept
      rw [mem_clusterUnion_iff]
      exact ⟨i, hxK⟩
    have hxPool := haddSubsetPool j hxA
    exact (Finset.mem_sdiff.mp hxPool).2 hxKU
  let balanced : Fin q → Finset V := fun i ↦ kept i ∪ added i
  have hbalancedCard (i : Fin q) : (balanced i).card = target i := by
    rw [show balanced i = kept i ∪ added i by rfl,
      Finset.card_union_of_disjoint (hkeptAdded i i), hkeptCard i,
      haddCard i]
    dsimp only [deficit]
    exact Nat.add_sub_of_le (hkeepSizeTarget i)
  have hbasePos : 0 < base := by
    apply Nat.div_pos (b := q)
    · rw [hpartsCard]
      calc
        q = ∑ _i : Fin q, 1 := by simp
        _ ≤ ∑ i : Fin q, (parts i).card := by
          exact Finset.sum_le_sum fun i _ ↦ (Finset.card_pos.mpr (hnonempty i))
    · exact hq
  refine ⟨balanced, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply Finset.card_pos.mp
    rw [hbalancedCard]
    dsimp only [target]
    split <;> omega
  · intro i _ j _ hij
    change Disjoint (balanced i) (balanced j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    rw [Finset.mem_union] at hxi hxj
    rcases hxi with hxi | hxi <;> rcases hxj with hxj | hxj
    · exact Finset.disjoint_left.mp
        (hkeptDisj (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxj
    · exact Finset.disjoint_left.mp (hkeptAdded i j) hxi hxj
    · exact Finset.disjoint_left.mp (hkeptAdded j i) hxj hxi
    · exact Finset.disjoint_left.mp
        (haddDisj (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxj
  · calc
      clusterUnion balanced = keptUnion ∪ clusterUnion added := by
        ext x
        constructor
        · intro hx
          rw [mem_clusterUnion_iff] at hx
          obtain ⟨i, hxi⟩ := hx
          rw [Finset.mem_union] at hxi ⊢
          rcases hxi with hxi | hxi
          · left
            change x ∈ clusterUnion kept
            rw [mem_clusterUnion_iff]
            exact ⟨i, hxi⟩
          · right
            rw [mem_clusterUnion_iff]
            exact ⟨i, hxi⟩
        · intro hx
          rw [Finset.mem_union] at hx
          rw [mem_clusterUnion_iff]
          rcases hx with hx | hx
          · change x ∈ clusterUnion kept at hx
            rw [mem_clusterUnion_iff] at hx
            obtain ⟨i, hxi⟩ := hx
            exact ⟨i, Finset.mem_union_left _ hxi⟩
          · rw [mem_clusterUnion_iff] at hx
            obtain ⟨i, hxi⟩ := hx
            exact ⟨i, Finset.mem_union_right _ hxi⟩
      _ = keptUnion ∪ pool := by rw [haddUnion]
      _ = S := Finset.union_sdiff_of_subset hkeptUnionSubset
      _ = clusterUnion parts := rfl
  · intro i j _ _
    change (balanced i).card ≤ (balanced j).card + 1
    rw [hbalancedCard i, hbalancedCard j]
    dsimp only [target]
    split <;> split <;> omega
  · have hmovedDisj :
        Set.PairwiseDisjoint (Set.univ : Set (Fin q))
          (fun i ↦ parts i \ balanced i) := by
      intro i _ j _ hij
      exact (hdisj (Set.mem_univ i) (Set.mem_univ j) hij).mono
        Finset.sdiff_subset Finset.sdiff_subset
    rw [card_clusterUnion _ hmovedDisj]
    calc
      ∑ i, (parts i \ balanced i).card ≤
          ∑ _i : Fin q, e := by
        exact Finset.sum_le_sum fun i _ ↦ by
          have hsub : parts i \ balanced i ⊆ parts i \ kept i := by
            intro x hx
            rw [Finset.mem_sdiff] at hx ⊢
            refine ⟨hx.1, fun hxK ↦ hx.2 ?_⟩
            exact Finset.mem_union_left _ hxK
          have hkeepMin : (parts imin).card ≤ keepSize i := by
            dsimp only [keepSize]
            rw [Nat.le_min]
            exact ⟨hmin i (Finset.mem_univ i), htargetMin i⟩
          calc
            (parts i \ balanced i).card ≤ (parts i \ kept i).card :=
              Finset.card_le_card hsub
            _ = (parts i).card - keepSize i := by
              rw [Finset.card_sdiff_of_subset (hkeptSubset i), hkeptCard i]
            _ ≤ (parts i).card - (parts imin).card := by omega
            _ ≤ e := hpartMinusMin i
      _ = q * e := by simp

/-! ## Finite connected components and canonical relabeling -/

/-- The vertices in a connected component, as a finset of ambient vertices. -/
noncomputable def connectedComponentSupport
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (q : G.ConnectedComponent) : Finset V := by
  classical
  exact q.supp.toFinset

@[simp]
theorem mem_connectedComponentSupport
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (q : G.ConnectedComponent) (v : V) :
    v ∈ connectedComponentSupport q ↔ v ∈ q.supp := by
  classical
  simp [connectedComponentSupport]

theorem connectedComponentSupport_nonempty
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (q : G.ConnectedComponent) :
    (connectedComponentSupport q).Nonempty := by
  obtain ⟨v, hv⟩ := q.nonempty_supp
  exact ⟨v, (mem_connectedComponentSupport q v).2 hv⟩

/-- Distinct connected components have disjoint finite supports. -/
theorem connectedComponentSupport_pairwiseDisjoint
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    Set.PairwiseDisjoint (Set.univ : Set G.ConnectedComponent)
      (connectedComponentSupport (G := G)) := by
  classical
  intro q _ r _ hqr
  change Disjoint (connectedComponentSupport q) (connectedComponentSupport r)
  rw [Finset.disjoint_left]
  intro v hvq hvr
  exact Set.disjoint_left.mp
    (G.pairwise_disjoint_supp_connectedComponent hqr)
    ((mem_connectedComponentSupport q v).mp hvq)
    ((mem_connectedComponentSupport r v).mp hvr)

/-- The finite supports of all connected components partition the vertex set. -/
theorem clusterUnion_connectedComponentSupport
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableEq G.ConnectedComponent] :
    clusterUnion (connectedComponentSupport (G := G)) =
      (Finset.univ : Finset V) := by
  classical
  ext v
  rw [mem_clusterUnion_iff]
  simp [mem_connectedComponentSupport]

/-- The component-induced graph is connected.  This names the exact Mathlib
fact in the vocabulary used by the stability assembly. -/
theorem connectedComponent_toSimpleGraph_connected
    {V : Type*} {G : SimpleGraph V} (q : G.ConnectedComponent) :
    q.toSimpleGraph.Connected :=
  q.connected_toSimpleGraph

/-- The neighbor set of a vertex in its component graph is equivalent to its
full neighbor set in the ambient graph. -/
private def connectedComponentNeighborEquiv
    {V : Type*} {G : SimpleGraph V} (q : G.ConnectedComponent) (v : q) :
    q.toSimpleGraph.neighborSet v ≃ G.neighborSet (v : V) where
  toFun w :=
    ⟨w.1.1, (q.toSimpleGraph_adj v.property w.1.property).mp w.property⟩
  invFun w := by
    have hwq : (w.1 : V) ∈ q :=
      q.mem_supp_of_adj_mem_supp v.property w.property
    exact ⟨⟨w.1, hwq⟩,
      (q.toSimpleGraph_adj v.property hwq).mpr w.property⟩
  left_inv w := by ext; rfl
  right_inv w := by ext; rfl

/-- Inducing a finite regular graph on one connected component preserves the
exact degree.  The explicit local instances make the induced degree
normalization independent of instance synthesis. -/
theorem connectedComponent_toSimpleGraph_isRegularOfDegree
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (q : G.ConnectedComponent) [Fintype q]
    [DecidableRel q.toSimpleGraph.Adj] {d : ℕ}
    (hG : G.IsRegularOfDegree d) :
    q.toSimpleGraph.IsRegularOfDegree d := by
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree,
    Fintype.card_congr (connectedComponentNeighborEquiv q v),
    SimpleGraph.card_neighborSet_eq_degree, hG v]

/-- Canonically relabel a finite connected component by
`Fin (Nat.card q)`. -/
noncomputable def connectedComponentRelabel
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (q : G.ConnectedComponent) : SimpleGraph (Fin (Nat.card q)) :=
  q.toSimpleGraph.comap (Finite.equivFin q).symm

noncomputable instance connectedComponentRelabelAdjDecidable
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (q : G.ConnectedComponent) :
    DecidableRel (connectedComponentRelabel q).Adj := by
  intro i j
  change Decidable (G.Adj _ _)
  infer_instance

/-- The canonical relabeling is graph-isomorphic to the component graph. -/
noncomputable def connectedComponentRelabelIso
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (q : G.ConnectedComponent) :
    connectedComponentRelabel q ≃g q.toSimpleGraph :=
  SimpleGraph.Iso.comap (Finite.equivFin q).symm q.toSimpleGraph

theorem connectedComponentRelabel_connected
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (q : G.ConnectedComponent) :
    (connectedComponentRelabel q).Connected :=
  (connectedComponentRelabelIso q).connected_iff.mpr
    q.connected_toSimpleGraph

/-- Canonical relabeling preserves the exact regular degree. -/
theorem connectedComponentRelabel_isRegularOfDegree
    {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (q : G.ConnectedComponent) {d : ℕ}
    (hG : G.IsRegularOfDegree d) :
    (connectedComponentRelabel q).IsRegularOfDegree d := by
  classical
  letI : Fintype q := Fintype.ofFinite q
  letI : DecidableRel q.toSimpleGraph.Adj := Classical.decRel _
  have hq := connectedComponent_toSimpleGraph_isRegularOfDegree q hG
  intro v
  exact ((connectedComponentRelabelIso q).degree_eq v).symm.trans
    (hq (connectedComponentRelabelIso q v))

/-!
Construction-friendly, color-free shapes for exact extremal colorings.
These shapes support the componentwise assembly used by the outer iteration.
-/

/-- The combinatorial shape of one exact regular core, embedded in an
ambient vertex type but independent of any coloring. -/
structure RegularCoreShape (k : ℕ) (V : Type*) where
  support : Finset V
  coreSize_lower : k ≤ support.card
  clusterCount : ℕ
  clusterCount_lower : k - 1 ≤ clusterCount
  clusterCount_upper : clusterCount ≤ support.card
  clusters : Fin clusterCount → Finset V
  clusters_nonempty : ∀ i, (clusters i).Nonempty
  clusters_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin clusterCount)) clusters
  clusters_cover : ∀ x, x ∈ support ↔ ∃ i, x ∈ clusters i
  reducedGraph : SimpleGraph (Fin clusterCount)
  reducedGraphAdjDecidable : DecidableRel reducedGraph.Adj
  reducedGraph_connected : reducedGraph.Connected
  reducedGraph_regular :
    letI := reducedGraphAdjDecidable
    ∀ i, reducedGraph.degree i = delta k
  clusterEquitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1

namespace RegularCoreShape

variable {k : ℕ} {V W : Type*}

theorem cluster_subset_support (S : RegularCoreShape k V) (i) :
    S.clusters i ⊆ S.support := by
  intro x hx
  exact (S.clusters_cover x).2 ⟨i, hx⟩

theorem cluster_eq_of_mem (S : RegularCoreShape k V) {i j}
    {x : V} (hxi : x ∈ S.clusters i) (hxj : x ∈ S.clusters j) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp
    (S.clusters_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxj

/-- Push a core shape forward along an injective ambient vertex map. -/
def map (S : RegularCoreShape k V) (f : V ↪ W) : RegularCoreShape k W where
  support := S.support.map f
  coreSize_lower := by simpa using S.coreSize_lower
  clusterCount := S.clusterCount
  clusterCount_lower := S.clusterCount_lower
  clusterCount_upper := by simpa using S.clusterCount_upper
  clusters := fun i ↦ (S.clusters i).map f
  clusters_nonempty := by
    intro i
    obtain ⟨x, hx⟩ := S.clusters_nonempty i
    exact ⟨f x, Finset.mem_map.mpr ⟨x, hx, rfl⟩⟩
  clusters_pairwiseDisjoint := by
    intro i _ j _ hij
    change Disjoint ((S.clusters i).map f) ((S.clusters j).map f)
    rw [Finset.disjoint_left]
    intro y hyi hyj
    obtain ⟨x, hxi, rfl⟩ := Finset.mem_map.mp hyi
    obtain ⟨z, hzj, hxz⟩ := Finset.mem_map.mp hyj
    have : x = z := f.injective hxz.symm
    subst z
    exact Finset.disjoint_left.mp
      (S.clusters_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hxi hzj
  clusters_cover := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
      obtain ⟨i, hxi⟩ := (S.clusters_cover x).1 hx
      exact ⟨i, Finset.mem_map.mpr ⟨x, hxi, rfl⟩⟩
    · rintro ⟨i, hyi⟩
      obtain ⟨x, hxi, rfl⟩ := Finset.mem_map.mp hyi
      exact Finset.mem_map.mpr ⟨x, (S.clusters_cover x).2 ⟨i, hxi⟩, rfl⟩
  reducedGraph := S.reducedGraph
  reducedGraphAdjDecidable := S.reducedGraphAdjDecidable
  reducedGraph_connected := S.reducedGraph_connected
  reducedGraph_regular := S.reducedGraph_regular
  clusterEquitable := by simpa using S.clusterEquitable

end RegularCoreShape

/-- A finite pairwise-disjoint family of embedded regular-core shapes. -/
structure ExtremalFamilyShape (k : ℕ) (V : Type*) where
  shapeCount : ℕ
  shapes : Fin shapeCount → RegularCoreShape k V
  supports_pairwiseDisjoint :
    Set.PairwiseDisjoint (Set.univ : Set (Fin shapeCount))
      (fun a ↦ (shapes a).support)

namespace ExtremalFamilyShape

variable {k : ℕ} {V W : Type*}

/-- Two shapes containing the same vertex have the same family index. -/
theorem shape_eq_of_mem_support (E : ExtremalFamilyShape k V) {a b}
    {x : V} (hxa : x ∈ (E.shapes a).support)
    (hxb : x ∈ (E.shapes b).support) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp
    (E.supports_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab) hxa hxb

/-- The two vertices lie in a common cluster of a common shape. -/
def BluePair (E : ExtremalFamilyShape k V) (x y : V) : Prop :=
  ∃ a i, x ∈ (E.shapes a).clusters i ∧ y ∈ (E.shapes a).clusters i

/-- The two vertices lie in skeleton-adjacent clusters of a common shape. -/
def RedPair (E : ExtremalFamilyShape k V) (x y : V) : Prop :=
  ∃ a i j, (E.shapes a).reducedGraph.Adj i j ∧
    x ∈ (E.shapes a).clusters i ∧ y ∈ (E.shapes a).clusters j

theorem bluePair_comm (E : ExtremalFamilyShape k V) (x y : V) :
    E.BluePair x y ↔ E.BluePair y x := by
  constructor <;> rintro ⟨a, i, hx, hy⟩ <;> exact ⟨a, i, hy, hx⟩

theorem redPair_comm (E : ExtremalFamilyShape k V) (x y : V) :
    E.RedPair x y ↔ E.RedPair y x := by
  constructor
  · rintro ⟨a, i, j, hij, hx, hy⟩
    exact ⟨a, j, i, hij.symm, hy, hx⟩
  · rintro ⟨a, i, j, hij, hy, hx⟩
    exact ⟨a, j, i, hij.symm, hx, hy⟩

/-- The canonical exact coloring determined by a family shape: blue within
clusters, red across skeleton edges, and green everywhere else. -/
noncomputable def canonicalColoring (E : ExtremalFamilyShape k V) : ColoredGraph V :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if E.BluePair x y then .blue else if E.RedPair x y then .red else .green)
    (by
      intro x y _
      rw [E.bluePair_comm x y, E.redPair_comm x y])

theorem canonicalColoring_color_of_ne [DecidableEq V]
    (E : ExtremalFamilyShape k V) {x y : V} (hxy : x ≠ y) :
    E.canonicalColoring.color x y =
      if E.BluePair x y then .blue else if E.RedPair x y then .red else .green := by
  rw [ColoredGraph.color_eq_get _ hxy]
  exact SimpleGraph.EdgeLabeling.get_mk _ _ _ _ _

theorem redWitness_not_bluePair (E : ExtremalFamilyShape k V)
    {a} {i j : Fin (E.shapes a).clusterCount} {x y : V}
    (hij : (E.shapes a).reducedGraph.Adj i j)
    (hxi : x ∈ (E.shapes a).clusters i)
    (hyj : y ∈ (E.shapes a).clusters j) : ¬ E.BluePair x y := by
  rintro ⟨b, h, hxh, hyh⟩
  have hab : a = b := E.shape_eq_of_mem_support
    ((E.shapes a).cluster_subset_support i hxi)
    ((E.shapes b).cluster_subset_support h hxh)
  subst b
  have hih : i = h := (E.shapes a).cluster_eq_of_mem hxi hxh
  have hjh : j = h := (E.shapes a).cluster_eq_of_mem hyj hyh
  subst i
  subst j
  exact (E.shapes a).reducedGraph.loopless.irrefl h hij

theorem redWitness_ne (E : ExtremalFamilyShape k V)
    {a} {i j : Fin (E.shapes a).clusterCount} {x y : V}
    (hij : (E.shapes a).reducedGraph.Adj i j)
    (hxi : x ∈ (E.shapes a).clusters i)
    (hyj : y ∈ (E.shapes a).clusters j) : x ≠ y := by
  intro hxy
  subst y
  have : i = j := (E.shapes a).cluster_eq_of_mem hxi hyj
  subst j
  exact (E.shapes a).reducedGraph.loopless.irrefl i hij

/-- Exact blue color within every shape cluster. -/
theorem canonicalColoring_blue [DecidableEq V]
    (E : ExtremalFamilyShape k V) (a) (i : Fin (E.shapes a).clusterCount)
    {x y : V} (hx : x ∈ (E.shapes a).clusters i)
    (hy : y ∈ (E.shapes a).clusters i) :
    E.canonicalColoring.color x y = .blue := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [E.canonicalColoring_color_of_ne hxy, if_pos]
    exact ⟨a, i, hx, hy⟩

/-- Exact red color across every skeleton edge. -/
theorem canonicalColoring_red [DecidableEq V]
    (E : ExtremalFamilyShape k V) (a) {i j : Fin (E.shapes a).clusterCount}
    (hij : (E.shapes a).reducedGraph.Adj i j)
    {x y : V} (hx : x ∈ (E.shapes a).clusters i)
    (hy : y ∈ (E.shapes a).clusters j) :
    E.canonicalColoring.color x y = .red := by
  rw [E.canonicalColoring_color_of_ne (E.redWitness_ne hij hx hy),
    if_neg (E.redWitness_not_bluePair hij hx hy), if_pos]
  exact ⟨a, i, j, hij, hx, hy⟩

/-- Exact green color across a nonedge of a shape skeleton. -/
theorem canonicalColoring_green_nonedge [DecidableEq V]
    (E : ExtremalFamilyShape k V) (a) {i j : Fin (E.shapes a).clusterCount}
    (hij : i ≠ j) (hnadj : ¬ (E.shapes a).reducedGraph.Adj i j)
    {x y : V} (hx : x ∈ (E.shapes a).clusters i)
    (hy : y ∈ (E.shapes a).clusters j) :
    E.canonicalColoring.color x y = .green := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hij ((E.shapes a).cluster_eq_of_mem hx hy)
  rw [E.canonicalColoring_color_of_ne hxy, if_neg, if_neg]
  · rintro ⟨b, p, q, hpq, hxp, hyq⟩
    have hab : a = b := E.shape_eq_of_mem_support
      ((E.shapes a).cluster_subset_support i hx)
      ((E.shapes b).cluster_subset_support p hxp)
    subst b
    have hip : i = p := (E.shapes a).cluster_eq_of_mem hx hxp
    have hjq : j = q := (E.shapes a).cluster_eq_of_mem hy hyq
    subst p
    subst q
    exact hnadj hpq
  · rintro ⟨b, p, hxp, hyp⟩
    have hab : a = b := E.shape_eq_of_mem_support
      ((E.shapes a).cluster_subset_support i hx)
      ((E.shapes b).cluster_subset_support p hxp)
    subst b
    have hip : i = p := (E.shapes a).cluster_eq_of_mem hx hxp
    have hjp : j = p := (E.shapes a).cluster_eq_of_mem hy hyp
    exact hij (hip.trans hjp.symm)

/-- Every off-diagonal pair not contained in one shape support is green. -/
theorem canonicalColoring_green_of_no_common_support [DecidableEq V]
    (E : ExtremalFamilyShape k V) {x y : V} (hxy : x ≠ y)
    (hout : ∀ a, ¬ (x ∈ (E.shapes a).support ∧ y ∈ (E.shapes a).support)) :
    E.canonicalColoring.color x y = .green := by
  rw [E.canonicalColoring_color_of_ne hxy, if_neg, if_neg]
  · rintro ⟨a, i, j, _, hxi, hyj⟩
    exact hout a ⟨(E.shapes a).cluster_subset_support i hxi,
      (E.shapes a).cluster_subset_support j hyj⟩
  · rintro ⟨a, i, hxi, hyi⟩
    exact hout a ⟨(E.shapes a).cluster_subset_support i hxi,
      (E.shapes a).cluster_subset_support i hyi⟩

/-- In particular, distinct core shapes are green-adjacent. -/
theorem canonicalColoring_green_between_shapes [DecidableEq V]
    (E : ExtremalFamilyShape k V) {a b} (hab : a ≠ b)
    {x y : V} (hx : x ∈ (E.shapes a).support)
    (hy : y ∈ (E.shapes b).support) :
    E.canonicalColoring.color x y = .green := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hab (E.shape_eq_of_mem_support hx hy)
  apply E.canonicalColoring_green_of_no_common_support hxy
  intro c hboth
  have hac : a = c := E.shape_eq_of_mem_support hx hboth.1
  have hbc : b = c := E.shape_eq_of_mem_support hy hboth.2
  exact hab (hac.trans hbc.symm)

/-! Pulling a shape's partition back through `restrictionEmbedding`. -/

noncomputable def pulledCluster (S : RegularCoreShape k V)
    (i : Fin S.clusterCount) : Finset (Fin S.support.card) :=
  (S.clusters i).preimage (restrictionEmbedding S.support)
    (restrictionEmbedding S.support).injective.injOn

@[simp]
theorem mem_pulledCluster (S : RegularCoreShape k V)
    (i : Fin S.clusterCount) (u : Fin S.support.card) :
    u ∈ pulledCluster S i ↔ restrictionEmbedding S.support u ∈ S.clusters i := by
  simp [pulledCluster]

theorem card_pulledCluster [DecidableEq V] (S : RegularCoreShape k V)
    (i : Fin S.clusterCount) :
    (pulledCluster S i).card = (S.clusters i).card := by
  classical
  apply Finset.card_bij
      (fun u _ ↦ restrictionEmbedding S.support u)
  · intro u hu
    simpa using hu
  · intro u _ v _ huv
    exact (restrictionEmbedding S.support).injective huv
  · intro x hx
    obtain ⟨u, hu⟩ := restrictionEmbedding_surjectiveOn S.support
      (S.cluster_subset_support i hx)
    refine ⟨u, ?_, hu⟩
    simpa [hu] using hx

/-- The canonical restriction to one shape support is an existing
`RegularCoreWitness`. -/
noncomputable def canonicalRegularCoreWitness [Fintype V] [DecidableEq V]
    (E : ExtremalFamilyShape k V) (hk : 3 ≤ k) (a : Fin E.shapeCount) :
    RegularCoreWitness k (E.shapes a).support.card
      (E.canonicalColoring.restrictToFin (E.shapes a).support) := by
  let S := E.shapes a
  refine {
    three_le_k := hk
    k_le_n := S.coreSize_lower
    clusterCount := S.clusterCount
    clusterCount_lower := S.clusterCount_lower
    clusterCount_upper := S.clusterCount_upper
    clusters := pulledCluster S
    clusters_nonempty := ?_
    clusters_pairwiseDisjoint := ?_
    clusters_cover := ?_
    reducedGraph := S.reducedGraph
    reducedGraphAdjDecidable := S.reducedGraphAdjDecidable
    reducedGraph_connected := S.reducedGraph_connected
    reducedGraph_regular := S.reducedGraph_regular
    clusterEquitable := ?_
    internalBlue := ?_
    redBetween := ?_
    greenBetween := ?_ }
  · intro i
    obtain ⟨x, hx⟩ := S.clusters_nonempty i
    obtain ⟨u, hu⟩ := restrictionEmbedding_surjectiveOn S.support
      (S.cluster_subset_support i hx)
    exact ⟨u, by simpa [hu] using hx⟩
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    exact Finset.disjoint_left.mp
      (S.clusters_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)
      (mem_pulledCluster S i u |>.mp hui) (mem_pulledCluster S j u |>.mp huj)
  · ext u
    simp only [mem_clusterUnion_iff, Finset.mem_univ, iff_true]
    have huSupport := restrictionEmbedding_mem S.support u
    obtain ⟨i, hi⟩ := (S.clusters_cover _).1 huSupport
    exact ⟨i, (mem_pulledCluster S i u).2 hi⟩
  · intro i j
    rw [card_pulledCluster, card_pulledCluster]
    exact S.clusterEquitable i j
  · intro i u v hu hv _
    rw [restrictToFin_color]
    exact E.canonicalColoring_blue a i
      ((mem_pulledCluster S i u).1 hu) ((mem_pulledCluster S i v).1 hv)
  · intro i j hij u hu v hv
    rw [restrictToFin_color]
    exact E.canonicalColoring_red a hij
      ((mem_pulledCluster S i u).1 hu) ((mem_pulledCluster S j v).1 hv)
  · intro i j hij hnadj u hu v hv
    rw [restrictToFin_color]
    exact E.canonicalColoring_green_nonedge a hij hnadj
      ((mem_pulledCluster S i u).1 hu) ((mem_pulledCluster S j v).1 hv)

/-- The canonical coloring of a shape family belongs to the paper's exact
extremal family. -/
theorem canonicalColoring_mem_extremalFamily
    {n : ℕ} (E : ExtremalFamilyShape k (Fin n)) (hk : 3 ≤ k) :
    E.canonicalColoring ∈ extremalFamily k n := by
  refine ⟨{
    coreCount := E.shapeCount
    coreVertices := fun a ↦ (E.shapes a).support
    coreVertices_pairwiseDisjoint := E.supports_pairwiseDisjoint
    coreSize_lower := fun a ↦ (E.shapes a).coreSize_lower
    coreRegular := fun a ↦ E.canonicalRegularCoreWitness hk a
    offCoreGreen := ?_ }⟩
  intro x y hxy hout
  exact E.canonicalColoring_green_of_no_common_support hxy hout

/-- The shape family with no cores. -/
def empty (k : ℕ) (V : Type*) : ExtremalFamilyShape k V where
  shapeCount := 0
  shapes := fun i ↦ Fin.elim0 i
  supports_pairwiseDisjoint := by
    intro i
    exact Fin.elim0 i

/-- The canonical coloring of the empty shape family is all green. -/
theorem canonicalColoring_empty [Fintype V] [DecidableEq V] :
    (empty k V).canonicalColoring = (allGreen : ColoredGraph V) := by
  apply ColoredGraph.ext
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [(empty k V).canonicalColoring_green_of_no_common_support hxy]
    · simp [hxy]
    · intro a
      exact Fin.elim0 a

/-- Push an entire family shape forward along an injective ambient map. -/
def map (E : ExtremalFamilyShape k V) (f : V ↪ W) : ExtremalFamilyShape k W where
  shapeCount := E.shapeCount
  shapes := fun a ↦ (E.shapes a).map f
  supports_pairwiseDisjoint := by
    intro a _ b _ hab
    change Disjoint ((E.shapes a).support.map f) ((E.shapes b).support.map f)
    rw [Finset.disjoint_left]
    intro y hya hyb
    obtain ⟨x, hxa, rfl⟩ := Finset.mem_map.mp hya
    obtain ⟨z, hzb, hxz⟩ := Finset.mem_map.mp hyb
    have : x = z := f.injective hxz.symm
    subst z
    exact Finset.disjoint_left.mp
      (E.supports_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab) hxa hzb

@[simp]
theorem bluePair_map (E : ExtremalFamilyShape k V) (f : V ↪ W) (x y : V) :
    (E.map f).BluePair (f x) (f y) ↔ E.BluePair x y := by
  constructor
  · rintro ⟨a, i, hxi, hyi⟩
    change f x ∈ ((E.shapes a).clusters i).map f at hxi
    change f y ∈ ((E.shapes a).clusters i).map f at hyi
    obtain ⟨x', hx', hxx⟩ := Finset.mem_map.mp hxi
    obtain ⟨y', hy', hyy⟩ := Finset.mem_map.mp hyi
    have hxeq : x' = x := f.injective hxx
    have hyeq : y' = y := f.injective hyy
    subst x'
    subst y'
    exact ⟨a, i, hx', hy'⟩
  · rintro ⟨a, i, hxi, hyi⟩
    exact ⟨a, i, Finset.mem_map.mpr ⟨x, hxi, rfl⟩,
      Finset.mem_map.mpr ⟨y, hyi, rfl⟩⟩

@[simp]
theorem redPair_map (E : ExtremalFamilyShape k V) (f : V ↪ W) (x y : V) :
    (E.map f).RedPair (f x) (f y) ↔ E.RedPair x y := by
  constructor
  · rintro ⟨a, i, j, hij, hxi, hyj⟩
    change f x ∈ ((E.shapes a).clusters i).map f at hxi
    change f y ∈ ((E.shapes a).clusters j).map f at hyj
    obtain ⟨x', hx', hxx⟩ := Finset.mem_map.mp hxi
    obtain ⟨y', hy', hyy⟩ := Finset.mem_map.mp hyj
    have hxeq : x' = x := f.injective hxx
    have hyeq : y' = y := f.injective hyy
    subst x'
    subst y'
    exact ⟨a, i, j, hij, hx', hy'⟩
  · rintro ⟨a, i, j, hij, hxi, hyj⟩
    exact ⟨a, i, j, hij, Finset.mem_map.mpr ⟨x, hxi, rfl⟩,
      Finset.mem_map.mpr ⟨y, hyj, rfl⟩⟩

/-- Canonical coloring commutes with injective transport on pairs from the
source vertex type. -/
theorem canonicalColoring_map [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (E : ExtremalFamilyShape k V) (f : V ↪ W) (x y : V) :
    (E.map f).canonicalColoring.color (f x) (f y) =
      E.canonicalColoring.color x y := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [(E.map f).canonicalColoring_color_of_ne (f.injective.ne hxy),
      E.canonicalColoring_color_of_ne hxy, bluePair_map, redPair_map]

/-! Concatenating disjoint families of shapes. -/

/-- The shape at an index in the concatenation of two shape families. -/
def appendShape (E F : ExtremalFamilyShape k V)
    (i : Fin (E.shapeCount + F.shapeCount)) : RegularCoreShape k V :=
  Fin.addCases E.shapes F.shapes i

@[simp]
theorem appendShape_castAdd (E F : ExtremalFamilyShape k V)
    (a : Fin E.shapeCount) :
    appendShape E F (Fin.castAdd F.shapeCount a) = E.shapes a := by
  simp [appendShape]

@[simp]
theorem appendShape_natAdd (E F : ExtremalFamilyShape k V)
    (b : Fin F.shapeCount) :
    appendShape E F (Fin.natAdd E.shapeCount b) = F.shapes b := by
  simp [appendShape]

/-- Concatenate two shape families whose supports are disjoint across the
two families. -/
def append (E F : ExtremalFamilyShape k V)
    (hcross : ∀ a b, Disjoint (E.shapes a).support (F.shapes b).support) :
    ExtremalFamilyShape k V where
  shapeCount := E.shapeCount + F.shapeCount
  shapes := appendShape E F
  supports_pairwiseDisjoint := by
    intro i _ j _ hij
    induction i using Fin.addCases with
    | left a =>
        induction j using Fin.addCases with
        | left b =>
            have hab : a ≠ b := by
              intro hab
              subst b
              exact hij rfl
            simpa only [Function.onFun, appendShape_castAdd] using
              E.supports_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab
        | right b =>
            simpa only [Function.onFun, appendShape_castAdd, appendShape_natAdd] using
              hcross a b
    | right a =>
        induction j using Fin.addCases with
        | left b =>
            simpa only [Function.onFun, appendShape_castAdd, appendShape_natAdd] using
              (hcross b a).symm
        | right b =>
            have hab : a ≠ b := by
              intro hab
              subst b
              exact hij rfl
            simpa only [Function.onFun, appendShape_natAdd] using
              F.supports_pairwiseDisjoint (Set.mem_univ a) (Set.mem_univ b) hab

@[simp]
theorem append_shapes_castAdd (E F : ExtremalFamilyShape k V)
    (hcross) (a : Fin E.shapeCount) :
    ((E.append F hcross).shapes (Fin.castAdd F.shapeCount a)) = E.shapes a := by
  simp [append, appendShape]

@[simp]
theorem append_shapes_natAdd (E F : ExtremalFamilyShape k V)
    (hcross) (b : Fin F.shapeCount) :
    ((E.append F hcross).shapes (Fin.natAdd E.shapeCount b)) = F.shapes b := by
  simp [append, appendShape]

/-- Every edge between a left-hand shape and a right-hand shape is green in
the canonical coloring of the concatenation. -/
theorem canonicalColoring_append_green_cross [Fintype V] [DecidableEq V]
    (E F : ExtremalFamilyShape k V) (hcross)
    (a : Fin E.shapeCount) (b : Fin F.shapeCount) {x y : V}
    (hx : x ∈ (E.shapes a).support) (hy : y ∈ (F.shapes b).support) :
    (E.append F hcross).canonicalColoring.color x y = .green := by
  apply (E.append F hcross).canonicalColoring_green_between_shapes
    (a := Fin.castAdd F.shapeCount a) (b := Fin.natAdd E.shapeCount b)
  · intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  · simpa using hx
  · simpa using hy

end ExtremalFamilyShape

section InternalColorCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three color classes partition the unordered pairs internal to a
finite vertex set. -/
theorem red_add_green_add_blue_edgeCountIn (C : ColoredGraph V)
    (S : Finset V) :
    C.redEdgeCountIn S + C.greenEdgeCountIn S + C.blueEdgeCountIn S =
      Nat.choose S.card 2 := by
  have hdegrees :
      ∑ v ∈ S,
          (C.redDegreeIn v S + C.greenDegreeIn v S + C.blueDegreeIn v S) =
        S.card * (S.card - 1) := by
    calc
      ∑ v ∈ S,
          (C.redDegreeIn v S + C.greenDegreeIn v S + C.blueDegreeIn v S) =
          ∑ _v ∈ S, (S.card - 1) := by
            apply Finset.sum_congr rfl
            intro v hv
            exact C.redDegreeIn_add_greenDegreeIn_add_blueDegreeIn_of_mem hv
      _ = S.card * (S.card - 1) := by simp
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    C.sum_degreeIn_eq_two_mul_edgeCountIn .red S,
    C.sum_degreeIn_eq_two_mul_edgeCountIn .green S,
    C.sum_degreeIn_eq_two_mul_edgeCountIn .blue S] at hdegrees
  have hchoose :
      2 * Nat.choose S.card 2 = S.card * (S.card - 1) := by
    rw [Nat.choose_two_right, mul_comm]
    exact Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self S.card)
  change C.edgeCountIn .red S + C.edgeCountIn .green S +
      C.edgeCountIn .blue S = Nat.choose S.card 2
  omega

/-- A lower bound on the internal blue density bounds the number of
nonblue internal edges. -/
theorem red_add_green_edgeCountIn_le_of_blueDense
    (C : ColoredGraph V) (S : Finset V) (error : ℝ)
    (hblue :
      (1 - error) * (Nat.choose S.card 2 : ℝ) ≤
        (C.blueEdgeCountIn S : ℝ)) :
    (C.redEdgeCountIn S : ℝ) + (C.greenEdgeCountIn S : ℝ) ≤
      error * (Nat.choose S.card 2 : ℝ) := by
  have hpartitionNat := C.red_add_green_add_blue_edgeCountIn S
  have hpartition :
      (C.redEdgeCountIn S : ℝ) + (C.greenEdgeCountIn S : ℝ) +
          (C.blueEdgeCountIn S : ℝ) =
        (Nat.choose S.card 2 : ℝ) := by
    exact_mod_cast hpartitionNat
  nlinarith

/-- On `Fin n`, the nonblue internal-edge error supplied by a blue-density
hypothesis is at most `error * n²`. -/
theorem red_add_green_edgeCountIn_le_sq_of_blueDense
    {n : ℕ} (C : ColoredGraph (Fin n)) (S : Finset (Fin n))
    (error : ℝ) (herror : 0 ≤ error)
    (hblue :
      (1 - error) * (Nat.choose S.card 2 : ℝ) ≤
        (C.blueEdgeCountIn S : ℝ)) :
    (C.redEdgeCountIn S : ℝ) + (C.greenEdgeCountIn S : ℝ) ≤
      error * (n : ℝ) ^ 2 := by
  have hcardNat : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  have hcard : (S.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcardNat
  have hchoose :
      (Nat.choose S.card 2 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [Nat.cast_choose_two]
    have hSnonneg : 0 ≤ (S.card : ℝ) := by positivity
    have hnnonneg : 0 ≤ (n : ℝ) := by positivity
    have hpred : (S.card : ℝ) - 1 ≤ (S.card : ℝ) := by linarith
    nlinarith [sq_nonneg ((S.card : ℝ) - (n : ℝ))]
  calc
    (C.redEdgeCountIn S : ℝ) + (C.greenEdgeCountIn S : ℝ) ≤
        error * (Nat.choose S.card 2 : ℝ) :=
      red_add_green_edgeCountIn_le_of_blueDense C S error hblue
    _ ≤ error * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hchoose herror

/-- The internal wrong-color count in any cluster of an extraction witness
is at most `ξ n²`. -/
theorem CoreExtractionResult.redGreenInside_le_sq
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) (hξ : 0 ≤ ξ)
    (i : Fin R.clusterCount) :
    (C.redEdgeCountIn (R.clusters i) : ℝ) +
        (C.greenEdgeCountIn (R.clusters i) : ℝ) ≤
      ξ * (n : ℝ) ^ 2 :=
  red_add_green_edgeCountIn_le_sq_of_blueDense C (R.clusters i) ξ hξ
    (R.blueDense i)

end InternalColorCounts

section BetweenColorCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If red has density at least `1 - error` across a nonempty disjoint pair,
then green and blue together occupy at most an `error` proportion. -/
theorem green_add_blue_colorEdgeCountBetween_le_of_redDensity
    (C : ColoredGraph V) {S T : Finset V} (hS : S.Nonempty)
    (hT : T.Nonempty) (hST : Disjoint S T) (error : ℝ)
    (hred : 1 - error ≤ C.colorDensity .red S T) :
    (C.colorEdgeCountBetween .green S T : ℝ) +
        (C.colorEdgeCountBetween .blue S T : ℝ) ≤
      error * ((S.card : ℝ) * (T.card : ℝ)) := by
  have hpartitionNat := C.red_add_green_add_blue_colorEdgeCountBetween hST
  have hpartition :
      (C.colorEdgeCountBetween .red S T : ℝ) +
          (C.colorEdgeCountBetween .green S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) =
        (S.card : ℝ) * (T.card : ℝ) := by
    exact_mod_cast hpartitionNat
  have hden : 0 < (S.card : ℝ) * (T.card : ℝ) := by positivity
  have hredCount :
      (1 - error) * ((S.card : ℝ) * (T.card : ℝ)) ≤
        (C.colorEdgeCountBetween .red S T : ℝ) := by
    rw [show C.colorDensity .red S T =
        (C.colorEdgeCountBetween .red S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) by rfl] at hred
    exact (le_div_iff₀ hden).mp hred
  nlinarith

/-- If green has density at least `1 - error` across a nonempty disjoint
pair, then red and blue together occupy at most an `error` proportion. -/
theorem red_add_blue_colorEdgeCountBetween_le_of_greenDensity
    (C : ColoredGraph V) {S T : Finset V} (hS : S.Nonempty)
    (hT : T.Nonempty) (hST : Disjoint S T) (error : ℝ)
    (hgreen : 1 - error ≤ C.colorDensity .green S T) :
    (C.colorEdgeCountBetween .red S T : ℝ) +
        (C.colorEdgeCountBetween .blue S T : ℝ) ≤
      error * ((S.card : ℝ) * (T.card : ℝ)) := by
  have hpartitionNat := C.red_add_green_add_blue_colorEdgeCountBetween hST
  have hpartition :
      (C.colorEdgeCountBetween .red S T : ℝ) +
          (C.colorEdgeCountBetween .green S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) =
        (S.card : ℝ) * (T.card : ℝ) := by
    exact_mod_cast hpartitionNat
  have hden : 0 < (S.card : ℝ) * (T.card : ℝ) := by positivity
  have hgreenCount :
      (1 - error) * ((S.card : ℝ) * (T.card : ℝ)) ≤
        (C.colorEdgeCountBetween .green S T : ℝ) := by
    rw [show C.colorDensity .green S T =
        (C.colorEdgeCountBetween .green S T : ℝ) /
          ((S.card : ℝ) * (T.card : ℝ)) by rfl] at hgreen
    exact (le_div_iff₀ hden).mp hgreen
  nlinarith

/-- Ambient-`Fin n` weakening of the red-dominant between-pair estimate. -/
theorem green_add_blue_colorEdgeCountBetween_le_sq_of_redDensity
    {n : ℕ} (C : ColoredGraph (Fin n)) {S T : Finset (Fin n)}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T)
    (error : ℝ) (herror : 0 ≤ error)
    (hred : 1 - error ≤ C.colorDensity .red S T) :
    (C.colorEdgeCountBetween .green S T : ℝ) +
        (C.colorEdgeCountBetween .blue S T : ℝ) ≤
      error * (n : ℝ) ^ 2 := by
  have hSCardNat : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hTCardNat : T.card ≤ n := by simpa using Finset.card_le_univ T
  have hSCard : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hSCardNat
  have hTCard : (T.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTCardNat
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hSnonneg : 0 ≤ (S.card : ℝ) := by positivity
  have hTnonneg : 0 ≤ (T.card : ℝ) := by positivity
  have hprod :
      (S.card : ℝ) * (T.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  calc
    (C.colorEdgeCountBetween .green S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) ≤
        error * ((S.card : ℝ) * (T.card : ℝ)) :=
      green_add_blue_colorEdgeCountBetween_le_of_redDensity C hS hT hST error hred
    _ ≤ error * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hprod herror

/-- Ambient-`Fin n` weakening of the green-dominant between-pair estimate. -/
theorem red_add_blue_colorEdgeCountBetween_le_sq_of_greenDensity
    {n : ℕ} (C : ColoredGraph (Fin n)) {S T : Finset (Fin n)}
    (hS : S.Nonempty) (hT : T.Nonempty) (hST : Disjoint S T)
    (error : ℝ) (herror : 0 ≤ error)
    (hgreen : 1 - error ≤ C.colorDensity .green S T) :
    (C.colorEdgeCountBetween .red S T : ℝ) +
        (C.colorEdgeCountBetween .blue S T : ℝ) ≤
      error * (n : ℝ) ^ 2 := by
  have hSCardNat : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hTCardNat : T.card ≤ n := by simpa using Finset.card_le_univ T
  have hSCard : (S.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hSCardNat
  have hTCard : (T.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hTCardNat
  have hnnonneg : 0 ≤ (n : ℝ) := by positivity
  have hSnonneg : 0 ≤ (S.card : ℝ) := by positivity
  have hTnonneg : 0 ≤ (T.card : ℝ) := by positivity
  have hprod :
      (S.card : ℝ) * (T.card : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith
  calc
    (C.colorEdgeCountBetween .red S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) ≤
        error * ((S.card : ℝ) * (T.card : ℝ)) :=
      red_add_blue_colorEdgeCountBetween_le_of_greenDensity C hS hT hST error hgreen
    _ ≤ error * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hprod herror

end BetweenColorCounts

/-! ## Unordered support sets for edits -/

section EditSupports

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The unordered images of the color-`c` edges oriented from `S` to `T`.
This turns the ordered representation used by `interedges` into a support
set compatible with unordered-edge Hamming distance. -/
def unorderedColorInteredges (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) : Finset (Sym2 V) :=
  ((C.colorGraph c).interedges S T).image Sym2.mk.uncurry

/-- Passing from oriented interedges to unordered pairs cannot increase
cardinality. -/
theorem unorderedColorInteredges_card_le (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) :
    (C.unorderedColorInteredges c S T).card ≤
      C.colorEdgeCountBetween c S T := by
  unfold unorderedColorInteredges colorEdgeCountBetween
  exact Finset.card_image_le

/-- A color-`c` edge with endpoints in the designated source and target
sets belongs to the corresponding unordered support. -/
theorem pair_mem_unorderedColorInteredges (C : ColoredGraph V)
    (c : EdgeColor) (S T : Finset V) {x y : V}
    (hx : x ∈ S) (hy : y ∈ T) (hc : C.color x y = c) (hxy : x ≠ y) :
    s(x, y) ∈ C.unorderedColorInteredges c S T := by
  unfold unorderedColorInteredges
  apply Finset.mem_image.mpr
  refine ⟨(x, y), ?_, rfl⟩
  exact ((C.colorGraph c).mk_mem_interedges_iff).mpr
    ⟨hx, hy, (C.colorGraph_adj c x y).mpr ⟨hxy, hc⟩⟩

/-- Every unordered pair with at least one endpoint in `M`, represented by
orienting an endpoint in `M` first.  Diagonal pairs are harmless in an edit
support because Hamming support itself is loop-free. -/
def unorderedPairsIncidentTo (M : Finset V) : Finset (Sym2 V) :=
  (M ×ˢ (Finset.univ : Finset V)).image Sym2.mk.uncurry

theorem pair_mem_unorderedPairsIncidentTo_left (M : Finset V) {x y : V}
    (hx : x ∈ M) :
    s(x, y) ∈ unorderedPairsIncidentTo M := by
  apply Finset.mem_image.mpr
  exact ⟨(x, y), by simp [hx], rfl⟩

theorem pair_mem_unorderedPairsIncidentTo_right (M : Finset V) {x y : V}
    (hy : y ∈ M) :
    s(x, y) ∈ unorderedPairsIncidentTo M := by
  apply Finset.mem_image.mpr
  refine ⟨(y, x), by simp [hy], ?_⟩
  exact Sym2.eq_swap

/-- There are at most `|M| |V|` unordered pairs incident to `M`. -/
theorem unorderedPairsIncidentTo_card_le (M : Finset V) :
    (unorderedPairsIncidentTo M).card ≤ M.card * Fintype.card V := by
  unfold unorderedPairsIncidentTo
  calc
    ((M ×ˢ (Finset.univ : Finset V)).image Sym2.mk.uncurry).card ≤
        (M ×ˢ (Finset.univ : Finset V)).card := Finset.card_image_le
    _ = M.card * Fintype.card V := by simp

/-- If `M` has at most `error * n` vertices, all unordered pairs incident
to `M` form a support of size at most `error * n²`. -/
theorem unorderedPairsIncidentTo_card_le_sq
    {n : ℕ} (M : Finset (Fin n)) (error : ℝ) (_herror : 0 ≤ error)
    (hM : (M.card : ℝ) ≤ error * (n : ℝ)) :
    ((unorderedPairsIncidentTo M).card : ℝ) ≤ error * (n : ℝ) ^ 2 := by
  have hcardNat := unorderedPairsIncidentTo_card_le M
  have hcardNat' :
      (unorderedPairsIncidentTo M).card ≤ M.card * n := by
    simpa using hcardNat
  have hcard :
      ((unorderedPairsIncidentTo M).card : ℝ) ≤
        (M.card : ℝ) * (n : ℝ) := by
    exact_mod_cast hcardNat'
  have hn : 0 ≤ (n : ℝ) := by positivity
  calc
    ((unorderedPairsIncidentTo M).card : ℝ) ≤
        (M.card : ℝ) * (n : ℝ) := hcard
    _ ≤ (error * (n : ℝ)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hM hn
    _ = error * (n : ℝ) ^ 2 := by ring

end EditSupports

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- An unordered copy of the color-`c` ordered interedges from `S` to `T`.
The image presentation is convenient for Hamming-support covers; injectivity
is not needed for the basic cardinal upper bound. -/
def unorderedColorEdgesBetween (C : ColoredGraph V) (c : EdgeColor)
    (S T : Finset V) : Finset (Sym2 V) :=
  ((C.colorGraph c).interedges S T).image fun p ↦ s(p.1, p.2)

theorem pair_mem_unorderedColorEdgesBetween_of_mem
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V)
    {x y : V} (hx : x ∈ S) (hy : y ∈ T) (hxy : x ≠ y)
    (hcolor : C.color x y = c) :
    s(x, y) ∈ unorderedColorEdgesBetween C c S T := by
  apply Finset.mem_image.mpr
  refine ⟨(x, y), ?_, rfl⟩
  rw [SimpleGraph.mk_mem_interedges_iff]
  exact ⟨hx, hy, (C.colorGraph_adj c x y).2 ⟨hxy, hcolor⟩⟩

theorem card_unorderedColorEdgesBetween_le
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V) :
    (unorderedColorEdgesBetween C c S T).card ≤
      C.colorEdgeCountBetween c S T := by
  exact Finset.card_image_le

/-- A deliberately overcounting finite set containing every unordered edge
with at least one endpoint in `M`. -/
def unorderedEdgesIncident (M : Finset V) : Finset (Sym2 V) :=
  (M ×ˢ (Finset.univ : Finset V)).image fun p ↦ s(p.1, p.2)

theorem pair_mem_unorderedEdgesIncident_left (M : Finset V)
    {x y : V} (hx : x ∈ M) : s(x, y) ∈ unorderedEdgesIncident M := by
  apply Finset.mem_image.mpr
  exact ⟨(x, y), by simp [hx], rfl⟩

theorem pair_mem_unorderedEdgesIncident_right (M : Finset V)
    {x y : V} (hy : y ∈ M) : s(x, y) ∈ unorderedEdgesIncident M := by
  rw [Sym2.eq_swap]
  exact pair_mem_unorderedEdgesIncident_left M hy

theorem card_unorderedEdgesIncident_le (M : Finset V) :
    (unorderedEdgesIncident M).card ≤ M.card * Fintype.card V := by
  exact Finset.card_image_le.trans_eq (Finset.card_product _ _)

/-- Injective transport of unordered edges. -/
def sym2MapEmbedding (f : W ↪ V) : Sym2 W ↪ Sym2 V where
  toFun := Sym2.map f
  inj' := Sym2.map.injective f.injective

@[simp]
theorem sym2MapEmbedding_pair (f : W ↪ V) (x y : W) :
    sym2MapEmbedding f s(x, y) = s(f x, f y) := by
  simp [sym2MapEmbedding]

/-- Transport a finite unordered-edge support along an injection. -/
def mapUnorderedEdges (f : W ↪ V) (S : Finset (Sym2 W)) :
    Finset (Sym2 V) := S.map (sym2MapEmbedding f)

@[simp]
theorem card_mapUnorderedEdges (f : W ↪ V) (S : Finset (Sym2 W)) :
    (mapUnorderedEdges f S).card = S.card := by
  simp [mapUnorderedEdges]

theorem pair_mem_mapUnorderedEdges (f : W ↪ V)
    (S : Finset (Sym2 W)) (x y : W) (h : s(x, y) ∈ S) :
    s(f x, f y) ∈ mapUnorderedEdges f S := by
  exact Finset.mem_map.mpr ⟨s(x, y), h, by simp [sym2MapEmbedding]⟩

/-- Every raw Hamming distance is bounded by the number of unordered edges
of the complete graph. -/
theorem coloringHammingDistance_le_choose (C D : ColoredGraph V) :
    coloringHammingDistance C D ≤ Nat.choose (Fintype.card V) 2 := by
  unfold coloringHammingDistance coloringHammingSupport
  exact (Finset.card_filter_le _ _).trans_eq
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := V))

/-- Coarse square bound for raw Hamming distance. -/
theorem coloringHammingDistance_le_card_sq (C D : ColoredGraph V) :
    (coloringHammingDistance C D : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
  have h := coloringHammingDistance_le_choose C D
  have hchoose : Nat.choose (Fintype.card V) 2 ≤ Fintype.card V ^ 2 := by
    exact (Nat.choose_le_pow _ _)
  exact_mod_cast h.trans hchoose

/-! ## Overlaying a recursive target on a finite remainder -/

/-- Replace the colors inside `S` by `inside`, leaving `base` on every
other off-diagonal pair. -/
def overlayInside (base inside : ColoredGraph V) (S : Finset V) : ColoredGraph V :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if x ∈ S ∧ y ∈ S then inside.color x y else base.color x y)
    (by
      intro x y _
      by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
        simp [hx, hy, base.color_comm, inside.color_comm])

@[simp]
theorem overlayInside_color_of_ne (base inside : ColoredGraph V)
    (S : Finset V) {x y : V} (hxy : x ≠ y) :
    (overlayInside base inside S).color x y =
      if x ∈ S ∧ y ∈ S then inside.color x y else base.color x y := by
  rw [(overlayInside base inside S).color_eq_get hxy]
  rfl

theorem overlayInside_color_of_mem (base inside : ColoredGraph V)
    (S : Finset V) {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    (overlayInside base inside S).color x y = inside.color x y := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [overlayInside_color_of_ne _ _ S hxy, if_pos ⟨hx, hy⟩]

theorem overlayInside_color_of_not_both (base inside : ColoredGraph V)
    (S : Finset V) {x y : V} (hxy : x ≠ y)
    (hout : ¬ (x ∈ S ∧ y ∈ S)) :
    (overlayInside base inside S).color x y = base.color x y := by
  rw [overlayInside_color_of_ne _ _ S hxy, if_neg hout]

/-- Changing an overlay's inside coloring costs no more than the Hamming
distance of the two induced colorings on `S`. -/
theorem coloringHammingDistance_overlayInside_le
    (base C D : ColoredGraph V) (S : Finset V) :
    coloringHammingDistance (overlayInside base C S) (overlayInside base D S) ≤
      coloringHammingDistance (C.restrictToFin S) (D.restrictToFin S) := by
  let f := restrictionEmbedding S
  let lifted := mapUnorderedEdges f
    (coloringHammingSupport (C.restrictToFin S) (D.restrictToFin S))
  have hsubset : coloringHammingSupport (overlayInside base C S)
      (overlayInside base D S) ⊆ lifted := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [pair_mem_coloringHammingSupport] at he
        have hxy := he.1
        by_cases hmem : x ∈ S ∧ y ∈ S
        · obtain ⟨i, hi⟩ := restrictionEmbedding_surjectiveOn S hmem.1
          obtain ⟨j, hj⟩ := restrictionEmbedding_surjectiveOn S hmem.2
          subst x
          subst y
          apply pair_mem_mapUnorderedEdges
          rw [pair_mem_coloringHammingSupport]
          constructor
          · intro hij
            apply hxy
            exact congrArg f hij
          · simp only [restrictToFin_color]
            simpa only [overlayInside_color_of_mem _ _ S hmem.1 hmem.2]
              using he.2
        · rw [overlayInside_color_of_not_both _ _ S hxy hmem,
            overlayInside_color_of_not_both _ _ S hxy hmem] at he
          exact (he.2 rfl).elim
  calc
    coloringHammingDistance (overlayInside base C S) (overlayInside base D S) ≤
        lifted.card := coloringHammingDistance_le_card_of_support_subset
          _ _ _ hsubset
    _ = coloringHammingDistance (C.restrictToFin S) (D.restrictToFin S) := by
      simp [lifted, coloringHammingDistance]


theorem delta_real_one_le {k : ℕ} (hk : 3 ≤ k) :
    (1 : ℝ) ≤ (delta k : ℝ) := by
  exact_mod_cast (show 1 ≤ delta k by unfold delta; omega)

/-- The paper's initial low-red branch: near-extremality and few red edges
make the coloring close to the all-green member of the extremal family. -/
theorem closeToAllGreen_of_redCount_small
    {k n : ℕ} (hk : 3 ≤ k) {C : ColoredGraph (Fin n)}
    {epsilon inputDelta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : inputDelta ≤ epsilon / 4)
    (hnear : -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (hred : (C.redEdgeCount : ℝ) ≤ epsilon * (n : ℝ) ^ 2 / 4) :
    (coloringHammingDistance C (allGreen : ColoredGraph (Fin n)) : ℝ) ≤
      epsilon * (n : ℝ) ^ 2 := by
  have hDelta := delta_real_one_le hk
  have hobj : (objective k C : ℝ) =
      (C.redEdgeCount : ℝ) - (delta k : ℝ) * (C.blueEdgeCount : ℝ) := by
    unfold objective
    push_cast
    rfl
  have hblue : (C.blueEdgeCount : ℝ) ≤
      (C.redEdgeCount : ℝ) + inputDelta * (n : ℝ) ^ 2 := by
    have hb : 0 ≤ (C.blueEdgeCount : ℝ) := by positivity
    rw [hobj] at hnear
    nlinarith
  rw [coloringHammingDistance_allGreen]
  push_cast
  have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  nlinarith

/-- A maximum-red-degree bound gives the paper's coarse red-edge estimate. -/
theorem redEdgeCount_le_half_of_redDegree_lt
    {n : ℕ} (C : ColoredGraph (Fin n)) {eta : ℝ}
    (hred : ∀ v, (C.redDegree v : ℝ) < eta * (n : ℝ)) :
    (C.redEdgeCount : ℝ) ≤ eta * (n : ℝ) ^ 2 / 2 := by
  have hsumNat := C.sum_degree_eq_two_mul_edgeCount .red
  have hsum : (∑ v, (C.redDegree v : ℝ)) =
      2 * (C.redEdgeCount : ℝ) := by
    exact_mod_cast hsumNat
  have hle : (∑ v, (C.redDegree v : ℝ)) ≤
      ∑ _v : Fin n, eta * (n : ℝ) := by
    exact Finset.sum_le_sum fun v _ ↦ (hred v).le
  rw [hsum] at hle
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  nlinarith

/-- The low-maximum-red-degree stopping branch is close to all green. -/
theorem closeToAllGreen_of_maxRedDegree_small
    {k n : ℕ} (hk : 3 ≤ k) {C : ColoredGraph (Fin n)}
    {eta inputDelta : ℝ} (heta : 0 < eta)
    (hdelta : inputDelta ≤ eta)
    (hnear : -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ))
    (hred : ∀ v, (C.redDegree v : ℝ) < eta * (n : ℝ)) :
    (coloringHammingDistance C (allGreen : ColoredGraph (Fin n)) : ℝ) ≤
      2 * eta * (n : ℝ) ^ 2 := by
  have hredCount := redEdgeCount_le_half_of_redDegree_lt C hred
  have hDelta := delta_real_one_le hk
  have hobj : (objective k C : ℝ) =
      (C.redEdgeCount : ℝ) - (delta k : ℝ) * (C.blueEdgeCount : ℝ) := by
    unfold objective
    push_cast
    rfl
  have hblue : (C.blueEdgeCount : ℝ) ≤
      (C.redEdgeCount : ℝ) + inputDelta * (n : ℝ) ^ 2 := by
    have hb : 0 ≤ (C.blueEdgeCount : ℝ) := by positivity
    rw [hobj] at hnear
    nlinarith
  rw [coloringHammingDistance_allGreen]
  push_cast
  have hn : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  nlinarith


noncomputable def stabilityEpsilon (epsilon : ℝ) : ℝ := min epsilon 1

theorem stabilityEpsilon_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < stabilityEpsilon epsilon := by
  simp [stabilityEpsilon, hepsilon]

theorem stabilityEpsilon_le (epsilon : ℝ) : stabilityEpsilon epsilon ≤ epsilon := by
  exact min_le_left _ _

theorem stabilityEpsilon_le_one (epsilon : ℝ) : stabilityEpsilon epsilon ≤ 1 := by
  exact min_le_right _ _

noncomputable def stabilityEta (epsilon : ℝ) : ℝ := stabilityEpsilon epsilon / 100

theorem stabilityEta_mem_Ioo {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    stabilityEta epsilon ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · exact div_pos (stabilityEpsilon_pos hepsilon) (by norm_num)
  · have h := stabilityEpsilon_le_one epsilon
    unfold stabilityEta
    linarith

noncomputable def stabilityContraction (epsilon : ℝ) : ℝ :=
  1 - stabilityEta epsilon / 2

theorem stabilityContraction_mem_Ioo {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    stabilityContraction epsilon ∈ Set.Ioo (0 : ℝ) 1 := by
  rcases stabilityEta_mem_Ioo hepsilon with ⟨hetaPos, hetaOne⟩
  constructor <;> unfold stabilityContraction <;> linarith

theorem exists_stabilityStageBound {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ r : ℕ,
      stabilityContraction epsilon ^ r ≤ stabilityEpsilon epsilon / 20 := by
  have htarget : 0 < stabilityEpsilon epsilon / 20 :=
    div_pos (stabilityEpsilon_pos hepsilon) (by norm_num)
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one htarget
    (stabilityContraction_mem_Ioo hepsilon).2
  exact ⟨r, hr.le⟩

noncomputable def stabilityAmplification (epsilon : ℝ) : ℝ :=
  (20 / stabilityEpsilon epsilon) ^ 2

theorem stabilityAmplification_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < stabilityAmplification epsilon := by
  unfold stabilityAmplification
  have hcap := stabilityEpsilon_pos hepsilon
  exact sq_pos_of_pos (div_pos (by norm_num) hcap)

noncomputable def stabilityEditConstant (c : ℝ) : ℝ :=
  100 * (1 + 1 / c ^ 2)

theorem stabilityEditConstant_pos {c : ℝ} (hc : 0 < c) :
    0 < stabilityEditConstant c := by
  unfold stabilityEditConstant
  positivity

/-- One entry of the backwards finite stability hierarchy.  Its extraction
theorem is the chosen specialization of `kthOrderRecursion`; `gamma` is the
current admissible objective error and `gammaNext` is the next one. -/
structure ColoredStabilityStep
    (k : ℕ) (eta epsilon A K c gammaNext : ℝ) where
  xi : ℝ
  xi_mem : xi ∈ Set.Ioo (0 : ℝ) (eta / 20)
  edit_small : K * xi ≤ epsilon * eta / 16
  amplification_xi : A * xi ≤ gammaNext / 4
  deltaStar : ℝ
  deltaStar_mem : deltaStar ∈ Set.Ioo (0 : ℝ) 1
  nStar : ℕ
  extract : ∀ n ≥ nStar, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) deltaStar,
    ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
      -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
      (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
      Nonempty (CoreExtractionResult k n C eta inputDelta xi c)
  gamma : ℝ
  gamma_pos : 0 < gamma
  gamma_le_eta : gamma ≤ eta
  gamma_lt_deltaStar : gamma < deltaStar
  amplification_gamma : A * gamma ≤ gammaNext / 4
  update_le : A * (gamma + xi) ≤ gammaNext

/-- Choose one stability scale strictly below all three available reserves. -/
theorem exists_coloredStabilityStep
    (k : ℕ) {eta epsilon A K c gammaNext : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (hA : 0 < A)
    (hK : 0 < K) (hnext : 0 < gammaNext)
    (recurse : ∀ xi ∈ Set.Ioo (0 : ℝ) (eta / 20),
      ∃ deltaStar : ℝ, deltaStar ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ nStar : ℕ,
        ∀ n ≥ nStar, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) deltaStar,
          ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
            -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
            (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
            Nonempty (CoreExtractionResult k n C eta inputDelta xi c)) :
    Nonempty (ColoredStabilityStep k eta epsilon A K c gammaNext) := by
  let xi := min (eta / 40) (min (gammaNext / (4 * A))
    (epsilon * eta / (32 * K)))
  have hxi : 0 < xi := by
    dsimp [xi]
    exact lt_min (div_pos heta (by norm_num))
      (lt_min (div_pos hnext (mul_pos (by norm_num) hA))
        (div_pos (mul_pos hepsilon heta) (mul_pos (by norm_num) hK)))
  have hxiEta : xi < eta / 20 := by
    have hle : xi ≤ eta / 40 := min_le_left _ _
    linarith
  obtain ⟨deltaStar, hdeltaStar, nStar, hextract⟩ :=
    recurse xi ⟨hxi, hxiEta⟩
  let gamma := min (deltaStar / 2) (min (gammaNext / (4 * A)) eta)
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    exact lt_min (div_pos hdeltaStar.1 (by norm_num))
      (lt_min (div_pos hnext (mul_pos (by norm_num) hA)) heta)
  have hgammaEta : gamma ≤ eta :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hgammaDelta : gamma < deltaStar := by
    have hle : gamma ≤ deltaStar / 2 := min_le_left _ _
    linarith
  have hxiReserve : xi ≤ gammaNext / (4 * A) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hgammaReserve : gamma ≤ gammaNext / (4 * A) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hAxi : A * xi ≤ gammaNext / 4 := by
    calc
      A * xi ≤ A * (gammaNext / (4 * A)) :=
        mul_le_mul_of_nonneg_left hxiReserve hA.le
      _ = gammaNext / 4 := by field_simp [ne_of_gt hA]
  have hAgamma : A * gamma ≤ gammaNext / 4 := by
    calc
      A * gamma ≤ A * (gammaNext / (4 * A)) :=
        mul_le_mul_of_nonneg_left hgammaReserve hA.le
      _ = gammaNext / 4 := by field_simp [ne_of_gt hA]
  have hxiEditReserve : xi ≤ epsilon * eta / (32 * K) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKxi : K * xi ≤ epsilon * eta / 16 := by
    calc
      K * xi ≤ K * (epsilon * eta / (32 * K)) :=
        mul_le_mul_of_nonneg_left hxiEditReserve hK.le
      _ = epsilon * eta / 32 := by field_simp [ne_of_gt hK]
      _ ≤ epsilon * eta / 16 := by
        have hprod := mul_pos hepsilon heta
        linarith
  exact ⟨{
    xi := xi
    xi_mem := ⟨hxi, hxiEta⟩
    edit_small := hKxi
    amplification_xi := hAxi
    deltaStar := deltaStar
    deltaStar_mem := hdeltaStar
    nStar := nStar
    extract := hextract
    gamma := gamma
    gamma_pos := hgamma
    gamma_le_eta := hgammaEta
    gamma_lt_deltaStar := hgammaDelta
    amplification_gamma := hAgamma
    update_le := by linarith
  }⟩

/-- A backwards-chosen hierarchy with `r` usable extraction stages and the
terminal error `eta`.  The inductive shape lets the outer proof consume the
scales in forward order without array-index arithmetic. -/
inductive ColoredStabilityHierarchy
    (k : ℕ) (eta epsilon A K c : ℝ) : (r : ℕ) → (gamma : ℝ) → Type
  | terminal : ColoredStabilityHierarchy k eta epsilon A K c 0 eta
  | cons {r : ℕ} {gammaNext : ℝ}
      (step : ColoredStabilityStep k eta epsilon A K c gammaNext)
      (tail : ColoredStabilityHierarchy k eta epsilon A K c r gammaNext) :
      ColoredStabilityHierarchy k eta epsilon A K c (r + 1) step.gamma

namespace ColoredStabilityHierarchy

/-- Every scale carried by the finite hierarchy is positive. -/
theorem gamma_pos {k : ℕ} {eta epsilon A K c gamma : ℝ} {r : ℕ}
    (H : ColoredStabilityHierarchy k eta epsilon A K c r gamma)
    (heta : 0 < eta) :
    0 < gamma := by
  cases H with
  | terminal => exact heta
  | cons step _ => exact step.gamma_pos

/-- Every admissible objective scale in the hierarchy is at most `eta`. -/
theorem gamma_le_eta {k : ℕ} {eta epsilon A K c gamma : ℝ} {r : ℕ}
    (H : ColoredStabilityHierarchy k eta epsilon A K c r gamma) :
    gamma ≤ eta := by
  cases H with
  | terminal => exact le_rfl
  | cons step _ => exact step.gamma_le_eta

def maxN {k : ℕ} {eta epsilon A K c gamma : ℝ} {r : ℕ} :
    ColoredStabilityHierarchy k eta epsilon A K c r gamma → ℕ
  | .terminal => 0
  | .cons step tail => max step.nStar tail.maxN

/-- The extraction threshold at the head of a nonterminal hierarchy is
bounded by its finite maximum threshold. -/
theorem head_nStar_le_maxN
    {k r : ℕ} {eta epsilon A K c gammaNext : ℝ}
    (step : ColoredStabilityStep k eta epsilon A K c gammaNext)
    (tail : ColoredStabilityHierarchy k eta epsilon A K c r gammaNext) :
    step.nStar ≤ (ColoredStabilityHierarchy.cons step tail).maxN := by
  exact Nat.le_max_left _ _

/-- The maximum extraction threshold of the tail is bounded by the maximum
threshold of the whole nonterminal hierarchy. -/
theorem tail_maxN_le_maxN
    {k r : ℕ} {eta epsilon A K c gammaNext : ℝ}
    (step : ColoredStabilityStep k eta epsilon A K c gammaNext)
    (tail : ColoredStabilityHierarchy k eta epsilon A K c r gammaNext) :
    tail.maxN ≤ (ColoredStabilityHierarchy.cons step tail).maxN := by
  exact Nat.le_max_right _ _

theorem exists_of_recursion
    (k r : ℕ) {eta epsilon A K c : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) (hA : 0 < A) (hK : 0 < K)
    (recurse : ∀ xi ∈ Set.Ioo (0 : ℝ) (eta / 20),
      ∃ deltaStar : ℝ, deltaStar ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ nStar : ℕ,
        ∀ n ≥ nStar, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) deltaStar,
          ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
            -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
            (∃ x, eta * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
            Nonempty (CoreExtractionResult k n C eta inputDelta xi c)) :
    ∃ gamma : ℝ, 0 < gamma ∧
      Nonempty (ColoredStabilityHierarchy k eta epsilon A K c r gamma) := by
  induction r with
  | zero => exact ⟨eta, heta, ⟨.terminal⟩⟩
  | succ r ih =>
      obtain ⟨gammaNext, hnext, Htail⟩ := ih
      obtain ⟨step⟩ := exists_coloredStabilityStep k heta hepsilon hA hK hnext recurse
      exact ⟨step.gamma, step.gamma_pos, ⟨.cons step Htail.some⟩⟩

end ColoredStabilityHierarchy


open ExtremalFamilyShape

/-! ## Restricting a mapped canonical shape coloring -/

/-- Mapping a shape family into `S` by its canonical enumeration and then
restricting its canonical coloring back to `S` recovers the original
canonical coloring exactly. -/
theorem canonicalColoring_map_restrictToFin
    (S : Finset (Fin n))
    (E : ExtremalFamilyShape k (Fin S.card)) :
    ((E.map (restrictionEmbedding S)).canonicalColoring.restrictToFin S) =
      E.canonicalColoring := by
  apply ColoredGraph.ext
  intro x y
  rw [restrictToFin_color, canonicalColoring_map]

/-! ## Shape-local predicates eliminate dependent append transports -/

def ShapeBluePair {V : Type*} (A : RegularCoreShape k V) (x y : V) : Prop :=
  ∃ i, x ∈ A.clusters i ∧ y ∈ A.clusters i

def ShapeRedPair {V : Type*} (A : RegularCoreShape k V) (x y : V) : Prop :=
  ∃ i j, A.reducedGraph.Adj i j ∧
    x ∈ A.clusters i ∧ y ∈ A.clusters j

theorem shapeBluePair_congr {V : Type*} {A B : RegularCoreShape k V}
    (h : A = B) (x y : V) : ShapeBluePair A x y ↔ ShapeBluePair B x y := by
  subst B
  rfl

theorem shapeRedPair_congr {V : Type*} {A B : RegularCoreShape k V}
    (h : A = B) (x y : V) : ShapeRedPair A x y ↔ ShapeRedPair B x y := by
  subst B
  rfl

theorem bluePair_iff_exists_shape {V : Type*}
    (E : ExtremalFamilyShape k V) (x y : V) :
    E.BluePair x y ↔ ∃ a, ShapeBluePair (E.shapes a) x y :=
  Iff.rfl

theorem redPair_iff_exists_shape {V : Type*}
    (E : ExtremalFamilyShape k V) (x y : V) :
    E.RedPair x y ↔ ∃ a, ShapeRedPair (E.shapes a) x y :=
  Iff.rfl

/-- Blue-pair classification of an appended shape family. -/
theorem bluePair_append_iff {V : Type*}
    (L R : ExtremalFamilyShape k V)
    (hcross : ∀ a b, Disjoint (L.shapes a).support (R.shapes b).support)
    (x y : V) :
    (L.append R hcross).BluePair x y ↔ L.BluePair x y ∨ R.BluePair x y := by
  rw [bluePair_iff_exists_shape, bluePair_iff_exists_shape,
    bluePair_iff_exists_shape]
  constructor
  · rintro ⟨q, hq⟩
    induction q using Fin.addCases with
    | left a =>
        exact Or.inl ⟨a,
          (shapeBluePair_congr (append_shapes_castAdd L R hcross a) x y).mp hq⟩
    | right b =>
        exact Or.inr ⟨b,
          (shapeBluePair_congr (append_shapes_natAdd L R hcross b) x y).mp hq⟩
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := h
      exact ⟨Fin.castAdd R.shapeCount a,
        (shapeBluePair_congr (append_shapes_castAdd L R hcross a) x y).mpr ha⟩
    · obtain ⟨b, hb⟩ := h
      exact ⟨Fin.natAdd L.shapeCount b,
        (shapeBluePair_congr (append_shapes_natAdd L R hcross b) x y).mpr hb⟩

/-- Red-pair classification of an appended shape family. -/
theorem redPair_append_iff {V : Type*}
    (L R : ExtremalFamilyShape k V)
    (hcross : ∀ a b, Disjoint (L.shapes a).support (R.shapes b).support)
    (x y : V) :
    (L.append R hcross).RedPair x y ↔ L.RedPair x y ∨ R.RedPair x y := by
  rw [redPair_iff_exists_shape, redPair_iff_exists_shape,
    redPair_iff_exists_shape]
  constructor
  · rintro ⟨q, hq⟩
    induction q using Fin.addCases with
    | left a =>
        exact Or.inl ⟨a,
          (shapeRedPair_congr (append_shapes_castAdd L R hcross a) x y).mp hq⟩
    | right b =>
        exact Or.inr ⟨b,
          (shapeRedPair_congr (append_shapes_natAdd L R hcross b) x y).mp hq⟩
  · rintro (h | h)
    · obtain ⟨a, ha⟩ := h
      exact ⟨Fin.castAdd R.shapeCount a,
        (shapeRedPair_congr (append_shapes_castAdd L R hcross a) x y).mpr ha⟩
    · obtain ⟨b, hb⟩ := h
      exact ⟨Fin.natAdd L.shapeCount b,
        (shapeRedPair_congr (append_shapes_natAdd L R hcross b) x y).mpr hb⟩

/-- Exact off-diagonal canonical-color formula for an appended family. -/
theorem canonicalColoring_append_of_ne {V : Type*} [Fintype V] [DecidableEq V]
    (L R : ExtremalFamilyShape k V)
    (hcross : ∀ a b, Disjoint (L.shapes a).support (R.shapes b).support)
    {x y : V} (hxy : x ≠ y) :
    (L.append R hcross).canonicalColoring.color x y =
      if L.BluePair x y ∨ R.BluePair x y then .blue
      else if L.RedPair x y ∨ R.RedPair x y then .red else .green := by
  rw [(L.append R hcross).canonicalColoring_color_of_ne hxy,
    bluePair_append_iff, redPair_append_iff]
  by_cases hblue : L.BluePair x y ∨ R.BluePair x y
  · simp [hblue]
  · by_cases hred : L.RedPair x y ∨ R.RedPair x y <;>
      simp [hblue, hred]

/-! ## Appending an outside family to an inside family -/

/-- Cross-disjointness obtained from `L` lying outside `S` and `R` lying
inside `S`. -/
def appendCrossDisjoint
    (L R : ExtremalFamilyShape k (Fin n)) (S : Finset (Fin n))
    (hL : ∀ a, Disjoint (L.shapes a).support S)
    (hR : ∀ b, (R.shapes b).support ⊆ S) :
    ∀ a b, Disjoint (L.shapes a).support (R.shapes b).support :=
  fun a b ↦ (hL a).mono_right (hR b)

/-- If `L` lies outside the remainder and `R` lies inside it, the canonical
coloring of their concatenation is exactly the overlay of the two canonical
colorings. -/
theorem canonicalColoring_append_eq_overlayInside
    (L R : ExtremalFamilyShape k (Fin n)) (S : Finset (Fin n))
    (hL : ∀ a, Disjoint (L.shapes a).support S)
    (hR : ∀ b, (R.shapes b).support ⊆ S) :
    (L.append R (appendCrossDisjoint L R S hL hR)).canonicalColoring =
      overlayInside L.canonicalColoring R.canonicalColoring S := by
  let hcross := appendCrossDisjoint L R S hL hR
  apply ColoredGraph.ext
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [canonicalColoring_append_of_ne L R hcross hxy,
      overlayInside_color_of_ne _ _ S hxy]
    by_cases hmem : x ∈ S ∧ y ∈ S
    · have hLBlue : ¬ L.BluePair x y := by
        rintro ⟨a, i, hxi, _⟩
        exact Finset.disjoint_left.mp (hL a)
          ((L.shapes a).cluster_subset_support i hxi) hmem.1
      have hLRed : ¬ L.RedPair x y := by
        rintro ⟨a, i, _, _, hxi, _⟩
        exact Finset.disjoint_left.mp (hL a)
          ((L.shapes a).cluster_subset_support i hxi) hmem.1
      rw [if_pos hmem, R.canonicalColoring_color_of_ne hxy]
      simp [hLBlue, hLRed]
    · have hRBlue : ¬ R.BluePair x y := by
        rintro ⟨b, i, hxi, hyi⟩
        apply hmem
        exact ⟨hR b ((R.shapes b).cluster_subset_support i hxi),
          hR b ((R.shapes b).cluster_subset_support i hyi)⟩
      have hRRed : ¬ R.RedPair x y := by
        rintro ⟨b, i, j, _, hxi, hyj⟩
        apply hmem
        exact ⟨hR b ((R.shapes b).cluster_subset_support i hxi),
          hR b ((R.shapes b).cluster_subset_support j hyj)⟩
      rw [if_neg hmem, L.canonicalColoring_color_of_ne hxy]
      simp [hRBlue, hRRed]


/-!
Componentwise assembly of a regular reduced graph and its cluster partition
into a color-free extremal-family shape.
-/

/-- Two ambient vertices lie in the same member of a cluster family. -/
def SameClusterPair {I V : Type*} (clusters : I → Finset V) (x y : V) : Prop :=
  ∃ i, x ∈ clusters i ∧ y ∈ clusters i

/-- Two ambient vertices lie in reduced-graph adjacent clusters. -/
def ReducedAdjacentPair {I V : Type*} (R : SimpleGraph I)
    (clusters : I → Finset V) (x y : V) : Prop :=
  ∃ i j, R.Adj i j ∧ x ∈ clusters i ∧ y ∈ clusters j

theorem sameClusterPair_comm {I V : Type*} (clusters : I → Finset V)
    (x y : V) : SameClusterPair clusters x y ↔ SameClusterPair clusters y x := by
  constructor <;> rintro ⟨i, hx, hy⟩ <;> exact ⟨i, hy, hx⟩

theorem reducedAdjacentPair_comm {I V : Type*} (R : SimpleGraph I)
    (clusters : I → Finset V) (x y : V) :
    ReducedAdjacentPair R clusters x y ↔
      ReducedAdjacentPair R clusters y x := by
  constructor
  · rintro ⟨i, j, hij, hx, hy⟩
    exact ⟨j, i, hij.symm, hy, hx⟩
  · rintro ⟨i, j, hij, hy, hx⟩
    exact ⟨j, i, hij.symm, hx, hy⟩

/-- The exact blow-up coloring of a reduced graph: blue within clusters,
red across reduced edges, and green on every remaining pair. -/
noncomputable def clusterBlowupColoring {I V : Type*} (R : SimpleGraph I)
    (clusters : I → Finset V) : ColoredGraph V :=
  SimpleGraph.EdgeLabeling.mk
    (fun x y _ ↦ if SameClusterPair clusters x y then .blue
      else if ReducedAdjacentPair R clusters x y then .red else .green)
    (by
      intro x y _
      rw [sameClusterPair_comm clusters x y,
        reducedAdjacentPair_comm R clusters x y])

@[simp]
theorem clusterBlowupColoring_color_of_ne
    {I V : Type*} [DecidableEq V] (R : SimpleGraph I)
    (clusters : I → Finset V) {x y : V} (hxy : x ≠ y) :
    (clusterBlowupColoring R clusters).color x y =
      if SameClusterPair clusters x y then .blue
      else if ReducedAdjacentPair R clusters x y then .red else .green := by
  rw [(clusterBlowupColoring R clusters).color_eq_get hxy]
  exact SimpleGraph.EdgeLabeling.get_mk _ _ _ _ _

/-- The cluster with canonical `Fin` label `a` inside the reduced-graph
component `q`. -/
noncomputable def componentShapeCluster
    {I V : Type*} [Fintype I] {R : SimpleGraph I}
    (clusters : I → Finset V) (q : R.ConnectedComponent)
    (a : Fin (Nat.card q)) : Finset V :=
  clusters ((Finite.equivFin q).symm a).1

/-- The ambient support covered by the clusters whose reduced vertices lie
in `q`. -/
noncomputable def componentShapeSupport
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {R : SimpleGraph I} (clusters : I → Finset V)
    (q : R.ConnectedComponent) : Finset V :=
  clusterUnion (componentShapeCluster clusters q)

@[simp]
theorem mem_componentShapeSupport_iff
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq V]
    {R : SimpleGraph I} (clusters : I → Finset V)
    (q : R.ConnectedComponent) (x : V) :
    x ∈ componentShapeSupport clusters q ↔
      ∃ a : Fin (Nat.card q), x ∈ componentShapeCluster clusters q a := by
  simp [componentShapeSupport]

theorem componentShapeClusters_pairwiseDisjoint
    {I V : Type*} [Fintype I] [DecidableEq I]
    {R : SimpleGraph I} (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (q : R.ConnectedComponent) :
    Set.PairwiseDisjoint (Set.univ : Set (Fin (Nat.card q)))
      (componentShapeCluster clusters q) := by
  classical
  intro a _ b _ hab
  have hindex :
      ((Finite.equivFin q).symm a).1 ≠ ((Finite.equivFin q).symm b).1 := by
    intro h
    apply hab
    apply (Finite.equivFin q).symm.injective
    exact Subtype.ext h
  exact hdisj (Set.mem_univ _) (Set.mem_univ _) hindex

theorem componentShapeSupport_card_eq_sum
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] {R : SimpleGraph I}
    (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (q : R.ConnectedComponent) :
    (componentShapeSupport clusters q).card =
      ∑ a : Fin (Nat.card q), (componentShapeCluster clusters q a).card := by
  exact card_clusterUnion _
    (componentShapeClusters_pairwiseDisjoint clusters hdisj q)

/-- A `delta k`-regular component has at least `k - 1` reduced vertices. -/
theorem k_sub_one_le_natCard_connectedComponent
    {k : ℕ} {I : Type*} [Fintype I] {R : SimpleGraph I}
    [DecidableRel R.Adj] (hk : 3 ≤ k)
    (hregular : R.IsRegularOfDegree (delta k))
    (q : R.ConnectedComponent) :
    k - 1 ≤ Nat.card q := by
  classical
  letI : Nonempty q := ⟨⟨q.out, q.out_eq⟩⟩
  have hcard : 0 < Nat.card q := Nat.card_pos
  let a : Fin (Nat.card q) := ⟨0, hcard⟩
  have hlt := (connectedComponentRelabel q).degree_lt_card_verts a
  have hdegree := connectedComponentRelabel_isRegularOfDegree q hregular
  rw [hdegree a] at hlt
  have hlt' : delta k < Nat.card q := by simpa using hlt
  simp only [delta] at hlt'
  omega

theorem natCard_connectedComponent_le_componentShapeSupport_card
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] {R : SimpleGraph I}
    (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (q : R.ConnectedComponent) :
    Nat.card q ≤ (componentShapeSupport clusters q).card := by
  rw [componentShapeSupport_card_eq_sum clusters hdisj q]
  calc
    Nat.card q = ∑ _a : Fin (Nat.card q), 1 := by simp
    _ ≤ ∑ a : Fin (Nat.card q),
        (componentShapeCluster clusters q a).card := by
      exact Finset.sum_le_sum fun a _ ↦ by
        exact Finset.card_pos.mpr
          (hnonempty ((Finite.equivFin q).symm a).1)

theorem k_le_componentShapeSupport_card
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] {R : SimpleGraph I}
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    (q : R.ConnectedComponent) :
    k ≤ (componentShapeSupport clusters q).card := by
  have hsum :
      ∑ _a : Fin (Nat.card q), 2 ≤
        ∑ a : Fin (Nat.card q),
          (componentShapeCluster clusters q a).card := by
    exact Finset.sum_le_sum fun a _ ↦
      htwo ((Finite.equivFin q).symm a).1
  have htwoCard :
      2 * Nat.card q ≤ (componentShapeSupport clusters q).card := by
    rw [componentShapeSupport_card_eq_sum clusters hdisj q]
    simpa [mul_comm] using hsum
  have hcount :=
    k_sub_one_le_natCard_connectedComponent hk hregular q
  omega

/-- The regular-core shape carried by one connected component of the reduced
graph. -/
noncomputable def connectedComponentRegularCoreShape
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    (q : R.ConnectedComponent) : RegularCoreShape k V where
  support := componentShapeSupport clusters q
  coreSize_lower :=
    k_le_componentShapeSupport_card clusters hdisj htwo hk hregular q
  clusterCount := Nat.card q
  clusterCount_lower :=
    k_sub_one_le_natCard_connectedComponent hk hregular q
  clusterCount_upper :=
    natCard_connectedComponent_le_componentShapeSupport_card
      clusters hnonempty hdisj q
  clusters := componentShapeCluster clusters q
  clusters_nonempty := fun a ↦
    hnonempty ((Finite.equivFin q).symm a).1
  clusters_pairwiseDisjoint :=
    componentShapeClusters_pairwiseDisjoint clusters hdisj q
  clusters_cover := by
    intro x
    exact mem_componentShapeSupport_iff clusters q x
  reducedGraph := connectedComponentRelabel q
  reducedGraphAdjDecidable := connectedComponentRelabelAdjDecidable q
  reducedGraph_connected := connectedComponentRelabel_connected q
  reducedGraph_regular := by
    exact connectedComponentRelabel_isRegularOfDegree q hregular
  clusterEquitable := fun a b ↦
    hequitable ((Finite.equivFin q).symm a).1
      ((Finite.equivFin q).symm b).1

theorem disjoint_componentShapeSupport_of_ne
    {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] {R : SimpleGraph I}
    (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    {q r : R.ConnectedComponent} (hqr : q ≠ r) :
    Disjoint (componentShapeSupport clusters q)
      (componentShapeSupport clusters r) := by
  rw [Finset.disjoint_left]
  intro x hxq hxr
  rw [mem_componentShapeSupport_iff] at hxq hxr
  obtain ⟨a, hxa⟩ := hxq
  obtain ⟨b, hxb⟩ := hxr
  let i : I := ((Finite.equivFin q).symm a).1
  let j : I := ((Finite.equivFin r).symm b).1
  have hiq : R.connectedComponentMk i = q :=
    (q.mem_supp_iff i).mp ((Finite.equivFin q).symm a).2
  have hjr : R.connectedComponentMk j = r :=
    (r.mem_supp_iff j).mp ((Finite.equivFin r).symm b).2
  have hij : i ≠ j := by
    intro hij
    apply hqr
    rw [← hiq, ← hjr, hij]
  exact Finset.disjoint_left.mp
    (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hxa hxb

/-- Assemble all connected reduced-graph components into a finite extremal
family shape. -/
noncomputable def connectedComponentExtremalFamilyShape
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k)) :
    ExtremalFamilyShape k V where
  shapeCount := Fintype.card R.ConnectedComponent
  shapes := fun a ↦ connectedComponentRegularCoreShape R clusters
    hnonempty hdisj hequitable htwo hk hregular
    ((Fintype.equivFin R.ConnectedComponent).symm a)
  supports_pairwiseDisjoint := by
    intro a _ b _ hab
    apply disjoint_componentShapeSupport_of_ne clusters hdisj
    intro hcomp
    exact hab ((Fintype.equivFin R.ConnectedComponent).symm.injective hcomp)

/-- The union of the assembled core supports is exactly the union of the
original cluster family. -/
theorem connectedComponentExtremalFamilyShape_supportUnion
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k)) :
    clusterUnion (fun a ↦
      ((connectedComponentExtremalFamilyShape R clusters hnonempty
        hdisj hequitable htwo hk hregular).shapes a).support) =
      clusterUnion clusters := by
  classical
  ext x
  rw [mem_clusterUnion_iff, mem_clusterUnion_iff]
  constructor
  · rintro ⟨a, hxa⟩
    change x ∈ componentShapeSupport clusters
      ((Fintype.equivFin R.ConnectedComponent).symm a) at hxa
    rw [mem_componentShapeSupport_iff] at hxa
    obtain ⟨b, hxb⟩ := hxa
    exact ⟨((Finite.equivFin _).symm b).1, hxb⟩
  · rintro ⟨i, hxi⟩
    let q : R.ConnectedComponent := R.connectedComponentMk i
    let a : Fin (Fintype.card R.ConnectedComponent) :=
      Fintype.equivFin R.ConnectedComponent q
    refine ⟨a, ?_⟩
    change x ∈ componentShapeSupport clusters
      ((Fintype.equivFin R.ConnectedComponent).symm a)
    rw [show (Fintype.equivFin R.ConnectedComponent).symm a = q by
      exact (Fintype.equivFin R.ConnectedComponent).symm_apply_apply q]
    rw [mem_componentShapeSupport_iff]
    let qi : q := ⟨i, by rfl⟩
    let b : Fin (Nat.card q) := Finite.equivFin q qi
    refine ⟨b, ?_⟩
    change x ∈ clusters ((Finite.equivFin q).symm b).1
    simpa [b, qi] using hxi

theorem connectedComponentExtremalFamilyShape_bluePair_iff
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    (x y : V) :
    (connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
      hequitable htwo hk hregular).BluePair x y ↔
      SameClusterPair clusters x y := by
  let E := connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
    hequitable htwo hk hregular
  change E.BluePair x y ↔ SameClusterPair clusters x y
  constructor
  · rintro ⟨a, b, hxb, hyb⟩
    let q : R.ConnectedComponent :=
      (Fintype.equivFin R.ConnectedComponent).symm a
    change x ∈ componentShapeCluster clusters q b at hxb
    change y ∈ componentShapeCluster clusters q b at hyb
    exact ⟨((Finite.equivFin q).symm b).1, hxb, hyb⟩
  · rintro ⟨i, hxi, hyi⟩
    let a : Fin (Fintype.card R.ConnectedComponent) :=
      Fintype.equivFin R.ConnectedComponent (R.connectedComponentMk i)
    let q : R.ConnectedComponent :=
      (Fintype.equivFin R.ConnectedComponent).symm a
    have hiq : i ∈ q.supp := by
      rw [q.mem_supp_iff]
      dsimp only [q, a]
      exact (Fintype.equivFin R.ConnectedComponent).symm_apply_apply _ |>.symm
    let qi : q := ⟨i, hiq⟩
    let b : Fin (Nat.card q) := Finite.equivFin q qi
    refine ⟨a, b, ?_, ?_⟩
    · change x ∈ componentShapeCluster clusters q b
      simpa [componentShapeCluster, b, qi] using hxi
    · change y ∈ componentShapeCluster clusters q b
      simpa [componentShapeCluster, b, qi] using hyi

theorem connectedComponentExtremalFamilyShape_redPair_iff
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    (x y : V) :
    (connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
      hequitable htwo hk hregular).RedPair x y ↔
      ReducedAdjacentPair R clusters x y := by
  let E := connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
    hequitable htwo hk hregular
  change E.RedPair x y ↔ ReducedAdjacentPair R clusters x y
  constructor
  · rintro ⟨a, b, c, hbc, hxb, hyc⟩
    let q : R.ConnectedComponent :=
      (Fintype.equivFin R.ConnectedComponent).symm a
    let qb : q := (Finite.equivFin q).symm b
    let qc : q := (Finite.equivFin q).symm c
    change (connectedComponentRelabel q).Adj b c at hbc
    change q.toSimpleGraph.Adj ((Finite.equivFin q).symm b)
      ((Finite.equivFin q).symm c) at hbc
    have hqadj : q.toSimpleGraph.Adj qb qc := by
      exact hbc
    have hRadj : R.Adj qb.1 qc.1 :=
      (q.toSimpleGraph_adj qb.2 qc.2).mp hqadj
    change x ∈ componentShapeCluster clusters q b at hxb
    change y ∈ componentShapeCluster clusters q c at hyc
    exact ⟨qb.1, qc.1, hRadj, hxb, hyc⟩
  · rintro ⟨i, j, hij, hxi, hyj⟩
    let a : Fin (Fintype.card R.ConnectedComponent) :=
      Fintype.equivFin R.ConnectedComponent (R.connectedComponentMk i)
    let q : R.ConnectedComponent :=
      (Fintype.equivFin R.ConnectedComponent).symm a
    have hiq : i ∈ q.supp := by
      rw [q.mem_supp_iff]
      dsimp only [q, a]
      exact (Fintype.equivFin R.ConnectedComponent).symm_apply_apply _ |>.symm
    have hjq : j ∈ q.supp := q.mem_supp_of_adj_mem_supp hiq hij
    let qi : q := ⟨i, hiq⟩
    let qj : q := ⟨j, hjq⟩
    let b : Fin (Nat.card q) := Finite.equivFin q qi
    let c : Fin (Nat.card q) := Finite.equivFin q qj
    refine ⟨a, b, c, ?_, ?_, ?_⟩
    · change (connectedComponentRelabel q).Adj b c
      have hqadj : q.toSimpleGraph.Adj qi qj :=
        (q.toSimpleGraph_adj hiq hjq).mpr hij
      simpa [connectedComponentRelabel, b, c] using hqadj
    · change x ∈ componentShapeCluster clusters q b
      simpa [componentShapeCluster, b, qi] using hxi
    · change y ∈ componentShapeCluster clusters q c
      simpa [componentShapeCluster, c, qj] using hyj

/-! The next lemmas expose the target colors in the original reduced graph
and cluster labels. -/

theorem connectedComponentExtremalFamilyShape_canonicalColoring_blue
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    (i : I) {x y : V} (hx : x ∈ clusters i) (hy : y ∈ clusters i) :
    (connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
      hequitable htwo hk hregular).canonicalColoring.color x y = .blue := by
  let E := connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
    hequitable htwo hk hregular
  let a : Fin (Fintype.card R.ConnectedComponent) :=
    Fintype.equivFin R.ConnectedComponent (R.connectedComponentMk i)
  let q : R.ConnectedComponent :=
    (Fintype.equivFin R.ConnectedComponent).symm a
  have hiq : i ∈ q.supp := by
    rw [q.mem_supp_iff]
    dsimp only [q, a]
    exact (Fintype.equivFin R.ConnectedComponent).symm_apply_apply _ |>.symm
  let qi : q := ⟨i, hiq⟩
  let b : Fin (Nat.card q) := Finite.equivFin q qi
  change E.canonicalColoring.color x y = .blue
  apply E.canonicalColoring_blue a b
  · change x ∈ componentShapeCluster clusters q b
    simpa [componentShapeCluster, b, qi] using hx
  · change y ∈ componentShapeCluster clusters q b
    simpa [componentShapeCluster, b, qi] using hy

theorem connectedComponentExtremalFamilyShape_canonicalColoring_red
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k))
    {i j : I} (hij : R.Adj i j) {x y : V}
    (hx : x ∈ clusters i) (hy : y ∈ clusters j) :
    (connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
      hequitable htwo hk hregular).canonicalColoring.color x y = .red := by
  let E := connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
    hequitable htwo hk hregular
  let a : Fin (Fintype.card R.ConnectedComponent) :=
    Fintype.equivFin R.ConnectedComponent (R.connectedComponentMk i)
  let q : R.ConnectedComponent :=
    (Fintype.equivFin R.ConnectedComponent).symm a
  have hiq : i ∈ q.supp := by
    rw [q.mem_supp_iff]
    dsimp only [q, a]
    exact (Fintype.equivFin R.ConnectedComponent).symm_apply_apply _ |>.symm
  have hjq : j ∈ q.supp := q.mem_supp_of_adj_mem_supp hiq hij
  let qi : q := ⟨i, hiq⟩
  let qj : q := ⟨j, hjq⟩
  let b : Fin (Nat.card q) := Finite.equivFin q qi
  let c : Fin (Nat.card q) := Finite.equivFin q qj
  change E.canonicalColoring.color x y = .red
  apply E.canonicalColoring_red a
  · change (connectedComponentRelabel q).Adj b c
    have hqadj : q.toSimpleGraph.Adj qi qj :=
      (q.toSimpleGraph_adj hiq hjq).mpr hij
    simpa [connectedComponentRelabel, b, c] using hqadj
  · change x ∈ componentShapeCluster clusters q b
    simpa [componentShapeCluster, b, qi] using hx
  · change y ∈ componentShapeCluster clusters q c
    simpa [componentShapeCluster, c, qj] using hy

/-- Componentwise assembly does not alter the evident reduced-graph blow-up:
its canonical coloring is blue precisely within an original cluster, red
precisely across an original reduced edge, and green otherwise. -/
theorem connectedComponentExtremalFamilyShape_canonicalColoring_eq_clusterBlowupColoring
    {k : ℕ} {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (R : SimpleGraph I)
    [DecidableRel R.Adj] (clusters : I → Finset V)
    (hnonempty : ∀ i, (clusters i).Nonempty)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    (hequitable : ∀ i j, (clusters i).card ≤ (clusters j).card + 1)
    (htwo : ∀ i, 2 ≤ (clusters i).card)
    (hk : 3 ≤ k) (hregular : R.IsRegularOfDegree (delta k)) :
    (connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
      hequitable htwo hk hregular).canonicalColoring =
      clusterBlowupColoring R clusters := by
  let E := connectedComponentExtremalFamilyShape R clusters hnonempty hdisj
    hequitable htwo hk hregular
  change E.canonicalColoring = clusterBlowupColoring R clusters
  apply ColoredGraph.ext
  intro x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [E.canonicalColoring_color_of_ne hxy,
      clusterBlowupColoring_color_of_ne R clusters hxy,
      connectedComponentExtremalFamilyShape_bluePair_iff R clusters hnonempty
        hdisj hequitable htwo hk hregular,
      connectedComponentExtremalFamilyShape_redPair_iff R clusters hnonempty
        hdisj hequitable htwo hk hregular]


variable {I V : Type*} [Fintype I] [DecidableEq I]
  [Fintype V] [DecidableEq V]


/-- Vertices removed from their old labeled cluster during a rebalance. -/
def clusterMovedSet (old new : I → Finset V) : Finset V :=
  clusterUnion fun i ↦ old i \ new i

omit [Fintype V] in
@[simp]
theorem mem_clusterMovedSet_iff (old new : I → Finset V) (x : V) :
    x ∈ clusterMovedSet old new ↔
      ∃ i, x ∈ old i ∧ x ∉ new i := by
  simp [clusterMovedSet, mem_clusterUnion_iff]

/-- Away from the moved set, every vertex has the same cluster label
before and after a rebalance.  Disjointness of the new family rules out a
second label after using equality of the two cluster unions. -/
theorem mem_old_iff_mem_new_of_not_mem_clusterMovedSet
    (old new : I → Finset V)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x : V} (hx : x ∉ clusterMovedSet old new) (i : I) :
    x ∈ old i ↔ x ∈ new i := by
  constructor
  · intro hxi
    by_contra hxin
    exact hx (mem_clusterMovedSet_iff old new x |>.2 ⟨i, hxi, hxin⟩)
  · intro hxi
    have hxUnionNew : x ∈ clusterUnion new :=
      cluster_subset_clusterUnion new i hxi
    have hxUnionOld : x ∈ clusterUnion old := by
      simpa only [hunion] using hxUnionNew
    obtain ⟨j, hxj⟩ := mem_clusterUnion_iff.mp hxUnionOld
    have hxjNew : x ∈ new j := by
      by_contra hxjn
      exact hx (mem_clusterMovedSet_iff old new x |>.2 ⟨j, hxj, hxjn⟩)
    have hij : i = j := by
      by_contra hij
      exact Finset.disjoint_left.mp
        (hnew (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxjNew
    simpa only [hij] using hxj

theorem sameClusterPair_iff_of_not_mem_clusterMovedSet
    (old new : I → Finset V)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x y : V} (hx : x ∉ clusterMovedSet old new)
    (hy : y ∉ clusterMovedSet old new) :
    SameClusterPair old x y ↔ SameClusterPair new x y := by
  constructor
  · rintro ⟨i, hxi, hyi⟩
    exact ⟨i,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hx i).mp hxi,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hy i).mp hyi⟩
  · rintro ⟨i, hxi, hyi⟩
    exact ⟨i,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hx i).mpr hxi,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hy i).mpr hyi⟩

theorem reducedAdjacentPair_iff_of_not_mem_clusterMovedSet
    (R : SimpleGraph I) (old new : I → Finset V)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x y : V} (hx : x ∉ clusterMovedSet old new)
    (hy : y ∉ clusterMovedSet old new) :
    ReducedAdjacentPair R old x y ↔ ReducedAdjacentPair R new x y := by
  constructor
  · rintro ⟨i, j, hij, hxi, hyj⟩
    exact ⟨i, j, hij,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hx i).mp hxi,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hy j).mp hyj⟩
  · rintro ⟨i, j, hij, hxi, hyj⟩
    exact ⟨i, j, hij,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hx i).mpr hxi,
      (mem_old_iff_mem_new_of_not_mem_clusterMovedSet old new hnew hunion hy j).mpr hyj⟩

/-! ## Pointwise and Hamming edit bounds -/

/-- The exact old and new blow-up colorings agree on every off-diagonal
pair whose endpoints both avoid the moved set. -/
theorem clusterBlowupColoring_color_eq_of_not_mem_clusterMovedSet
    (R : SimpleGraph I) (old new : I → Finset V)
    (_hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x y : V} (hxy : x ≠ y)
    (hx : x ∉ clusterMovedSet old new)
    (hy : y ∉ clusterMovedSet old new) :
    (clusterBlowupColoring R old).color x y =
      (clusterBlowupColoring R new).color x y := by
  rw [clusterBlowupColoring_color_of_ne R old hxy,
    clusterBlowupColoring_color_of_ne R new hxy]
  rw [sameClusterPair_iff_of_not_mem_clusterMovedSet old new hnew hunion hx hy,
    reducedAdjacentPair_iff_of_not_mem_clusterMovedSet R old new hnew hunion hx hy]

/-- Incident-support form of pointwise agreement. -/
theorem clusterBlowupColoring_color_eq_of_pair_not_mem_incident
    (R : SimpleGraph I) (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    {x y : V} (hxy : x ≠ y)
    (hpair : s(x, y) ∉ unorderedPairsIncidentTo (clusterMovedSet old new)) :
    (clusterBlowupColoring R old).color x y =
      (clusterBlowupColoring R new).color x y := by
  apply clusterBlowupColoring_color_eq_of_not_mem_clusterMovedSet
    R old new hold hnew hunion hxy
  · intro hx
    exact hpair (pair_mem_unorderedPairsIncidentTo_left _ hx)
  · intro hy
    exact hpair (pair_mem_unorderedPairsIncidentTo_right _ hy)

/-- Every edge changed by exact cluster rebalancing is incident to a moved
vertex. -/
theorem clusterBlowupColoring_hammingSupport_subset_incident
    (R : SimpleGraph I) (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new) :
    coloringHammingSupport (clusterBlowupColoring R old)
        (clusterBlowupColoring R new) ⊆
      unorderedPairsIncidentTo (clusterMovedSet old new) := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [pair_mem_coloringHammingSupport] at he
      by_contra hpair
      exact he.2 (clusterBlowupColoring_color_eq_of_pair_not_mem_incident
        R old new hold hnew hunion he.1 hpair)

/-- Rebalancing exact blow-up clusters changes at most `|M| |V|` unordered
edges, where `M` is the set of vertices removed from their old labels. -/
theorem coloringHammingDistance_clusterBlowupColoring_le_moved_mul_card
    (R : SimpleGraph I) (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new) :
    coloringHammingDistance (clusterBlowupColoring R old)
        (clusterBlowupColoring R new) ≤
      (clusterMovedSet old new).card * Fintype.card V := by
  calc
    coloringHammingDistance (clusterBlowupColoring R old)
        (clusterBlowupColoring R new) ≤
        (unorderedPairsIncidentTo (clusterMovedSet old new)).card :=
      coloringHammingDistance_le_card_of_support_subset _ _ _
        (clusterBlowupColoring_hammingSupport_subset_incident
          R old new hold hnew hunion)
    _ ≤ (clusterMovedSet old new).card * Fintype.card V :=
      unorderedPairsIncidentTo_card_le _

/-! ## The same edit under a common recursive overlay -/

/-- A common inside overlay preserves agreement outside the incident
support.  No disjointness condition on `T` is needed: when both endpoints
lie in `T`, both sides use the same coloring `C`. -/
theorem overlayInside_clusterBlowupColoring_color_eq_of_pair_not_mem_incident
    (R : SimpleGraph I) (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    (C : ColoredGraph V) (T : Finset V)
    {x y : V} (hxy : x ≠ y)
    (hpair : s(x, y) ∉ unorderedPairsIncidentTo (clusterMovedSet old new)) :
    (overlayInside (clusterBlowupColoring R old) C T).color x y =
      (overlayInside (clusterBlowupColoring R new) C T).color x y := by
  rw [overlayInside_color_of_ne _ _ T hxy,
    overlayInside_color_of_ne _ _ T hxy]
  by_cases hT : x ∈ T ∧ y ∈ T
  · simp [hT]
  · simp only [hT, ↓reduceIte]
    exact clusterBlowupColoring_color_eq_of_pair_not_mem_incident
      R old new hold hnew hunion hxy hpair

/-- The same `|M| |V|` balancing bound holds after placing an identical
recursive coloring inside any finite set `T`. -/
theorem coloringHammingDistance_overlayInside_clusterBlowupColoring_le_moved_mul_card
    (R : SimpleGraph I) (old new : I → Finset V)
    (hold : Set.PairwiseDisjoint (Set.univ : Set I) old)
    (hnew : Set.PairwiseDisjoint (Set.univ : Set I) new)
    (hunion : clusterUnion old = clusterUnion new)
    (C : ColoredGraph V) (T : Finset V) :
    coloringHammingDistance
        (overlayInside (clusterBlowupColoring R old) C T)
        (overlayInside (clusterBlowupColoring R new) C T) ≤
      (clusterMovedSet old new).card * Fintype.card V := by
  calc
    coloringHammingDistance
        (overlayInside (clusterBlowupColoring R old) C T)
        (overlayInside (clusterBlowupColoring R new) C T) ≤
        (unorderedPairsIncidentTo (clusterMovedSet old new)).card := by
      apply coloringHammingDistance_le_card_of_eq_outside
      intro e _he hpair
      induction e using Sym2.inductionOn with
      | _ x y =>
          simp only [unorderedPairColor_pair]
          by_cases hxy : x = y
          · subst y
            simp
          · exact
              overlayInside_clusterBlowupColoring_color_eq_of_pair_not_mem_incident
                R old new hold hnew hunion C T hxy hpair
    _ ≤ (clusterMovedSet old new).card * Fintype.card V :=
      unorderedPairsIncidentTo_card_le _



/-- The chosen contraction factor is nonnegative. -/
theorem stabilityContraction_nonneg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ≤ stabilityContraction epsilon :=
  (stabilityContraction_mem_Ioo hepsilon).1.le

/-- A successful extraction preserves the powered shrinkage invariant used
by the finite outer recursion. -/
theorem stabilityContraction_pow_shrink
    {epsilon m m' : ℝ} {r : ℕ} (hepsilon : 0 < epsilon)
    (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (hshrink : m' ≤ stabilityContraction epsilon * m) :
    stabilityContraction epsilon ^ r * m' ≤
      stabilityContraction epsilon ^ (r + 1) * m := by
  have hpow : 0 ≤ stabilityContraction epsilon ^ r :=
    pow_nonneg (stabilityContraction_nonneg hepsilon) _
  calc
    stabilityContraction epsilon ^ r * m' ≤
        stabilityContraction epsilon ^ r *
          (stabilityContraction epsilon * m) :=
      mul_le_mul_of_nonneg_left hshrink hpow
    _ = stabilityContraction epsilon ^ (r + 1) * m := by ring

/-- The local edit reserve is small enough to telescope against the square
lost in one contraction step. -/
theorem stability_stage_cost_telescope
    {epsilon coefficient m m' : ℝ} (hepsilon : 0 < epsilon)
    (hcoefficient : coefficient ≤
      stabilityEpsilon epsilon * stabilityEta epsilon / 16)
    (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (hshrink : m' ≤ stabilityContraction epsilon * m) :
    coefficient * m ^ 2 +
        stabilityEpsilon epsilon / 4 * m' ^ 2 ≤
      stabilityEpsilon epsilon / 4 * m ^ 2 := by
  have hebar := stabilityEpsilon_pos hepsilon
  have heta := stabilityEta_mem_Ioo hepsilon
  have hq := stabilityContraction_mem_Ioo hepsilon
  have hsquares : m' ^ 2 ≤
      (stabilityContraction epsilon * m) ^ 2 := by
    nlinarith
  have hreserve : coefficient ≤
      stabilityEpsilon epsilon / 4 *
        (1 - stabilityContraction epsilon ^ 2) := by
    have hthree : 0 ≤ 3 - stabilityEta epsilon := by linarith [heta.2]
    have hpositive : 0 ≤ stabilityEpsilon epsilon * stabilityEta epsilon *
        (3 - stabilityEta epsilon) :=
      mul_nonneg (mul_nonneg hebar.le heta.1.le) hthree
    unfold stabilityContraction
    nlinarith
  have hmulReserve := mul_le_mul_of_nonneg_right hreserve (sq_nonneg m)
  have hmulShrink : stabilityEpsilon epsilon / 4 * m' ^ 2 ≤
      stabilityEpsilon epsilon / 4 *
        (stabilityContraction epsilon * m) ^ 2 :=
    mul_le_mul_of_nonneg_left hsquares (div_nonneg hebar.le (by norm_num))
  calc
    coefficient * m ^ 2 + stabilityEpsilon epsilon / 4 * m' ^ 2 ≤
        stabilityEpsilon epsilon / 4 *
            (1 - stabilityContraction epsilon ^ 2) * m ^ 2 +
          stabilityEpsilon epsilon / 4 *
            (stabilityContraction epsilon * m) ^ 2 :=
      add_le_add hmulReserve hmulShrink
    _ = stabilityEpsilon epsilon / 4 * m ^ 2 := by ring

/-- If a remainder is not tiny relative to the original ambient order, the
fixed amplification factor absorbs the change from the old square scale to
the new one. -/
theorem stabilityAmplification_absorbs
    {epsilon N m m' d : ℝ} (hepsilon : 0 < epsilon)
    (hN : 0 ≤ N) (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (hmN : m ≤ N)
    (hlarge : stabilityEpsilon epsilon * N / 20 < m')
    (hd : 0 ≤ d) :
    d * m ^ 2 ≤ stabilityAmplification epsilon * d * m' ^ 2 := by
  have hebar := stabilityEpsilon_pos hepsilon
  have hlinear : m ≤ (20 / stabilityEpsilon epsilon) * m' := by
    have hlinear' : m ≤ (20 * m') / stabilityEpsilon epsilon := by
      apply (le_div_iff₀ hebar).2
      have : stabilityEpsilon epsilon * m < 20 * m' := by
        have hem := mul_le_mul_of_nonneg_left hmN hebar.le
        nlinarith
      nlinarith
    convert hlinear' using 1 <;> ring
  have hscale : 0 ≤ (20 / stabilityEpsilon epsilon) * m' := by positivity
  have hsquare : m ^ 2 ≤
      ((20 / stabilityEpsilon epsilon) * m') ^ 2 := by
    nlinarith
  unfold stabilityAmplification
  nlinarith

/-- A remainder below the global stopping scale has a square-sized edit
cost fitting comfortably inside the terminal reserve. -/
theorem stability_small_remainder_square
    {epsilon N m : ℝ} (hepsilon : 0 < epsilon)
    (hN : 0 ≤ N) (hm : 0 ≤ m)
    (hsmall : m ≤ stabilityEpsilon epsilon * N / 20) :
    m ^ 2 ≤ stabilityEpsilon epsilon * N ^ 2 / 20 := by
  have hebar := stabilityEpsilon_pos hepsilon
  have heone := stabilityEpsilon_le_one epsilon
  have hboundNonneg : 0 ≤ stabilityEpsilon epsilon * N / 20 := by positivity
  have hsquare : m ^ 2 ≤
      (stabilityEpsilon epsilon * N / 20) ^ 2 := by
    nlinarith
  have hcoef : stabilityEpsilon epsilon ^ 2 / 400 ≤
      stabilityEpsilon epsilon / 20 := by
    nlinarith [sq_nonneg (stabilityEpsilon epsilon)]
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg N)]

/-- The two global reserves used by the recursive proof fit inside the
requested (capped) error. -/
theorem stability_global_reserves_le
    {epsilon N : ℝ} (hepsilon : 0 < epsilon) (hN : 0 ≤ N) :
    stabilityEpsilon epsilon / 4 * N ^ 2 +
        stabilityEpsilon epsilon * N ^ 2 / 20 ≤
      epsilon * N ^ 2 := by
  have hcap := stabilityEpsilon_le epsilon
  have hebar := stabilityEpsilon_pos hepsilon
  have hsq := sq_nonneg N
  nlinarith

/-- Any fixed natural threshold is eventually below a positive linear
fraction of the ambient order. -/
theorem exists_nat_threshold_below_linear {a : ℝ} (ha : 0 < a) (M : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (M : ℝ) ≤ a * (N : ℝ) := by
  simpa using exists_nat_forall_mul_add_le_mul
    (show (0 : ℝ) < a by exact ha) (show 0 ≤ (M : ℝ) by positivity)



/-! Quantitative support for the old-partition core-extraction edit. -/

private theorem left_nonempty_of_colorDensity_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V)
    (h : 0 < C.colorDensity c S T) : S.Nonempty := by
  by_contra hS
  have hSempty : S = ∅ := not_nonempty_iff_eq_empty.mp hS
  subst S
  simp [colorDensity, colorEdgeCountBetween] at h

private theorem right_nonempty_of_colorDensity_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (C : ColoredGraph V) (c : EdgeColor) (S T : Finset V)
    (h : 0 < C.colorDensity c S T) : T.Nonempty := by
  rw [C.colorDensity_comm c S T] at h
  exact left_nonempty_of_colorDensity_pos C c T S h

/-- Wrong-colored edges internal to one of the extracted clusters. -/
noncomputable def extractionInternalWrongSupport
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin R.clusterCount)).biUnion fun i ↦
    C.edgeFinsetIn .red (R.clusters i) ∪
      C.edgeFinsetIn .green (R.clusters i)

/-- Wrong-colored edges between two distinct extracted clusters.  Ordered
cluster pairs deliberately overcount unordered cluster pairs. -/
noncomputable def extractionBetweenWrongSupport
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin R.clusterCount × Fin R.clusterCount)).biUnion
    fun p ↦
      if p.1 = p.2 then ∅
      else if R.reducedGraph.Adj p.1 p.2 then
        C.unorderedColorInteredges .green (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)
      else
        C.unorderedColorInteredges .red (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)

/-- Non-green edges crossing from the extracted core to its remainder. -/
noncomputable def extractionBoundaryWrongSupport
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) : Finset (Sym2 (Fin n)) :=
  C.unorderedColorInteredges .red
      (coreExtractionCore R.exceptional R.clusters)
      (coreExtractionRemainder R.exceptional R.clusters) ∪
    C.unorderedColorInteredges .blue
      (coreExtractionCore R.exceptional R.clusters)
      (coreExtractionRemainder R.exceptional R.clusters)

/-- A single explicit finite support containing every old-partition stage
edit. -/
noncomputable def extractionOldPartitionWrongSupport
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) : Finset (Sym2 (Fin n)) :=
  extractionInternalWrongSupport R ∪ extractionBetweenWrongSupport R ∪
    extractionBoundaryWrongSupport R ∪ unorderedPairsIncidentTo R.exceptional

private theorem extractionInternalWrongSupport_card_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) (hξ : 0 ≤ ξ) :
    ((extractionInternalWrongSupport R).card : ℝ) ≤
      (R.clusterCount : ℝ) * ξ * (n : ℝ) ^ 2 := by
  have hcardNat :
      (extractionInternalWrongSupport R).card ≤
        ∑ i : Fin R.clusterCount,
          (C.edgeFinsetIn .red (R.clusters i) ∪
            C.edgeFinsetIn .green (R.clusters i)).card := by
    unfold extractionInternalWrongSupport
    exact Finset.card_biUnion_le
  have hcard :
      ((extractionInternalWrongSupport R).card : ℝ) ≤
        ∑ i : Fin R.clusterCount,
          ((C.edgeFinsetIn .red (R.clusters i) ∪
            C.edgeFinsetIn .green (R.clusters i)).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((extractionInternalWrongSupport R).card : ℝ) ≤
        ∑ i : Fin R.clusterCount,
          ((C.edgeFinsetIn .red (R.clusters i) ∪
            C.edgeFinsetIn .green (R.clusters i)).card : ℝ) := hcard
    _ ≤ ∑ _i : Fin R.clusterCount, ξ * (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hunionNat := Finset.card_union_le
        (C.edgeFinsetIn .red (R.clusters i))
        (C.edgeFinsetIn .green (R.clusters i))
      have hunion :
          ((C.edgeFinsetIn .red (R.clusters i) ∪
              C.edgeFinsetIn .green (R.clusters i)).card : ℝ) ≤
            (C.redEdgeCountIn (R.clusters i) : ℝ) +
              (C.greenEdgeCountIn (R.clusters i) : ℝ) := by
        exact_mod_cast hunionNat
      exact hunion.trans (R.redGreenInside_le_sq hξ i)
    _ = (R.clusterCount : ℝ) * ξ * (n : ℝ) ^ 2 := by
      simp
      ring

private theorem extractionBetweenWrongPiece_card_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1)
    (p : Fin R.clusterCount × Fin R.clusterCount) :
    (((if p.1 = p.2 then ∅
      else if R.reducedGraph.Adj p.1 p.2 then
        C.unorderedColorInteredges .green (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)
      else
        C.unorderedColorInteredges .red (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)).card : ℝ) ≤
      ξ * (n : ℝ) ^ 2) := by
  classical
  by_cases hp : p.1 = p.2
  · simp only [hp, ↓reduceIte, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hξ0 (sq_nonneg _)
  · have hdisj : Disjoint (R.clusters p.1) (R.clusters p.2) :=
      R.clusters_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hp
    by_cases hadj : R.reducedGraph.Adj p.1 p.2
    · have hdense := R.redDenseOnEdges p.1 p.2 hadj
      have hdensePos : 0 < C.colorDensity .red (R.clusters p.1) (R.clusters p.2) :=
        (sub_pos.mpr hξ1).trans_le hdense
      have hleft := left_nonempty_of_colorDensity_pos C .red
        (R.clusters p.1) (R.clusters p.2) hdensePos
      have hright := right_nonempty_of_colorDensity_pos C .red
        (R.clusters p.1) (R.clusters p.2) hdensePos
      have hunionNat := Finset.card_union_le
        (C.unorderedColorInteredges .green (R.clusters p.1) (R.clusters p.2))
        (C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2))
      have hgreen := C.unorderedColorInteredges_card_le .green
        (R.clusters p.1) (R.clusters p.2)
      have hblue := C.unorderedColorInteredges_card_le .blue
        (R.clusters p.1) (R.clusters p.2)
      have hsupport :
          ((C.unorderedColorInteredges .green (R.clusters p.1) (R.clusters p.2) ∪
            C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)).card : ℝ) ≤
          (C.colorEdgeCountBetween .green (R.clusters p.1) (R.clusters p.2) : ℝ) +
            (C.colorEdgeCountBetween .blue (R.clusters p.1) (R.clusters p.2) : ℝ) := by
        exact_mod_cast hunionNat.trans (Nat.add_le_add hgreen hblue)
      simp only [hp, ↓reduceIte, hadj]
      exact hsupport.trans
        (green_add_blue_colorEdgeCountBetween_le_sq_of_redDensity C
          hleft hright hdisj ξ hξ0 hdense)
    · have hdense := R.greenDenseOnNonedges p.1 p.2 hp hadj
      have hdensePos : 0 < C.colorDensity .green (R.clusters p.1) (R.clusters p.2) :=
        (sub_pos.mpr hξ1).trans_le hdense
      have hleft := left_nonempty_of_colorDensity_pos C .green
        (R.clusters p.1) (R.clusters p.2) hdensePos
      have hright := right_nonempty_of_colorDensity_pos C .green
        (R.clusters p.1) (R.clusters p.2) hdensePos
      have hunionNat := Finset.card_union_le
        (C.unorderedColorInteredges .red (R.clusters p.1) (R.clusters p.2))
        (C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2))
      have hred := C.unorderedColorInteredges_card_le .red
        (R.clusters p.1) (R.clusters p.2)
      have hblue := C.unorderedColorInteredges_card_le .blue
        (R.clusters p.1) (R.clusters p.2)
      have hsupport :
          ((C.unorderedColorInteredges .red (R.clusters p.1) (R.clusters p.2) ∪
            C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)).card : ℝ) ≤
          (C.colorEdgeCountBetween .red (R.clusters p.1) (R.clusters p.2) : ℝ) +
            (C.colorEdgeCountBetween .blue (R.clusters p.1) (R.clusters p.2) : ℝ) := by
        exact_mod_cast hunionNat.trans (Nat.add_le_add hred hblue)
      simp only [hp, ↓reduceIte, hadj]
      exact hsupport.trans
        (red_add_blue_colorEdgeCountBetween_le_sq_of_greenDensity C
          hleft hright hdisj ξ hξ0 hdense)

private theorem extractionBetweenWrongSupport_card_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) :
    ((extractionBetweenWrongSupport R).card : ℝ) ≤
      (R.clusterCount : ℝ) ^ 2 * ξ * (n : ℝ) ^ 2 := by
  let piece : (Fin R.clusterCount × Fin R.clusterCount) → Finset (Sym2 (Fin n)) :=
    fun p ↦
      if p.1 = p.2 then ∅
      else if R.reducedGraph.Adj p.1 p.2 then
        C.unorderedColorInteredges .green (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)
      else
        C.unorderedColorInteredges .red (R.clusters p.1) (R.clusters p.2) ∪
          C.unorderedColorInteredges .blue (R.clusters p.1) (R.clusters p.2)
  have hcardNat :
      (extractionBetweenWrongSupport R).card ≤
        ∑ p : Fin R.clusterCount × Fin R.clusterCount, (piece p).card := by
    unfold extractionBetweenWrongSupport
    exact Finset.card_biUnion_le
  have hcard :
      ((extractionBetweenWrongSupport R).card : ℝ) ≤
        ∑ p : Fin R.clusterCount × Fin R.clusterCount, ((piece p).card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    ((extractionBetweenWrongSupport R).card : ℝ) ≤
        ∑ p : Fin R.clusterCount × Fin R.clusterCount,
          ((piece p).card : ℝ) := hcard
    _ ≤ ∑ _p : Fin R.clusterCount × Fin R.clusterCount,
        ξ * (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact extractionBetweenWrongPiece_card_le R hξ0 hξ1 p
    _ = (R.clusterCount : ℝ) ^ 2 * ξ * (n : ℝ) ^ 2 := by
      simp
      ring

private theorem extractionBoundaryWrongSupport_card_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) :
    ((extractionBoundaryWrongSupport R).card : ℝ) ≤
      ξ * (n : ℝ) ^ 2 := by
  let S := coreExtractionCore R.exceptional R.clusters
  let T := coreExtractionRemainder R.exceptional R.clusters
  have hunionNat := Finset.card_union_le
    (C.unorderedColorInteredges .red S T)
    (C.unorderedColorInteredges .blue S T)
  have hred := C.unorderedColorInteredges_card_le .red S T
  have hblue := C.unorderedColorInteredges_card_le .blue S T
  have hsupport :
      ((extractionBoundaryWrongSupport R).card : ℝ) ≤
        (C.colorEdgeCountBetween .red S T : ℝ) +
          (C.colorEdgeCountBetween .blue S T : ℝ) := by
    exact_mod_cast hunionNat.trans (Nat.add_le_add hred hblue)
  exact hsupport.trans R.boundarySmall

private theorem cluster_index_eq_of_mem
    {I V : Type*} [DecidableEq I]
    (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    {i j : I} {x : V} (hxi : x ∈ clusters i) (hxj : x ∈ clusters j) :
    i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp
    (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hxi hxj

private theorem clusterBlowupColoring_color_same
    {I V : Type*} [DecidableEq V] (R : SimpleGraph I)
    (clusters : I → Finset V) (i : I) {x y : V}
    (hx : x ∈ clusters i) (hy : y ∈ clusters i) :
    (clusterBlowupColoring R clusters).color x y = .blue := by
  by_cases hxy : x = y
  · subst y
    simp
  · rw [clusterBlowupColoring_color_of_ne R clusters hxy]
    have hsame : SameClusterPair clusters x y := ⟨i, hx, hy⟩
    simp [hsame]

private theorem clusterBlowupColoring_color_adj
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (R : SimpleGraph I) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    {i j : I} (hij : R.Adj i j) {x y : V}
    (hx : x ∈ clusters i) (hy : y ∈ clusters j) :
    (clusterBlowupColoring R clusters).color x y = .red := by
  have hijne : i ≠ j := R.ne_of_adj hij
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Finset.disjoint_left.mp
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hijne) hx hy
  have hsame : ¬ SameClusterPair clusters x y := by
    rintro ⟨a, hxa, hya⟩
    have hia := cluster_index_eq_of_mem clusters hdisj hx hxa
    have hja := cluster_index_eq_of_mem clusters hdisj hy hya
    exact hijne (hia.trans hja.symm)
  have hadj : ReducedAdjacentPair R clusters x y :=
    ⟨i, j, hij, hx, hy⟩
  rw [clusterBlowupColoring_color_of_ne R clusters hxy]
  simp [hsame, hadj]

private theorem clusterBlowupColoring_color_nonadj
    {I V : Type*} [DecidableEq I] [DecidableEq V]
    (R : SimpleGraph I) (clusters : I → Finset V)
    (hdisj : Set.PairwiseDisjoint (Set.univ : Set I) clusters)
    {i j : I} (hij : i ≠ j) (hnadj : ¬ R.Adj i j) {x y : V}
    (hx : x ∈ clusters i) (hy : y ∈ clusters j) :
    (clusterBlowupColoring R clusters).color x y = .green := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Finset.disjoint_left.mp
      (hdisj (Set.mem_univ i) (Set.mem_univ j) hij) hx hy
  have hsame : ¬ SameClusterPair clusters x y := by
    rintro ⟨a, hxa, hya⟩
    have hia := cluster_index_eq_of_mem clusters hdisj hx hxa
    have hja := cluster_index_eq_of_mem clusters hdisj hy hya
    exact hij (hia.trans hja.symm)
  have hred : ¬ ReducedAdjacentPair R clusters x y := by
    rintro ⟨a, b, hab, hxa, hyb⟩
    have hia := cluster_index_eq_of_mem clusters hdisj hx hxa
    have hjb := cluster_index_eq_of_mem clusters hdisj hy hyb
    apply hnadj
    simpa [hia, hjb] using hab
  rw [clusterBlowupColoring_color_of_ne R clusters hxy]
  simp [hsame, hred]

private theorem clusterBlowupColoring_color_green_of_right_outside
    {I V : Type*} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (R : SimpleGraph I) (clusters : I → Finset V) {x y : V}
    (hxy : x ≠ y) (hy : y ∉ clusterUnion clusters) :
    (clusterBlowupColoring R clusters).color x y = .green := by
  have hsame : ¬ SameClusterPair clusters x y := by
    rintro ⟨i, _, hyi⟩
    exact hy (cluster_subset_clusterUnion clusters i hyi)
  have hred : ¬ ReducedAdjacentPair R clusters x y := by
    rintro ⟨i, j, _, _, hyj⟩
    exact hy (cluster_subset_clusterUnion clusters j hyj)
  rw [clusterBlowupColoring_color_of_ne R clusters hxy]
  simp [hsame, hred]

private theorem coloringHammingSupport_oldPartition_subset
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) :
    coloringHammingSupport C
        (overlayInside
          (clusterBlowupColoring R.reducedGraph R.clusters) C
          (coreExtractionRemainder R.exceptional R.clusters)) ⊆
      extractionOldPartitionWrongSupport R := by
  classical
  let U : Finset (Fin n) := coreExtractionClusterUnion R.clusters
  let S : Finset (Fin n) := coreExtractionCore R.exceptional R.clusters
  let T : Finset (Fin n) := coreExtractionRemainder R.exceptional R.clusters
  let B : ColoredGraph (Fin n) :=
    clusterBlowupColoring R.reducedGraph R.clusters
  change coloringHammingSupport C (overlayInside B C T) ⊆
    extractionOldPartitionWrongSupport R
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [pair_mem_coloringHammingSupport] at he
      obtain ⟨hxy, hdiff⟩ := he
      have endpoint_mem_core_or_remainder (z : Fin n) : z ∈ S ∨ z ∈ T := by
        by_cases hz : z ∈ S
        · exact Or.inl hz
        · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)
      rcases endpoint_mem_core_or_remainder x with hxS | hxT
      · rcases endpoint_mem_core_or_remainder y with hyS | hyT
        · have hxT : x ∉ T := fun hxT ↦ (Finset.mem_sdiff.mp hxT).2 hxS
          have hyT : y ∉ T := fun hyT ↦ (Finset.mem_sdiff.mp hyT).2 hyS
          have hover :
              (overlayInside B C T).color x y = B.color x y :=
            overlayInside_color_of_not_both B C T hxy (by simp [hxT])
          have hxEU : x ∈ R.exceptional ∨ x ∈ U := by
            simpa [S, U, coreExtractionCore] using hxS
          have hyEU : y ∈ R.exceptional ∨ y ∈ U := by
            simpa [S, U, coreExtractionCore] using hyS
          rcases hxEU with hxE | hxU
          · have hinc : s(x, y) ∈ unorderedPairsIncidentTo R.exceptional :=
              pair_mem_unorderedPairsIncidentTo_left R.exceptional hxE
            simpa [extractionOldPartitionWrongSupport, hinc]
          · rcases hyEU with hyE | hyU
            · have hinc : s(x, y) ∈ unorderedPairsIncidentTo R.exceptional :=
                pair_mem_unorderedPairsIncidentTo_right R.exceptional hyE
              simpa [extractionOldPartitionWrongSupport, hinc]
            · change x ∈ clusterUnion R.clusters at hxU
              change y ∈ clusterUnion R.clusters at hyU
              rw [mem_clusterUnion_iff] at hxU hyU
              obtain ⟨i, hxi⟩ := hxU
              obtain ⟨j, hyj⟩ := hyU
              by_cases hij : i = j
              · subst j
                have hB : B.color x y = .blue := by
                  exact clusterBlowupColoring_color_same R.reducedGraph
                    R.clusters i hxi hyj
                have htarget : (overlayInside B C T).color x y = .blue :=
                  hover.trans hB
                have hCne : C.color x y ≠ .blue := fun hc ↦
                  hdiff (hc.trans htarget.symm)
                have hinternal : s(x, y) ∈ extractionInternalWrongSupport R := by
                  unfold extractionInternalWrongSupport
                  rw [Finset.mem_biUnion]
                  refine ⟨i, Finset.mem_univ i, ?_⟩
                  cases hc : C.color x y with
                  | red =>
                      exact Finset.mem_union_left _
                        ((C.pair_mem_edgeFinsetIn .red (R.clusters i) x y).2
                          ⟨hxy, hc, hxi, hyj⟩)
                  | green =>
                      exact Finset.mem_union_right _
                        ((C.pair_mem_edgeFinsetIn .green (R.clusters i) x y).2
                          ⟨hxy, hc, hxi, hyj⟩)
                  | blue => exact (hCne hc).elim
                simpa [extractionOldPartitionWrongSupport, hinternal]
              · by_cases hadj : R.reducedGraph.Adj i j
                · have hB : B.color x y = .red := by
                    exact clusterBlowupColoring_color_adj R.reducedGraph R.clusters
                      R.clusters_pairwiseDisjoint hadj hxi hyj
                  have htarget : (overlayInside B C T).color x y = .red :=
                    hover.trans hB
                  have hCne : C.color x y ≠ .red := fun hc ↦
                    hdiff (hc.trans htarget.symm)
                  have hbetween : s(x, y) ∈ extractionBetweenWrongSupport R := by
                    unfold extractionBetweenWrongSupport
                    rw [Finset.mem_biUnion]
                    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
                    simp only [hij, ↓reduceIte, hadj]
                    cases hc : C.color x y with
                    | red => exact (hCne hc).elim
                    | green =>
                        exact Finset.mem_union_left _
                          (C.pair_mem_unorderedColorInteredges .green
                            (R.clusters i) (R.clusters j) hxi hyj hc hxy)
                    | blue =>
                        exact Finset.mem_union_right _
                          (C.pair_mem_unorderedColorInteredges .blue
                            (R.clusters i) (R.clusters j) hxi hyj hc hxy)
                  simpa [extractionOldPartitionWrongSupport, hbetween]
                · have hB : B.color x y = .green := by
                    exact clusterBlowupColoring_color_nonadj R.reducedGraph R.clusters
                      R.clusters_pairwiseDisjoint hij hadj hxi hyj
                  have htarget : (overlayInside B C T).color x y = .green :=
                    hover.trans hB
                  have hCne : C.color x y ≠ .green := fun hc ↦
                    hdiff (hc.trans htarget.symm)
                  have hbetween : s(x, y) ∈ extractionBetweenWrongSupport R := by
                    unfold extractionBetweenWrongSupport
                    rw [Finset.mem_biUnion]
                    refine ⟨(i, j), Finset.mem_univ _, ?_⟩
                    simp only [hij, ↓reduceIte, hadj]
                    cases hc : C.color x y with
                    | red =>
                        exact Finset.mem_union_left _
                          (C.pair_mem_unorderedColorInteredges .red
                            (R.clusters i) (R.clusters j) hxi hyj hc hxy)
                    | green => exact (hCne hc).elim
                    | blue =>
                        exact Finset.mem_union_right _
                          (C.pair_mem_unorderedColorInteredges .blue
                            (R.clusters i) (R.clusters j) hxi hyj hc hxy)
                  simpa [extractionOldPartitionWrongSupport, hbetween]
        · have hyU : y ∉ U := by
            intro hyU
            exact (Finset.mem_sdiff.mp hyT).2 (by
              change y ∈ R.exceptional ∪ U
              exact Finset.mem_union_right _ hyU)
          have hB : B.color x y = .green := by
            change y ∉ clusterUnion R.clusters at hyU
            exact clusterBlowupColoring_color_green_of_right_outside
              R.reducedGraph R.clusters hxy hyU
          have hover : (overlayInside B C T).color x y = B.color x y :=
            overlayInside_color_of_not_both B C T hxy (by
              intro hboth
              exact (Finset.mem_sdiff.mp hboth.1).2 hxS)
          have htarget : (overlayInside B C T).color x y = .green :=
            hover.trans hB
          have hCne : C.color x y ≠ .green := fun hc ↦
            hdiff (hc.trans htarget.symm)
          have hboundary : s(x, y) ∈ extractionBoundaryWrongSupport R := by
            unfold extractionBoundaryWrongSupport
            cases hc : C.color x y with
            | red =>
                exact Finset.mem_union_left _
                  (C.pair_mem_unorderedColorInteredges .red S T
                    hxS hyT hc hxy)
            | green => exact (hCne hc).elim
            | blue =>
                exact Finset.mem_union_right _
                  (C.pair_mem_unorderedColorInteredges .blue S T
                    hxS hyT hc hxy)
          unfold extractionOldPartitionWrongSupport
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hboundary)
      · rcases endpoint_mem_core_or_remainder y with hyS | hyT
        · have hxU : x ∉ U := by
            intro hxU
            exact (Finset.mem_sdiff.mp hxT).2 (by
              change x ∈ R.exceptional ∪ U
              exact Finset.mem_union_right _ hxU)
          have hB : B.color x y = .green := by
            rw [B.color_comm]
            change x ∉ clusterUnion R.clusters at hxU
            exact clusterBlowupColoring_color_green_of_right_outside
              R.reducedGraph R.clusters hxy.symm hxU
          have hover : (overlayInside B C T).color x y = B.color x y :=
            overlayInside_color_of_not_both B C T hxy (by
              intro hboth
              exact (Finset.mem_sdiff.mp hboth.2).2 hyS)
          have htarget : (overlayInside B C T).color x y = .green :=
            hover.trans hB
          have hCne : C.color x y ≠ .green := fun hc ↦
            hdiff (hc.trans htarget.symm)
          have hboundary : s(x, y) ∈ extractionBoundaryWrongSupport R := by
            unfold extractionBoundaryWrongSupport
            cases hc : C.color x y with
            | red =>
                have hm := C.pair_mem_unorderedColorInteredges .red S T
                  hyS hxT (by simpa only [C.color_comm] using hc) hxy.symm
                rw [Sym2.eq_swap] at hm
                exact Finset.mem_union_left _ hm
            | green => exact (hCne hc).elim
            | blue =>
                have hm := C.pair_mem_unorderedColorInteredges .blue S T
                  hyS hxT (by simpa only [C.color_comm] using hc) hxy.symm
                rw [Sym2.eq_swap] at hm
                exact Finset.mem_union_right _ hm
          unfold extractionOldPartitionWrongSupport
          exact Finset.mem_union_left _
            (Finset.mem_union_right _ hboundary)
        · have heq := overlayInside_color_of_mem B C T hxT hyT
          exact (hdiff heq.symm).elim

private theorem extractionOldPartitionWrongSupport_card_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) :
    ((extractionOldPartitionWrongSupport R).card : ℝ) ≤
      ((R.clusterCount : ℝ) ^ 2 + (R.clusterCount : ℝ) + 2) *
        ξ * (n : ℝ) ^ 2 := by
  let I := extractionInternalWrongSupport R
  let P := extractionBetweenWrongSupport R
  let D := extractionBoundaryWrongSupport R
  let E := unorderedPairsIncidentTo R.exceptional
  have hIP := Finset.card_union_le I P
  have hIPD := Finset.card_union_le (I ∪ P) D
  have hIPDE := Finset.card_union_le ((I ∪ P) ∪ D) E
  have hcardNat :
      (extractionOldPartitionWrongSupport R).card ≤
        I.card + P.card + D.card + E.card := by
    change (((I ∪ P) ∪ D) ∪ E).card ≤
      I.card + P.card + D.card + E.card
    omega
  have hcard :
      ((extractionOldPartitionWrongSupport R).card : ℝ) ≤
        (I.card : ℝ) + (P.card : ℝ) + (D.card : ℝ) + (E.card : ℝ) := by
    exact_mod_cast hcardNat
  have hI : (I.card : ℝ) ≤
      (R.clusterCount : ℝ) * ξ * (n : ℝ) ^ 2 := by
    exact extractionInternalWrongSupport_card_le R hξ0
  have hP : (P.card : ℝ) ≤
      (R.clusterCount : ℝ) ^ 2 * ξ * (n : ℝ) ^ 2 := by
    exact extractionBetweenWrongSupport_card_le R hξ0 hξ1
  have hD : (D.card : ℝ) ≤ ξ * (n : ℝ) ^ 2 := by
    exact extractionBoundaryWrongSupport_card_le R
  have hE : (E.card : ℝ) ≤ ξ * (n : ℝ) ^ 2 := by
    exact unorderedPairsIncidentTo_card_le_sq R.exceptional ξ hξ0
      R.exceptionalSmall
  calc
    ((extractionOldPartitionWrongSupport R).card : ℝ) ≤
        (I.card : ℝ) + (P.card : ℝ) + (D.card : ℝ) + (E.card : ℝ) := hcard
    _ ≤ (R.clusterCount : ℝ) * ξ * (n : ℝ) ^ 2 +
          (R.clusterCount : ℝ) ^ 2 * ξ * (n : ℝ) ^ 2 +
          ξ * (n : ℝ) ^ 2 + ξ * (n : ℝ) ^ 2 := by
      exact add_le_add (add_le_add (add_le_add hI hP) hD) hE
    _ = ((R.clusterCount : ℝ) ^ 2 + (R.clusterCount : ℝ) + 2) *
          ξ * (n : ℝ) ^ 2 := by ring

/-- One extraction stage, before balancing the clusters, differs from the
old-partition reduced-graph blow-up (while retaining the original coloring
on the remainder) on at most `(ℓ² + ℓ + 2) ξ n²` unordered edges. -/
theorem coreExtraction_oldPartition_hamming_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η inputDelta ξ c : ℝ}
    (R : CoreExtractionResult k n C η inputDelta ξ c)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) :
    (coloringHammingDistance C
      (overlayInside
        (clusterBlowupColoring R.reducedGraph R.clusters) C
        (coreExtractionRemainder R.exceptional R.clusters)) : ℝ) ≤
      ((R.clusterCount : ℝ) ^ 2 + (R.clusterCount : ℝ) + 2) *
        ξ * (n : ℝ) ^ 2 := by
  have hdistNat := coloringHammingDistance_le_card_of_support_subset C
    (overlayInside
      (clusterBlowupColoring R.reducedGraph R.clusters) C
      (coreExtractionRemainder R.exceptional R.clusters))
    (extractionOldPartitionWrongSupport R)
    (coloringHammingSupport_oldPartition_subset R)
  have hdist :
      (coloringHammingDistance C
        (overlayInside
          (clusterBlowupColoring R.reducedGraph R.clusters) C
          (coreExtractionRemainder R.exceptional R.clusters)) : ℝ) ≤
        ((extractionOldPartitionWrongSupport R).card : ℝ) := by
    exact_mod_cast hdistNat
  exact hdist.trans (extractionOldPartitionWrongSupport_card_le R hξ0 hξ1)



/-- A real lower bound of three on the extraction scale forces every old
cluster to contain at least three vertices. -/
theorem CoreExtractionResult.three_le_cluster_card
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hthree : (3 : ℝ) ≤ c * (n : ℝ)) (i : Fin R.clusterCount) :
    3 ≤ (R.clusters i).card := by
  have h := hthree.trans (R.clusterLowerBound i)
  exact_mod_cast h

/-- The paper-style threshold `3 / c ≤ n`, with `c > 0`, is a convenient
way to discharge the scale hypothesis in `three_le_cluster_card`. -/
theorem CoreExtractionResult.three_le_cluster_card_of_div_le
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hc : 0 < c) (hn : 3 / c ≤ (n : ℝ)) (i : Fin R.clusterCount) :
    3 ≤ (R.clusters i).card := by
  apply R.three_le_cluster_card (i := i)
  rw [div_le_iff₀ hc] at hn
  simpa [mul_comm] using hn

/-- A real absolute-difference bound gives the exact natural-distance bound
needed by `exists_equitableRepartition`, with no additive rounding loss. -/
theorem natDist_le_floor_of_abs_cast_sub_le
    {a b : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (h : |(a : ℝ) - (b : ℝ)| ≤ x) :
    Nat.dist a b ≤ ⌊x⌋₊ := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab, Nat.le_floor_iff hx]
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    rw [abs_of_nonpos (sub_nonpos.mpr hab'), neg_sub] at h
    simpa [Nat.cast_sub hab] using h
  · rw [Nat.dist_eq_sub_of_le_right hba, Nat.le_floor_iff hx]
    have hba' : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    rw [abs_of_nonneg (sub_nonneg.mpr hba')] at h
    simpa [Nat.cast_sub hba] using h

/-- The balance conclusion of core extraction supplies the natural-distance
hypothesis for equitable repartition at error `floor (ξ n)`. -/
theorem CoreExtractionResult.clusterNatDist_le_floor
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c) (hξ : 0 ≤ ξ)
    (i j : Fin R.clusterCount) :
    Nat.dist (R.clusters i).card (R.clusters j).card ≤
      ⌊ξ * (n : ℝ)⌋₊ := by
  apply natDist_le_floor_of_abs_cast_sub_le
  · positivity
  · exact R.clusterBalanced i j

/-- If a family of parts, each of size at least three, is repartitioned
without changing its union and the new sizes are equitable, then every new
part still has size at least three (and hence at least two). -/
theorem three_le_card_of_equitable_sameUnion
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} (hq : 0 < q)
    (old balanced : Fin q → Finset V)
    (holdDisj : Set.PairwiseDisjoint (Set.univ : Set (Fin q)) old)
    (hbalancedDisj :
      Set.PairwiseDisjoint (Set.univ : Set (Fin q)) balanced)
    (hunion : clusterUnion balanced = clusterUnion old)
    (hequitable : Set.EquitableOn (Set.univ : Set (Fin q))
      (fun i ↦ (balanced i).card))
    (hthree : ∀ i, 3 ≤ (old i).card) (i : Fin q) :
    3 ≤ (balanced i).card := by
  have holdSum : 3 * q ≤ ∑ j : Fin q, (old j).card := by
    calc
      3 * q = ∑ _j : Fin q, 3 := by simp [mul_comm]
      _ ≤ ∑ j : Fin q, (old j).card := by
        exact Finset.sum_le_sum fun j _ ↦ hthree j
  have hsumEq :
      ∑ j : Fin q, (balanced j).card = ∑ j : Fin q, (old j).card := by
    rw [← card_clusterUnion balanced hbalancedDisj,
      ← card_clusterUnion old holdDisj, hunion]
  have havg : 3 ≤ (∑ j : Fin q, (balanced j).card) / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [hsumEq] using holdSum
  have hminimum :
      (∑ j : Fin q, (balanced j).card) / q ≤ (balanced i).card := by
    have hequitable' :
        Set.EquitableOn ((Finset.univ : Finset (Fin q)) : Set (Fin q))
          (fun j ↦ (balanced j).card) := by
      simpa using hequitable
    have h := Finset.EquitableOn.le hequitable' (Finset.mem_univ i)
    simpa using h
  exact havg.trans hminimum

/-- Complete one-shot packaging: equitably repartition the extracted
clusters, retain their union and the standard moved-set bound, and obtain
the size-two hypothesis needed for componentwise exact core shapes. -/
theorem CoreExtractionResult.exists_balancedClustersForExtremalShape
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hk : 3 ≤ k) (hξ : 0 ≤ ξ)
    (hthree : (3 : ℝ) ≤ c * (n : ℝ)) :
    ∃ balanced : Fin R.clusterCount → Finset (Fin n),
      (∀ i, (balanced i).Nonempty) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin R.clusterCount)) balanced ∧
      clusterUnion balanced = clusterUnion R.clusters ∧
      (∀ i j, (balanced i).card ≤ (balanced j).card + 1) ∧
      (clusterUnion fun i ↦ R.clusters i \ balanced i).card ≤
        R.clusterCount * ⌊ξ * (n : ℝ)⌋₊ ∧
      ∀ i, 2 ≤ (balanced i).card := by
  have hq : 0 < R.clusterCount := by
    have hcount := R.clusterCount_ge
    omega
  obtain ⟨balanced, hnonempty, hdisj, hunion, hequitable, hmoved⟩ :=
    exists_equitableRepartition hq R.clusters
      (fun i ↦ Finset.card_pos.mp (by
        have hi := R.three_le_cluster_card hthree i
        omega))
      R.clusters_pairwiseDisjoint
      (R.clusterNatDist_le_floor hξ)
  refine ⟨balanced, hnonempty, hdisj, hunion, ?_, hmoved, ?_⟩
  · intro i j
    exact hequitable (Set.mem_univ i) (Set.mem_univ j)
  · intro i
    have hthreeBalanced := three_le_card_of_equitable_sameUnion hq
      R.clusters balanced R.clusters_pairwiseDisjoint hdisj hunion
      hequitable (R.three_le_cluster_card hthree) i
    omega

/-- The fully assembled form of the preceding result.  Besides returning the
balanced clusters, it constructs the exact extremal-family shape obtained by
splitting the regular reduced graph into connected components.  Its
canonical coloring is definitionally characterized by the reduced-graph
blow-up, and every component support has at least `k` vertices. -/
theorem CoreExtractionResult.exists_balancedExtremalFamilyShape
    {k n : ℕ} {C : ColoredGraph (Fin n)} {η δ ξ c : ℝ}
    (R : CoreExtractionResult k n C η δ ξ c)
    (hk : 3 ≤ k) (hξ : 0 ≤ ξ)
    (hthree : (3 : ℝ) ≤ c * (n : ℝ)) :
    ∃ balanced : Fin R.clusterCount → Finset (Fin n),
      (∀ i, (balanced i).Nonempty) ∧
      Set.PairwiseDisjoint (Set.univ : Set (Fin R.clusterCount)) balanced ∧
      clusterUnion balanced = clusterUnion R.clusters ∧
      (∀ i j, (balanced i).card ≤ (balanced j).card + 1) ∧
      (clusterUnion fun i ↦ R.clusters i \ balanced i).card ≤
        R.clusterCount * ⌊ξ * (n : ℝ)⌋₊ ∧
      (∀ i, 2 ≤ (balanced i).card) ∧
      ∃ E : ExtremalFamilyShape k (Fin n),
        clusterUnion (fun a ↦ (E.shapes a).support) =
            clusterUnion R.clusters ∧
        E.canonicalColoring =
            clusterBlowupColoring R.reducedGraph balanced ∧
        ∀ a, k ≤ (E.shapes a).support.card := by
  obtain ⟨balanced, hnonempty, hdisj, hunion, hequitable, hmoved, htwo⟩ :=
    R.exists_balancedClustersForExtremalShape hk hξ hthree
  letI := R.reducedGraphAdjDecidable
  have hregular : R.reducedGraph.IsRegularOfDegree (delta k) :=
    R.reducedGraph_regular
  let E : ExtremalFamilyShape k (Fin n) :=
    connectedComponentExtremalFamilyShape R.reducedGraph balanced
      hnonempty hdisj hequitable htwo hk hregular
  refine ⟨balanced, hnonempty, hdisj, hunion, hequitable, hmoved, htwo,
    E, ?_, ?_, ?_⟩
  · calc
      clusterUnion (fun a ↦ (E.shapes a).support) =
          clusterUnion balanced := by
            dsimp only [E]
            exact connectedComponentExtremalFamilyShape_supportUnion
              R.reducedGraph balanced hnonempty hdisj hequitable htwo hk hregular
      _ = clusterUnion R.clusters := hunion
  · dsimp only [E]
    exact
      connectedComponentExtremalFamilyShape_canonicalColoring_eq_clusterBlowupColoring
        R.reducedGraph balanced hnonempty hdisj hequitable htwo hk hregular
  · intro a
    exact (E.shapes a).coreSize_lower



/-- Lowering the advertised cluster scale preserves a core-extraction
certificate. -/
noncomputable def CoreExtractionResult.weakenClusterScale
    {k n : ℕ} {C : ColoredGraph (Fin n)} {eta inputDelta xi c c' : ℝ}
    (R : CoreExtractionResult k n C eta inputDelta xi c) (hcc : c' ≤ c) :
    CoreExtractionResult k n C eta inputDelta xi c' := {
  clusterCount := R.clusterCount
  clusterCount_ge := R.clusterCount_ge
  exceptional := R.exceptional
  clusters := R.clusters
  clusters_pairwiseDisjoint := R.clusters_pairwiseDisjoint
  exceptional_disjoint_clusters := R.exceptional_disjoint_clusters
  reducedGraph := R.reducedGraph
  reducedGraphAdjDecidable := R.reducedGraphAdjDecidable
  reducedGraph_regular := R.reducedGraph_regular
  blueDense := R.blueDense
  clusterLowerBound := fun i ↦ (mul_le_mul_of_nonneg_right hcc (by positivity)).trans
    (R.clusterLowerBound i)
  clusterBalanced := R.clusterBalanced
  exceptionalSmall := R.exceptionalSmall
  clusterUnionLarge := R.clusterUnionLarge
  redDenseOnEdges := R.redDenseOnEdges
  greenDenseOnNonedges := R.greenDenseOnNonedges
  boundarySmall := R.boundarySmall
  remainderNearExtremal := R.remainderNearExtremal
}

/-- A successful extraction removes a fixed fraction of the current
ambient vertices. -/
theorem CoreExtractionResult.remainder_card_le_contraction
    {k n : ℕ} {C : ColoredGraph (Fin n)} {eta inputDelta xi c : ℝ}
    (R : CoreExtractionResult k n C eta inputDelta xi c)
    (heta : 0 < eta) (hxi : xi < eta / 20) :
    ((coreExtractionRemainder R.exceptional R.clusters).card : ℝ) ≤
      (1 - eta / 2) * (n : ℝ) := by
  let U := coreExtractionClusterUnion R.clusters
  let T := coreExtractionRemainder R.exceptional R.clusters
  have hUT : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro x hxU hxT
    have hxCore : x ∈ coreExtractionCore R.exceptional R.clusters := by
      exact Finset.mem_union_right _ hxU
    exact (Finset.mem_sdiff.mp hxT).2 hxCore
  have hcardNat : U.card + T.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hUT]
    simpa using Finset.card_le_univ (U ∪ T)
  have hcard : (U.card : ℝ) + (T.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hcardNat
  have hcovered : (eta / 2) * (n : ℝ) ≤ (U.card : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hlarge := R.clusterUnionLarge
    change (eta - xi) * (n : ℝ) ≤ (U.card : ℝ) at hlarge
    nlinarith
  change (T.card : ℝ) ≤ (1 - eta / 2) * (n : ℝ)
  nlinarith

/-- The extraction remainder, transferred to its canonical `Fin` type,
inherits the exact objective lower bound. -/
theorem CoreExtractionResult.remainder_nearExtremal_restrictToFin
    {k n : ℕ} {C : ColoredGraph (Fin n)} {eta inputDelta xi c : ℝ}
    (R : CoreExtractionResult k n C eta inputDelta xi c) :
    -((inputDelta + xi) * (n : ℝ) ^ 2) ≤
      (objective k (C.restrictToFin
        (coreExtractionRemainder R.exceptional R.clusters)) : ℝ) := by
  rw [objective_restrictToFin]
  unfold objectiveIn
  push_cast
  exact R.remainderNearExtremal

/-- The exact local output consumed by the finite outer stability
iteration.  Its shape contains the newly extracted regular cores and lies
outside the remainder; its canonical overlay costs at most `K xi n²` edits. -/
structure CoreStageEdit
    {k n : ℕ} {C : ColoredGraph (Fin n)} {eta inputDelta xi c : ℝ}
    (R : CoreExtractionResult k n C eta inputDelta xi c) (K : ℝ) where
  shape : ExtremalFamilyShape k (Fin n)
  support_disjoint_remainder : ∀ a,
    Disjoint (shape.shapes a).support
      (coreExtractionRemainder R.exceptional R.clusters)
  hamming_le :
    (coloringHammingDistance C
      (overlayInside shape.canonicalColoring C
        (coreExtractionRemainder R.exceptional R.clusters)) : ℝ) ≤
      K * xi * (n : ℝ) ^ 2

/-- Every shape transported into a finite remainder is supported in that
remainder. -/
theorem mappedShape_support_subset
    {k n : ℕ} (T : Finset (Fin n))
    (E : ExtremalFamilyShape k (Fin T.card)) (a : Fin E.shapeCount) :
    ((E.map (restrictionEmbedding T)).shapes a).support ⊆ T := by
  intro x hx
  change x ∈ (E.shapes a).support.map (restrictionEmbedding T) at hx
  obtain ⟨y, _hy, rfl⟩ := Finset.mem_map.mp hx
  exact restrictionEmbedding_mem T y

/-- Output certificate for the bounded outer extraction iteration. -/
structure StabilityIterationResult
    (k m N : ℕ) (epsilon : ℝ) (C : ColoredGraph (Fin m)) where
  target : ExtremalFamilyShape k (Fin m)
  hamming_le :
    (coloringHammingDistance C target.canonicalColoring : ℝ) ≤
      stabilityEpsilon epsilon / 4 * (m : ℝ) ^ 2 +
        stabilityEpsilon epsilon * (N : ℝ) ^ 2 / 20

/-- Abstract availability of the proved one-stage editing construction. -/
def CoreStageEditor (k : ℕ) (epsilon c K : ℝ) : Prop :=
  ∀ {m : ℕ} {C : ColoredGraph (Fin m)} {inputDelta xi : ℝ}
    (R : CoreExtractionResult k m C (stabilityEta epsilon) inputDelta xi c),
    xi ∈ Set.Ioo (0 : ℝ) (stabilityEta epsilon / 20) →
    (3 : ℝ) ≤ c * (m : ℝ) → Nonempty (CoreStageEdit R K)

/-- The finite outer iteration.  The powered shrinkage invariant makes the
terminal hierarchy level small; at nonterminal levels the proof either
stops at all green or consumes one `kthOrderRecursion` certificate and
appends its exact component shapes to the recursively constructed family. -/
theorem ColoredStabilityHierarchy.exists_iterationResult
    {k r m N : ℕ} {epsilon c K gamma : ℝ}
    (H : ColoredStabilityHierarchy k (stabilityEta epsilon)
      (stabilityEpsilon epsilon) (stabilityAmplification epsilon) K c r gamma)
    (hk : 3 ≤ k) (hepsilon : 0 < epsilon) (hc : 0 < c)
    (hedit : CoreStageEditor k epsilon c K)
    (C : ColoredGraph (Fin m))
    (hmN : m ≤ N)
    (hpower : stabilityContraction epsilon ^ r * (m : ℝ) ≤
      stabilityEpsilon epsilon * (N : ℝ) / 20)
    (hthreshold : (H.maxN : ℝ) ≤
      stabilityEpsilon epsilon * (N : ℝ) / 20)
    (hcoreSize : (3 : ℝ) ≤
      c * (stabilityEpsilon epsilon * (N : ℝ) / 20))
    (hC : C ∈ Ck k m)
    (hnear : stabilityEpsilon epsilon * (N : ℝ) / 20 < (m : ℝ) →
      -(gamma * (m : ℝ) ^ 2) ≤ (objective k C : ℝ)) :
    Nonempty (StabilityIterationResult k m N epsilon C) := by
  induction H generalizing m with
  | terminal =>
      have hsmall : (m : ℝ) ≤
          stabilityEpsilon epsilon * (N : ℝ) / 20 := by
        simpa using hpower
      let E := ExtremalFamilyShape.empty k (Fin m)
      refine ⟨{ target := E, hamming_le := ?_ }⟩
      have hraw : (coloringHammingDistance C E.canonicalColoring : ℝ) ≤
          (m : ℝ) ^ 2 := by
        rw [ExtremalFamilyShape.canonicalColoring_empty]
        simpa using coloringHammingDistance_le_card_sq C allGreen
      have hterminal := stability_small_remainder_square hepsilon
        (show 0 ≤ (N : ℝ) by positivity) (show 0 ≤ (m : ℝ) by positivity) hsmall
      have hmain : 0 ≤ stabilityEpsilon epsilon / 4 * (m : ℝ) ^ 2 := by
        exact mul_nonneg (div_nonneg (stabilityEpsilon_pos hepsilon).le (by norm_num))
          (sq_nonneg _)
      exact hraw.trans (by nlinarith)
  | @cons r gammaNext step tail ih =>
      let scale := stabilityEpsilon epsilon * (N : ℝ) / 20
      by_cases hsmall : (m : ℝ) ≤ scale
      · let E := ExtremalFamilyShape.empty k (Fin m)
        refine ⟨{ target := E, hamming_le := ?_ }⟩
        have hraw : (coloringHammingDistance C E.canonicalColoring : ℝ) ≤
            (m : ℝ) ^ 2 := by
          rw [ExtremalFamilyShape.canonicalColoring_empty]
          simpa using coloringHammingDistance_le_card_sq C allGreen
        have hterminal := stability_small_remainder_square hepsilon
          (show 0 ≤ (N : ℝ) by positivity) (show 0 ≤ (m : ℝ) by positivity) hsmall
        have hmain : 0 ≤ stabilityEpsilon epsilon / 4 * (m : ℝ) ^ 2 := by
          exact mul_nonneg (div_nonneg (stabilityEpsilon_pos hepsilon).le (by norm_num))
            (sq_nonneg _)
        exact hraw.trans (by nlinarith)
      · have hlarge : scale < (m : ℝ) := lt_of_not_ge hsmall
        by_cases hred : ∀ v,
            (C.redDegree v : ℝ) < stabilityEta epsilon * (m : ℝ)
        · let E := ExtremalFamilyShape.empty k (Fin m)
          refine ⟨{ target := E, hamming_le := ?_ }⟩
          have hclose :
              (coloringHammingDistance C E.canonicalColoring : ℝ) ≤
                2 * stabilityEta epsilon * (m : ℝ) ^ 2 := by
            rw [ExtremalFamilyShape.canonicalColoring_empty]
            exact closeToAllGreen_of_maxRedDegree_small hk
              (stabilityEta_mem_Ioo hepsilon).1 step.gamma_le_eta
              (hnear hlarge) hred
          have hbudget : 2 * stabilityEta epsilon * (m : ℝ) ^ 2 ≤
              stabilityEpsilon epsilon / 4 * (m : ℝ) ^ 2 := by
            unfold stabilityEta
            have hsquare : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
            have hebar := stabilityEpsilon_pos hepsilon
            nlinarith
          have hterminal : 0 ≤
              stabilityEpsilon epsilon * (N : ℝ) ^ 2 / 20 := by
            exact div_nonneg (mul_nonneg (stabilityEpsilon_pos hepsilon).le
              (sq_nonneg _)) (by norm_num)
          exact hclose.trans (hbudget.trans (by linarith))
        · have hmax : ∃ x,
              stabilityEta epsilon * (m : ℝ) ≤ (C.redDegree x : ℝ) := by
            simpa only [not_forall, not_lt] using hred
          have hmaxNReal : ((ColoredStabilityHierarchy.cons step tail).maxN : ℝ) ≤
              (m : ℝ) := hthreshold.trans hlarge.le
          have hmaxNNat : (ColoredStabilityHierarchy.cons step tail).maxN ≤ m := by
            exact_mod_cast hmaxNReal
          have hnStar : step.nStar ≤ m :=
            (ColoredStabilityHierarchy.head_nStar_le_maxN step tail).trans hmaxNNat
          obtain ⟨R⟩ := step.extract m hnStar step.gamma
            ⟨step.gamma_pos, step.gamma_lt_deltaStar⟩ C hC (hnear hlarge) hmax
          let T := coreExtractionRemainder R.exceptional R.clusters
          let D := C.restrictToFin T
          have hsize : (3 : ℝ) ≤ c * (m : ℝ) := by
            have hmul := mul_lt_mul_of_pos_left hlarge hc
            exact hcoreSize.trans hmul.le
          obtain ⟨stage⟩ := hedit R step.xi_mem hsize
          have hshrink : (T.card : ℝ) ≤
              stabilityContraction epsilon * (m : ℝ) := by
            simpa [T, stabilityContraction] using
              R.remainder_card_le_contraction
                (stabilityEta_mem_Ioo hepsilon).1 step.xi_mem.2
          have hm'Nonneg : 0 ≤ (T.card : ℝ) := by positivity
          have hmNonneg : 0 ≤ (m : ℝ) := by positivity
          have hpowerTail : stabilityContraction epsilon ^ r * (T.card : ℝ) ≤
              stabilityEpsilon epsilon * (N : ℝ) / 20 :=
            (stabilityContraction_pow_shrink hepsilon hmNonneg hm'Nonneg hshrink).trans
              hpower
          have hm'Nat : T.card ≤ m := by
            simpa [T] using Finset.card_le_univ T
          have hm'N : T.card ≤ N := hm'Nat.trans hmN
          have hthresholdTail : (tail.maxN : ℝ) ≤
              stabilityEpsilon epsilon * (N : ℝ) / 20 := by
            have htailNat := ColoredStabilityHierarchy.tail_maxN_le_maxN step tail
            have htailReal : (tail.maxN : ℝ) ≤
                ((ColoredStabilityHierarchy.cons step tail).maxN : ℝ) := by
              exact_mod_cast htailNat
            exact htailReal.trans hthreshold
          have hD : D ∈ Ck k T.card := by
            exact restrictToFin_mem_Ck hC T
          have hnearD : scale < (T.card : ℝ) →
              -(gammaNext * (T.card : ℝ) ^ 2) ≤ (objective k D : ℝ) := by
            intro hlargeT
            have hbase := R.remainder_nearExtremal_restrictToFin
            have hamp := stabilityAmplification_absorbs hepsilon
              (show 0 ≤ (N : ℝ) by positivity) hmNonneg hm'Nonneg
              (show (m : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN)
              hlargeT (add_nonneg step.gamma_pos.le step.xi_mem.1.le)
            have hupdate : (step.gamma + step.xi) * (m : ℝ) ^ 2 ≤
                gammaNext * (T.card : ℝ) ^ 2 := by
              calc
                (step.gamma + step.xi) * (m : ℝ) ^ 2 ≤
                    stabilityAmplification epsilon * (step.gamma + step.xi) *
                      (T.card : ℝ) ^ 2 := hamp
                _ ≤ gammaNext * (T.card : ℝ) ^ 2 :=
                  mul_le_mul_of_nonneg_right step.update_le (sq_nonneg _)
            change -((step.gamma + step.xi) * (m : ℝ) ^ 2) ≤
              (objective k D : ℝ) at hbase
            linarith
          obtain ⟨rec⟩ := ih D hm'N hpowerTail
            hthresholdTail hD hnearD
          let recMap := rec.target.map (restrictionEmbedding T)
          have hrecSubset : ∀ b, (recMap.shapes b).support ⊆ T := by
            intro b
            exact mappedShape_support_subset T rec.target b
          let target := stage.shape.append recMap
            (appendCrossDisjoint stage.shape recMap T
              stage.support_disjoint_remainder hrecSubset)
          refine ⟨{ target := target, hamming_le := ?_ }⟩
          have htarget : target.canonicalColoring =
              overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T := by
            exact canonicalColoring_append_eq_overlayInside stage.shape recMap T
              stage.support_disjoint_remainder hrecSubset
          have hoverNat := coloringHammingDistance_overlayInside_le
            stage.shape.canonicalColoring C recMap.canonicalColoring T
          have hover :
              (coloringHammingDistance
                (overlayInside stage.shape.canonicalColoring C T)
                (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T) : ℝ) ≤
              (coloringHammingDistance D rec.target.canonicalColoring : ℝ) := by
            exact_mod_cast (by
              simpa [D, recMap, canonicalColoring_map_restrictToFin] using hoverNat)
          have htriangleNat := coloringHammingDistance_triangle C
            (overlayInside stage.shape.canonicalColoring C T)
            (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T)
          have htriangle :
              (coloringHammingDistance C
                (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T) : ℝ) ≤
              (coloringHammingDistance C
                (overlayInside stage.shape.canonicalColoring C T) : ℝ) +
              (coloringHammingDistance
                (overlayInside stage.shape.canonicalColoring C T)
                (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T) : ℝ) := by
            exact_mod_cast htriangleNat
          rw [htarget]
          calc
            (coloringHammingDistance C
                (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T) : ℝ) ≤
                (coloringHammingDistance C
                  (overlayInside stage.shape.canonicalColoring C T) : ℝ) +
                (coloringHammingDistance
                  (overlayInside stage.shape.canonicalColoring C T)
                  (overlayInside stage.shape.canonicalColoring recMap.canonicalColoring T) : ℝ) :=
              htriangle
            _ ≤ K * step.xi * (m : ℝ) ^ 2 +
                (stabilityEpsilon epsilon / 4 * (T.card : ℝ) ^ 2 +
                  stabilityEpsilon epsilon * (N : ℝ) ^ 2 / 20) :=
              add_le_add stage.hamming_le (hover.trans rec.hamming_le)
            _ ≤ stabilityEpsilon epsilon / 4 * (m : ℝ) ^ 2 +
                stabilityEpsilon epsilon * (N : ℝ) ^ 2 / 20 := by
              have htelescope := stability_stage_cost_telescope hepsilon
                step.edit_small hmNonneg hm'Nonneg hshrink
              linarith



/-- The extraction lower bound forces the number of reduced vertices to be
at most the reciprocal cluster scale. -/
theorem CoreExtractionResult.clusterCount_le_inv_clusterScale
    {k n : ℕ} {C : ColoredGraph (Fin n)} {eta inputDelta xi c : ℝ}
    (R : CoreExtractionResult k n C eta inputDelta xi c)
    (hc : 0 < c) (hthree : (3 : ℝ) ≤ c * (n : ℝ)) :
    (R.clusterCount : ℝ) ≤ 1 / c := by
  have hn : 0 < (n : ℝ) := by
    by_contra hn0
    have hnzero : (n : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hn0) (by positivity)
    rw [hnzero, mul_zero] at hthree
    norm_num at hthree
  have hcount := card_mul_clusterLower_le_card R.clusters (c * (n : ℝ))
    R.clusters_pairwiseDisjoint R.clusterLowerBound
  have hcount' : ((R.clusterCount : ℝ) * c) * (n : ℝ) ≤
      1 * (n : ℝ) := by
    simpa [mul_assoc] using hcount
  have hqc : (R.clusterCount : ℝ) * c ≤ 1 :=
    le_of_mul_le_mul_right hcount' hn
  exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hqc)

/-- The fixed master editing constant dominates both the old-partition
color correction and the equitable-relabeling correction. -/
theorem stageEditCoefficient_le_stabilityEditConstant
    {q : ℕ} {c : ℝ} (hc : 0 < c) (hcOne : c ≤ 1)
    (hq : (q : ℝ) ≤ 1 / c) :
    (q : ℝ) ^ 2 + 2 * (q : ℝ) + 2 ≤ stabilityEditConstant c := by
  let x : ℝ := 1 / c
  have hx : 0 < x := by dsimp [x]; positivity
  have hxOne : 1 ≤ x := by
    dsimp [x]
    exact (le_div_iff₀ hc).2 (by simpa using hcOne)
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  have hq2 : (q : ℝ) ^ 2 ≤ x ^ 2 := by
    nlinarith
  unfold stabilityEditConstant
  have hinvSq : (1 / c) ^ 2 = 1 / c ^ 2 := by ring
  rw [← hinvSq]
  change (q : ℝ) ^ 2 + 2 * (q : ℝ) + 2 ≤ 100 * (1 + x ^ 2)
  nlinarith [sq_nonneg (x - 1)]

/-- One extracted stage can be replaced by its exact balanced component
cores at cost bounded by the single master constant. -/
theorem CoreExtractionResult.exists_coreStageEdit
    {k n : ℕ} {C : ColoredGraph (Fin n)} {epsilon inputDelta xi c : ℝ}
    (R : CoreExtractionResult k n C (stabilityEta epsilon) inputDelta xi c)
    (hk : 3 ≤ k) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hcOne : c ≤ 1)
    (hxi : xi ∈ Set.Ioo (0 : ℝ) (stabilityEta epsilon / 20))
    (hthree : (3 : ℝ) ≤ c * (n : ℝ)) :
    Nonempty (CoreStageEdit R (stabilityEditConstant c)) := by
  let T := coreExtractionRemainder R.exceptional R.clusters
  have hxi0 : 0 ≤ xi := hxi.1.le
  have hxi1 : xi < 1 := by
    have hetaOne := (stabilityEta_mem_Ioo hepsilon).2
    nlinarith [hxi.2]
  obtain ⟨balanced, _hnonempty, hbalancedDisj, hunion, _hequitable,
      hmoved, _htwo, E, hEUnion, hEColor, _hcoreSizes⟩ :=
    R.exists_balancedExtremalFamilyShape hk hxi0 hthree
  refine ⟨{ shape := E, support_disjoint_remainder := ?_, hamming_le := ?_ }⟩
  · intro a
    rw [Finset.disjoint_left]
    intro x hxE hxT
    have hxUnion : x ∈ clusterUnion (fun b ↦ (E.shapes b).support) :=
      cluster_subset_clusterUnion (fun b ↦ (E.shapes b).support) a hxE
    rw [hEUnion] at hxUnion
    have hxCore : x ∈ coreExtractionCore R.exceptional R.clusters :=
      Finset.mem_union_right _ hxUnion
    exact (Finset.mem_sdiff.mp hxT).2 hxCore
  · have hold := coreExtraction_oldPartition_hamming_le R hxi0 hxi1
    have hbalanceNat :=
      coloringHammingDistance_overlayInside_clusterBlowupColoring_le_moved_mul_card
        R.reducedGraph R.clusters balanced R.clusters_pairwiseDisjoint
        hbalancedDisj hunion.symm C T
    have hbalanceRaw :
        (coloringHammingDistance
          (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
          (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) ≤
          ((clusterMovedSet R.clusters balanced).card : ℝ) * (n : ℝ) := by
      have hbalanceNat' :
          coloringHammingDistance
            (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
            (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) ≤
            (clusterMovedSet R.clusters balanced).card * n := by
        simpa using hbalanceNat
      exact_mod_cast hbalanceNat'
    have hmovedReal : ((clusterMovedSet R.clusters balanced).card : ℝ) ≤
        (R.clusterCount : ℝ) * (⌊xi * (n : ℝ)⌋₊ : ℝ) := by
      change ((clusterUnion fun i ↦ R.clusters i \ balanced i).card : ℝ) ≤ _
      exact_mod_cast hmoved
    have hfloor : (⌊xi * (n : ℝ)⌋₊ : ℝ) ≤ xi * (n : ℝ) := by
      exact Nat.floor_le (mul_nonneg hxi0 (by positivity))
    have hbalance :
        (coloringHammingDistance
          (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
          (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) ≤
          (R.clusterCount : ℝ) * xi * (n : ℝ) ^ 2 := by
      calc
        _ ≤ ((clusterMovedSet R.clusters balanced).card : ℝ) * (n : ℝ) :=
          hbalanceRaw
        _ ≤ ((R.clusterCount : ℝ) * (⌊xi * (n : ℝ)⌋₊ : ℝ)) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right hmovedReal (by positivity)
        _ ≤ ((R.clusterCount : ℝ) * (xi * (n : ℝ))) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfloor (by positivity)) (by positivity)
        _ = (R.clusterCount : ℝ) * xi * (n : ℝ) ^ 2 := by ring
    have htriangleNat := coloringHammingDistance_triangle C
      (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
      (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T)
    have htriangle :
        (coloringHammingDistance C
          (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) ≤
        (coloringHammingDistance C
          (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T) : ℝ) +
        (coloringHammingDistance
          (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
          (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) := by
      exact_mod_cast htriangleNat
    have hq := R.clusterCount_le_inv_clusterScale hc hthree
    have hcoefficient :=
      stageEditCoefficient_le_stabilityEditConstant hc hcOne hq
    have hfactor : 0 ≤ xi * (n : ℝ) ^ 2 :=
      mul_nonneg hxi0 (sq_nonneg _)
    rw [hEColor]
    calc
      (coloringHammingDistance C
          (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) ≤
          (coloringHammingDistance C
            (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T) : ℝ) +
          (coloringHammingDistance
            (overlayInside (clusterBlowupColoring R.reducedGraph R.clusters) C T)
            (overlayInside (clusterBlowupColoring R.reducedGraph balanced) C T) : ℝ) :=
        htriangle
      _ ≤ ((R.clusterCount : ℝ) ^ 2 + (R.clusterCount : ℝ) + 2) * xi *
            (n : ℝ) ^ 2 + (R.clusterCount : ℝ) * xi * (n : ℝ) ^ 2 :=
        add_le_add hold hbalance
      _ = ((R.clusterCount : ℝ) ^ 2 + 2 * (R.clusterCount : ℝ) + 2) *
            (xi * (n : ℝ) ^ 2) := by ring
      _ ≤ stabilityEditConstant c * (xi * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hcoefficient hfactor
      _ = stabilityEditConstant c * xi * (n : ℝ) ^ 2 := by ring

/-- The one-stage editor used by the outer hierarchy exists uniformly. -/
theorem coreStageEditor_stability
    (k : ℕ) (hk : 3 ≤ k) {epsilon c : ℝ}
    (hepsilon : 0 < epsilon) (hc : 0 < c) (hcOne : c ≤ 1) :
    CoreStageEditor k epsilon c (stabilityEditConstant c) := by
  intro m C inputDelta xi R hxi hthree
  exact R.exists_coreStageEdit hk hepsilon hc hcOne hxi hthree



/-- Initial-state interface for the finite extraction iteration. -/
theorem ColoredStabilityHierarchy.exists_initialTarget
    {k N r : ℕ} {epsilon c gamma : ℝ}
    (H : ColoredStabilityHierarchy k (stabilityEta epsilon)
      (stabilityEpsilon epsilon) (stabilityAmplification epsilon)
      (stabilityEditConstant c) c r gamma)
    (hk : 3 ≤ k) (hepsilon : 0 < epsilon)
    (hc : 0 < c) (hcOne : c ≤ 1)
    (hstageBound : stabilityContraction epsilon ^ r ≤
      stabilityEpsilon epsilon / 20)
    (hthreshold : (H.maxN : ℝ) ≤
      stabilityEpsilon epsilon * (N : ℝ) / 20)
    (hcoreSize : (3 : ℝ) ≤
      c * (stabilityEpsilon epsilon * (N : ℝ) / 20))
    (C : ColoredGraph (Fin N)) (hC : C ∈ Ck k N)
    (hnear : -(gamma * (N : ℝ) ^ 2) ≤ (objective k C : ℝ)) :
    ∃ Cstar : ColoredGraph (Fin N),
      Cstar ∈ extremalFamily k N ∧
      (coloringHammingDistance C Cstar : ℝ) ≤ epsilon * (N : ℝ) ^ 2 := by
  have hpowered : stabilityContraction epsilon ^ r * (N : ℝ) ≤
      stabilityEpsilon epsilon * (N : ℝ) / 20 := by
    have hmul := mul_le_mul_of_nonneg_right hstageBound
      (show 0 ≤ (N : ℝ) by positivity)
    nlinarith
  obtain ⟨A⟩ := H.exists_iterationResult hk hepsilon hc
    (coreStageEditor_stability k hk hepsilon hc hcOne) C le_rfl hpowered
    hthreshold hcoreSize hC (fun _ ↦ hnear)
  refine ⟨A.target.canonicalColoring,
    A.target.canonicalColoring_mem_extremalFamily hk, ?_⟩
  have hreserves := stability_global_reserves_le hepsilon
    (show 0 ≤ (N : ℝ) by positivity)
  exact A.hamming_le.trans hreserves

/-- The cluster scale returned by `kthOrderRecursion` may be capped at one
without changing any conclusion. -/
theorem kthOrderRecursion_cappedClusterScale
    (k : ℕ) (hk : 3 ≤ k) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ c : ℝ, c ∈ Set.Ioc (0 : ℝ) 1 ∧
      ∀ xi ∈ Set.Ioo (0 : ℝ) (stabilityEta epsilon / 20),
        ∃ deltaStar : ℝ, deltaStar ∈ Set.Ioo (0 : ℝ) 1 ∧ ∃ nStar : ℕ,
          ∀ n ≥ nStar, ∀ inputDelta ∈ Set.Ioo (0 : ℝ) deltaStar,
            ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
              -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
              (∃ x, stabilityEta epsilon * (n : ℝ) ≤ (C.redDegree x : ℝ)) →
              Nonempty (CoreExtractionResult k n C
                (stabilityEta epsilon) inputDelta xi c) := by
  obtain ⟨c₀, hc₀, recurse₀⟩ := kthOrderRecursion k hk
    (stabilityEta epsilon) (stabilityEta_mem_Ioo hepsilon)
  let c := min c₀ 1
  have hc : 0 < c := by simp [c, hc₀]
  have hcOne : c ≤ 1 := min_le_right _ _
  refine ⟨c, ⟨hc, hcOne⟩, ?_⟩
  intro xi hxi
  obtain ⟨deltaStar, hdeltaStar, nStar, hextract⟩ := recurse₀ xi hxi
  refine ⟨deltaStar, hdeltaStar, nStar, ?_⟩
  intro n hn inputDelta hinputDelta C hC hnear hred
  obtain ⟨R⟩ := hextract n hn inputDelta hinputDelta C hC hnear hred
  exact ⟨R.weakenClusterScale (min_le_left c₀ 1)⟩

/-- Paper: Theorem `thm:kth-order-stability`.

For every `k ≥ 3` and every positive (not necessarily subunit) `epsilon`,
there is a positive objective tolerance and an ambient threshold such that
each near-extremal member of `Ck` differs on at most `epsilon n²` unordered
edges from a literal member of the exact extremal family.

The internal cap `stabilityEpsilon epsilon = min epsilon 1` leaves the
exported theorem valid for every positive error tolerance. -/
theorem kthOrderStability
    (k : ℕ) (hk : 3 ≤ k) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ inputDelta : ℝ, 0 < inputDelta ∧ ∃ n₀ : ℕ,
      ∀ n ≥ n₀, ∀ C : ColoredGraph (Fin n), C ∈ Ck k n →
        -(inputDelta * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) →
        ∃ Cstar : ColoredGraph (Fin n),
          Cstar ∈ extremalFamily k n ∧
          (coloringHammingDistance C Cstar : ℝ) ≤ epsilon * (n : ℝ) ^ 2 := by
  have hebar : 0 < stabilityEpsilon epsilon := stabilityEpsilon_pos hepsilon
  have heta := stabilityEta_mem_Ioo hepsilon
  have hA : 0 < stabilityAmplification epsilon :=
    stabilityAmplification_pos hepsilon
  obtain ⟨c, ⟨hc, hcOne⟩, recurse⟩ :=
    kthOrderRecursion_cappedClusterScale k hk epsilon hepsilon
  have hK : 0 < stabilityEditConstant c := stabilityEditConstant_pos hc
  obtain ⟨r, hr⟩ := exists_stabilityStageBound hepsilon
  obtain ⟨gamma, hgamma, H⟩ :=
    ColoredStabilityHierarchy.exists_of_recursion k r heta.1 hebar hA hK recurse
  let hierarchy := H.some
  let inputDelta := min (gamma / 2) (stabilityEpsilon epsilon / 8)
  have hinputDelta : 0 < inputDelta := by
    dsimp [inputDelta]
    exact lt_min (div_pos hgamma (by norm_num))
      (div_pos hebar (by norm_num))
  have hinputDeltaGamma : inputDelta ≤ gamma := by
    have hle : inputDelta ≤ gamma / 2 := min_le_left _ _
    linarith
  have hinputDeltaEpsilon : inputDelta ≤ stabilityEpsilon epsilon / 4 := by
    have hle : inputDelta ≤ stabilityEpsilon epsilon / 8 := min_le_right _ _
    linarith
  obtain ⟨nThreshold, hnThreshold⟩ :=
    exists_nat_threshold_below_linear
      (a := stabilityEpsilon epsilon / 20)
      (div_pos hebar (by norm_num)) hierarchy.maxN
  obtain ⟨nCore, hnCore⟩ :=
    exists_nat_threshold_below_linear
      (a := c * stabilityEpsilon epsilon / 20)
      (div_pos (mul_pos hc hebar) (by norm_num)) 3
  let n₀ := max nThreshold nCore
  refine ⟨inputDelta, hinputDelta, n₀, ?_⟩
  intro n hn C hC hnear
  have hnThreshold' : nThreshold ≤ n := (Nat.le_max_left _ _).trans hn
  have hnCore' : nCore ≤ n := (Nat.le_max_right _ _).trans hn
  have hthreshold : (hierarchy.maxN : ℝ) ≤
      stabilityEpsilon epsilon * (n : ℝ) / 20 := by
    have h := hnThreshold n hnThreshold'
    nlinarith
  have hcoreSize : (3 : ℝ) ≤
      c * (stabilityEpsilon epsilon * (n : ℝ) / 20) := by
    have h := hnCore n hnCore'
    nlinarith
  by_cases hred : (C.redEdgeCount : ℝ) ≤
      stabilityEpsilon epsilon * (n : ℝ) ^ 2 / 4
  · refine ⟨allGreen, allGreen_mem_extremalFamily k n, ?_⟩
    have hclose := closeToAllGreen_of_redCount_small hk hebar
      hinputDeltaEpsilon hnear hred
    exact hclose.trans (mul_le_mul_of_nonneg_right
      (stabilityEpsilon_le epsilon) (sq_nonneg _))
  · have hnearGamma : -(gamma * (n : ℝ) ^ 2) ≤ (objective k C : ℝ) := by
      have hsquare : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      have hcoeff : inputDelta * (n : ℝ) ^ 2 ≤ gamma * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hinputDeltaGamma hsquare
      linarith
    exact hierarchy.exists_initialTarget hk hepsilon hc hcOne hr hthreshold
      hcoreSize C hC hnearGamma


end ColoredGraph

end InducedStars
