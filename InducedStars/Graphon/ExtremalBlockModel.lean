import InducedStars.EdgeColoring.Stability
import InducedStars.Graphon.CandidateBlocks
import InducedStars.Graphon.ColorProfile
import InducedStars.Graphon.ProfileBlocks
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

/-!
# Finite block data carried by exact extremal witnesses

This file converts every literal `ColoredGraph.ExtremalFamilyWitness` into
the finite, size-ordered component data used by the reverse graphon
classification.  It deliberately stops before graphon relabeling and block
equalization: those coordinate-sensitive estimates are developed in the
next layer, following `prop:graphon-char-fixed-gamma`.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators Classical

namespace InducedStars

namespace ColoredGraph

/-! ## Literal conversion of one regular-core witness -/

/-- Forget the equitable blow-up data of a regular-core witness while
retaining its literal reduced graph. -/
noncomputable def RegularCoreWitness.toRegularBlockCore
    {k n : ℕ} {C : ColoredGraph (Fin n)}
    (Q : RegularCoreWitness k n C) : RegularBlockCore k := by
  refine {
    order := Q.clusterCount
    order_pos := ?_
    graph := Q.reducedGraph
    connected := Q.reducedGraph_connected
    regular := ?_ }
  · have hk := Q.three_le_k
    have hcount := Q.clusterCount_lower
    omega
  · intro i
    change (Q.reducedGraph.neighborSet i).toFinset.card = k - 2
    rw [← Set.ncard_eq_toFinset_card']
    letI : DecidableRel Q.reducedGraph.Adj :=
      Q.reducedGraphAdjDecidable
    have hregular := Q.reducedGraph_regular i
    change (Q.reducedGraph.neighborSet i).toFinset.card = delta k at hregular
    rw [← Set.ncard_eq_toFinset_card'] at hregular
    simpa only [delta] using hregular

@[simp] theorem RegularCoreWitness.toRegularBlockCore_order
    {k n : ℕ} {C : ColoredGraph (Fin n)}
    (Q : RegularCoreWitness k n C) :
    Q.toRegularBlockCore.order = Q.clusterCount :=
  rfl

@[simp] theorem RegularCoreWitness.toRegularBlockCore_graph
    {k n : ℕ} {C : ColoredGraph (Fin n)}
    (Q : RegularCoreWitness k n C) :
    Q.toRegularBlockCore.graph = Q.reducedGraph :=
  rfl

/-! ## Ambient clusters of an extremal component -/

namespace ExtremalFamilyWitness

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (E : ExtremalFamilyWitness k q C)

/-- The cluster of an exact core witness, transported from its canonical
restricted `Fin` type back to the original ambient vertex labels. -/
noncomputable def ambientCoreCluster (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) : Finset (Fin q) :=
  ((E.coreRegular a).clusters i).map
    (restrictionEmbedding (E.coreVertices a))

@[simp] theorem mem_ambientCoreCluster (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) (x : Fin q) :
    x ∈ E.ambientCoreCluster a i ↔
      ∃ u, u ∈ (E.coreRegular a).clusters i ∧
        restrictionEmbedding (E.coreVertices a) u = x := by
  simp [ambientCoreCluster]

/-- Every transported cluster remains inside its literal ambient core
support. -/
theorem ambientCoreCluster_subset (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) :
    E.ambientCoreCluster a i ⊆ E.coreVertices a := by
  intro x hx
  obtain ⟨u, _hu, rfl⟩ := (E.mem_ambientCoreCluster a i x).1 hx
  exact restrictionEmbedding_mem (E.coreVertices a) u

/-- Every transported ambient cluster is nonempty. -/
theorem ambientCoreCluster_nonempty (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) :
    (E.ambientCoreCluster a i).Nonempty := by
  obtain ⟨u, hu⟩ := (E.coreRegular a).clusters_nonempty i
  exact ⟨restrictionEmbedding (E.coreVertices a) u,
    (E.mem_ambientCoreCluster a i _).2 ⟨u, hu, rfl⟩⟩

/-- The ambient clusters of one core remain pairwise disjoint. -/
theorem ambientCoreClusters_pairwiseDisjoint (a : Fin E.coreCount) :
    Set.PairwiseDisjoint
      (Set.univ : Set (Fin (E.coreRegular a).clusterCount))
      (E.ambientCoreCluster a) := by
  intro i _ j _ hij
  change Disjoint (E.ambientCoreCluster a i) (E.ambientCoreCluster a j)
  rw [Finset.disjoint_left]
  intro x hxi hxj
  obtain ⟨u, hui, hux⟩ := (E.mem_ambientCoreCluster a i x).1 hxi
  obtain ⟨v, hvj, hvx⟩ := (E.mem_ambientCoreCluster a j x).1 hxj
  have huv : u = v :=
    (restrictionEmbedding (E.coreVertices a)).injective (hux.trans hvx.symm)
  subst v
  exact Finset.disjoint_left.mp
    ((E.coreRegular a).clusters_pairwiseDisjoint
      (Set.mem_univ i) (Set.mem_univ j) hij) hui hvj

/-- The transported clusters cover exactly the original ambient core
support, with no relabeling of ambient vertices. -/
theorem ambientCoreClusters_cover (a : Fin E.coreCount) :
    clusterUnion (E.ambientCoreCluster a) = E.coreVertices a := by
  ext x
  constructor
  · intro hx
    rw [mem_clusterUnion_iff] at hx
    obtain ⟨i, hxi⟩ := hx
    exact E.ambientCoreCluster_subset a i hxi
  · intro hx
    obtain ⟨u, rfl⟩ := restrictionEmbedding_surjectiveOn
      (E.coreVertices a) hx
    have hu : u ∈ clusterUnion (E.coreRegular a).clusters := by
      rw [(E.coreRegular a).clusters_cover]
      exact Finset.mem_univ u
    rw [mem_clusterUnion_iff] at hu ⊢
    obtain ⟨i, hui⟩ := hu
    exact ⟨i, (E.mem_ambientCoreCluster a i _).2 ⟨u, hui, rfl⟩⟩

/-- Transport does not change cluster cardinality. -/
@[simp] theorem card_ambientCoreCluster (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) :
    (E.ambientCoreCluster a i).card =
      ((E.coreRegular a).clusters i).card := by
  simp [ambientCoreCluster]

/-- The ambient cluster sizes are equitable. -/
theorem ambientCoreCluster_equitable (a : Fin E.coreCount)
    (i j : Fin (E.coreRegular a).clusterCount) :
    (E.ambientCoreCluster a i).card ≤
      (E.ambientCoreCluster a j).card + 1 := by
  simpa using (E.coreRegular a).clusterEquitable i j

/-- Inside every transported cluster the original ambient coloring is blue. -/
theorem ambientCoreCluster_internalBlue (a : Fin E.coreCount)
    (i : Fin (E.coreRegular a).clusterCount) {x y : Fin q}
    (hx : x ∈ E.ambientCoreCluster a i)
    (hy : y ∈ E.ambientCoreCluster a i) (hxy : x ≠ y) :
    C.color x y = .blue := by
  obtain ⟨u, hui, rfl⟩ := (E.mem_ambientCoreCluster a i x).1 hx
  obtain ⟨v, hvi, rfl⟩ := (E.mem_ambientCoreCluster a i y).1 hy
  have huv : u ≠ v := fun huv ↦ hxy (congrArg
    (restrictionEmbedding (E.coreVertices a)) huv)
  have h := (E.coreRegular a).internalBlue i u v hui hvi huv
  simpa only [restrictToFin_color] using h

/-- Across every reduced edge, the original ambient coloring is red. -/
theorem ambientCoreCluster_redBetween (a : Fin E.coreCount)
    {i j : Fin (E.coreRegular a).clusterCount}
    (hij : (E.coreRegular a).reducedGraph.Adj i j)
    {x y : Fin q} (hx : x ∈ E.ambientCoreCluster a i)
    (hy : y ∈ E.ambientCoreCluster a j) :
    C.color x y = .red := by
  obtain ⟨u, hui, rfl⟩ := (E.mem_ambientCoreCluster a i x).1 hx
  obtain ⟨v, hvj, rfl⟩ := (E.mem_ambientCoreCluster a j y).1 hy
  have h := (E.coreRegular a).redBetween i j hij u hui v hvj
  simpa only [restrictToFin_color] using h

/-- Across distinct reduced nonedges, the original ambient coloring is
green. -/
theorem ambientCoreCluster_greenBetween (a : Fin E.coreCount)
    {i j : Fin (E.coreRegular a).clusterCount} (hij : i ≠ j)
    (hnadj : ¬ (E.coreRegular a).reducedGraph.Adj i j)
    {x y : Fin q} (hx : x ∈ E.ambientCoreCluster a i)
    (hy : y ∈ E.ambientCoreCluster a j) :
    C.color x y = .green := by
  obtain ⟨u, hui, rfl⟩ := (E.mem_ambientCoreCluster a i x).1 hx
  obtain ⟨v, hvj, rfl⟩ := (E.mem_ambientCoreCluster a j y).1 hy
  have h := (E.coreRegular a).greenBetween i j hij hnadj u hui v hvj
  simpa only [restrictToFin_color] using h

/-- Two literal core supports containing the same ambient vertex have the
same component index. -/
theorem coreIndex_eq_of_mem {a b : Fin E.coreCount} {x : Fin q}
    (hxa : x ∈ E.coreVertices a) (hxb : x ∈ E.coreVertices b) : a = b := by
  by_contra hab
  exact Finset.disjoint_left.mp
    (E.coreVertices_pairwiseDisjoint
      (Set.mem_univ a) (Set.mem_univ b) hab) hxa hxb

/-- Every edge between distinct exact core supports is green. -/
theorem green_between_distinct_cores {a b : Fin E.coreCount} (hab : a ≠ b)
    {x y : Fin q} (hx : x ∈ E.coreVertices a)
    (hy : y ∈ E.coreVertices b) : C.color x y = .green := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hab (E.coreIndex_eq_of_mem hx hy)
  apply E.offCoreGreen x y hxy
  intro c hboth
  have hac : a = c := E.coreIndex_eq_of_mem hx hboth.1
  have hbc : b = c := E.coreIndex_eq_of_mem hy hboth.2
  exact hab (hac.trans hbc.symm)

/-- The union of all literal ambient core supports. -/
def coveredCoreVertices : Finset (Fin q) :=
  clusterUnion E.coreVertices

/-- Vertices outside every exact core support. -/
def uncoveredVertices : Finset (Fin q) :=
  Finset.univ \ E.coveredCoreVertices

@[simp] theorem mem_coveredCoreVertices (x : Fin q) :
    x ∈ E.coveredCoreVertices ↔ ∃ a, x ∈ E.coreVertices a := by
  simp [coveredCoreVertices, mem_clusterUnion_iff]

@[simp] theorem mem_uncoveredVertices (x : Fin q) :
    x ∈ E.uncoveredVertices ↔ ∀ a, x ∉ E.coreVertices a := by
  simp [uncoveredVertices]

/-- Every off-diagonal edge incident with an uncovered vertex is green. -/
theorem green_of_mem_uncovered_left {x y : Fin q} (hxy : x ≠ y)
    (hx : x ∈ E.uncoveredVertices) : C.color x y = .green := by
  apply E.offCoreGreen x y hxy
  intro a hboth
  exact (E.mem_uncoveredVertices x).1 hx a hboth.1

/-- Symmetric form of the uncovered-vertex coloring identity. -/
theorem green_of_mem_uncovered_right {x y : Fin q} (hxy : x ≠ y)
    (hy : y ∈ E.uncoveredVertices) : C.color x y = .green := by
  rw [C.color_comm]
  exact E.green_of_mem_uncovered_left hxy.symm hy

/-! ## Deterministic nonincreasing component order -/

/-- The deterministic component permutation obtained by sorting the dual
natural-valued support sizes.  `Tuple.sort` breaks equal-size ties by the
original component index. -/
noncomputable def componentOrder : Equiv.Perm (Fin E.coreCount) :=
  Tuple.sort (fun a : Fin E.coreCount ↦
    OrderDual.toDual (E.coreVertices a).card)

/-- Original witness index occupying ordered component position `a`. -/
def orderedCoreIndex (a : Fin E.coreCount) : Fin E.coreCount :=
  E.componentOrder a

/-- Ambient support size of the component in ordered position `a`. -/
def orderedCoreSize (a : Fin E.coreCount) : ℕ :=
  (E.coreVertices (E.orderedCoreIndex a)).card

/-- Ordered component sizes are nonincreasing. -/
theorem orderedCoreSize_antitone : Antitone E.orderedCoreSize := by
  have h := Tuple.monotone_sort
    (fun a : Fin E.coreCount ↦
      OrderDual.toDual (E.coreVertices a).card)
  intro a b hab
  exact h hab

/-- Sorting does not change the sum of component support sizes. -/
theorem sum_orderedCoreSize :
    ∑ a : Fin E.coreCount, E.orderedCoreSize a =
      ∑ a : Fin E.coreCount, (E.coreVertices a).card := by
  exact Equiv.sum_comp E.componentOrder
    (fun a : Fin E.coreCount ↦ (E.coreVertices a).card)

/-- The exact regular block core occupying ordered component position `a`.
Its graph is the literal reduced graph of the corresponding witness. -/
noncomputable def orderedRegularBlockCore (a : Fin E.coreCount) :
    RegularBlockCore k :=
  (E.coreRegular (E.orderedCoreIndex a)).toRegularBlockCore

@[simp] theorem orderedRegularBlockCore_order (a : Fin E.coreCount) :
    (E.orderedRegularBlockCore a).order =
      (E.coreRegular (E.orderedCoreIndex a)).clusterCount :=
  rfl

@[simp] theorem orderedRegularBlockCore_graph (a : Fin E.coreCount) :
    (E.orderedRegularBlockCore a).graph =
      (E.coreRegular (E.orderedCoreIndex a)).reducedGraph :=
  rfl

/-! ## Normalized component lengths -/

/-- Ordered ambient support size divided by the ambient order. -/
def orderedCoreLength (a : Fin E.coreCount) : ℝ :=
  (E.orderedCoreSize a : ℝ) / (q : ℝ)

theorem orderedCoreLength_pos (hk : 3 ≤ k) (hq : 0 < q)
    (a : Fin E.coreCount) : 0 < E.orderedCoreLength a := by
  apply div_pos
  · exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k)
      (E.coreSize_lower (E.orderedCoreIndex a)))
  · exact_mod_cast hq

theorem orderedCoreLength_nonneg (hq : 0 < q)
    (a : Fin E.coreCount) : 0 ≤ E.orderedCoreLength a := by
  exact div_nonneg (by positivity) (by positivity)

theorem orderedCoreLength_le_one (hq : 0 < q)
    (a : Fin E.coreCount) : E.orderedCoreLength a ≤ 1 := by
  have hcard : E.orderedCoreSize a ≤ q := by
    simpa [orderedCoreSize] using
      Finset.card_le_univ (E.coreVertices (E.orderedCoreIndex a))
  unfold orderedCoreLength
  rw [div_le_one (by exact_mod_cast hq)]
  exact_mod_cast hcard

/-- Normalized ordered component lengths remain nonincreasing. -/
theorem orderedCoreLength_antitone (hq : 0 < q) :
    Antitone E.orderedCoreLength := by
  intro a b hab
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast E.orderedCoreSize_antitone hab)
    (by positivity)

/-- Exact finite sum of the ordered normalized component lengths. -/
theorem sum_orderedCoreLength :
    ∑ a : Fin E.coreCount, E.orderedCoreLength a =
      (∑ a : Fin E.coreCount, (E.coreVertices a).card : ℕ) / (q : ℝ) := by
  simp only [orderedCoreLength]
  rw [← Finset.sum_div]
  congr 1
  exact_mod_cast E.sum_orderedCoreSize

/-- The total normalized component length is at most one. -/
theorem sum_orderedCoreLength_le_one (hq : 0 < q) :
    ∑ a : Fin E.coreCount, E.orderedCoreLength a ≤ 1 := by
  rw [E.sum_orderedCoreLength, div_le_one (by exact_mod_cast hq)]
  exact_mod_cast E.sum_coreSize_le

/-- The unused normalized interval length is exactly the fraction of
ambient vertices outside all core supports. -/
theorem one_sub_sum_orderedCoreLength_eq_uncovered (hq : 0 < q) :
    1 - ∑ a : Fin E.coreCount, E.orderedCoreLength a =
      (E.uncoveredVertices.card : ℝ) / (q : ℝ) := by
  have hcovered : E.coveredCoreVertices.card =
      ∑ a : Fin E.coreCount, (E.coreVertices a).card := by
    exact card_clusterUnion E.coreVertices E.coreVertices_pairwiseDisjoint
  have hsubset : E.coveredCoreVertices ⊆ (Finset.univ : Finset (Fin q)) :=
    Finset.subset_univ _
  have huncovered : E.uncoveredVertices.card = q - E.coveredCoreVertices.card := by
    rw [uncoveredVertices, Finset.card_sdiff_of_subset hsubset,
      Finset.card_univ, Fintype.card_fin]
  rw [E.sum_orderedCoreLength, ← hcovered, huncovered]
  have hcard : E.coveredCoreVertices.card ≤ q := by
    simpa using Finset.card_le_univ E.coveredCoreVertices
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  push_cast [Nat.cast_sub hcard]
  field_simp

/-! ## The exact finite admissible block sequence -/

/-- The ordered normalized length, extended by zero beyond the finite list
of components. -/
def finiteBlockAlpha (i : ℕ) : ℝ :=
  if hi : i < E.coreCount then E.orderedCoreLength ⟨i, hi⟩ else 0

@[simp] theorem finiteBlockAlpha_of_lt {i : ℕ} (hi : i < E.coreCount) :
    E.finiteBlockAlpha i = E.orderedCoreLength ⟨i, hi⟩ := by
  simp [finiteBlockAlpha, hi]

@[simp] theorem finiteBlockAlpha_of_le {i : ℕ} (hi : E.coreCount ≤ i) :
    E.finiteBlockAlpha i = 0 := by
  simp [finiteBlockAlpha, Nat.not_lt_of_ge hi]

/-- The ordered literal reduced core, extended by a harmless complete core
beyond the finite active range. -/
noncomputable def finiteBlockCore (hk : 3 ≤ k) (i : ℕ) :
    RegularBlockCore k :=
  if hi : i < E.coreCount then E.orderedRegularBlockCore ⟨i, hi⟩
  else RegularBlockCore.complete k hk

@[simp] theorem finiteBlockCore_of_lt (hk : 3 ≤ k) {i : ℕ}
    (hi : i < E.coreCount) :
    E.finiteBlockCore hk i = E.orderedRegularBlockCore ⟨i, hi⟩ := by
  simp [finiteBlockCore, hi]

theorem finiteBlockAlpha_antitone (hq : 0 < q) :
    Antitone E.finiteBlockAlpha := by
  intro i j hij
  by_cases hj : j < E.coreCount
  · have hi : i < E.coreCount := lt_of_le_of_lt hij hj
    simp only [E.finiteBlockAlpha_of_lt hi, E.finiteBlockAlpha_of_lt hj]
    exact E.orderedCoreLength_antitone hq hij
  · rw [E.finiteBlockAlpha_of_le (Nat.le_of_not_gt hj)]
    by_cases hi : i < E.coreCount
    · rw [E.finiteBlockAlpha_of_lt hi]
      exact E.orderedCoreLength_nonneg hq _
    · rw [E.finiteBlockAlpha_of_le (Nat.le_of_not_gt hi)]

theorem finiteBlockAlpha_summable : Summable E.finiteBlockAlpha := by
  apply summable_of_hasFiniteSupport
  exact (Set.finite_Iio E.coreCount).subset (by
    intro i hi
    change E.finiteBlockAlpha i ≠ 0 at hi
    by_contra hlt
    exact hi (E.finiteBlockAlpha_of_le (Nat.le_of_not_gt hlt)))

/-- The exact `tsum` of the zero-extended finite length list. -/
theorem tsum_finiteBlockAlpha :
    ∑' i, E.finiteBlockAlpha i =
      ∑ a : Fin E.coreCount, E.orderedCoreLength a := by
  rw [tsum_eq_sum (s := Finset.range E.coreCount)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simpa using E.finiteBlockAlpha_of_lt i.isLt
  · intro i hi
    rw [E.finiteBlockAlpha_of_le]
    simpa using hi

/-- Canonical finite admissible block sequence extracted from the witness. -/
noncomputable def finiteBlockSequence (hk : 3 ≤ k) (hq : 0 < q)
    (hcore : 0 < E.coreCount) : AdmissibleBlockSequence k where
  count := some E.coreCount
  count_pos := by
    intro n hn
    simpa using Option.some.inj hn ▸ hcore
  alpha := E.finiteBlockAlpha
  core := E.finiteBlockCore hk
  alpha_pos_of_active := by
    intro i hi
    simp only [blockIndexActive] at hi
    rw [E.finiteBlockAlpha_of_lt hi]
    exact E.orderedCoreLength_pos hk hq _
  alpha_eq_zero_of_inactive := by
    intro i hi
    simp only [blockIndexActive, not_lt] at hi
    exact E.finiteBlockAlpha_of_le hi
  alpha_antitone := E.finiteBlockAlpha_antitone hq
  summable_alpha := E.finiteBlockAlpha_summable
  tsum_alpha_le_one := by
    rw [E.tsum_finiteBlockAlpha]
    exact E.sum_orderedCoreLength_le_one hq

@[simp] theorem finiteBlockSequence_count (hk : 3 ≤ k) (hq : 0 < q)
    (hcore : 0 < E.coreCount) :
    (E.finiteBlockSequence hk hq hcore).count = some E.coreCount :=
  rfl

@[simp] theorem finiteBlockSequence_alpha (hk : 3 ≤ k) (hq : 0 < q)
    (hcore : 0 < E.coreCount) (i : ℕ) :
    (E.finiteBlockSequence hk hq hcore).alpha i = E.finiteBlockAlpha i :=
  rfl

@[simp] theorem finiteBlockSequence_core (hk : 3 ≤ k) (hq : 0 < q)
    (hcore : 0 < E.coreCount) (i : ℕ) :
    (E.finiteBlockSequence hk hq hcore).core i = E.finiteBlockCore hk i :=
  rfl

end ExtremalFamilyWitness

end ColoredGraph

/-! ## Bundled finite extremal block models -/

/-- The canonical finite block data carried by an exact extremal-family
witness.  Proof fields record only the hypotheses needed to normalize the
ambient support sizes and build the admissible sequence. -/
structure FiniteExtremalBlockModel (k q : ℕ) (C : ColoredGraph (Fin q)) where
  witness : ColoredGraph.ExtremalFamilyWitness k q C
  three_le_k : 3 ≤ k
  ambientOrder_pos : 0 < q
  coreCount_pos : 0 < witness.coreCount

/-- Total constructor from an exact finite extremal witness. -/
def finiteExtremalBlockModel {k q : ℕ} {C : ColoredGraph (Fin q)}
    (hk : 3 ≤ k) (hq : 0 < q)
    (E : ColoredGraph.ExtremalFamilyWitness k q C)
    (hcore : 0 < E.coreCount) : FiniteExtremalBlockModel k q C where
  witness := E
  three_le_k := hk
  ambientOrder_pos := hq
  coreCount_pos := hcore

namespace FiniteExtremalBlockModel

variable {k q : ℕ} {C : ColoredGraph (Fin q)}
    (M : FiniteExtremalBlockModel k q C)

/-- Number of active finite components. -/
def componentCount : ℕ := M.witness.coreCount

theorem componentCount_pos : 0 < M.componentCount := M.coreCount_pos

/-- Deterministic permutation ordering components by nonincreasing support
size. -/
noncomputable def componentOrder : Equiv.Perm (Fin M.componentCount) :=
  M.witness.componentOrder

/-- Original witness index at ordered position `a`. -/
def orderedIndex (a : Fin M.componentCount) : Fin M.witness.coreCount :=
  M.witness.orderedCoreIndex a

/-- Normalized ambient support length at ordered position `a`. -/
def orderedLength (a : Fin M.componentCount) : ℝ :=
  M.witness.orderedCoreLength a

/-- Literal reduced regular core at ordered position `a`. -/
noncomputable def orderedCore (a : Fin M.componentCount) : RegularBlockCore k :=
  M.witness.orderedRegularBlockCore a

/-- Order of the literal reduced core at ordered position `a`. -/
def orderedCoreOrder (a : Fin M.componentCount) : ℕ :=
  (M.orderedCore a).order

/-- Exact finite admissible block sequence, zero-extended on `ℕ`. -/
noncomputable def blockSequence : AdmissibleBlockSequence k :=
  M.witness.finiteBlockSequence M.three_le_k M.ambientOrder_pos M.coreCount_pos

/-- Arbitrary-profile graphon associated with the finite block data. -/
def profileGraphon (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Graphon :=
  profileWLambda p M.blockSequence hp

/-- First position in the nonempty ordered component list. -/
def firstIndex : Fin M.componentCount := ⟨0, M.componentCount_pos⟩

/-- Largest normalized block length. -/
def largestBlockLength : ℝ := M.orderedLength M.firstIndex

/-- Second ordered block length, totalized to zero when there is only one
component. -/
def secondBlockLength : ℝ :=
  if h : 1 < M.componentCount then M.orderedLength ⟨1, h⟩ else 0

/-- Sum of all normalized finite block lengths. -/
def blockLengthSum : ℝ := ∑ a : Fin M.componentCount, M.orderedLength a

/-- Sum of the squares of all normalized finite block lengths. -/
def blockLengthSquareSum : ℝ :=
  ∑ a : Fin M.componentCount, M.orderedLength a ^ 2

/-- Sum of all normalized lengths except the largest one. -/
def tailBlockLength : ℝ :=
  ∑ a ∈ (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex,
    M.orderedLength a

/-- Sum of squared block lengths after the largest component. -/
def tailBlockSquareSum : ℝ :=
  ∑ a ∈ (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex,
    M.orderedLength a ^ 2

/-- Exact scalar mass of the finite sequence. -/
def blockMass : ℝ := M.blockSequence.mass

@[simp] theorem blockSequence_count :
    M.blockSequence.count = some M.componentCount :=
  rfl

@[simp] theorem blockSequence_alpha_of_lt {i : ℕ}
    (hi : i < M.componentCount) :
    M.blockSequence.alpha i = M.orderedLength ⟨i, hi⟩ := by
  change M.witness.finiteBlockAlpha i =
    M.witness.orderedCoreLength ⟨i, hi⟩
  exact M.witness.finiteBlockAlpha_of_lt hi

@[simp] theorem blockSequence_alpha_of_le {i : ℕ}
    (hi : M.componentCount ≤ i) : M.blockSequence.alpha i = 0 := by
  change M.witness.finiteBlockAlpha i = 0
  exact M.witness.finiteBlockAlpha_of_le hi

@[simp] theorem blockSequence_core_of_lt {i : ℕ}
    (hi : i < M.componentCount) :
    M.blockSequence.core i = M.orderedCore ⟨i, hi⟩ := by
  change M.witness.finiteBlockCore M.three_le_k i =
    M.witness.orderedRegularBlockCore ⟨i, hi⟩
  exact M.witness.finiteBlockCore_of_lt M.three_le_k hi

theorem orderedLength_pos (a : Fin M.componentCount) :
    0 < M.orderedLength a :=
  M.witness.orderedCoreLength_pos M.three_le_k M.ambientOrder_pos a

theorem orderedLength_nonneg (a : Fin M.componentCount) :
    0 ≤ M.orderedLength a := (M.orderedLength_pos a).le

theorem orderedLength_le_one (a : Fin M.componentCount) :
    M.orderedLength a ≤ 1 :=
  M.witness.orderedCoreLength_le_one M.ambientOrder_pos a

theorem orderedLength_antitone : Antitone M.orderedLength :=
  M.witness.orderedCoreLength_antitone M.ambientOrder_pos

theorem orderedCoreOrder_pos (a : Fin M.componentCount) :
    0 < M.orderedCoreOrder a :=
  (M.orderedCore a).order_pos

theorem k_sub_one_le_orderedCoreOrder (a : Fin M.componentCount) :
    k - 1 ≤ M.orderedCoreOrder a :=
  RegularBlockCore.k_sub_one_le_order M.three_le_k (M.orderedCore a)

theorem orderedLength_le_largest (a : Fin M.componentCount) :
    M.orderedLength a ≤ M.largestBlockLength := by
  apply M.orderedLength_antitone
  change 0 ≤ a.val
  omega

theorem blockLengthSum_eq_tsum :
    M.blockLengthSum = ∑' i, M.blockSequence.alpha i := by
  change (∑ a : Fin M.witness.coreCount,
      M.witness.orderedCoreLength a) =
    ∑' i, M.witness.finiteBlockAlpha i
  rw [M.witness.tsum_finiteBlockAlpha]

theorem blockLengthSum_nonneg : 0 ≤ M.blockLengthSum := by
  exact Finset.sum_nonneg fun a _ ↦ M.orderedLength_nonneg a

theorem blockLengthSum_le_one : M.blockLengthSum ≤ 1 :=
  M.witness.sum_orderedCoreLength_le_one M.ambientOrder_pos

theorem largestBlockLength_pos : 0 < M.largestBlockLength :=
  M.orderedLength_pos M.firstIndex

theorem largestBlockLength_nonneg : 0 ≤ M.largestBlockLength :=
  M.largestBlockLength_pos.le

theorem largestBlockLength_le_one : M.largestBlockLength ≤ 1 :=
  M.orderedLength_le_one M.firstIndex

theorem blockLengthSum_eq_largest_add_tail :
    M.blockLengthSum = M.largestBlockLength + M.tailBlockLength := by
  rw [blockLengthSum, largestBlockLength, tailBlockLength]
  have hmem : M.firstIndex ∈
      (Finset.univ : Finset (Fin M.componentCount)) := Finset.mem_univ _
  rw [← Finset.sum_erase_add _ _ hmem, add_comm]

theorem tailBlockLength_nonneg : 0 ≤ M.tailBlockLength := by
  exact Finset.sum_nonneg fun a _ ↦ M.orderedLength_nonneg a

theorem tailBlockLength_le_one_sub_largest :
    M.tailBlockLength ≤ 1 - M.largestBlockLength := by
  linarith [M.blockLengthSum_eq_largest_add_tail, M.blockLengthSum_le_one]

theorem secondBlockLength_nonneg : 0 ≤ M.secondBlockLength := by
  by_cases h : 1 < M.componentCount
  · rw [secondBlockLength, dif_pos h]
    exact M.orderedLength_nonneg _
  · simp [secondBlockLength, h]

theorem secondBlockLength_le_one : M.secondBlockLength ≤ 1 := by
  by_cases h : 1 < M.componentCount
  · rw [secondBlockLength, dif_pos h]
    exact M.orderedLength_le_one _
  · simp [secondBlockLength, h]

private theorem tailIndexFinset_eq_empty_of_not_one_lt
    (h : ¬ 1 < M.componentCount) :
    (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hne : a ≠ M.firstIndex := (Finset.mem_erase.mp ha).1
  apply hne
  apply Fin.ext
  change a.val = 0
  omega

private theorem orderedLength_le_second_of_mem_tail
    (hcount : 1 < M.componentCount) {a : Fin M.componentCount}
    (ha : a ∈
      (Finset.univ : Finset (Fin M.componentCount)).erase M.firstIndex) :
    M.orderedLength a ≤ M.secondBlockLength := by
  rw [secondBlockLength, dif_pos hcount]
  apply M.orderedLength_antitone
  have hne : a ≠ M.firstIndex := (Finset.mem_erase.mp ha).1
  change 1 ≤ a.val
  by_contra hval
  have ha0 : a.val = 0 := by omega
  apply hne
  exact Fin.ext ha0

theorem tailBlockSquareSum_nonneg : 0 ≤ M.tailBlockSquareSum := by
  exact Finset.sum_nonneg fun a _ ↦ sq_nonneg (M.orderedLength a)

/-- The squared tail is controlled by the second length times the tail
length, including the one-component case by totalization. -/
theorem tailBlockSquareSum_le_second_mul_tail :
    M.tailBlockSquareSum ≤
      M.secondBlockLength * M.tailBlockLength := by
  by_cases hcount : 1 < M.componentCount
  · rw [tailBlockSquareSum, tailBlockLength, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    nlinarith [M.orderedLength_nonneg a,
      M.orderedLength_le_second_of_mem_tail hcount ha]
  · have hempty := M.tailIndexFinset_eq_empty_of_not_one_lt hcount
    simp [tailBlockSquareSum, tailBlockLength, secondBlockLength,
      hcount, hempty]

theorem second_mul_tail_le_tail :
    M.secondBlockLength * M.tailBlockLength ≤ M.tailBlockLength := by
  calc
    M.secondBlockLength * M.tailBlockLength ≤ 1 * M.tailBlockLength :=
      mul_le_mul_of_nonneg_right M.secondBlockLength_le_one
        M.tailBlockLength_nonneg
    _ = M.tailBlockLength := one_mul _

theorem blockLengthSquareSum_nonneg : 0 ≤ M.blockLengthSquareSum := by
  exact Finset.sum_nonneg fun a _ ↦ sq_nonneg (M.orderedLength a)

/-- The sequence mass is exactly the finite sum over ordered components. -/
theorem blockMass_eq_sum :
    M.blockMass =
      ∑ a : Fin M.componentCount,
        M.orderedLength a ^ 2 / (M.orderedCoreOrder a : ℝ) := by
  rw [blockMass, AdmissibleBlockSequence.mass,
    tsum_eq_sum (s := Finset.range M.componentCount)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro a _ha
    simp only [AdmissibleBlockSequence.massTerm]
    rw [M.blockSequence_alpha_of_lt a.isLt,
      M.blockSequence_core_of_lt a.isLt]
    rfl
  · intro i hi
    have hle : M.componentCount ≤ i := by simpa using hi
    simp [AdmissibleBlockSequence.massTerm,
      M.blockSequence_alpha_of_le hle]

theorem blockMass_nonneg : 0 ≤ M.blockMass :=
  M.blockSequence.mass_nonneg

@[simp] theorem blockSequence_mass : M.blockSequence.mass = M.blockMass :=
  rfl

/-- The largest ordered length is bounded by the total length. -/
theorem largestBlockLength_le_blockLengthSum :
    M.largestBlockLength ≤ M.blockLengthSum := by
  linarith [M.blockLengthSum_eq_largest_add_tail,
    M.tailBlockLength_nonneg]

/-- Finite quadratic mass is controlled below by the minimum possible core
order `k-1`. -/
theorem k_sub_one_mul_blockMass_le_blockLengthSquareSum :
    ((k - 1 : ℕ) : ℝ) * M.blockMass ≤ M.blockLengthSquareSum := by
  rw [M.blockMass_eq_sum, blockLengthSquareSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  have horderNat : k - 1 ≤ M.orderedCoreOrder a :=
    RegularBlockCore.k_sub_one_le_order M.three_le_k (M.orderedCore a)
  have horder : ((k - 1 : ℕ) : ℝ) ≤
      (M.orderedCoreOrder a : ℝ) := by
    exact_mod_cast horderNat
  have horderPos : 0 < (M.orderedCoreOrder a : ℝ) := by
    exact_mod_cast (M.orderedCore a).order_pos
  calc
    ((k - 1 : ℕ) : ℝ) *
          (M.orderedLength a ^ 2 / (M.orderedCoreOrder a : ℝ)) =
        (((k - 1 : ℕ) : ℝ) * M.orderedLength a ^ 2) /
          (M.orderedCoreOrder a : ℝ) := by ring
    _ ≤ M.orderedLength a ^ 2 := by
      rw [div_le_iff₀ horderPos]
      nlinarith [sq_nonneg (M.orderedLength a)]

/-- The sum of squared lengths is at most largest length times total
length. -/
theorem blockLengthSquareSum_le_largest_mul_sum :
    M.blockLengthSquareSum ≤
      M.largestBlockLength * M.blockLengthSum := by
  rw [blockLengthSquareSum, blockLengthSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  nlinarith [M.orderedLength_nonneg a,
    M.orderedLength_le_largest a]

theorem largest_mul_sum_le_largest :
    M.largestBlockLength * M.blockLengthSum ≤
      M.largestBlockLength := by
  calc
    M.largestBlockLength * M.blockLengthSum ≤
        M.largestBlockLength * 1 :=
      mul_le_mul_of_nonneg_left M.blockLengthSum_le_one
        M.largestBlockLength_nonneg
    _ = M.largestBlockLength := mul_one _

/-- The finite sum of squares is at most the square of the total length. -/
theorem blockLengthSquareSum_le_sum_sq :
    M.blockLengthSquareSum ≤ M.blockLengthSum ^ 2 := by
  calc
    M.blockLengthSquareSum ≤
        M.largestBlockLength * M.blockLengthSum :=
      M.blockLengthSquareSum_le_largest_mul_sum
    _ ≤ M.blockLengthSum * M.blockLengthSum :=
      mul_le_mul_of_nonneg_right M.largestBlockLength_le_blockLengthSum
        M.blockLengthSum_nonneg
    _ = M.blockLengthSum ^ 2 := by ring

theorem blockLengthSum_sq_le_one : M.blockLengthSum ^ 2 ≤ 1 := by
  nlinarith [M.blockLengthSum_nonneg, M.blockLengthSum_le_one]

/-! ## Exact profile-graphon formulas -/

theorem profileGraphon_ae_threeValued (p : ℝ)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ z ∂unitSquareMeasure,
      (M.profileGraphon p hp).value z = 0 ∨
        (M.profileGraphon p hp).value z = p ∨
          (M.profileGraphon p hp).value z = 1 := by
  exact profileWLambda_ae_threeValued p M.blockSequence hp

theorem profileGraphon_oneMass {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    graphonOneMass
        (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) = M.blockMass := by
  simpa only [profileGraphon, blockMass] using
    graphonOneMass_profileWLambda M.three_le_k hp M.blockSequence

theorem profileGraphon_randomMass {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    graphonRandomMass
        (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) =
      ((k - 2 : ℕ) : ℝ) * M.blockMass := by
  simpa only [profileGraphon, blockMass] using
    graphonRandomMass_profileWLambda M.three_le_k hp M.blockSequence

theorem profileGraphon_nonzeroMass {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    graphonNonzeroMass
        (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) =
      ((k - 1 : ℕ) : ℝ) * M.blockMass := by
  simpa only [profileGraphon, blockMass] using
    graphonNonzeroMass_profileWLambda M.three_le_k hp M.blockSequence

theorem profileGraphon_edgeDensity {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    graphonEdgeDensity
        (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) =
      (1 + ((k - 2 : ℕ) : ℝ) * p) * M.blockMass := by
  simpa only [profileGraphon, blockMass] using
    graphonEdgeDensity_profileWLambda M.three_le_k hp M.blockSequence

theorem profileGraphon_entropy {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    graphonEntropy
        (M.profileGraphon p ⟨hp.1.le, hp.2.le⟩) =
      (((k - 2 : ℕ) : ℝ) * binaryEntropy p) * M.blockMass := by
  simpa only [profileGraphon, blockMass] using
    graphonEntropy_profileWLambda M.three_le_k hp M.blockSequence

end FiniteExtremalBlockModel

end InducedStars
