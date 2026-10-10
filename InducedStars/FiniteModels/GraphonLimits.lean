import InducedStars.FiniteModels.GraphFamiliesCore
import InducedStars.Graphon.Functionals
import InducedStars.Graphon.Metric
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Sym.NatCard
import Mathlib.Tactic

/-!
# Limit sets of labeled finite graph families

This file gives a representative-level definition of the graphon limit set
of a sequence of finite labeled graph families.  It also supplies the neutral
finite edit-distance infrastructure used by exact-edge repair arguments.
Nothing here uses a graph-limit compactness theorem or an external result.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal SimpleGraph Topology symmDiff

namespace InducedStars

/-! ## Labeled-family graphon limit sets -/

/-- The graphons obtainable as cut-distance limits along a strictly
increasing sequence of orders, choosing at each extracted order a labeled
graph from the specified finite family. -/
def labeledGraphFamilyLimitSet
    (Q : (n : ℕ) → Finset (SimpleGraph (Fin n))) : Set Graphon :=
  {W | ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ G : (j : ℕ) → SimpleGraph (Fin (σ j)),
        (∀ j, G j ∈ Q (σ j)) ∧
          Tendsto (fun j ↦ cutDist (graphGraphon (G j)) W)
            atTop (nhds 0)}

theorem mem_labeledGraphFamilyLimitSet
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))} {W : Graphon} :
    W ∈ labeledGraphFamilyLimitSet Q ↔
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ G : (j : ℕ) → SimpleGraph (Fin (σ j)),
          (∀ j, G j ∈ Q (σ j)) ∧
            Tendsto (fun j ↦ cutDist (graphGraphon (G j)) W)
              atTop (nhds 0) :=
  Iff.rfl

/-- Replacing a representative by one at cut distance zero does not change
membership in a labeled-family limit set. -/
theorem mem_labeledGraphFamilyLimitSet_of_cutDist_eq_zero
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))} {W U : Graphon}
    (hW : W ∈ labeledGraphFamilyLimitSet Q) (hWU : cutDist W U = 0) :
    U ∈ labeledGraphFamilyLimitSet Q := by
  obtain ⟨σ, hσ, G, hG, hlim⟩ := hW
  refine ⟨σ, hσ, G, hG, ?_⟩
  have hupper : Tendsto
      (fun j ↦ cutDist (graphGraphon (G j)) W + cutDist W U)
      atTop (nhds 0) := by
    simpa only [hWU, add_zero] using hlim
  apply squeeze_zero
  · intro j
    exact cutDist_nonneg _ _
  · intro j
    exact cutDist_triangle (graphGraphon (G j)) W U
  · exact hupper

/-- Cut-distance-zero representatives have equivalent membership in every
labeled-family limit set. -/
theorem mem_labeledGraphFamilyLimitSet_iff_of_cutDist_eq_zero
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))} {W U : Graphon}
    (hWU : cutDist W U = 0) :
    W ∈ labeledGraphFamilyLimitSet Q ↔
      U ∈ labeledGraphFamilyLimitSet Q := by
  constructor
  · intro hW
    exact mem_labeledGraphFamilyLimitSet_of_cutDist_eq_zero hW hWU
  · intro hU
    apply mem_labeledGraphFamilyLimitSet_of_cutDist_eq_zero hU
    rw [cutDist_comm, hWU]

/-- If every fixed cut neighborhood of `W` contains a member of `Q n` for
all sufficiently large orders, then `W` belongs to the labeled-family limit
set.  The proof diagonalizes the eventual witnesses along radii
`1 / (j + 1)`. -/
theorem mem_labeledGraphFamilyLimitSet_of_eventually_exists_cutDist_lt
    {Q : (n : ℕ) → Finset (SimpleGraph (Fin n))} {W : Graphon}
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, ∃ G : SimpleGraph (Fin n),
        G ∈ Q n ∧ cutDist (graphGraphon G) W < ε) :
    W ∈ labeledGraphFamilyLimitSet Q := by
  classical
  let ε : ℕ → ℝ := fun j ↦ 1 / ((j + 1 : ℕ) : ℝ)
  have hε (j : ℕ) : 0 < ε j := by
    dsimp [ε]
    positivity
  have hthreshold : ∀ j : ℕ, ∃ N : ℕ, ∀ n, N ≤ n →
      ∃ G : SimpleGraph (Fin n),
        G ∈ Q n ∧ cutDist (graphGraphon G) W < ε j := by
    intro j
    exact eventually_atTop.1 (happrox (ε j) (hε j))
  let N : ℕ → ℕ := fun j ↦ Classical.choose (hthreshold j)
  have hN (j : ℕ) : ∀ n, N j ≤ n →
      ∃ G : SimpleGraph (Fin n),
        G ∈ Q n ∧ cutDist (graphGraphon G) W < ε j :=
    Classical.choose_spec (hthreshold j)
  let σ : ℕ → ℕ := fun j ↦
    Nat.rec (N 0) (fun i s ↦ max (s + 1) (N (i + 1))) j
  have hσN : ∀ j, N j ≤ σ j := by
    intro j
    cases j with
    | zero => exact le_rfl
    | succ j =>
        change N (j + 1) ≤ max (σ j + 1) (N (j + 1))
        exact le_max_right _ _
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro j
    change σ j < max (σ j + 1) (N (j + 1))
    exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
  have hwitness (j : ℕ) : ∃ G : SimpleGraph (Fin (σ j)),
      G ∈ Q (σ j) ∧ cutDist (graphGraphon G) W < ε j :=
    hN j (σ j) (hσN j)
  let G : (j : ℕ) → SimpleGraph (Fin (σ j)) := fun j ↦
    Classical.choose (hwitness j)
  have hG (j : ℕ) : G j ∈ Q (σ j) ∧
      cutDist (graphGraphon (G j)) W < ε j :=
    Classical.choose_spec (hwitness j)
  refine ⟨σ, hσ, G, fun j ↦ (hG j).1, ?_⟩
  apply squeeze_zero
  · intro j
    exact cutDist_nonneg _ _
  · intro j
    exact (hG j).2.le
  · simpa only [ε, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ ↦ (1 : ℝ) / (j + 1)) atTop (nhds 0))

/-- The exact-edge induced-`H`-free limit set.  The density parameter is
retained in the interface so that later feasibility and enumeration theorems
state the intended fixed-density problem, while the finite family itself is
determined by `H` and `m`. -/
def exactEdgeInducedFreeLimitSet {h : ℕ} (H : SimpleGraph (Fin h))
    (_γ : ℝ) (m : ℕ → ℕ) : Set Graphon :=
  labeledGraphFamilyLimitSet fun n ↦
    inducedFreeGraphFinsetWithEdges H n (m n)

theorem mem_exactEdgeInducedFreeLimitSet {h : ℕ}
    {H : SimpleGraph (Fin h)} {γ : ℝ} {m : ℕ → ℕ} {W : Graphon} :
    W ∈ exactEdgeInducedFreeLimitSet H γ m ↔
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        ∃ G : (j : ℕ) → SimpleGraph (Fin (σ j)),
          (∀ j, G j ∈ inducedFreeGraphFinsetWithEdges H (σ j) (m (σ j))) ∧
            Tendsto (fun j ↦ cutDist (graphGraphon (G j)) W)
              atTop (nhds 0) :=
  Iff.rfl

/-! ## Finite edit distance -/

/-- The unordered edges on which two labeled graphs disagree. -/
def graphEditFinset {n : ℕ} (G H : SimpleGraph (Fin n)) :
    Finset (Sym2 (Fin n)) :=
  (Set.toFinite (G.edgeSet ∆ H.edgeSet)).toFinset

@[simp] theorem mem_graphEditFinset {n : ℕ}
    {G H : SimpleGraph (Fin n)} {e : Sym2 (Fin n)} :
    e ∈ graphEditFinset G H ↔
      (e ∈ G.edgeSet ∧ e ∉ H.edgeSet) ∨
        (e ∈ H.edgeSet ∧ e ∉ G.edgeSet) := by
  simp [graphEditFinset, Set.mem_symmDiff]

/-- The number of unordered edge toggles separating two labeled graphs. -/
def graphEditDistance {n : ℕ} (G H : SimpleGraph (Fin n)) : ℕ :=
  (graphEditFinset G H).card

@[simp] theorem graphEditDistance_self {n : ℕ}
    (G : SimpleGraph (Fin n)) : graphEditDistance G G = 0 := by
  simp [graphEditDistance, graphEditFinset]

theorem graphEditDistance_comm {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    graphEditDistance G H = graphEditDistance H G := by
  simp only [graphEditDistance]
  congr 1
  ext e
  simp only [mem_graphEditFinset]
  tauto

theorem graphEditFinset_injective_right {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    Function.Injective (graphEditFinset G) := by
  intro H K hHK
  apply SimpleGraph.edgeSet_injective
  apply symmDiff_right_injective G.edgeSet
  ext e
  have he := Finset.ext_iff.mp hHK e
  simpa [graphEditFinset] using he

/-- The finite Hamming ball around a labeled graph, measured in unordered
edge toggles. -/
def graphHammingBall {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) :
    Finset (SimpleGraph (Fin n)) :=
  Finset.univ.filter fun H ↦ graphEditDistance G H ≤ r

@[simp] theorem mem_graphHammingBall {n r : ℕ}
    {G H : SimpleGraph (Fin n)} :
    H ∈ graphHammingBall G r ↔ graphEditDistance G H ≤ r := by
  simp [graphHammingBall]

/-- The complete unordered edge set on `Fin n`. -/
def completeEdgeFinset (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (Set.toFinite (⊤ : SimpleGraph (Fin n)).edgeSet).toFinset

@[simp] theorem completeEdgeFinset_card (n : ℕ) :
    (completeEdgeFinset n).card = completeEdgeCount n := by
  calc
    (completeEdgeFinset n).card =
        (⊤ : SimpleGraph (Fin n)).edgeSet.ncard := by
      exact (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
    _ = completeEdgeCount n := by
      simp [SimpleGraph.edgeSet_top, Sym2.ncard_diagSet_compl,
        completeEdgeCount]

theorem graphEditFinset_subset_completeEdgeFinset {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    graphEditFinset G H ⊆ completeEdgeFinset n := by
  intro e he
  rw [mem_graphEditFinset] at he
  change e ∈ (Set.toFinite (⊤ : SimpleGraph (Fin n)).edgeSet).toFinset
  simp only [Set.Finite.mem_toFinset]
  rcases he with ⟨he, -⟩ | ⟨he, -⟩
  · exact SimpleGraph.edgeSet_mono le_top he
  · exact SimpleGraph.edgeSet_mono le_top he

/-- All subsets of the complete edge set having cardinality at most `r`. -/
def edgeSubsetFinsetUpTo (n r : ℕ) : Finset (Finset (Sym2 (Fin n))) :=
  (Finset.range (r + 1)).biUnion fun j ↦
    (completeEdgeFinset n).powersetCard j

@[simp] theorem mem_edgeSubsetFinsetUpTo {n r : ℕ}
    {s : Finset (Sym2 (Fin n))} :
    s ∈ edgeSubsetFinsetUpTo n r ↔
      s ⊆ completeEdgeFinset n ∧ s.card ≤ r := by
  classical
  constructor
  · intro hs
    obtain ⟨j, hj, hs⟩ := Finset.mem_biUnion.mp hs
    have hj' : j ≤ r := by simpa using (Finset.mem_range.mp hj)
    exact ⟨(Finset.mem_powersetCard.mp hs).1,
      (Finset.mem_powersetCard.mp hs).2.le.trans hj'⟩
  · rintro ⟨hsub, hcard⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨s.card, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)
    · exact Finset.mem_powersetCard.mpr ⟨hsub, rfl⟩

theorem edgeSubsetFinsetUpTo_card (n r : ℕ) :
    (edgeSubsetFinsetUpTo n r).card =
      ∑ j ∈ Finset.range (r + 1), Nat.choose (completeEdgeCount n) j := by
  classical
  rw [edgeSubsetFinsetUpTo, Finset.card_biUnion
    ((completeEdgeFinset n).pairwise_disjoint_powersetCard.set_pairwise _)]
  simp [completeEdgeFinset_card]

/-- The standard binomial-sum bound for a finite graph Hamming ball. -/
theorem graphHammingBall_card_le {n r : ℕ} (G : SimpleGraph (Fin n)) :
    (graphHammingBall G r).card ≤
      ∑ j ∈ Finset.range (r + 1), Nat.choose (completeEdgeCount n) j := by
  classical
  calc
    (graphHammingBall G r).card ≤ (edgeSubsetFinsetUpTo n r).card := by
      apply Finset.card_le_card_of_injOn (graphEditFinset G)
      · intro H hH
        change graphEditFinset G H ∈ edgeSubsetFinsetUpTo n r
        rw [mem_edgeSubsetFinsetUpTo]
        exact ⟨graphEditFinset_subset_completeEdgeFinset G H,
          (mem_graphHammingBall.mp hH)⟩
      · exact (graphEditFinset_injective_right G).injOn
    _ = _ := edgeSubsetFinsetUpTo_card n r

/-! ## Exact finite graphon normalizations -/

/-- Ordered adjacent vertex pairs.  Unlike `finiteGraphEdges`, this counts
each unordered edge in both orientations. -/
def orderedAdjacencyPairFinset {n : ℕ} (G : SimpleGraph (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p ↦ G.Adj p.1 p.2

@[simp] theorem mem_orderedAdjacencyPairFinset {n : ℕ}
    {G : SimpleGraph (Fin n)} {p : Fin n × Fin n} :
    p ∈ orderedAdjacencyPairFinset G ↔ G.Adj p.1 p.2 := by
  simp [orderedAdjacencyPairFinset]

/-- Each unordered graph edge contributes its two orientations. -/
theorem orderedAdjacencyPairFinset_card {n : ℕ}
  (G : SimpleGraph (Fin n)) :
    (orderedAdjacencyPairFinset G).card =
      2 * (finiteGraphEdges G).card := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hedge : G.edgeFinset = finiteGraphEdges G := by
    ext e
    rw [SimpleGraph.mem_edgeFinset, mem_finiteGraphEdges]
  calc
    (orderedAdjacencyPairFinset G).card =
        (Finset.univ.filter fun p : Fin n × Fin n ↦ G.Adj p.1 p.2).card := rfl
    _ = 2 * G.edgeFinset.card := G.two_mul_card_edgeFinset.symm
    _ = 2 * (finiteGraphEdges G).card := by rw [hedge]

/-- The ordered sum of the finite adjacency matrix is twice the number of
unordered edges. -/
theorem sum_graphAdjacencyMatrix {n : ℕ} (G : SimpleGraph (Fin n)) :
    (∑ i : Fin n, ∑ j : Fin n, graphAdjacencyMatrix G i j) =
      (2 * (finiteGraphEdges G).card : ℕ) := by
  classical
  rw [← Fintype.sum_prod_type
    (f := fun p : Fin n × Fin n ↦ graphAdjacencyMatrix G p.1 p.2)]
  calc
    (∑ p : Fin n × Fin n, graphAdjacencyMatrix G p.1 p.2) =
        ((orderedAdjacencyPairFinset G).card : ℝ) := by
      change (∑ p : Fin n × Fin n,
        if G.Adj p.1 p.2 then (1 : ℝ) else 0) = _
      rw [← Finset.sum_filter]
      simp [orderedAdjacencyPairFinset]
    _ = (2 * (finiteGraphEdges G).card : ℕ) := by
      exact_mod_cast orderedAdjacencyPairFinset_card G

/-- Exact ordered-square normalization of the finite adjacency graphon.
The factor two records the two matrix cells belonging to each unordered
edge. -/
theorem graphonEdgeDensity_graphGraphon {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    graphonEdgeDensity (graphGraphon G) =
      2 * ((finiteGraphEdges G).card : ℝ) / (n : ℝ) ^ 2 := by
  rw [show graphonEdgeDensity (graphGraphon G) =
      (1 / (n : ℝ)) ^ 2 *
        ∑ i : Fin n, ∑ j : Fin n, graphAdjacencyMatrix G i j by
    simpa only [graphGraphon] using
      graphonEdgeDensity_matrixGraphon hn (graphAdjacencyMatrix G)
        (graphAdjacencyMatrix_isSymm G)
        (graphAdjacencyMatrix_nonneg G) (graphAdjacencyMatrix_le_one G)]
  rw [sum_graphAdjacencyMatrix]
  push_cast
  ring

/-! ## Finite edits control graphon distance -/

/-- Ordered vertex pairs on which two finite graphs have different
adjacency. -/
def orderedGraphEditPairFinset {n : ℕ}
    (G H : SimpleGraph (Fin n)) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p ↦ G.Adj p.1 p.2 ≠ H.Adj p.1 p.2

@[simp] theorem mem_orderedGraphEditPairFinset {n : ℕ}
    {G H : SimpleGraph (Fin n)} {p : Fin n × Fin n} :
    p ∈ orderedGraphEditPairFinset G H ↔
      G.Adj p.1 p.2 ≠ H.Adj p.1 p.2 := by
  simp [orderedGraphEditPairFinset]

/-- Each changed unordered edge contributes exactly two ordered adjacency
disagreements. -/
theorem orderedGraphEditPairFinset_card {n : ℕ}
    (G H : SimpleGraph (Fin n)) :
    (orderedGraphEditPairFinset G H).card =
      2 * graphEditDistance G H := by
  classical
  let D : SimpleGraph (Fin n) := (G \ H) ⊔ (H \ G)
  have hedge : finiteGraphEdges D = graphEditFinset G H := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [mem_finiteGraphEdges, SimpleGraph.mem_edgeSet,
          mem_graphEditFinset]
        change (((G.Adj x y ∧ ¬H.Adj x y) ∨
            (H.Adj x y ∧ ¬G.Adj x y))) ↔ _
        tauto
  have hpairs :
      orderedGraphEditPairFinset G H =
        Finset.univ.filter fun p : Fin n × Fin n ↦ D.Adj p.1 p.2 := by
    ext p
    simp only [mem_orderedGraphEditPairFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change (G.Adj p.1 p.2 ≠ H.Adj p.1 p.2) ↔
      ((G.Adj p.1 p.2 ∧ ¬H.Adj p.1 p.2) ∨
        (H.Adj p.1 p.2 ∧ ¬G.Adj p.1 p.2))
    tauto
  calc
    (orderedGraphEditPairFinset G H).card =
        (Finset.univ.filter fun p : Fin n × Fin n ↦ D.Adj p.1 p.2).card := by
      rw [hpairs]
    _ = (orderedAdjacencyPairFinset D).card := by
      congr 1
      ext p
      simp
    _ = 2 * (finiteGraphEdges D).card := orderedAdjacencyPairFinset_card D
    _ = 2 * graphEditDistance G H := by
      rw [hedge]
      rfl

private theorem abs_propIndicator_sub_propIndicator
    (P Q : Prop) [Decidable P] [Decidable Q] :
    |(if P then (1 : ℝ) else 0) - (if Q then 1 else 0)| =
      if P ≠ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- The exact `L¹` cost of changing unordered edges in an `n`-vertex
adjacency graphon. -/
theorem graphonL1Dist_graphGraphon {n : ℕ} (hn : 0 < n)
    (G H : SimpleGraph (Fin n)) :
    graphonL1Dist (graphGraphon G) (graphGraphon H) =
      2 * (graphEditDistance G H : ℝ) / (n : ℝ) ^ 2 := by
  classical
  have hcell (i j : Fin n) :
      (∫ z in equalCell i ×ˢ equalCell j,
          |graphGraphon G z - graphGraphon H z| ∂unitSquareMeasure) =
        (1 / (n : ℝ)) ^ 2 *
          (if G.Adj i j ≠ H.Adj i j then (1 : ℝ) else 0) := by
    calc
      (∫ z in equalCell i ×ˢ equalCell j,
          |graphGraphon G z - graphGraphon H z| ∂unitSquareMeasure) =
          ∫ _z in equalCell i ×ˢ equalCell j,
            |(if G.Adj i j then (1 : ℝ) else 0) -
              (if H.Adj i j then 1 else 0)| ∂unitSquareMeasure := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem
            ((measurableSet_equalCell i).prod (measurableSet_equalCell j)),
          ae_restrict_of_ae (graphGraphon_ae_eq_on_cell G i j),
          ae_restrict_of_ae (graphGraphon_ae_eq_on_cell H i j)]
          with z hzMem hzG hzH
        rw [hzG hzMem, hzH hzMem]
      _ = (unitSquareMeasure (equalCell i ×ˢ equalCell j)).toReal *
          |(if G.Adj i j then (1 : ℝ) else 0) -
            (if H.Adj i j then 1 else 0)| := by
        rw [integral_const]
        simp [smul_eq_mul, Measure.real_def]
      _ = (1 / (n : ℝ)) ^ 2 *
          (if G.Adj i j ≠ H.Adj i j then (1 : ℝ) else 0) := by
        rw [show unitSquareMeasure (equalCell i ×ˢ equalCell j) =
            ENNReal.ofReal (1 / (n : ℝ)) ^ 2 from volume_equalCell_prod i j,
          ENNReal.toReal_pow, ENNReal.toReal_ofReal,
          abs_propIndicator_sub_propIndicator]
        positivity
  rw [graphonL1Dist_eq_integral,
    integral_eq_setIntegral (ae_mem_iUnion_equalCell_prod hn),
    integral_iUnion_fintype]
  · calc
      (∑ p : Fin n × Fin n,
          ∫ z in equalCell p.1 ×ˢ equalCell p.2,
            |graphGraphon G z - graphGraphon H z| ∂unitSquareMeasure) =
          ∑ p : Fin n × Fin n, (1 / (n : ℝ)) ^ 2 *
            (if G.Adj p.1 p.2 ≠ H.Adj p.1 p.2 then (1 : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro p _hp
        exact hcell p.1 p.2
      _ = (1 / (n : ℝ)) ^ 2 *
          ((orderedGraphEditPairFinset G H).card : ℝ) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_filter]
        simp [orderedGraphEditPairFinset]
      _ = 2 * (graphEditDistance G H : ℝ) / (n : ℝ) ^ 2 := by
        rw [orderedGraphEditPairFinset_card]
        push_cast
        ring
  · intro p
    exact (measurableSet_equalCell p.1).prod (measurableSet_equalCell p.2)
  · exact pairwise_disjoint_equalCell_prod
  · intro p
    exact ((graphGraphon G).integrable.sub
      (graphGraphon H).integrable).abs.integrableOn

/-- The same edit estimate controls cut distance, using the identity
alignment. -/
theorem cutDist_graphGraphon_le_edit {n : ℕ} (hn : 0 < n)
    (G H : SimpleGraph (Fin n)) :
    cutDist (graphGraphon G) (graphGraphon H) ≤
      2 * (graphEditDistance G H : ℝ) / (n : ℝ) ^ 2 := by
  calc
    cutDist (graphGraphon G) (graphGraphon H) ≤
        graphonL1Dist (graphGraphon G) (graphGraphon H) :=
      cutDist_le_graphonL1Dist _ _
    _ = _ := graphonL1Dist_graphGraphon hn G H

end InducedStars
