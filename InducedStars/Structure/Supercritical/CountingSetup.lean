import InducedStars.Structure.Supercritical.FarFamily
import InducedStars.Structure.Supercritical.Division
import InducedStars.FiniteModels.EntropyAsymptotics
import DenseGraph.Combinatorics.BinomialProfiles
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Supercritical counting setup

This file contains the deterministic finite bookkeeping used before the
probabilistic medium-degree estimate.  In particular, unordered main-part
pairs are represented only once, cross-edge profiles retain their capacity
proofs, and the graph families are literal finite filters of the close
family.
-/

noncomputable section

open Filter Finset Set
open scoped BigOperators

namespace InducedStars

noncomputable local instance countingSetupDecidableRel
    {W : Type*} (G : SimpleGraph W) : DecidableRel G.Adj :=
  Classical.decRel _

/-! ## Unordered main-part pairs and cross-edge profiles -/

/-- A stable, duplicate-free index for an unordered pair of distinct main
parts.  The increasing endpoints are part of the data. -/
@[ext]
structure SupercriticalPartPair (k : ℕ) where
  left : Fin (k - 1)
  right : Fin (k - 1)
  left_lt_right : left < right
deriving DecidableEq, Fintype

namespace SupercriticalPartPair

variable {k : ℕ}

theorem left_ne_right (e : SupercriticalPartPair k) : e.left ≠ e.right :=
  ne_of_lt e.left_lt_right

theorem right_ne_left (e : SupercriticalPartPair k) : e.right ≠ e.left :=
  e.left_ne_right.symm

/-- Forget the chosen increasing orientation. -/
def toSym2 (e : SupercriticalPartPair k) : Sym2 (Fin (k - 1)) :=
  s(e.left, e.right)

@[simp] theorem toSym2_not_isDiag (e : SupercriticalPartPair k) :
    ¬ e.toSym2.IsDiag := by
  simpa [toSym2, Sym2.mk_isDiag_iff] using e.left_ne_right

end SupercriticalPartPair

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of possible edges across the main-part pair `e`. -/
def crossEdgeCapacity (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) : ℕ :=
  (D.parts e.left).card * (D.parts e.right).card

/-- A feasible vector of cross-part edge counts. -/
structure SupercriticalEdgeProfile (D : SupercriticalDivision k V) where
  count : SupercriticalPartPair k → ℕ
  count_le_capacity : ∀ e, count e ≤ crossEdgeCapacity D e

@[ext] theorem SupercriticalEdgeProfile.ext
    {D : SupercriticalDivision k V} {p q : SupercriticalEdgeProfile D}
    (h : p.count = q.count) : p = q := by
  cases p
  cases q
  cases h
  rfl

/-- Extract the actual cross-edge counts of a graph. -/
def crossEdgeProfile (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    SupercriticalEdgeProfile D where
  count e := (G.interedges (D.parts e.left) (D.parts e.right)).card
  count_le_capacity e := G.card_interedges_le_mul _ _

@[simp] theorem crossEdgeProfile_count (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (e : SupercriticalPartPair k) :
    (crossEdgeProfile G D).count e =
      (G.interedges (D.parts e.left) (D.parts e.right)).card :=
  rfl

/-- Total number of cross-part edges encoded by a profile. -/
def profileTotal {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D) : ℕ :=
  ∑ e, p.count e

/-- Density of one cell of a cross-edge profile. -/
def profileDensity {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D) (e : SupercriticalPartPair k) : ℝ :=
  (p.count e : ℝ) /
    ((D.parts e.left).card * (D.parts e.right).card : ℕ)

theorem crossEdgeCapacity_pos (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) : 0 < crossEdgeCapacity D e := by
  exact Nat.mul_pos (D.parts_nonempty e.left).card_pos
    (D.parts_nonempty e.right).card_pos

theorem profileDensity_crossEdgeProfile (G : SimpleGraph V)
    (D : SupercriticalDivision k V) (e : SupercriticalPartPair k) :
    profileDensity (crossEdgeProfile G D) e =
      Regularity.graphDensity G (D.parts e.left) (D.parts e.right) := by
  rw [profileDensity, Regularity.graphDensity_eq]
  simp only [crossEdgeProfile_count, Nat.cast_mul]

/-! ## Internal capacity and the literal integer defect shift -/

/-- Edge capacity contributed by completing every main part to a clique. -/
def divisionInternalCliqueCapacity (D : SupercriticalDivision k V) : ℕ :=
  ∑ i, (D.parts i).card.choose 2

/-- The number of edges of `G` whose two endpoints lie in `S`. -/
def inducedEdgeCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  (G.induce (S : Set V)).edgeFinset.card

/-- The ordered adjacency count on `S × S` is twice the number of induced
unordered edges. -/
theorem card_interedges_self_eq_two_mul_inducedEdgeCount
    (G : SimpleGraph V) (S : Finset V) :
    (G.interedges S S).card = 2 * inducedEdgeCount G S := by
  classical
  let H := G.induce (S : Set V)
  let emb : (↥S × ↥S) ↪ (V × V) :=
    ⟨fun p ↦ (p.1.1, p.2.1), by
      intro p q hpq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hpq)
      · exact Subtype.ext (congrArg Prod.snd hpq)⟩
  have hmap :
      (Finset.univ.filter fun p : ↥S × ↥S ↦ H.Adj p.1 p.2).map emb =
        G.interedges S S := by
    ext p
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      SimpleGraph.mem_interedges_iff]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.1.2, q.2.2, hq⟩
    · rintro ⟨hp1, hp2, hG⟩
      refine ⟨(⟨p.1, hp1⟩, ⟨p.2, hp2⟩), ?_, rfl⟩
      exact hG
  calc
    (G.interedges S S).card =
        (Finset.univ.filter fun p : ↥S × ↥S ↦ H.Adj p.1 p.2).card := by
      rw [← hmap, Finset.card_map]
    _ = 2 * H.edgeFinset.card := H.two_mul_card_edgeFinset.symm
    _ = 2 * inducedEdgeCount G S := rfl

theorem inducedEdgeCount_add_compl (G : SimpleGraph V) (S : Finset V) :
    inducedEdgeCount G S + inducedEdgeCount Gᶜ S = S.card.choose 2 := by
  classical
  letI : DecidableRel G.Adj := countingSetupDecidableRel G
  letI : DecidableRel Gᶜ.Adj := countingSetupDecidableRel Gᶜ
  have hdisj : Disjoint (G.induce (S : Set V)).edgeFinset
      (Gᶜ.induce (S : Set V)).edgeFinset := by
    rw [Finset.disjoint_left]
    intro e he hec
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he hec
        exact hec.2 he
  have hunion : (G.induce (S : Set V)).edgeFinset ∪
      (Gᶜ.induce (S : Set V)).edgeFinset =
      (⊤ : SimpleGraph ↥S).edgeFinset := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [Finset.mem_union, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj,
          SimpleGraph.compl_adj]
        constructor
        · rintro (h | h)
          · change x ≠ y
            exact fun hxy ↦ G.ne_of_adj h (congrArg Subtype.val hxy)
          · change x ≠ y
            exact fun hxy ↦ h.1 (congrArg Subtype.val hxy)
        · intro hxy
          have hxy' : (x : V) ≠ (y : V) := fun h ↦
            hxy (Subtype.ext h)
          by_cases hH : G.Adj x y
          · exact Or.inl hH
          · exact Or.inr ⟨hxy', hH⟩
  simp only [inducedEdgeCount]
  calc
    (G.induce (S : Set V)).edgeFinset.card +
        (Gᶜ.induce (S : Set V)).edgeFinset.card =
      ((G.induce (S : Set V)).edgeFinset ∪
        (Gᶜ.induce (S : Set V)).edgeFinset).card :=
      (Finset.card_union_of_disjoint hdisj).symm
    _ = (⊤ : SimpleGraph ↥S).edgeFinset.card := by rw [hunion]
    _ = S.card.choose 2 := by
      rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp

private theorem card_interedges_union_left_of_disjoint
    (G : SimpleGraph V) (A B C : Finset V) (hAB : Disjoint A B) :
    (G.interedges (A ∪ B) C).card =
      (G.interedges A C).card + (G.interedges B C).card := by
  classical
  have hunion : G.interedges (A ∪ B) C =
      G.interedges A C ∪ G.interedges B C := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    tauto
  rw [hunion, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_left hAB C

private theorem card_interedges_union_right_of_disjoint
    (G : SimpleGraph V) (A B C : Finset V) (hAB : Disjoint A B) :
    (G.interedges C (A ∪ B)).card =
      (G.interedges C A).card + (G.interedges C B).card := by
  classical
  have hunion : G.interedges C (A ∪ B) =
      G.interedges C A ∪ G.interedges C B := by
    ext p
    simp only [SimpleGraph.mem_interedges_iff, Finset.mem_union]
    tauto
  rw [hunion, Finset.card_union_of_disjoint]
  exact G.interedges_disjoint_right C hAB

/-- Decompose the ordered adjacency count into support-support,
support-sparse, and sparse-sparse cells. -/
theorem two_mul_card_finiteGraphEdges_eq_support_sparse_cells
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    2 * (finiteGraphEdges G).card =
      (G.interedges D.support D.support).card +
        2 * (G.interedges D.support D.sparse).card +
        (G.interedges D.sparse D.sparse).card := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : Std.Symm G.Adj := G.symm
  have hedge : finiteGraphEdges G = G.edgeFinset := by
    ext e
    simp [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  have hall : G.interedges (Finset.univ : Finset V) Finset.univ =
      Finset.univ.filter fun p : V × V ↦ G.Adj p.1 p.2 := by
    ext p
    simp [SimpleGraph.mem_interedges_iff]
  have hdisj : Disjoint D.support D.sparse := by
    rw [Finset.disjoint_left]
    intro v hv hvs
    exact (SupercriticalDivision.mem_sparse.mp hvs) hv
  have hcross : (G.interedges D.sparse D.support).card =
      (G.interedges D.support D.sparse).card := by
    exact Rel.card_interedges_comm (r := G.Adj) _ _
  calc
    2 * (finiteGraphEdges G).card = 2 * G.edgeFinset.card := by rw [hedge]
    _ = (Finset.univ.filter fun p : V × V ↦ G.Adj p.1 p.2).card :=
      G.two_mul_card_edgeFinset
    _ = (G.interedges (Finset.univ : Finset V) Finset.univ).card := by
      rw [hall]
    _ = (G.interedges (D.support ∪ D.sparse)
        (D.support ∪ D.sparse)).card := by
      rw [D.support_union_sparse]
    _ = ((G.interedges D.support D.support).card +
          (G.interedges D.support D.sparse).card) +
        ((G.interedges D.sparse D.support).card +
          (G.interedges D.sparse D.sparse).card) := by
      rw [card_interedges_union_left_of_disjoint G D.support D.sparse
        (D.support ∪ D.sparse) hdisj,
        card_interedges_union_right_of_disjoint G D.support D.sparse
          D.support hdisj,
        card_interedges_union_right_of_disjoint G D.support D.sparse
          D.sparse hdisj]
    _ = (G.interedges D.support D.support).card +
        2 * (G.interedges D.support D.sparse).card +
        (G.interedges D.sparse D.sparse).card := by omega

/-- The support-support ordered cell is the disjoint sum over all ordered
pairs of main parts. -/
theorem card_interedges_support_support_eq_sum_part_cells
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (G.interedges D.support D.support).card =
      ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts j)).card := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  have hpairwise :
      (↑((Finset.univ : Finset (Fin (k - 1))) ×ˢ
          (Finset.univ : Finset (Fin (k - 1)))) : Set
            (Fin (k - 1) × Fin (k - 1))).PairwiseDisjoint
        (fun ij ↦ G.interedges (D.parts ij.1) (D.parts ij.2)) := by
    intro ij _ ij' _ hij
    change Disjoint
      (G.interedges (D.parts ij.1) (D.parts ij.2))
      (G.interedges (D.parts ij'.1) (D.parts ij'.2))
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [SimpleGraph.mem_interedges_iff] at hp hp'
    have hi : ij.1 = ij'.1 := D.mem_part_unique hp.1 hp'.1
    have hj : ij.2 = ij'.2 := D.mem_part_unique hp.2.1 hp'.2.1
    exact hij (Prod.ext hi hj)
  calc
    (G.interedges D.support D.support).card =
        ((Finset.univ ×ˢ Finset.univ).biUnion fun ij ↦
          G.interedges (D.parts ij.1) (D.parts ij.2)).card := by
      rw [SupercriticalDivision.support, G.interedges_biUnion]
    _ = ∑ ij ∈ (Finset.univ : Finset (Fin (k - 1))) ×ˢ Finset.univ,
        (G.interedges (D.parts ij.1) (D.parts ij.2)).card := by
      exact Finset.card_biUnion hpairwise
    _ = ∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts j)).card := by
      rw [Finset.sum_product]

private theorem sum_part_cells_eq_diag_add_two_profile
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (∑ i : Fin (k - 1), ∑ j : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts j)).card) =
      (∑ i : Fin (k - 1),
        (G.interedges (D.parts i) (D.parts i)).card) +
        2 * profileTotal (crossEdgeProfile G D) := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  letI : Std.Symm G.Adj := G.symm
  let I := Fin (k - 1)
  let f : I → I → ℕ := fun i j ↦
    (G.interedges (D.parts i) (D.parts j)).card
  let pairs : Finset (I × I) := Finset.univ ×ˢ Finset.univ
  let ltPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 < p.2
  let gtPairs : Finset (I × I) := pairs.filter fun p ↦ p.2 < p.1
  let diagPairs : Finset (I × I) := pairs.filter fun p ↦ p.1 = p.2
  have hsymm (i j : I) : f i j = f j i := by
    exact Rel.card_interedges_comm (r := G.Adj) _ _
  have hsplit :
      (∑ p ∈ pairs, f p.1 p.2) =
        (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rcases lt_trichotomy p.1 p.2 with hlt | heq | hgt
    · simp [hlt, ne_of_lt hlt, not_lt_of_ge hlt.le]
    · simp [heq, lt_irrefl p.2]
    · simp [hgt, ne_of_gt hgt, not_lt_of_ge hgt.le]
  have hdiag :
      (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) =
        ∑ i : I, f i i := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ diagPairs, f p.1 p.2) = _
    apply Finset.sum_bij (fun p _ ↦ p.1)
    · intro p hp
      simp
    · intro p hp q hq hpq
      have hpEq := (Finset.mem_filter.mp hp).2
      have hqEq := (Finset.mem_filter.mp hq).2
      apply Prod.ext hpq
      simpa [hpEq, hqEq] using hpq
    · intro i hi
      refine ⟨(i, i), ?_, rfl⟩
      simp [diagPairs, pairs]
    · intro p hp
      have hpEq := (Finset.mem_filter.mp hp).2
      simpa [hpEq]
  have hlt :
      (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) =
        profileTotal (crossEdgeProfile G D) := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ ltPairs, f p.1 p.2) = _
    unfold profileTotal
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.left hpq)
        (congrArg SupercriticalPartPair.right hpq)
    · intro e he
      refine ⟨(e.left, e.right), ?_, ?_⟩
      · simp [ltPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p hp
      rfl
  have hgt :
      (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) =
        profileTotal (crossEdgeProfile G D) := by
    rw [← Finset.sum_filter]
    change (∑ p ∈ gtPairs, f p.1 p.2) = _
    unfold profileTotal
    apply Finset.sum_bij
        (fun p hp ↦
          (⟨p.2, p.1, (Finset.mem_filter.mp hp).2⟩ :
            SupercriticalPartPair k))
    · intro p hp
      simp
    · intro p hp q hq hpq
      exact Prod.ext (congrArg SupercriticalPartPair.right hpq)
        (congrArg SupercriticalPartPair.left hpq)
    · intro e he
      refine ⟨(e.right, e.left), ?_, ?_⟩
      · simp [gtPairs, pairs, e.left_lt_right]
      · exact SupercriticalPartPair.ext rfl rfl
    · intro p hp
      exact hsymm p.1 p.2
  change (∑ i : I, ∑ j : I, f i j) =
    (∑ i : I, f i i) + 2 * profileTotal (crossEdgeProfile G D)
  calc
    (∑ i : I, ∑ j : I, f i j) =
        ∑ p ∈ pairs, f p.1 p.2 := by
      simpa [pairs] using
        (Fintype.sum_prod_type
          (fun p : I × I ↦ f p.1 p.2)).symm
    _ = (∑ p ∈ pairs, if p.1 = p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.1 < p.2 then f p.1 p.2 else 0) +
          (∑ p ∈ pairs, if p.2 < p.1 then f p.1 p.2 else 0) := hsplit
    _ = (∑ i : I, f i i) +
        2 * profileTotal (crossEdgeProfile G D) := by
      rw [hdiag, hlt, hgt]
      omega

theorem crossEdgeProfile_combinedSupercriticalDefectGraph_count_eq_zero
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) :
    (crossEdgeProfile (combinedSupercriticalDefectGraph G D) D).count e = 0 := by
  rw [crossEdgeProfile_count, Finset.card_eq_zero]
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨p, hp⟩
  rw [SimpleGraph.mem_interedges_iff] at hp
  exact combinedSupercriticalDefectGraph_not_adj_of_mem_distinct_parts
    G D e.left_ne_right hp.1 hp.2.1 hp.2.2

@[simp] theorem profileTotal_crossEdgeProfile_combinedSupercriticalDefectGraph
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    profileTotal (crossEdgeProfile (combinedSupercriticalDefectGraph G D) D) = 0 := by
  unfold profileTotal
  apply Finset.sum_eq_zero
  intro e _
  exact crossEdgeProfile_combinedSupercriticalDefectGraph_count_eq_zero G D e

theorem card_interedges_combined_part_eq_compl
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (i : Fin (k - 1)) :
    ((combinedSupercriticalDefectGraph G D).interedges
      (D.parts i) (D.parts i)).card =
        (Gᶜ.interedges (D.parts i) (D.parts i)).card := by
  congr 1
  ext p
  simp only [SimpleGraph.mem_interedges_iff]
  constructor
  · rintro ⟨hx, hy, hT⟩
    refine ⟨hx, hy, ?_⟩
    simpa using
      (combinedSupercriticalDefectGraph_adj_of_mem_same_part
        G D i hx hy).mp hT
  · rintro ⟨hx, hy, hC⟩
    refine ⟨hx, hy, ?_⟩
    apply (combinedSupercriticalDefectGraph_adj_of_mem_same_part
      G D i hx hy).mpr
    simpa using hC

/-- Missing main-part edges are exactly the combined defect edges induced
on the support. -/
theorem two_mul_inducedEdgeCount_combined_support
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    2 * inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.support =
      ∑ i, (Gᶜ.interedges (D.parts i) (D.parts i)).card := by
  let T := combinedSupercriticalDefectGraph G D
  calc
    2 * inducedEdgeCount T D.support =
        (T.interedges D.support D.support).card :=
      (card_interedges_self_eq_two_mul_inducedEdgeCount T D.support).symm
    _ = ∑ i, ∑ j, (T.interedges (D.parts i) (D.parts j)).card :=
      card_interedges_support_support_eq_sum_part_cells T D
    _ = (∑ i, (T.interedges (D.parts i) (D.parts i)).card) +
        2 * profileTotal (crossEdgeProfile T D) :=
      sum_part_cells_eq_diag_add_two_profile T D
    _ = ∑ i, (Gᶜ.interedges (D.parts i) (D.parts i)).card := by
      simp [T, card_interedges_combined_part_eq_compl]

/-- The paper's integer defect shift
`e_T(support,sparse) + e(T[sparse]) - e(T[support])`. -/
def supercriticalDefectShift (T : SimpleGraph V)
    (D : SupercriticalDivision k V) : ℤ :=
  ((T.interedges D.support D.sparse).card : ℤ) +
    (inducedEdgeCount T D.sparse : ℤ) -
    (inducedEdgeCount T D.support : ℤ)

@[simp] theorem supercriticalDefectShift_eq (T : SimpleGraph V)
    (D : SupercriticalDivision k V) :
    supercriticalDefectShift T D =
      ((T.interedges D.support D.sparse).card : ℤ) +
        (inducedEdgeCount T D.sparse : ℤ) -
        (inducedEdgeCount T D.support : ℤ) :=
  rfl

/-- The combined-defect cost is exactly the sum of its three geometric edge
classes. -/
theorem supercriticalDefectCost_eq_shift_components
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    supercriticalDefectCost G D =
      ((combinedSupercriticalDefectGraph G D).interedges
          D.support D.sparse).card +
        inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.sparse +
        inducedEdgeCount (combinedSupercriticalDefectGraph G D) D.support := by
  let T := combinedSupercriticalDefectGraph G D
  have hdecomp :=
    two_mul_card_finiteGraphEdges_eq_support_sparse_cells T D
  have hsupport := card_interedges_self_eq_two_mul_inducedEdgeCount
    T D.support
  have hsparse := card_interedges_self_eq_two_mul_inducedEdgeCount
    T D.sparse
  have hcost := card_finiteGraphEdges_combinedSupercriticalDefectGraph G D
  dsimp [T] at hdecomp hsupport hsparse
  rw [hcost, hsupport, hsparse] at hdecomp
  omega

/-- The absolute integer shift is bounded by the combined-defect cost. -/
theorem supercriticalDefectShift_natAbs_le_cost
    (G : SimpleGraph V) (D : SupercriticalDivision k V) :
    (supercriticalDefectShift
      (combinedSupercriticalDefectGraph G D) D).natAbs ≤
        supercriticalDefectCost G D := by
  let T := combinedSupercriticalDefectGraph G D
  let a := (T.interedges D.support D.sparse).card
  let b := inducedEdgeCount T D.sparse
  let c := inducedEdgeCount T D.support
  have hcost : supercriticalDefectCost G D = a + b + c := by
    simpa [T, a, b, c] using supercriticalDefectCost_eq_shift_components G D
  have habs : (((a : ℤ) + (b : ℤ) - (c : ℤ))).natAbs ≤ a + b + c := by
    calc
      (((a : ℤ) + (b : ℤ) - (c : ℤ))).natAbs ≤
          ((a : ℤ) + (b : ℤ)).natAbs + ((c : ℤ)).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ (a : ℤ).natAbs + (b : ℤ).natAbs + (c : ℤ).natAbs := by
        omega
      _ = a + b + c := by simp
  simpa [supercriticalDefectShift, T, a, b, c, hcost] using habs

/-! ## Admissible profiles -/

/-- The exact profile family `M_{Π,t}` at one integer defect shift. -/
def SupercriticalProfileAtShift (D : SupercriticalDivision k V)
    (m : ℕ) (rho delta : ℝ) (t : ℤ)
    (p : SupercriticalEdgeProfile D) : Prop :=
  (profileTotal p : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + t = m ∧
    ∀ e, rho - delta ≤ profileDensity p e ∧
      profileDensity p e ≤ rho + delta

/-- The bounded union of admissible shift-profile families. -/
def SupercriticalProfileWindow (D : SupercriticalDivision k V)
    (m : ℕ) (rho delta : ℝ) (budget : ℕ)
    (p : SupercriticalEdgeProfile D) : Prop :=
  ∃ t : ℤ, t.natAbs ≤ budget ∧
    SupercriticalProfileAtShift D m rho delta t p

theorem profile_mem_window_iff_exists_shift
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (budget : ℕ) (p : SupercriticalEdgeProfile D) :
    SupercriticalProfileWindow D m rho delta budget p ↔
      ∃ t : ℤ, t.natAbs ≤ budget ∧
        SupercriticalProfileAtShift D m rho delta t p :=
  Iff.rfl

/-- Once the exact integer edge decomposition and the cross-density bounds
have been established, the actual profile belongs to the corresponding
bounded window.  Keeping the decomposition as an explicit hypothesis makes
this lemma reusable for canonical and prescribed divisions alike. -/
theorem crossEdgeProfile_mem_window_of_edge_identity
    (G : SimpleGraph V) (D : SupercriticalDivision k V)
    (m budget : ℕ) (rho delta : ℝ)
    (hedges : (finiteGraphEdges G).card = m)
    (hidentity :
      ((finiteGraphEdges G).card : ℤ) =
        (divisionInternalCliqueCapacity D : ℤ) +
          (profileTotal (crossEdgeProfile G D) : ℤ) +
          supercriticalDefectShift
            (combinedSupercriticalDefectGraph G D) D)
    (hshift : (supercriticalDefectShift
      (combinedSupercriticalDefectGraph G D) D).natAbs ≤ budget)
    (hdensity : ∀ e : SupercriticalPartPair k,
      |Regularity.graphDensity G (D.parts e.left) (D.parts e.right) - rho| ≤
        delta) :
    SupercriticalProfileWindow D m rho delta budget
      (crossEdgeProfile G D) := by
  refine ⟨supercriticalDefectShift
    (combinedSupercriticalDefectGraph G D) D, hshift, ?_, ?_⟩
  · rw [hedges] at hidentity
    omega
  · intro e
    rw [profileDensity_crossEdgeProfile]
    rcases abs_le.mp (hdensity e) with ⟨hlower, hupper⟩
    constructor <;> linarith

/-! ## Profile multiplicity -/

/-- The number of independent cross-edge choices with profile `p`. -/
def supercriticalProfileMultiplicity {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D) : ℕ :=
  ∏ e, (crossEdgeCapacity D e).choose (p.count e)

theorem supercriticalProfileMultiplicity_pos
    {D : SupercriticalDivision k V} (p : SupercriticalEdgeProfile D) :
    0 < supercriticalProfileMultiplicity p := by
  classical
  exact Finset.prod_pos fun e _ ↦ Nat.choose_pos (p.count_le_capacity e)

/-- The literal finite set of independent coordinate choices realizing a
profile.  Coordinates are oriented from the smaller to the larger part
index, but still represent unordered graph edges because the parts are
disjoint. -/
def supercriticalProfileChoiceFinset (D : SupercriticalDivision k V)
    (p : SupercriticalEdgeProfile D) :
    Finset (SupercriticalPartPair k → Finset (V × V)) := by
  classical
  exact Fintype.piFinset fun e ↦
    ((D.parts e.left ×ˢ D.parts e.right).powersetCard (p.count e))

@[simp] theorem mem_supercriticalProfileChoiceFinset
    (D : SupercriticalDivision k V) (p : SupercriticalEdgeProfile D)
    (f : SupercriticalPartPair k → Finset (V × V)) :
    f ∈ supercriticalProfileChoiceFinset D p ↔
      ∀ e, f e ⊆ D.parts e.left ×ˢ D.parts e.right ∧
        (f e).card = p.count e := by
  classical
  simp [supercriticalProfileChoiceFinset]

theorem card_supercriticalProfileChoiceFinset
    (D : SupercriticalDivision k V) (p : SupercriticalEdgeProfile D) :
    (supercriticalProfileChoiceFinset D p).card =
      supercriticalProfileMultiplicity p := by
  classical
  simp [supercriticalProfileChoiceFinset, supercriticalProfileMultiplicity,
    crossEdgeCapacity]

theorem supercriticalProfileMultiplicity_le_two_pow
    {D : SupercriticalDivision k V} (p : SupercriticalEdgeProfile D) :
    supercriticalProfileMultiplicity p ≤
      2 ^ (∑ e, crossEdgeCapacity D e) := by
  classical
  calc
    supercriticalProfileMultiplicity p ≤
        ∏ e : SupercriticalPartPair k, 2 ^ crossEdgeCapacity D e := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun e _ ↦ Nat.choose_le_two_pow _ _)
    _ = 2 ^ (∑ e : SupercriticalPartPair k, crossEdgeCapacity D e) := by
      rw [Finset.prod_pow_eq_pow_sum]

/-- Profiles whose coordinate densities lie in the same compact band have
comparable multiplicities.  The displayed exponent retains the exact total
cross-cell capacity, which is useful before replacing it by a coarse `O(n²)`
bound. -/
theorem supercriticalProfileMultiplicity_le_mul_exp_of_density_band
    {D : SupercriticalDivision k V}
    (p q : SupercriticalEdgeProfile D) {rho delta : ℝ}
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hp : ∀ e, rho - delta ≤ profileDensity p e ∧
      profileDensity p e ≤ rho + delta)
    (hq : ∀ e, rho - delta ≤ profileDensity q e ∧
      profileDensity q e ≤ rho + delta) :
    (supercriticalProfileMultiplicity p : ℝ) ≤
      (supercriticalProfileMultiplicity q : ℝ) *
        Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
          (∑ e, crossEdgeCapacity D e : ℕ)) := by
  classical
  have hcoordinate (e : SupercriticalPartPair k) :
      ((crossEdgeCapacity D e).choose (p.count e) : ℝ) ≤
        ((crossEdgeCapacity D e).choose (q.count e) : ℝ) *
          Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
            crossEdgeCapacity D e) := by
    apply DenseGraph.choose_le_choose_mul_exp_of_density_band
      (p.count_le_capacity e) (q.count_le_capacity e)
      hdelta hlower hupper
    · simpa [profileDensity, crossEdgeCapacity] using hp e
    · simpa [profileDensity, crossEdgeCapacity] using hq e
  calc
    (supercriticalProfileMultiplicity p : ℝ) =
        ∏ e : SupercriticalPartPair k,
          ((crossEdgeCapacity D e).choose (p.count e) : ℝ) := by
      simp [supercriticalProfileMultiplicity]
    _ ≤ ∏ e : SupercriticalPartPair k,
        (((crossEdgeCapacity D e).choose (q.count e) : ℝ) *
          Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
            crossEdgeCapacity D e)) := by
      exact Finset.prod_le_prod (fun _ _ ↦ by positivity)
        (fun e _ ↦ hcoordinate e)
    _ = (∏ e : SupercriticalPartPair k,
          ((crossEdgeCapacity D e).choose (q.count e) : ℝ)) *
        (∏ e : SupercriticalPartPair k,
          Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
            crossEdgeCapacity D e)) := by
      rw [Finset.prod_mul_distrib]
    _ = (supercriticalProfileMultiplicity q : ℝ) *
        Real.exp (∑ e : SupercriticalPartPair k,
          DenseGraph.binomialDensityBandConstant rho * delta *
            crossEdgeCapacity D e) := by
      rw [← Real.exp_sum]
      congr 1
      simp [supercriticalProfileMultiplicity]
    _ = (supercriticalProfileMultiplicity q : ℝ) *
        Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
          (∑ e, crossEdgeCapacity D e : ℕ)) := by
      simp only [Nat.cast_sum]
      congr 2
      rw [Finset.mul_sum]

/-- Window membership supplies the coordinate hypotheses of the preceding
comparison automatically. -/
theorem supercriticalProfileMultiplicity_le_mul_exp_of_mem_window
    {D : SupercriticalDivision k V} {m budget : ℕ} {rho delta : ℝ}
    (p q : SupercriticalEdgeProfile D)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hp : SupercriticalProfileWindow D m rho delta budget p)
    (hq : SupercriticalProfileWindow D m rho delta budget q) :
    (supercriticalProfileMultiplicity p : ℝ) ≤
      (supercriticalProfileMultiplicity q : ℝ) *
        Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
          (∑ e, crossEdgeCapacity D e : ℕ)) := by
  exact supercriticalProfileMultiplicity_le_mul_exp_of_density_band
    p q hdelta hlower hupper hp.choose_spec.2.2 hq.choose_spec.2.2

/-! ## A coarse finite count of all feasible profiles -/

/-- All feasible cross-count vectors, before the edge-sum and density-window
filters are imposed. -/
def supercriticalProfileCountVectorFinset
    (D : SupercriticalDivision k V) :
    Finset (SupercriticalPartPair k → ℕ) := by
  classical
  exact Fintype.piFinset fun e ↦ Finset.range (crossEdgeCapacity D e + 1)

@[simp] theorem mem_supercriticalProfileCountVectorFinset
    (D : SupercriticalDivision k V) (f : SupercriticalPartPair k → ℕ) :
    f ∈ supercriticalProfileCountVectorFinset D ↔
      ∀ e, f e ≤ crossEdgeCapacity D e := by
  classical
  simp [supercriticalProfileCountVectorFinset, Nat.lt_succ_iff]

theorem card_supercriticalProfileCountVectorFinset
    (D : SupercriticalDivision k V) :
    (supercriticalProfileCountVectorFinset D).card =
      ∏ e, (crossEdgeCapacity D e + 1) := by
  classical
  simp [supercriticalProfileCountVectorFinset]

theorem crossEdgeCapacity_le_card_sq (D : SupercriticalDivision k V)
    (e : SupercriticalPartPair k) :
    crossEdgeCapacity D e ≤ Fintype.card V ^ 2 := by
  rw [crossEdgeCapacity, pow_two]
  have hleft : (D.parts e.left).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (show D.parts e.left ⊆ Finset.univ from Finset.subset_univ _)
  have hright : (D.parts e.right).card ≤ Fintype.card V := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (show D.parts e.right ⊆ Finset.univ from Finset.subset_univ _)
  exact Nat.mul_le_mul hleft hright

theorem sum_crossEdgeCapacity_le_card_pair_mul_card_sq
    (D : SupercriticalDivision k V) :
    ∑ e, crossEdgeCapacity D e ≤
      Fintype.card (SupercriticalPartPair k) * Fintype.card V ^ 2 := by
  calc
    ∑ e, crossEdgeCapacity D e ≤
        ∑ _e : SupercriticalPartPair k, Fintype.card V ^ 2 := by
      exact Finset.sum_le_sum fun e _ ↦ crossEdgeCapacity_le_card_sq D e
    _ = Fintype.card (SupercriticalPartPair k) * Fintype.card V ^ 2 := by
      simp

/-- Coarse `exp(C_{k,rho} * delta * |V|²)` form of the profile comparison.
The displayed constant is independent of the division, ambient size, edge
count and the two profiles. -/
theorem supercriticalProfileMultiplicity_le_mul_exp_card_sq_of_mem_window
    {D : SupercriticalDivision k V} {m budget : ℕ} {rho delta : ℝ}
    (p q : SupercriticalEdgeProfile D)
    (hdelta : 0 ≤ delta) (hlower : 0 < rho - 2 * delta)
    (hupper : rho + 2 * delta < 1)
    (hp : SupercriticalProfileWindow D m rho delta budget p)
    (hq : SupercriticalProfileWindow D m rho delta budget q) :
    (supercriticalProfileMultiplicity p : ℝ) ≤
      (supercriticalProfileMultiplicity q : ℝ) *
        Real.exp ((DenseGraph.binomialDensityBandConstant rho *
            Fintype.card (SupercriticalPartPair k)) * delta *
          (Fintype.card V : ℝ) ^ 2) := by
  have hbase := supercriticalProfileMultiplicity_le_mul_exp_of_mem_window
    p q hdelta hlower hupper hp hq
  have hcoefficient :
      0 ≤ DenseGraph.binomialDensityBandConstant rho * delta :=
    mul_nonneg
      (DenseGraph.binomialDensityBandConstant_nonneg hdelta hlower hupper)
      hdelta
  have hcapReal :
      ((∑ e, crossEdgeCapacity D e : ℕ) : ℝ) ≤
        (Fintype.card (SupercriticalPartPair k) : ℝ) *
          (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast sum_crossEdgeCapacity_le_card_pair_mul_card_sq D
  have hexp :
      Real.exp (DenseGraph.binomialDensityBandConstant rho * delta *
        (∑ e, crossEdgeCapacity D e : ℕ)) ≤
      Real.exp ((DenseGraph.binomialDensityBandConstant rho *
          Fintype.card (SupercriticalPartPair k)) * delta *
        (Fintype.card V : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    calc
      DenseGraph.binomialDensityBandConstant rho * delta *
          ((∑ e, crossEdgeCapacity D e : ℕ) : ℝ) ≤
        (DenseGraph.binomialDensityBandConstant rho * delta) *
          ((Fintype.card (SupercriticalPartPair k) : ℝ) *
            (Fintype.card V : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcapReal hcoefficient
      _ = (DenseGraph.binomialDensityBandConstant rho *
          Fintype.card (SupercriticalPartPair k)) * delta *
            (Fintype.card V : ℝ) ^ 2 := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

theorem card_supercriticalProfileCountVectorFinset_le
    (D : SupercriticalDivision k V) :
    (supercriticalProfileCountVectorFinset D).card ≤
      (Fintype.card V ^ 2 + 1) ^ Fintype.card (SupercriticalPartPair k) := by
  classical
  rw [card_supercriticalProfileCountVectorFinset]
  calc
    (∏ e, (crossEdgeCapacity D e + 1)) ≤
        ∏ _e : SupercriticalPartPair k, (Fintype.card V ^ 2 + 1) := by
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun e _ ↦ Nat.add_le_add_right (crossEdgeCapacity_le_card_sq D e) 1)
    _ = (Fintype.card V ^ 2 + 1) ^
        Fintype.card (SupercriticalPartPair k) := by simp

/-- The endpoint map embeds part-pair indices into the square of all main
part indices.  This deliberately coarse bound is sufficient for the later
polynomial-loss estimate. -/
theorem card_supercriticalPartPair_le_sq :
    Fintype.card (SupercriticalPartPair k) ≤ (k - 1) ^ 2 := by
  let f : SupercriticalPartPair k → Fin (k - 1) × Fin (k - 1) :=
    fun e ↦ (e.left, e.right)
  have hf : Function.Injective f := by
    intro e e' h
    apply SupercriticalPartPair.ext
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  simpa [f, Fintype.card_prod, Fintype.card_fin, pow_two] using
    Fintype.card_le_of_injective f hf

theorem card_supercriticalProfileCountVectorFinset_le_coarse
    (D : SupercriticalDivision k V) :
    (supercriticalProfileCountVectorFinset D).card ≤
      (Fintype.card V ^ 2 + 1) ^ ((k - 1) ^ 2) := by
  exact (card_supercriticalProfileCountVectorFinset_le D).trans
    (Nat.pow_le_pow_right (by omega) card_supercriticalPartPair_le_sq)

/-- The literal finite profile window, represented by its count vectors.
The feasibility filter supplies the capacity inequalities; the second
filter is exactly the union over bounded integer shifts. -/
def supercriticalProfileWindowFinset
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (budget : ℕ) : Finset (SupercriticalPartPair k → ℕ) := by
  classical
  exact (supercriticalProfileCountVectorFinset D).filter fun f ↦
    ∃ t : ℤ, t.natAbs ≤ budget ∧
      (↑(∑ e, f e) : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + t = m ∧
      ∀ e, rho - delta ≤
          (f e : ℝ) / (crossEdgeCapacity D e : ℕ) ∧
        (f e : ℝ) / (crossEdgeCapacity D e : ℕ) ≤ rho + delta

@[simp] theorem mem_supercriticalProfileWindowFinset
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (budget : ℕ) (f : SupercriticalPartPair k → ℕ) :
    f ∈ supercriticalProfileWindowFinset D m rho delta budget ↔
      (∀ e, f e ≤ crossEdgeCapacity D e) ∧
      ∃ t : ℤ, t.natAbs ≤ budget ∧
        (↑(∑ e, f e) : ℤ) + (divisionInternalCliqueCapacity D : ℤ) + t = m ∧
        ∀ e, rho - delta ≤
            (f e : ℝ) / (crossEdgeCapacity D e : ℕ) ∧
          (f e : ℝ) / (crossEdgeCapacity D e : ℕ) ≤ rho + delta := by
  classical
  simp [supercriticalProfileWindowFinset]

theorem card_supercriticalProfileWindowFinset_le_coarse
    (D : SupercriticalDivision k V) (m : ℕ) (rho delta : ℝ)
    (budget : ℕ) :
    (supercriticalProfileWindowFinset D m rho delta budget).card ≤
      (Fintype.card V ^ 2 + 1) ^ ((k - 1) ^ 2) := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans
    (card_supercriticalProfileCountVectorFinset_le_coarse D)

/-- Every fixed-degree polynomial loss is eventually absorbed by an
arbitrarily small positive quadratic exponential. -/
theorem eventually_supercriticalProfilePolynomial_le_exp
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (((n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ) ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
  let r := (k - 1) ^ 2
  have hlittle :
      (fun x : ℝ ↦ (2 : ℝ) ^ r * x ^ (2 * r)) =o[atTop]
        (fun x : ℝ ↦ Real.exp (c * x)) :=
    (isLittleO_pow_exp_pos_mul_atTop (2 * r) hc).const_mul_left
      ((2 : ℝ) ^ r)
  have hgrowth := (hlittle.bound (c := 1) zero_lt_one).natCast_atTop
  filter_upwards [hgrowth, eventually_ge_atTop 1] with n hnGrowth hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hbase : (n : ℝ) ^ 2 + 1 ≤ 2 * (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hpoly :
      (2 : ℝ) ^ r * (n : ℝ) ^ (2 * r) ≤
        Real.exp (c * (n : ℝ)) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hnGrowth
  have hexp : Real.exp (c * (n : ℝ)) ≤
      Real.exp (c * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hnSq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hnSq hc.le
  calc
    (((n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ) =
        ((n : ℝ) ^ 2 + 1) ^ r := by simp [r]
    _ ≤ (2 * (n : ℝ) ^ 2) ^ r := by gcongr
    _ = (2 : ℝ) ^ r * (n : ℝ) ^ (2 * r) := by
      rw [mul_pow, ← pow_mul]
    _ ≤ Real.exp (c * (n : ℝ)) := hpoly
    _ ≤ Real.exp (c * (n : ℝ) ^ 2) := hexp

/-- Uniform eventual exponential bound for every literal profile window on
`Fin n`; all choices of the division and the window parameters are covered. -/
theorem eventually_card_supercriticalProfileWindowFinset_le_exp
    (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (D : SupercriticalDivision k (Fin n))
      (m budget : ℕ) (rho delta : ℝ),
      ((supercriticalProfileWindowFinset D m rho delta budget).card : ℝ) ≤
        Real.exp (c * (n : ℝ) ^ 2) := by
  filter_upwards [eventually_supercriticalProfilePolynomial_le_exp k hc]
    with n hn D m budget rho delta
  have hcardNat := card_supercriticalProfileWindowFinset_le_coarse
    D m rho delta budget
  have hcardReal :
      ((supercriticalProfileWindowFinset D m rho delta budget).card : ℝ) ≤
        (((n ^ 2 + 1) ^ ((k - 1) ^ 2) : ℕ) : ℝ) := by
    exact_mod_cast (by simpa using hcardNat)
  exact hcardReal.trans hn

theorem count_mem_supercriticalProfileWindowFinset
    {D : SupercriticalDivision k V} {m budget : ℕ} {rho delta : ℝ}
    {p : SupercriticalEdgeProfile D}
    (hp : SupercriticalProfileWindow D m rho delta budget p) :
    p.count ∈ supercriticalProfileWindowFinset D m rho delta budget := by
  rcases hp with ⟨t, ht, hsum, hdensity⟩
  rw [mem_supercriticalProfileWindowFinset]
  refine ⟨p.count_le_capacity, t, ht, hsum, ?_⟩
  simpa [profileDensity, crossEdgeCapacity] using hdensity

/-! ## Exact finite close families -/

noncomputable local instance countingSetupGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

/-- Close graphs whose selected canonical division is literally `D`. -/
def supercriticalDivisionGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalCloseGraphFinset k hk gamma hgamma m n tau).filter
    fun G ↦ canonicalSupercriticalDivision G (by simpa using hn) = D

@[simp] theorem mem_supercriticalDivisionGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalDivisionGraphFinset k hk gamma hgamma m n tau hn D ↔
      G ∈ supercriticalCloseGraphFinset k hk gamma hgamma m n tau ∧
        canonicalSupercriticalDivision G (by simpa using hn) = D := by
  classical
  simp [supercriticalDivisionGraphFinset]

/-- The paper's defective family `F_Π`: the ordinary canonical defect
graph is nonempty. -/
def supercriticalDivisionDefectGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionGraphFinset k hk gamma hgamma m n tau hn D).filter
    fun G ↦ (finiteGraphEdges
      (canonicalSupercriticalDefectGraph G (by simpa using hn))).Nonempty

@[simp] theorem mem_supercriticalDivisionDefectGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D ↔
      G ∈ supercriticalCloseGraphFinset k hk gamma hgamma m n tau ∧
      canonicalSupercriticalDivision G (by simpa using hn) = D ∧
      (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).Nonempty := by
  classical
  simp [supercriticalDivisionDefectGraphFinset, and_assoc]

/-- The paper's clean family `F_Π*`: the ordinary canonical defect graph
has no edges.  Sparse-induced edges are deliberately not excluded. -/
def supercriticalCleanDivisionGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionGraphFinset k hk gamma hgamma m n tau hn D).filter
    fun G ↦ (finiteGraphEdges
      (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0

@[simp] theorem mem_supercriticalCleanDivisionGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D ↔
      G ∈ supercriticalCloseGraphFinset k hk gamma hgamma m n tau ∧
      canonicalSupercriticalDivision G (by simpa using hn) = D ∧
      (finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn))).card = 0 := by
  classical
  simp [supercriticalCleanDivisionGraphFinset, and_assoc]

theorem supercriticalDivisionGraphFinset_eq_defect_union_clean
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    supercriticalDivisionGraphFinset k hk gamma hgamma m n tau hn D =
      supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D ∪
        supercriticalCleanDivisionGraphFinset
          k hk gamma hgamma m n tau hn D := by
  classical
  ext G
  simp only [mem_supercriticalDivisionGraphFinset,
    mem_supercriticalDivisionDefectGraphFinset,
    mem_supercriticalCleanDivisionGraphFinset, Finset.mem_union,
    Finset.card_eq_zero]
  constructor
  · intro hbase
    by_cases hE : finiteGraphEdges
        (canonicalSupercriticalDefectGraph G (by simpa using hn)) = ∅
    · exact Or.inr ⟨hbase.1, hbase.2, hE⟩
    · exact Or.inl ⟨hbase.1, hbase.2,
        Finset.nonempty_iff_ne_empty.mpr hE⟩
  · rintro (⟨hclose, hdiv, -⟩ | ⟨hclose, hdiv, -⟩) <;>
      exact ⟨hclose, hdiv⟩

theorem supercriticalDivisionDefectGraphFinset_disjoint_clean
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Disjoint
      (supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D)
      (supercriticalCleanDivisionGraphFinset
        k hk gamma hgamma m n tau hn D) := by
  classical
  rw [Finset.disjoint_left]
  intro G hdef hclean
  rw [mem_supercriticalDivisionDefectGraphFinset] at hdef
  rw [mem_supercriticalCleanDivisionGraphFinset] at hclean
  exact hdef.2.2.card_pos.ne' hclean.2.2

/-- Combined defect patterns generated by defective close graphs. -/
def supercriticalCombinedDefectPatternFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionDefectGraphFinset
    k hk gamma hgamma m n tau hn D).image fun G ↦
      canonicalCombinedDefectGraph G (by simpa using hn)

@[simp] theorem mem_supercriticalCombinedDefectPatternFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)} :
    T ∈ supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D ↔
      ∃ G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D,
        canonicalCombinedDefectGraph G (by simpa using hn) = T := by
  classical
  simp [supercriticalCombinedDefectPatternFinset, eq_comm]

/-- Every displayed pattern is generated by a defective graph and its edge
count is exactly that graph's canonical combined-defect cost. -/
theorem exists_generator_with_pattern_edge_count
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    ∃ G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D,
      canonicalCombinedDefectGraph G (by simpa using hn) = T ∧
      (finiteGraphEdges T).card = supercriticalDefectCost G D := by
  obtain ⟨G, hG, hGT⟩ :=
    mem_supercriticalCombinedDefectPatternFinset.mp hT
  refine ⟨G, hG, hGT, ?_⟩
  have hdivision :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hG).2.1
  have hcard := card_finiteGraphEdges_combinedSupercriticalDefectGraph G D
  rw [← hGT]
  simpa [canonicalCombinedDefectGraph, hdivision] using hcard

theorem pattern_edge_count_le_of_generators
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n r : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hcost : ∀ G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D,
      supercriticalDefectCost G D ≤ r)
    {T : SimpleGraph (Fin n)}
    (hT : T ∈ supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D) :
    (finiteGraphEdges T).card ≤ r := by
  obtain ⟨G, hG, -, hcard⟩ := exists_generator_with_pattern_edge_count hT
  rw [hcard]
  exact hcost G hG

@[simp] theorem graphEditDistance_bot_eq_edge_count
    {n : ℕ} (T : SimpleGraph (Fin n)) :
    graphEditDistance (⊥ : SimpleGraph (Fin n)) T =
      (finiteGraphEdges T).card := by
  rw [graphEditDistance]
  congr 1
  ext e
  simp [mem_graphEditFinset, mem_finiteGraphEdges]

/-- A uniform cost bound places every combined pattern in the radius-`r`
Hamming ball about the empty graph. -/
theorem card_supercriticalCombinedDefectPatternFinset_le_hammingBallVolume
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {m n r : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)}
    (hcost : ∀ G ∈ supercriticalDivisionDefectGraphFinset
        k hk gamma hgamma m n tau hn D,
      supercriticalDefectCost G D ≤ r) :
    (supercriticalCombinedDefectPatternFinset
      k hk gamma hgamma m n tau hn D).card ≤
        hammingBallVolume (completeEdgeCount n) r := by
  calc
    (supercriticalCombinedDefectPatternFinset
        k hk gamma hgamma m n tau hn D).card ≤
        (graphHammingBall (⊥ : SimpleGraph (Fin n)) r).card := by
      apply Finset.card_le_card
      intro T hT
      rw [mem_graphHammingBall, graphEditDistance_bot_eq_edge_count]
      exact pattern_edge_count_le_of_generators hcost hT
    _ ≤ hammingBallVolume (completeEdgeCount n) r :=
      graphHammingBall_card_le_hammingBallVolume _

/-- Defective close graphs with a medium combined-defect degree in some
canonical main part. -/
def supercriticalMediumDegreeGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionDefectGraphFinset
    k hk gamma hgamma m n tau hn D).filter fun G ↦
      ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i

@[simp] theorem mem_supercriticalMediumDegreeGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalMediumDegreeGraphFinset
        k hk gamma hgamma alpha m n tau hn D ↔
      G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D ∧
      ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i := by
  classical
  simp [supercriticalMediumDegreeGraphFinset]

/-- Defective close graphs with fixed combined defect graph and no medium
degree.  This is the family consumed by the matching-penalty argument. -/
def supercriticalFixedDefectGraphFinset
    (k : ℕ) (hk : 3 ≤ k) (gamma : ℝ)
    (hgamma : gamma ∈ Set.Ico (gammaK k) 1)
    (alpha : ℝ) (m n : ℕ) (tau : ℝ) (hn : k - 1 ≤ n)
    (D : SupercriticalDivision k (Fin n)) (T : SimpleGraph (Fin n)) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact (supercriticalDivisionDefectGraphFinset
    k hk gamma hgamma m n tau hn D).filter fun G ↦
      canonicalCombinedDefectGraph G (by simpa using hn) = T ∧
      ¬ ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i

@[simp] theorem mem_supercriticalFixedDefectGraphFinset
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {T G : SimpleGraph (Fin n)} :
    G ∈ supercriticalFixedDefectGraphFinset
        k hk gamma hgamma alpha m n tau hn D T ↔
      G ∈ supercriticalDivisionDefectGraphFinset
          k hk gamma hgamma m n tau hn D ∧
      canonicalCombinedDefectGraph G (by simpa using hn) = T ∧
      ¬ ∃ v i, HasMediumDegreeInPart
        (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i := by
  classical
  simp [supercriticalFixedDefectGraphFinset, and_assoc]

/-! ## Refined medium witnesses -/

/-- A medium-degree witness together with its exhaustive geometric
location. -/
structure SupercriticalMediumWitness
    {k n : ℕ} (G : SimpleGraph (Fin n)) (alpha : ℝ)
    (D : SupercriticalDivision k (Fin n)) where
  vertex : Fin n
  part : Fin (k - 1)
  medium : HasMediumDegreeInPart
    (combinedSupercriticalDefectGraph G D) alpha D vertex part
  location : vertex ∈ D.parts part ∨ vertex ∈ D.sparse

theorem medium_vertex_mem_witness_part_or_sparse
    {k n : ℕ} {G : SimpleGraph (Fin n)} {alpha : ℝ}
    (halpha : 0 < alpha) (D : SupercriticalDivision k (Fin n))
    {v : Fin n} {i : Fin (k - 1)}
    (hmedium : HasMediumDegreeInPart
      (combinedSupercriticalDefectGraph G D) alpha D v i) :
    v ∈ D.parts i ∨ v ∈ D.sparse := by
  rcases D.sparse_or_existsUnique_part v with hs | ⟨j, hvj, hj⟩
  · exact Or.inr hs
  · by_cases hji : j = i
    · subst j
      exact Or.inl hvj
    · have hzero := degreeInFinset_combinedDefect_part_of_mem_distinct
        G D (Ne.symm hji) hvj
      have hcard : 0 < ((D.parts i).card : ℝ) := by
        exact_mod_cast (D.parts_nonempty i).card_pos
      unfold HasMediumDegreeInPart at hmedium
      rw [hzero] at hmedium
      exfalso
      exact (not_le_of_gt (mul_pos halpha hcard)) (by simpa using hmedium.1)

/-- Package any positive-parameter medium-degree witness with its forced
main-part/sparse location. -/
def SupercriticalMediumWitness.ofMedium
    {k n : ℕ} {G : SimpleGraph (Fin n)} {alpha : ℝ}
    (halpha : 0 < alpha) (D : SupercriticalDivision k (Fin n))
    (v : Fin n) (i : Fin (k - 1))
    (hmedium : HasMediumDegreeInPart
      (combinedSupercriticalDefectGraph G D) alpha D v i) :
    SupercriticalMediumWitness G alpha D where
  vertex := v
  part := i
  medium := hmedium
  location := medium_vertex_mem_witness_part_or_sparse halpha D hmedium

/-- Select and geometrically locate a witness from the exact medium-degree
family. -/
noncomputable def supercriticalMediumWitnessOfMem
    {k : ℕ} {hk : 3 ≤ k} {gamma : ℝ}
    {hgamma : gamma ∈ Set.Ico (gammaK k) 1}
    {alpha : ℝ} (halpha : 0 < alpha)
    {m n : ℕ} {tau : ℝ} {hn : k - 1 ≤ n}
    {D : SupercriticalDivision k (Fin n)} {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalMediumDegreeGraphFinset
      k hk gamma hgamma alpha m n tau hn D) :
    SupercriticalMediumWitness G alpha D := by
  classical
  have hdef := (mem_supercriticalMediumDegreeGraphFinset.mp hG).1
  have hex := (mem_supercriticalMediumDegreeGraphFinset.mp hG).2
  let v := Classical.choose hex
  let i := Classical.choose (Classical.choose_spec hex)
  have hmedium := Classical.choose_spec (Classical.choose_spec hex)
  change HasMediumDegreeInPart
    (canonicalCombinedDefectGraph G (by simpa using hn)) alpha D v i at hmedium
  have hdivision :=
    (mem_supercriticalDivisionDefectGraphFinset.mp hdef).2.1
  have hmedium' : HasMediumDegreeInPart
      (combinedSupercriticalDefectGraph G D) alpha D v i := by
    simpa [canonicalCombinedDefectGraph, hdivision] using hmedium
  exact SupercriticalMediumWitness.ofMedium halpha D v i hmedium'

end InducedStars
