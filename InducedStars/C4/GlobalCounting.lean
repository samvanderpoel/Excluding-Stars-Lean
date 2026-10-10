import InducedStars.C4.CountingFamilies
import InducedStars.C4.CoverMultiplicity

/-!
# Exact global C4 counting algebra

Paper: `eqn:c4-union-bound` and the final counting comparison. Split graphs
are counted once as actual graphs. Only exceptional weighted fibers use the
proved polynomial cover multiplicity; no unique-cover assertion is assumed.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

def c4NonsplitGraphFinset (n m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  (inducedC4FreeGraphFinsetWithEdges n m).filter fun G ↦ ¬DenseGraph.IsSplitGraph G

@[simp] theorem mem_c4NonsplitGraphFinset {n m : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ c4NonsplitGraphFinset n m ↔
      G ∈ inducedC4FreeGraphFinsetWithEdges n m ∧ ¬DenseGraph.IsSplitGraph G := by
  simp [c4NonsplitGraphFinset]

theorem c4_split_filter_eq (n m : ℕ) :
    (inducedC4FreeGraphFinsetWithEdges n m).filter DenseGraph.IsSplitGraph =
      splitGraphFinsetWithEdges n m := by
  ext G
  simp only [mem_filter, mem_inducedC4FreeGraphFinsetWithEdges,
    mem_splitGraphFinsetWithEdges]
  exact ⟨fun h ↦ ⟨h.2, h.1.2⟩,
    fun h ↦ ⟨⟨splitGraph_not_inducedEmbeds_C4 h.1, h.2⟩, h.1⟩⟩

/-- Exact good/bad count, including early zero-size ambient families. -/
theorem splitGraphCount_add_c4NonsplitCount (n m : ℕ) :
    splitGraphCountWithEdges n m + (c4NonsplitGraphFinset n m).card =
      inducedC4FreeGraphCountWithEdges n m := by
  have h := card_filter_add_card_filter_not
    (s := inducedC4FreeGraphFinsetWithEdges n m) DenseGraph.IsSplitGraph
  simpa only [c4_split_filter_eq, splitGraphCountWithEdges,
    c4NonsplitGraphFinset, inducedC4FreeGraphCountWithEdges] using h

theorem splitGraphFinset_disjoint_nonsplit (n m : ℕ) :
    Disjoint (splitGraphFinsetWithEdges n m) (c4NonsplitGraphFinset n m) := by
  apply disjoint_left.mpr
  intro G hsplit hbad
  exact (mem_c4NonsplitGraphFinset.mp hbad).2 (mem_splitGraphFinsetWithEdges.mp hsplit).1

def c4SplitProbability (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedC4FreeGraphFinsetWithEdges n m)
    (splitGraphFinsetWithEdges n m)

def c4NonsplitProbability (n m : ℕ) : ℝ :=
  uniformSubfamilyProbability (inducedC4FreeGraphFinsetWithEdges n m)
    (c4NonsplitGraphFinset n m)

theorem c4SplitProbability_add_nonsplit {n m : ℕ}
    (hpos : 0 < inducedC4FreeGraphCountWithEdges n m) :
    c4SplitProbability n m + c4NonsplitProbability n m = 1 := by
  unfold c4SplitProbability c4NonsplitProbability uniformSubfamilyProbability
  rw [← add_div, ← Nat.cast_add]
  change ((splitGraphCountWithEdges n m + (c4NonsplitGraphFinset n m).card : ℕ) : ℝ) /
    (inducedC4FreeGraphCountWithEdges n m : ℝ) = 1
  rw [splitGraphCount_add_c4NonsplitCount, div_self (by exact_mod_cast hpos.ne')]

def c4DivisionExceptionalFinset (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (D : C4Division (Fin n)) : Finset (SimpleGraph (Fin n)) :=
  c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D ∪
    c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D ∪
      (Icc 1 n).biUnion (c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D)

theorem card_c4DivisionExceptionalFinset_le (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (D : C4Division (Fin n)) :
    (c4DivisionExceptionalFinset n m gamma epsilon zeta alpha D).card ≤
      (c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card +
        (c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card +
          ∑ q ∈ Icc 1 n, (c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card := by
  apply (card_union_le _ _).trans
  exact Nat.add_le_add (card_union_le _ _) card_biUnion_le

/-- Exact finite union bound over the five genuine exceptional branches. -/
theorem c4Nonsplit_card_le_master_sum (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (halpha : 0 ≤ alpha) :
    (c4NonsplitGraphFinset n m).card ≤
      (c4FarGraphFinset n m epsilon).card +
        (c4CloseDegenerateGraphFinset n m gamma epsilon zeta).card +
          ∑ D : C4Division (Fin n),
            ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card +
              (c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card +
                ∑ q ∈ Icc 1 n,
                  (c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card) := by
  have hsub : c4NonsplitGraphFinset n m ⊆
      c4FarGraphFinset n m epsilon ∪ c4CloseDegenerateGraphFinset n m gamma epsilon zeta ∪
        univ.biUnion (c4DivisionExceptionalFinset n m gamma epsilon zeta alpha) := by
    intro G hG
    obtain ⟨hfree, hnot⟩ := mem_c4NonsplitGraphFinset.mp hG
    rcases c4Graph_master_decomposition halpha hfree with h | h | h | ⟨D, h | h | ⟨q,hq,h⟩⟩
    · exact (hnot h).elim
    · exact mem_union_left _ (mem_union_left _ h)
    · exact mem_union_left _ (mem_union_right _ h)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨D, mem_univ _,
        mem_union_left _ (mem_union_left _ h)⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨D, mem_univ _,
        mem_union_left _ (mem_union_right _ h)⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨D, mem_univ _,
        mem_union_right _ (mem_biUnion.mpr ⟨q,hq,h⟩)⟩)
  apply (card_le_card hsub).trans
  apply (card_union_le _ _).trans
  apply Nat.add_le_add (card_union_le _ _)
  apply card_biUnion_le.trans
  exact sum_le_sum fun D _ ↦ card_c4DivisionExceptionalFinset_le n m gamma epsilon zeta alpha D

/-- Finite aggregation of already-established local estimates. The reference
is the actual guarded split fiber, so infeasible divisions contribute zero. -/
theorem c4Nonsplit_card_le_weighted_reference (n m : ℕ) (gamma epsilon zeta alpha : ℝ)
    (halpha : 0 ≤ alpha) {a b l : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hl : 0 ≤ l)
    (hA : ∀ D : C4Division (Fin n),
      ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
        (c4SplitFiber D m).card*a)
    (hB : ∀ D : C4Division (Fin n),
      ((c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) ≤
        (c4SplitFiber D m).card*b)
    (hL : ∀ D : C4Division (Fin n),
      (∑ q ∈ Icc 1 n,
        ((c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card : ℝ)) ≤
        (c4SplitFiber D m).card*l) :
    ((c4NonsplitGraphFinset n m).card : ℝ) ≤
      (c4FarGraphFinset n m epsilon).card +
        (c4CloseDegenerateGraphFinset n m gamma epsilon zeta).card +
          ((n : ℝ)+1)^2*(splitGraphCountWithEdges n m : ℝ)*(a+b+l) := by
  have hlocal (D : C4Division (Fin n)) :
      ((c4HighIndependentGraphFinset n m gamma epsilon zeta alpha D).card : ℝ) +
        (c4HighCliqueGraphFinset n m gamma epsilon zeta alpha D).card +
          (∑ q ∈ Icc 1 n,
            ((c4LowDegreeMatchingGraphFinset n m gamma epsilon zeta alpha D q).card : ℝ)) ≤
        (c4SplitFiber D m).card*(a+b+l) := by
    have hh := add_le_add (add_le_add (hA D) (hB D)) (hL D)
    nlinarith only [hh]
  have hcover : (∑ D : C4Division (Fin n), ((c4SplitFiber D m).card : ℝ)) ≤
      ((n : ℝ)+1)^2*(splitGraphCountWithEdges n m : ℝ) := by
    exact_mod_cast sum_card_c4SplitFiber_le n m
  have hmaster := (Nat.cast_le (α := ℝ)).mpr
    (c4Nonsplit_card_le_master_sum n m gamma epsilon zeta alpha halpha)
  push_cast at hmaster
  apply hmaster.trans
  gcongr
  calc
    _ ≤ ∑ D : C4Division (Fin n), (c4SplitFiber D m).card*(a+b+l) :=
      sum_le_sum fun D _ ↦ hlocal D
    _ = (∑ D : C4Division (Fin n), ((c4SplitFiber D m).card : ℝ))*(a+b+l) := by
      rw [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcover (by positivity)

end InducedStars
