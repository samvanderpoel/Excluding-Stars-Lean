import InducedStars.C4.MatchingExtraction

/-!
# Linear companion matchings outside a small defect graph

Paper: Lemma `lemma:c4-matching`. The dense-graph matching estimate is
proved from the endpoints of a maximum matching, not taken from the
unpublished appendix cited by the paper.
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem c4Within_complement_edgeCount_add (G : SimpleGraph V) (S : Finset V) :
    (finiteGraphEdges (c4WithinGraph Gᶜ S)).card +
      (finiteGraphEdges (c4WithinGraph G S)).card = S.card.choose 2 := by
  rw [card_finiteGraphEdges_c4WithinGraph, card_finiteGraphEdges_c4WithinGraph]
  have hind : Gᶜ.induce (S : Set V) = (G.induce (S : Set V))ᶜ := by
    ext x y
    simp only [SimpleGraph.induce_adj, SimpleGraph.compl_adj,
      Subtype.val_injective.ne_iff]
  rw [hind]
  let H := G.induce (S : Set V)
  change (finiteGraphEdges Hᶜ).card + (finiteGraphEdges H).card = _
  have hdis : Disjoint (finiteGraphEdges Hᶜ) (finiteGraphEdges H) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    induction e using Sym2.inductionOn with
    | _ x y =>
      exact ((mem_finiteGraphEdges _ _).mp he).2 ((mem_finiteGraphEdges _ _).mp hf)
  have heq : finiteGraphEdges Hᶜ ∪ finiteGraphEdges H =
      finiteGraphEdges (⊤ : SimpleGraph ↥S) := by
    ext e
    induction e using Sym2.inductionOn with
    | _ x y =>
      simp only [Finset.mem_union, mem_finiteGraphEdges, SimpleGraph.mem_edgeSet,
        SimpleGraph.compl_adj, SimpleGraph.top_adj]
      exact ⟨fun h ↦ h.elim And.left SimpleGraph.Adj.ne, fun h ↦ by
        by_cases ha : H.Adj x y
        · exact Or.inr ha
        · exact Or.inl ⟨h, ha⟩⟩
  rw [← Finset.card_union_of_disjoint hdis, heq]
  have hedge : finiteGraphEdges (⊤ : SimpleGraph ↥S) = (⊤ : SimpleGraph ↥S).edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [hedge, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
  simp

theorem c4Within_edgeCount_le (G : SimpleGraph V) (S : Finset V) :
    (finiteGraphEdges (c4WithinGraph G S)).card ≤ (finiteGraphEdges G).card := by
  rw [finiteGraphEdges_c4WithinGraph]
  exact Finset.card_filter_le _ _

/-- A side of size at least `beta*n`, with at most `beta²*n²/8`
defects in the entire graph, contains a complementary matching of size
at least `beta²*n/16`. All finite thresholds are explicit. -/
theorem c4Within_complement_matchingNumber_ge {n : ℕ} (T : SimpleGraph (Fin n))
    (S : Finset (Fin n)) {beta : ℝ} (hbeta : 0 < beta)
    (hn : 4 ≤ beta * n) (hsize : beta * n ≤ (S.card : ℝ))
    (hsmall : ((finiteGraphEdges T).card : ℝ) ≤ beta ^ 2 * (n : ℝ) ^ 2 / 8) :
    beta ^ 2 * n / 16 ≤ DenseGraph.matchingNumber (c4WithinGraph Tᶜ S) := by
  have hnpos : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg n)
    norm_num [hz] at hn
  have hs : (2 : ℝ) ≤ S.card := by linarith
  have hchoose : beta ^ 2 * (n : ℝ) ^ 2 / 4 ≤ (S.card.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    have hsq := sq_le_sq₀ (by positivity : 0 ≤ beta * (n : ℝ)) (by positivity) |>.mpr hsize
    nlinarith
  have hsum := c4Within_complement_edgeCount_add T S
  have hsumR : ((finiteGraphEdges (c4WithinGraph Tᶜ S)).card : ℝ) +
      (finiteGraphEdges (c4WithinGraph T S)).card = (S.card.choose 2 : ℝ) := by
    exact_mod_cast hsum
  have hdef : ((finiteGraphEdges (c4WithinGraph T S)).card : ℝ) ≤
      beta ^ 2 * (n : ℝ) ^ 2 / 8 :=
    (Nat.cast_le.mpr (c4Within_edgeCount_le T S)).trans hsmall
  let H := c4WithinGraph Tᶜ S
  have hdeg (v : Fin n) : (H.degree v : ℝ) ≤ 1 * Fintype.card (Fin n) := by
    simpa using (Nat.cast_le.mpr (H.degree_lt_card_verts v).le :
      (H.degree v : ℝ) ≤ (Fintype.card (Fin n) : ℝ))
  have hbound := DenseGraph.edgeFinset_card_le_matching_degree H hdeg
  change (H.edgeFinset.card : ℝ) ≤ _ at hbound
  have heq : (H.edgeFinset.card : ℝ) = (finiteGraphEdges H).card := by
    congr 2
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  rw [heq] at hbound
  simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, one_mul] at hbound
  change ((finiteGraphEdges (c4WithinGraph Tᶜ S)).card : ℝ) ≤ _ at hbound
  apply (le_of_mul_le_mul_right ?_ hnpos)
  nlinarith

/-- Monotonicity of the actual maximum matching number under edge inclusion. -/
theorem c4MatchingNumber_mono {G H : SimpleGraph V} (hGH : G ≤ H) :
    DenseGraph.matchingNumber G ≤ DenseGraph.matchingNumber H := by
  have h := DenseGraph.matching_card_le_matchingNumber
    ((DenseGraph.canonicalMaximumMatching_isMatching G).map_ofLE hGH)
  have hset : ((DenseGraph.canonicalMaximumMatching G).map (SimpleGraph.Hom.ofLE hGH)).edgeSet =
      (DenseGraph.canonicalMaximumMatching G).edgeSet := by
    rw [SimpleGraph.Subgraph.edgeSet_map]
    change Sym2.map id '' (DenseGraph.canonicalMaximumMatching G).edgeSet = _
    rw [Sym2.map_id, Set.image_id]
  rw [hset] at h
  exact h

/-- The maximum-matching cover argument with the actual side size, rather
than the ambient order. This is needed when the side is a small neighborhood. -/
theorem c4Within_edgeCount_le_matchingNumber_mul_card (G : SimpleGraph V) (S : Finset V) :
    ((finiteGraphEdges (c4WithinGraph G S)).card : ℝ) ≤
      2 * DenseGraph.matchingNumber (c4WithinGraph G S) * S.card := by
  let H := c4WithinGraph G S
  have hdeg (v : V) : H.degree v ≤ S.card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro x hx
    exact ((SimpleGraph.mem_neighborFinset H v x).mp hx).2.1
  have hedge : finiteGraphEdges H = H.edgeFinset := by
    ext e
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  change ((finiteGraphEdges H).card : ℝ) ≤ _
  rw [hedge]
  calc
    (H.edgeFinset.card : ℝ) ≤ ((DenseGraph.matchingCoverNeighborhoodCode H).card : ℝ) := by
      exact_mod_cast DenseGraph.edgeFinset_card_le_matchingCoverNeighborhoodCode H
    _ = ∑ v ∈ DenseGraph.canonicalMatchingCover H, (H.degree v : ℝ) := by
      rw [DenseGraph.card_matchingCoverNeighborhoodCode, Nat.cast_sum]
    _ ≤ ∑ _v ∈ DenseGraph.canonicalMatchingCover H, (S.card : ℝ) :=
      Finset.sum_le_sum (fun v _ ↦ Nat.cast_le.mpr (hdeg v))
    _ = _ := by simp [DenseGraph.card_canonicalMatchingCover, Nat.cast_mul, H]

theorem c4Within_matchingNumber_ge_of_dense (G : SimpleGraph V) (S : Finset V)
    (hS : 0 < S.card)
    (hdense : (S.card : ℝ) ^ 2 / 4 ≤ (finiteGraphEdges (G.induce (S : Set V))).card) :
    (S.card : ℝ) / 8 ≤ DenseGraph.matchingNumber (c4WithinGraph G S) := by
  have hbound := c4Within_edgeCount_le_matchingNumber_mul_card G S
  rw [card_finiteGraphEdges_c4WithinGraph] at hbound
  have hSR : (0 : ℝ) < S.card := by exact_mod_cast hS
  apply (le_of_mul_le_mul_right ?_ hSR)
  nlinarith

end InducedStars
