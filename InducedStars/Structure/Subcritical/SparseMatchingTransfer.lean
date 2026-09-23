import InducedStars.Structure.Subcritical.SparseMatchingGeometry

/-!
# Exact labeled sparse matching transfers

Paper: Lemma `lemma:sub-sparse-matching-transfer-K1k` and the isolated-matching
switching in the proof of `lemma:sub-Wstar-sparse-lower-tail-K1k`.

The first transfer uses new fixed labels and is injective without marking.
The second retains a marked inserted edge set, accounting for the binomial
inverse multiplicity explicitly.
-/

noncomputable section

namespace InducedStars

open DenseGraph

local instance sparseMatchingTransferEdgeSetFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite _

private theorem map_not_adj_of_disjoint {V W U : Type*}
    (e : V ↪ U) (f : W ↪ U) (hsep : ∀ v w, e v ≠ f w)
    (H : SimpleGraph W) (v : V) (u : U) : ¬(H.map f).Adj (e v) u := by
  rintro h
  obtain ⟨a, b, _, ha, _⟩ := (SimpleGraph.map_adj f H _ _).mp h
  exact hsep v a ha.symm

private theorem disjoint_map_sup_injective {V W U : Type*}
    (e : V ↪ U) (f : W ↪ U) (hsep : ∀ v w, e v ≠ f w) :
    Function.Injective (fun p : SimpleGraph V × SimpleGraph W ↦ p.1.map e ⊔ p.2.map f) := by
  rintro ⟨G, H⟩ ⟨G', H'⟩ h
  apply Prod.ext
  · ext a b
    have hh := congrArg (fun K : SimpleGraph U ↦ K.Adj (e a) (e b)) h
    simpa only [SimpleGraph.sup_adj, SimpleGraph.map_adj_apply,
      map_not_adj_of_disjoint e f hsep H a (e b),
      map_not_adj_of_disjoint e f hsep H' a (e b), or_false] using Eq.to_iff hh
  · ext a b
    have hh := congrArg (fun K : SimpleGraph U ↦ K.Adj (f a) (f b)) h
    simpa only [SimpleGraph.sup_adj, SimpleGraph.map_adj_apply,
      map_not_adj_of_disjoint f e (fun w v h ↦ hsep v w h.symm) G a (f b),
      map_not_adj_of_disjoint f e (fun w v h ↦ hsep v w h.symm) G' a (f b), false_or] using Eq.to_iff hh

theorem sparseMatching_sup_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G M : SimpleGraph V) (hiso : ∀ x y z, M.Adj x y → ¬G.Adj x z) :
    (G ⊔ M).edgeFinset.card = G.edgeFinset.card + M.edgeFinset.card := by
  classical
  rw [SimpleGraph.edgeFinset_sup, Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro e he hM
  induction e using Sym2.ind with
  | _ x y =>
    exact hiso x y y (SimpleGraph.mem_edgeFinset.mp hM) (SimpleGraph.mem_edgeFinset.mp he)

/-- Edge-count preservation under an injective labeled map, with the local
finite-edge instances normalized away. -/
theorem sparseMatching_map_edge_count {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (e : V ↪ W) (G : SimpleGraph V) :
    (G.map e).edgeFinset.card = G.edgeFinset.card := by
  classical
  have h := SimpleGraph.card_edgeFinset_map e G
  simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard] at h ⊢
  exact h

/-- Adding a labeled `q`-edge matching on a fixed set of `2*q` new vertices
gives the exact source matching-transfer inequality.  Any additional vertices
are isolated.  Paper: Lemma `lemma:sub-sparse-matching-transfer-K1k`. -/
theorem subcriticalSparseMatchingTransfer {k s s' b q : ℕ} (hk : 3 ≤ k)
    (hs : s + 2 * q ≤ s') :
    ((2 * q).factorial / (2 ^ q * q.factorial)) *
      inducedStarFreeGraphCountWithEdges k s b ≤
        inducedStarFreeGraphCountWithEdges k s' (b + q) := by
  classical
  let e : Fin s ↪ Fin s' := Fin.castLEEmb (by omega)
  let f : Fin (2 * q) ↪ Fin s' := {
    toFun := fun i ↦ ⟨s + i.val, by omega⟩
    inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; simpa using this }
  have hsep : ∀ i j, e i ≠ f j := by
    intro i j h
    have hh := congrArg Fin.val h
    change i.val = s + j.val at hh
    omega
  let F := inducedStarFreeGraphFinsetWithEdges k s b
  let M := edgeMatchingFinset (Fin (2 * q)) q
  let out : SimpleGraph (Fin s) × Finset (Sym2 (Fin (2 * q))) → SimpleGraph (Fin s') :=
    fun p ↦ p.1.map e ⊔ (sparseMatchingGraph p.2).map f
  have hout : ∀ p ∈ F ×ˢ M,
      out p ∈ inducedStarFreeGraphFinsetWithEdges k s' (b + q) := by
    rintro ⟨G, E⟩ hp
    obtain ⟨hG, hE⟩ := Finset.mem_product.mp hp
    obtain ⟨hfree, hcard⟩ := mem_inducedStarFreeGraphFinsetWithEdges.mp hG
    obtain ⟨hmatch, hEq⟩ := mem_edgeMatchingFinset.mp hE
    have hiso : ∀ x y z, ((sparseMatchingGraph E).map f).Adj x y →
        ¬(G.map e).Adj x z := by
      intro x y z h
      obtain ⟨a, c, _, rfl, _⟩ := (SimpleGraph.map_adj f _ _ _).mp h
      exact map_not_adj_of_disjoint f e (fun w v hh ↦ hsep v w hh.symm) G a z
    apply mem_inducedStarFreeGraphFinsetWithEdges.mpr
    constructor
    · exact inducedStarFree_sup_isolated_matching (by omega) _ _
        (inducedStarFree_map (by omega) G e hfree)
        (fun _ _ _ ↦ sparseMatchingGraph_map_neighbor_unique E hmatch f) hiso
    · have hh : (G.map e ⊔ (sparseMatchingGraph E).map f).edgeFinset.card = b + q := by
        rw [sparseMatching_sup_edge_count _ _ hiso,
        sparseMatching_map_edge_count, sparseMatching_map_edge_count,
        sparseMatchingGraph_edgeFinset E hmatch, hcard, hEq]
      simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard,
        out] using hh
  have hinj : (↑(F ×ˢ M) : Set _).InjOn out := by
    rintro ⟨G, E⟩ hp ⟨G', E'⟩ hp' h
    have hh := disjoint_map_sup_injective e f hsep
      (a₁ := (G, sparseMatchingGraph E)) (a₂ := (G', sparseMatchingGraph E')) h
    have hgraphs : sparseMatchingGraph E = sparseMatchingGraph E' := congrArg Prod.snd hh
    have hE := (mem_edgeMatchingFinset.mp (Finset.mem_product.mp hp).2).1
    have hE' := (mem_edgeMatchingFinset.mp (Finset.mem_product.mp hp').2).1
    refine Prod.ext ?_ ?_
    · exact congrArg (fun p : SimpleGraph (Fin s) × SimpleGraph (Fin (2 * q)) ↦ p.1) hh
    · have hsets := congrArg (fun H : SimpleGraph (Fin (2 * q)) ↦ H.edgeFinset) hgraphs
      simpa only [sparseMatchingGraph_edgeFinset E hE,
        sparseMatchingGraph_edgeFinset E' hE'] using hsets
  have hcount := Finset.card_le_card_of_injOn out hout hinj
  have hmatching : (2 * q).factorial / (2 ^ q * q.factorial) ≤ M.card := by
    simpa [labeledMatchingCoefficient, M] using
      (labeledMatchingCoefficient_le_card (V := Fin (2 * q)) q (by simp))
  calc
    _ ≤ M.card * F.card := Nat.mul_le_mul_right _ hmatching
    _ = (F ×ˢ M).card := by simp [Finset.card_product, mul_comm]
    _ ≤ _ := hcount

end InducedStars
