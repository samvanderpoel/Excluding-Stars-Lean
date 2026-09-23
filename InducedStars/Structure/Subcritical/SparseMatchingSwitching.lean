import InducedStars.Structure.Subcritical.SparseMatchingTransfer

/-!
# Marked isolated-matching switching on a fixed remainder

The inverse remembers which `q` edges were inserted.  Consequently each
output contributes at most `choose (b+q) q` preimages; the unmarked map is
not claimed to be injective.
-/

noncomputable section

namespace InducedStars

open DenseGraph

local instance sparseMatchingSwitchingEdgeSetFintype {V : Type*} [Fintype V]
    (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite _

/-- A graph with `b` edges has at least `n-2*b` isolated labeled vertices. -/
theorem exists_embedding_isolated_vertices {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (t : ℕ) (ht : t + 2 * G.edgeFinset.card ≤ Fintype.card V) :
    ∃ e : Fin t ↪ V, ∀ i y, ¬G.Adj (e i) y := by
  classical
  let A := matchingEndpoints G.edgeFinset
  have hA : A.card ≤ 2 * G.edgeFinset.card := by
    calc
      A.card ≤ ∑ e ∈ G.edgeFinset, e.toFinset.card := Finset.card_biUnion_le
      _ = ∑ _e ∈ G.edgeFinset, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        exact Sym2.card_toFinset_of_not_isDiag e (G.not_isDiag_of_mem_edgeFinset he)
      _ = 2 * G.edgeFinset.card := by simp [mul_comm]
  have hcomp : Fintype.card (Fin t) ≤ Aᶜ.card := by
    rw [Fintype.card_fin, Finset.card_compl]
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset hcomp
  refine ⟨e, fun i y hadj ↦ ?_⟩
  have hnot : e i ∉ A := Finset.mem_compl.mp (he ⟨i, rfl⟩)
  apply hnot
  exact (mem_matchingEndpoints _ _).mpr
    ⟨s(e i, y), SimpleGraph.mem_edgeFinset.mpr hadj, by simp⟩

/-- General isolated-matching switching.  The `t` available isolated labels
may be any fixed number guaranteed by the edge count.  Outputs carry the
marked inserted edge set, giving the exact binomial inverse bound. -/
theorem subcriticalSparseIsolatedMatchingSwitching {k s b q t : ℕ}
    (hk : 3 ≤ k) (ht : t + 2 * b ≤ s) (hq : 2 * q ≤ t) :
    labeledMatchingCoefficient t q * inducedStarFreeGraphCountWithEdges k s b ≤
      (b + q).choose q * inducedStarFreeGraphCountWithEdges k s (b + q) := by
  classical
  let F := inducedStarFreeGraphFinsetWithEdges k s b
  let F' := inducedStarFreeGraphFinsetWithEdges k s (b + q)
  let M := edgeMatchingFinset (Fin t) q
  have hex : ∀ G : F, ∃ e : Fin t ↪ Fin s, ∀ i y, ¬G.val.Adj (e i) y := by
    intro G
    apply exists_embedding_isolated_vertices
    simpa [(mem_inducedStarFreeGraphFinsetWithEdges.mp G.prop).2] using ht
  choose emb hemb using hex
  let added (G : F) (E : M) : SimpleGraph (Fin s) :=
    (sparseMatchingGraph E.val).map (emb G)
  have hiso : ∀ (G : F) (E : M) x y z, (added G E).Adj x y → ¬G.val.Adj x z := by
    intro G E x y z h
    obtain ⟨a, c, _, rfl, _⟩ := (SimpleGraph.map_adj (emb G) _ _ _).mp h
    exact hemb G a z
  have hcard : ∀ (G : F) (E : M), (added G E).edgeFinset.card = q := by
    intro G E
    obtain ⟨hm, hq⟩ := mem_edgeMatchingFinset.mp E.prop
    dsimp [added]
    rw [sparseMatching_map_edge_count, sparseMatchingGraph_edgeFinset E.val hm, hq]
  have hout : ∀ (G : F) (E : M), G.val ⊔ added G E ∈ F' := by
    intro G E
    obtain ⟨hfree, hb⟩ := mem_inducedStarFreeGraphFinsetWithEdges.mp G.prop
    obtain ⟨hm, _⟩ := mem_edgeMatchingFinset.mp E.prop
    apply mem_inducedStarFreeGraphFinsetWithEdges.mpr
    constructor
    · exact inducedStarFree_sup_isolated_matching (by omega) _ _ hfree
        (fun _ _ _ ↦ sparseMatchingGraph_map_neighbor_unique E.val hm (emb G))
        (hiso G E)
    · have hh := sparseMatching_sup_edge_count _ _ (hiso G E)
      have ha := hcard G E
      simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]
        at hh ha hb ⊢
      omega
  have hedges (H : SimpleGraph (Fin s)) : finiteGraphEdges H = H.edgeFinset := by
    ext z
    rw [mem_finiteGraphEdges, SimpleGraph.mem_edgeFinset]
  let Target := Σ G : F', ↑((finiteGraphEdges G.val).powersetCard q)
  let out : F × M → Target := by
    intro p
    refine ⟨⟨p.1.val ⊔ added p.1 p.2, hout p.1 p.2⟩,
      ⟨finiteGraphEdges (added p.1 p.2), ?_⟩⟩
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro e he
      rw [mem_finiteGraphEdges] at he ⊢
      exact (SimpleGraph.edgeSet_subset_edgeSet.mpr le_sup_right) he
    · rw [hedges]
      exact hcard p.1 p.2
  have hinj : Function.Injective out := by
    rintro ⟨G, E⟩ ⟨G', E'⟩ h
    have hgraph : G.val ⊔ added G E = G'.val ⊔ added G' E' :=
      congrArg (fun z : Target ↦ z.1.val) h
    have hmarked : finiteGraphEdges (added G E) = finiteGraphEdges (added G' E') :=
      congrArg (fun z : Target ↦ z.2.val) h
    rw [hedges, hedges] at hmarked
    have hadded : added G E = added G' E' := SimpleGraph.edgeFinset_inj.mp hmarked
    have hGval : G.val = G'.val := by
      calc
        G.val = (G.val ⊔ added G E).deleteEdges (added G E).edgeSet :=
          (sup_isolated_matching_deleteEdges _ _ (hiso G E)).symm
        _ = (G'.val ⊔ added G' E').deleteEdges (added G' E').edgeSet := by
          rw [hgraph, hadded]
        _ = G'.val := sup_isolated_matching_deleteEdges _ _ (hiso G' E')
    have hG : G = G' := Subtype.ext hGval
    subst G'
    have hsm : sparseMatchingGraph E.val = sparseMatchingGraph E'.val :=
      SimpleGraph.map_injective (emb G) hadded
    have hE : E = E' := by
      apply Subtype.ext
      have hh := congrArg (fun H : SimpleGraph (Fin t) ↦ H.edgeFinset) hsm
      simpa only [sparseMatchingGraph_edgeFinset E.val (mem_edgeMatchingFinset.mp E.prop).1,
        sparseMatchingGraph_edgeFinset E'.val (mem_edgeMatchingFinset.mp E'.prop).1] using hh
    subst E'
    rfl
  have hcount : F.card * M.card ≤ F'.card * (b + q).choose q := by
    have hh := Fintype.card_le_of_injective out hinj
    have htarget : Fintype.card Target = F'.card * (b + q).choose q := by
      rw [Fintype.card_sigma]
      have hfiber : ∀ G : F', Fintype.card ↑((finiteGraphEdges G.val).powersetCard q) =
          (b + q).choose q := by
        intro G
        rw [Fintype.card_coe, Finset.card_powersetCard, hedges]
        have hh := (mem_inducedStarFreeGraphFinsetWithEdges.mp G.prop).2
        simp only [SimpleGraph.edgeFinset, Set.toFinset_card, Set.fintypeCard_eq_ncard]
          at hh ⊢
        rw [hh]
      simp_rw [hfiber]
      simp
    simpa only [Fintype.card_prod, Fintype.card_coe, htarget] using hh
  have hmatching : labeledMatchingCoefficient t q ≤ M.card := by
    simpa [M] using labeledMatchingCoefficient_le_card (V := Fin t) q (by simpa using hq)
  calc
    _ ≤ M.card * F.card := Nat.mul_le_mul_right _ hmatching
    _ = F.card * M.card := Nat.mul_comm _ _
    _ ≤ F'.card * (b + q).choose q := hcount
    _ = _ := Nat.mul_comm _ _

/-- The source's low-edge-count switching range: at most `q` old edges and
at least `4*q` remainder vertices.  The same labels are retained. -/
theorem subcriticalSparseMatchingSwitching {k s b q : ℕ}
    (hk : 3 ≤ k) (hb : b ≤ q) (hs : 4 * q ≤ s) :
    labeledMatchingCoefficient (s - 2 * q) q *
      inducedStarFreeGraphCountWithEdges k s b ≤
        (b + q).choose q * inducedStarFreeGraphCountWithEdges k s (b + q) :=
  subcriticalSparseIsolatedMatchingSwitching hk (by omega) (by omega)

end InducedStars
