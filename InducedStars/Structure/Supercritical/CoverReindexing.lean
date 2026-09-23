import InducedStars.Structure.Supercritical.CoverMultiplicity

/-!
# Reindexing prescribed supercritical covers

The labels on the main parts of a supercritical division are auxiliary.  This
file records the corresponding invariance interfaces for part sizes, clique
covers, exact co-multipartite fibers, fullness, and profile multiplicities.
-/

noncomputable section

open Finset Set

namespace InducedStars

namespace SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Reindexing permutes the part-cardinality vector. -/
@[simp] theorem card_reindexParts_part
    (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) (i : Fin (k - 1)) :
    ((D.reindexParts sigma).parts i).card =
      (D.parts (sigma.symm i)).card := by
  rfl

/-- Forward-indexed form of `card_reindexParts_part`. -/
@[simp] theorem card_reindexParts_part_apply
    (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) (i : Fin (k - 1)) :
    ((D.reindexParts sigma).parts (sigma i)).card =
      (D.parts i).card := by
  simp

/-- Relabeling the parts preserves the assertion that they are cliques in a
fixed ambient graph. -/
theorem isCliqueCover_reindexParts_iff
    (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) (G : SimpleGraph V) :
    (∀ i, G.IsClique ((D.reindexParts sigma).parts i : Set V)) ↔
      ∀ i, G.IsClique (D.parts i : Set V) := by
  constructor
  · intro h i
    simpa using h (sigma i)
  · intro h i
    simpa using h (sigma.symm i)

/-- Named preservation wrapper for the existing fullness reindexing theorem. -/
theorem reindexParts_isFull_iff
    (D : SupercriticalDivision k V)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    (D.reindexParts sigma).IsFull ↔ D.IsFull :=
  D.isFull_reindexParts sigma

end SupercriticalDivision

/-- Named transport wrapper for exact profile multiplicity. -/
theorem supercriticalProfileMultiplicity_reindexParts_eq
    {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    {D : SupercriticalDivision k V}
    (p : SupercriticalEdgeProfile D)
    (sigma : Equiv.Perm (Fin (k - 1))) :
    supercriticalProfileMultiplicity (p.reindexParts sigma) =
      supercriticalProfileMultiplicity p :=
  supercriticalProfileMultiplicity_reindexParts p sigma

/-! ## A label-free characterization of a prescribed fiber -/

/-- Membership in a prescribed full-division fiber depends only on the
underlying (unlabeled) clique partition and the exact edge count. -/
theorem mem_supercriticalCoPartiteFiber_iff_isFull_card_isClique
    {k n m : ℕ} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCoPartiteFiber D m ↔
      D.IsFull ∧ (finiteGraphEdges G).card = m ∧
        ∀ i, G.IsClique (D.parts i : Set (Fin n)) := by
  classical
  constructor
  · intro hG
    exact ⟨(mem_supercriticalCoPartiteFiber.mp hG).1,
      card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber hG,
      fun i ↦ supercriticalCoPartiteFiber_isClique hG i⟩
  · rintro ⟨hfull, hcard, hclique⟩
    let A : Finset (SupercriticalTaggedCrossChoice k (Fin n)) :=
      (supercriticalTaggedCrossChoiceUniverse D).filter fun z ↦
        G.Adj z.2.1 z.2.2
    have hA : A ⊆ supercriticalTaggedCrossChoiceUniverse D := by
      intro z hz
      exact (Finset.mem_filter.mp hz).1
    have hinternal :
        supercriticalInternalEdgeFinset D ⊆ finiteGraphEdges G := by
      intro e he
      induction e using Sym2.inductionOn with
      | _ x y =>
          rw [mk_mem_supercriticalInternalEdgeFinset] at he
          rw [mk_mem_finiteGraphEdges]
          obtain ⟨hne, i, hxi, hyi⟩ := he
          exact hclique i hxi hyi hne
    have hcapacity : divisionInternalCliqueCapacity D ≤ m := by
      rw [← card_supercriticalInternalEdgeFinset D, ← hcard]
      exact Finset.card_le_card hinternal
    have hgraph : supercriticalGraphOfCrossChoice D A = G := by
      ext x y
      constructor
      · intro hxy
        rw [supercriticalGraphOfCrossChoice,
          DenseGraph.completeWithinParts_adj] at hxy
        rcases hxy with hselected | ⟨hne, i, hxi, hyi⟩
        · rw [supercriticalSelectedCrossGraph,
            SimpleGraph.fromEdgeSet_adj] at hselected
          obtain ⟨z, hzA, hzedge⟩ :=
            Finset.mem_image.mp hselected.1
          have hzG : G.Adj z.2.1 z.2.2 :=
            (Finset.mem_filter.mp hzA).2
          rcases Sym2.eq_iff.mp hzedge with h | h
          · simpa [h.1, h.2] using hzG
          · simpa [h.1, h.2] using hzG.symm
        · exact hclique i hxi hyi hne
      · intro hxy
        have hxSupport : x ∈ D.support := by
          rw [D.support_eq_univ hfull]
          simp
        have hySupport : y ∈ D.support := by
          rw [D.support_eq_univ hfull]
          simp
        obtain ⟨i, hxi⟩ := SupercriticalDivision.mem_support.mp hxSupport
        obtain ⟨j, hyj⟩ := SupercriticalDivision.mem_support.mp hySupport
        rw [supercriticalGraphOfCrossChoice,
          DenseGraph.completeWithinParts_adj]
        by_cases hij : i = j
        · subst j
          exact Or.inr ⟨G.ne_of_adj hxy, i, hxi, hyj⟩
        · left
          have hcross : s(x, y) ∈ supercriticalCrossEdgeFinset D :=
            (mk_mem_supercriticalCrossEdgeFinset D x y).2
              ⟨i, j, hij, hxi, hyj⟩
          rw [supercriticalCrossEdgeFinset, Finset.mem_image] at hcross
          obtain ⟨z, hzU, hzedge⟩ := hcross
          have hzG : G.Adj z.2.1 z.2.2 := by
            rcases Sym2.eq_iff.mp hzedge with h | h
            · simpa [h.1, h.2] using hxy
            · simpa [h.1, h.2] using hxy.symm
          have hzA : z ∈ A := by
            exact Finset.mem_filter.mpr ⟨hzU, hzG⟩
          have hzSelected :
              (supercriticalSelectedCrossGraph A).Adj z.2.1 z.2.2 :=
            (supercriticalSelectedCrossGraph_adj_iff D hA hzU).2 hzA
          rcases Sym2.eq_iff.mp hzedge with h | h
          · simpa [h.1, h.2] using hzSelected
          · simpa [h.1, h.2] using hzSelected.symm
    have hAcard : A.card = m - divisionInternalCliqueCapacity D := by
      have hedge := card_finiteGraphEdges_supercriticalGraphOfCrossChoice D hA
      rw [hgraph, hcard] at hedge
      omega
    exact mem_supercriticalCoPartiteFiber.mpr
      ⟨hfull, hcapacity, A, hA, hAcard, hgraph⟩

/-- Relabeling the parts of a division leaves its exact co-multipartite graph
fiber unchanged. -/
@[simp] theorem supercriticalCoPartiteFiber_reindexParts
    {k n : ℕ} (D : SupercriticalDivision k (Fin n))
    (sigma : Equiv.Perm (Fin (k - 1))) (m : ℕ) :
    supercriticalCoPartiteFiber (D.reindexParts sigma) m =
      supercriticalCoPartiteFiber D m := by
  classical
  ext G
  rw [mem_supercriticalCoPartiteFiber_iff_isFull_card_isClique,
    mem_supercriticalCoPartiteFiber_iff_isFull_card_isClique]
  constructor
  · rintro ⟨hfull, hcard, hclique⟩
    exact ⟨(D.isFull_reindexParts sigma).mp hfull, hcard,
      (D.isCliqueCover_reindexParts_iff sigma G).mp hclique⟩
  · rintro ⟨hfull, hcard, hclique⟩
    exact ⟨(D.isFull_reindexParts sigma).mpr hfull, hcard,
      (D.isCliqueCover_reindexParts_iff sigma G).mpr hclique⟩

end InducedStars
