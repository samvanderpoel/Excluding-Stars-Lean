import InducedStars.FiniteModels.CoMultipartiteStar
import InducedStars.FiniteModels.Uniform
import InducedStars.Structure.Supercritical.JointAbsorption

/-!
# Exact finite co-multipartite families

This file fixes the labeled finite sample spaces used by the final
supercritical aggregation.  All graphs have vertex set `Fin n`; no quotient
by graph isomorphism is taken.
-/

noncomputable section

namespace InducedStars

open DenseGraph

noncomputable local instance coPartiteFamiliesGraphDecidableEq (n : ℕ) :
    DecidableEq (SimpleGraph (Fin n)) :=
  Classical.decEq _

noncomputable local instance coPartiteFamiliesEdgeSetFintype
    {n : ℕ} (G : SimpleGraph (Fin n)) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-! ## The global exact-edge family -/

/-- Labeled co-`r`-partite graphs on `Fin n` with exactly `m` edges. -/
noncomputable def coMultipartiteGraphFinsetWithEdges
    (r n m : ℕ) : Finset (SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter fun G ↦
    IsCoMultipartite G r ∧ G.edgeFinset.card = m

@[simp] theorem mem_coMultipartiteGraphFinsetWithEdges
    {r n m : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ coMultipartiteGraphFinsetWithEdges r n m ↔
      IsCoMultipartite G r ∧ G.edgeFinset.card = m := by
  classical
  simp [coMultipartiteGraphFinsetWithEdges]

/-- The number of labeled co-`r`-partite graphs with exactly `m` edges. -/
noncomputable def coMultipartiteGraphCountWithEdges
    (r n m : ℕ) : ℕ :=
  (coMultipartiteGraphFinsetWithEdges r n m).card

@[simp] theorem coMultipartiteGraphCountWithEdges_eq_card
    (r n m : ℕ) :
    coMultipartiteGraphCountWithEdges r n m =
      (coMultipartiteGraphFinsetWithEdges r n m).card :=
  rfl

/-- Every exact-edge co-`(k-1)`-partite graph belongs to the corresponding
induced-star-free exact-edge family. -/
theorem coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree
    {k n m : ℕ} (hk : 1 ≤ k) :
    coMultipartiteGraphFinsetWithEdges (k - 1) n m ⊆
      inducedStarFreeGraphFinsetWithEdges k n m := by
  intro G hG
  rw [mem_coMultipartiteGraphFinsetWithEdges] at hG
  rw [mem_inducedStarFreeGraphFinsetWithEdges]
  exact ⟨coMultipartite_not_inducedEmbeds_inducedStar hk hG.1, hG.2⟩

/-! ## Good and exceptional supercritical families -/

/-- The good exact-edge family in the supercritical theorem. -/
noncomputable def supercriticalCoMultipartiteGraphFinset
    (k n m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  coMultipartiteGraphFinsetWithEdges (k - 1) n m

/-- Induced-star-free exact-edge graphs which are not co-`(k-1)`-partite. -/
noncomputable def supercriticalNonCoMultipartiteGraphFinset
    (k n m : ℕ) : Finset (SimpleGraph (Fin n)) :=
  inducedStarFreeGraphFinsetWithEdges k n m \
    supercriticalCoMultipartiteGraphFinset k n m

@[simp] theorem mem_supercriticalCoMultipartiteGraphFinset
    {k n m : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCoMultipartiteGraphFinset k n m ↔
      IsCoMultipartite G (k - 1) ∧ G.edgeFinset.card = m := by
  exact mem_coMultipartiteGraphFinsetWithEdges

@[simp] theorem mem_supercriticalNonCoMultipartiteGraphFinset
    {k n m : ℕ} {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalNonCoMultipartiteGraphFinset k n m ↔
      G ∈ inducedStarFreeGraphFinsetWithEdges k n m ∧
        ¬ IsCoMultipartite G (k - 1) := by
  classical
  rw [supercriticalNonCoMultipartiteGraphFinset, Finset.mem_sdiff,
    mem_supercriticalCoMultipartiteGraphFinset]
  constructor
  · rintro ⟨hfree, hnotgood⟩
    refine ⟨hfree, fun hco ↦ hnotgood ⟨hco, ?_⟩⟩
    exact (mem_inducedStarFreeGraphFinsetWithEdges.mp hfree).2
  · rintro ⟨hfree, hnotco⟩
    exact ⟨hfree, fun hgood ↦ hnotco hgood.1⟩

theorem supercriticalCoMultipartiteGraphFinset_subset
    {k n m : ℕ} (hk : 1 ≤ k) :
    supercriticalCoMultipartiteGraphFinset k n m ⊆
      inducedStarFreeGraphFinsetWithEdges k n m :=
  coMultipartiteGraphFinsetWithEdges_subset_inducedStarFree hk

/-- Exact good/bad cardinal decomposition of the induced-star-free family. -/
theorem inducedStarFreeGraphCountWithEdges_eq_coMultipartite_add_nonCoMultipartite
    {k n m : ℕ} (hk : 1 ≤ k) :
    inducedStarFreeGraphCountWithEdges k n m =
      coMultipartiteGraphCountWithEdges (k - 1) n m +
        (supercriticalNonCoMultipartiteGraphFinset k n m).card := by
  have hsub := supercriticalCoMultipartiteGraphFinset_subset
    (k := k) (n := n) (m := m) hk
  change (inducedStarFreeGraphFinsetWithEdges k n m).card =
    (supercriticalCoMultipartiteGraphFinset k n m).card +
      (inducedStarFreeGraphFinsetWithEdges k n m \
        supercriticalCoMultipartiteGraphFinset k n m).card
  simpa [Nat.add_comm] using
    (Finset.card_sdiff_add_card_eq_card hsub).symm

/-- Uniform proportion of good co-multipartite graphs inside the exact-edge
induced-star-free family. -/
noncomputable def supercriticalCoMultipartiteProbability
    (k n m : ℕ) : ℝ :=
  uniformSubfamilyProbability
    (inducedStarFreeGraphFinsetWithEdges k n m)
    (supercriticalCoMultipartiteGraphFinset k n m)

/-- Uniform proportion of exceptional non-co-multipartite graphs inside the
exact-edge induced-star-free family. -/
noncomputable def supercriticalNonCoMultipartiteProbability
    (k n m : ℕ) : ℝ :=
  uniformSubfamilyProbability
    (inducedStarFreeGraphFinsetWithEdges k n m)
    (supercriticalNonCoMultipartiteGraphFinset k n m)

theorem supercriticalCoMultipartiteProbability_add_nonCoMultipartiteProbability
    {k n m : ℕ} (hk : 1 ≤ k)
    (hne : (inducedStarFreeGraphFinsetWithEdges k n m).Nonempty) :
    supercriticalCoMultipartiteProbability k n m +
        supercriticalNonCoMultipartiteProbability k n m = 1 := by
  unfold supercriticalCoMultipartiteProbability
    supercriticalNonCoMultipartiteProbability uniformSubfamilyProbability
  have hcard := inducedStarFreeGraphCountWithEdges_eq_coMultipartite_add_nonCoMultipartite
    (k := k) (n := n) (m := m) hk
  have hpos : (0 : ℝ) <
      (inducedStarFreeGraphFinsetWithEdges k n m).card := by
    exact_mod_cast Finset.card_pos.mpr hne
  rw [show (supercriticalCoMultipartiteGraphFinset k n m).card =
      coMultipartiteGraphCountWithEdges (k - 1) n m from rfl]
  change ((coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) /
      (inducedStarFreeGraphCountWithEdges k n m : ℝ)) +
      (((supercriticalNonCoMultipartiteGraphFinset k n m).card : ℝ) /
        (inducedStarFreeGraphCountWithEdges k n m : ℝ)) = 1
  rw [← add_div]
  have hcardReal :
      (inducedStarFreeGraphCountWithEdges k n m : ℝ) =
        (coMultipartiteGraphCountWithEdges (k - 1) n m : ℝ) +
          ((supercriticalNonCoMultipartiteGraphFinset k n m).card : ℝ) := by
    exact_mod_cast hcard
  rw [← hcardReal]
  exact div_self (ne_of_gt hpos)

/-! ## Full divisions and their exact fibers -/

namespace SupercriticalDivision

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- A division is full when it has no sparse vertices. -/
def IsFull (D : SupercriticalDivision k V) : Prop :=
  D.sparse = ∅

instance (D : SupercriticalDivision k V) : Decidable D.IsFull :=
  Classical.propDecidable _

theorem isFull_iff_support_eq_univ (D : SupercriticalDivision k V) :
    D.IsFull ↔ D.support = Finset.univ := by
  constructor
  · intro h
    calc
      D.support = D.support ∪ D.sparse := by simp [IsFull] at h; simp [h]
      _ = Finset.univ := D.support_union_sparse
  · intro h
    simp [IsFull, SupercriticalDivision.sparse, h]

theorem support_eq_univ (D : SupercriticalDivision k V) (hD : D.IsFull) :
    D.support = Finset.univ :=
  (D.isFull_iff_support_eq_univ).mp hD

theorem parts_cover (D : SupercriticalDivision k V) (hD : D.IsFull) :
    Finset.univ.biUnion D.parts = (Finset.univ : Finset V) := by
  simpa [SupercriticalDivision.support] using D.support_eq_univ hD

/-- A full division whose parts are cliques is an explicit co-multipartite
cover. -/
theorem isCoMultipartite_of_isFull_of_isClique
    (D : SupercriticalDivision k V) (G : SimpleGraph V)
    (hD : D.IsFull) (hclique : ∀ i, G.IsClique (D.parts i : Set V)) :
    DenseGraph.IsCoMultipartite G (k - 1) :=
  ⟨{
    parts := D.parts
    cover := D.parts_cover hD
    pairwiseDisjoint := D.parts_pairwiseDisjoint
    isClique := hclique
  }⟩

@[simp] theorem absorbSparse_isFull (hk : 3 ≤ k)
    (D : SupercriticalDivision k V) :
    (supercriticalAbsorbSparseDivision hk D).IsFull := by
  exact supercriticalAbsorbSparseDivision_sparse hk D

end SupercriticalDivision

/-- Exact `m`-edge graphs obtained by completing every part of a prescribed
full division and choosing all remaining cross edges freely.  The family is
empty when the division is not full or its forced clique edges already exceed
`m`. -/
noncomputable def supercriticalCoPartiteFiber
    {k n : ℕ} (D : SupercriticalDivision k (Fin n)) (m : ℕ) :
    Finset (SimpleGraph (Fin n)) := by
  classical
  exact if D.IsFull then
    if divisionInternalCliqueCapacity D ≤ m then
      ((supercriticalTaggedCrossChoiceUniverse D).powersetCard
        (m - divisionInternalCliqueCapacity D)).image
          (supercriticalGraphOfCrossChoice D)
    else ∅
  else ∅

@[simp] theorem mem_supercriticalCoPartiteFiber
    {k n m : ℕ} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)} :
    G ∈ supercriticalCoPartiteFiber D m ↔
      D.IsFull ∧ divisionInternalCliqueCapacity D ≤ m ∧
        ∃ A : Finset (SupercriticalTaggedCrossChoice k (Fin n)),
          A ⊆ supercriticalTaggedCrossChoiceUniverse D ∧
          A.card = m - divisionInternalCliqueCapacity D ∧
          supercriticalGraphOfCrossChoice D A = G := by
  classical
  by_cases hfull : D.IsFull
  · by_cases hcapacity : divisionInternalCliqueCapacity D ≤ m
    · simp [supercriticalCoPartiteFiber, hfull, hcapacity,
        Finset.mem_powersetCard, and_assoc]
    · simp [supercriticalCoPartiteFiber, hfull, hcapacity]
  · simp [supercriticalCoPartiteFiber, hfull]

theorem supercriticalCoPartiteFiber_isClique
    {k n m : ℕ} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCoPartiteFiber D m)
    (i : Fin (k - 1)) :
    G.IsClique (D.parts i : Set (Fin n)) := by
  obtain ⟨_hfull, _hcapacity, A, hA, _hAcard, rfl⟩ :=
    mem_supercriticalCoPartiteFiber.mp hG
  exact DenseGraph.completeWithinParts_isClique
    (supercriticalSelectedCrossGraph A) D.parts i

theorem card_finiteGraphEdges_eq_of_mem_supercriticalCoPartiteFiber
    {k n m : ℕ} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCoPartiteFiber D m) :
    (finiteGraphEdges G).card = m := by
  obtain ⟨_hfull, hcapacity, A, hA, hAcard, rfl⟩ :=
    mem_supercriticalCoPartiteFiber.mp hG
  rw [card_finiteGraphEdges_supercriticalGraphOfCrossChoice D hA, hAcard]
  omega

theorem supercriticalCoPartiteFiber_isCoMultipartite
    {k n m : ℕ} {D : SupercriticalDivision k (Fin n)}
    {G : SimpleGraph (Fin n)}
    (hG : G ∈ supercriticalCoPartiteFiber D m) :
    DenseGraph.IsCoMultipartite G (k - 1) := by
  exact D.isCoMultipartite_of_isFull_of_isClique
    G (mem_supercriticalCoPartiteFiber.mp hG).1
    (fun i ↦ supercriticalCoPartiteFiber_isClique hG i)

/-- The repaired absorbed family is exactly the full-division fiber of the
absorbed division. -/
theorem supercriticalAbsorbedCoPartiteGraphFinset_eq_fiber
    {k n m : ℕ} (hk : 3 ≤ k)
    (D : SupercriticalDivision k (Fin n)) :
    supercriticalAbsorbedCoPartiteGraphFinset hk D m =
      supercriticalCoPartiteFiber
        (supercriticalAbsorbSparseDivision hk D) m := by
  classical
  simp only [supercriticalCoPartiteFiber,
    SupercriticalDivision.absorbSparse_isFull, if_true]
  rfl

/-- Exact cardinality of a prescribed full co-multipartite fiber. -/
theorem card_supercriticalCoPartiteFiber
    {k n m : ℕ} (D : SupercriticalDivision k (Fin n))
    (hfull : D.IsFull) :
    (supercriticalCoPartiteFiber D m).card =
      if divisionInternalCliqueCapacity D ≤ m then
        Nat.choose (supercriticalTotalCrossCapacity D)
          (m - divisionInternalCliqueCapacity D)
      else 0 := by
  classical
  by_cases hcapacity : divisionInternalCliqueCapacity D ≤ m
  · rw [supercriticalCoPartiteFiber, if_pos hfull, if_pos hcapacity]
    rw [Finset.card_image_iff.mpr]
    · simp [hcapacity]
    · intro A hA B hB hgraph
      apply supercriticalGraphOfCrossChoice_injectiveOn D
      · exact (Finset.mem_powersetCard.mp hA).1
      · exact (Finset.mem_powersetCard.mp hB).1
      · exact hgraph
  · simp [supercriticalCoPartiteFiber, hfull, hcapacity]

/-- Piecewise feasibility form of the exact fiber cardinality. -/
theorem card_supercriticalCoPartiteFiber_eq_if_feasible
    {k n m : ℕ} (D : SupercriticalDivision k (Fin n))
    (hfull : D.IsFull) :
    (supercriticalCoPartiteFiber D m).card =
      if divisionInternalCliqueCapacity D ≤ m ∧
          m ≤ divisionInternalCliqueCapacity D +
            supercriticalTotalCrossCapacity D then
        Nat.choose (supercriticalTotalCrossCapacity D)
          (m - divisionInternalCliqueCapacity D)
      else 0 := by
  rw [card_supercriticalCoPartiteFiber D hfull]
  by_cases hlower : divisionInternalCliqueCapacity D ≤ m
  · rw [if_pos hlower]
    by_cases hupper : m ≤ divisionInternalCliqueCapacity D +
        supercriticalTotalCrossCapacity D
    · simp [hlower, hupper]
    · have hlt : supercriticalTotalCrossCapacity D <
          m - divisionInternalCliqueCapacity D := by omega
      simp [hlower, hupper, Nat.choose_eq_zero_of_lt hlt]
  · simp [hlower]
end InducedStars
