import InducedStars.Structure.Subcritical.ResidualModel
import DenseGraph.FiniteModels.BernoulliPolarity

/-!
# Exact signed events of residual star witnesses

The support consists of individual unordered active coordinates. A successful
mixed event realizes an actual induced star avoiding every root and containing
a residual pair, including when that pair is a missing edge.
Global polarity is imposed on the whole family, never separately per event.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped Classical
open DenseGraph.FiniteBernoulliProduct
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {F : Finset (SimpleGraph V)} {p : SubcriticalProfile D eta R₀ theta}
  {TB R L : SimpleGraph V} {I : Type*} [Fintype I] [DecidableEq I]

/-- The finite deterministic content of an actual residual star selection.
Random requirements are deliberately not assumed here. -/
structure SubcriticalResidualStarWitness
    (p : SubcriticalProfile D eta R₀ theta) (R : SimpleGraph V)
    (I : Type*) [Fintype I] (center : I) where
  vertex : I ↪ V
  away : ∀ i, vertex i ∉ p.roots
  retained_pair : ∀ i j, i ≠ j →
    vertex i ∈ D.retainedVertices eta R₀ ∨ vertex j ∈ D.retainedVertices eta R₀
  deterministic : ∀ i j, i ≠ j → ¬ D.ActivePair (vertex i) (vertex j) →
    ((D.SamePart (vertex i) (vertex j) ≠ R.Adj (vertex i) (vertex j)) ↔
      (SimpleGraph.starGraph center).Adj i j)
  defect : ∃ i j, R.Adj (vertex i) (vertex j)

namespace SubcriticalResidualStarWitness
variable {center : I}

def present (K : SubcriticalResidualStarWitness p R I center) :
    Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun e ↦ ∃ i j,
    e.2.1 = s(K.vertex i, K.vertex j) ∧ (SimpleGraph.starGraph center).Adj i j

def absent (K : SubcriticalResidualStarWitness p R I center) :
    Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun e ↦ ∃ i j,
    e.2.1 = s(K.vertex i, K.vertex j) ∧ i ≠ j ∧
      ¬ (SimpleGraph.starGraph center).Adj i j

@[simp] theorem mem_present (K : SubcriticalResidualStarWitness p R I center)
    (e : SubcriticalActiveCoordinate D eta R₀) :
    e ∈ K.present ↔ ∃ i j,
      e.2.1 = s(K.vertex i, K.vertex j) ∧ (SimpleGraph.starGraph center).Adj i j := by
  simp [present]

@[simp] theorem mem_absent (K : SubcriticalResidualStarWitness p R I center)
    (e : SubcriticalActiveCoordinate D eta R₀) :
    e ∈ K.absent ↔ ∃ i j,
      e.2.1 = s(K.vertex i, K.vertex j) ∧ i ≠ j ∧
        ¬ (SimpleGraph.starGraph center).Adj i j := by
  simp [absent]

theorem present_disjoint_absent (K : SubcriticalResidualStarWitness p R I center) :
    Disjoint K.present K.absent := by
  apply Finset.disjoint_left.mpr
  intro e he ha
  obtain ⟨i, j, hij, hstar⟩ := (K.mem_present e).mp he
  obtain ⟨u, v, huv, _, hnstar⟩ := (K.mem_absent e).mp ha
  have hh := (Sym2.mk_eq_mk_iff
    (p := (K.vertex i, K.vertex j)) (q := (K.vertex u, K.vertex v))).mp
      (hij.symm.trans huv)
  simp only [Prod.mk.injEq, Prod.swap_prod_mk, K.vertex.injective.eq_iff] at hh
  rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hnstar hstar
  · exact hnstar hstar.symm

/-- A candidate constrains at most one coordinate for each unordered pair
of its distinct roles. -/
theorem required_card_le (K : SubcriticalResidualStarWitness p R I center)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    (K.present ∪ K.absent).card ≤ (Fintype.card I).choose 2 := by
  let Q := (⊤ : SimpleGraph I).edgeFinset
  have hsub : (K.present ∪ K.absent).image (fun e ↦ e.2.1) ⊆
      Q.image (Sym2.map K.vertex) := by
    intro z hz
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hz
    have hw : ∃ i j, e.2.1 = s(K.vertex i, K.vertex j) ∧ i ≠ j := by
      rcases Finset.mem_union.mp he with he | he
      · obtain ⟨i, j, hij, hs⟩ := (K.mem_present e).mp he
        exact ⟨i, j, hij, hs.ne⟩
      · obtain ⟨i, j, hij, hne, _⟩ := (K.mem_absent e).mp he
        exact ⟨i, j, hij, hne⟩
    obtain ⟨i, j, hij, hne⟩ := hw
    refine Finset.mem_image.mpr ⟨s(i, j), ?_, ?_⟩
    · simp [Q, SimpleGraph.mem_edgeFinset, hne]
    · simpa using hij.symm
  calc
    _ = ((K.present ∪ K.absent).image (fun e ↦ e.2.1)).card := by
      exact (Finset.card_image_of_injective _
        (show Function.Injective (fun e : SubcriticalActiveCoordinate D eta R₀ ↦ e.2.1)
          from subcriticalActiveCoordinate_val_injective mvec)).symm
    _ ≤ (Q.image (Sym2.map K.vertex)).card := Finset.card_le_card hsub
    _ ≤ Q.card := Finset.card_image_le
    _ = _ := SimpleGraph.card_edgeFinset_top_eq_card_choose_two

theorem activeCoordinate_exists (K : SubcriticalResidualStarWitness p R I center)
    {i j : I} (hne : i ≠ j) (ha : D.ActivePair (K.vertex i) (K.vertex j)) :
    ∃ e : SubcriticalActiveCoordinate D eta R₀,
      e.2.1 = s(K.vertex i, K.vertex j) := by
  have hu : s(K.vertex i, K.vertex j) ∈ retainedActiveEdgeUniverse D eta R₀ := by
    rcases K.retained_pair i j hne with hi | hj
    · exact (mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ _ _).mpr ⟨ha, hi⟩
    · have hrev := (mk_mem_retainedActiveEdgeUniverse_iff D eta R₀
        (K.vertex j) (K.vertex i)).mpr ⟨(D.activePair_comm _ _).mp ha, hj⟩
      simpa only [Sym2.eq_swap] using hrev
  obtain ⟨e, he⟩ := (mem_retainedActiveEdgeUniverse D eta R₀ _).mp hu
  exact ⟨⟨e, ⟨_, he⟩⟩, rfl⟩

/-- The signed event realizes the full adjacency equivalence, including
all deterministic same-part, inactive, and retained--sparse pairs. -/
theorem mixedSuccess_realizes
    (K : SubcriticalResidualStarWitness p R I center)
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : Finset (SubcriticalActiveCoordinate D eta R₀))
    (hS : S ∈ mixedSuccessEvent K.present K.absent) (i j : I) :
    (subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L)
      (mvec := mvec) S).Adj (K.vertex i) (K.vertex j) ↔
        (SimpleGraph.starGraph center).Adj i j := by
  by_cases hij : i = j
  · subst j; simp
  have hne := K.vertex.injective.ne hij
  have hS' : K.present ⊆ S ∧ Disjoint K.absent S := by
    simpa only [mixedSuccessEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hS
  by_cases ha : D.ActivePair (K.vertex i) (K.vertex j)
  · obtain ⟨e, he⟩ := K.activeCoordinate_exists hij ha
    have hbit := subcriticalResidualModel_active_coordinate h H mvec S e
    rw [he, mk_mem_finiteGraphEdges] at hbit
    rw [hbit]
    constructor
    · intro heS
      by_contra hn
      exact Finset.disjoint_left.mp hS'.2
        ((K.mem_absent e).mpr ⟨i, j, he, hij, hn⟩) heS
    · exact fun hs ↦ hS'.1 ((K.mem_present e).mpr ⟨i, j, he, hs⟩)
  · have hA : s(K.vertex i, K.vertex j) ∉ subcriticalActiveSelectedEdges
        (mvec := mvec) S := by
      intro he
      exact ha ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ _ _).mp
        (subcriticalActiveSelectedEdges_subset S he)).1
    rw [subcriticalResidualModel_adj_away_roots h H mvec S
      (K.away i) (K.away j) (K.retained_pair i j hij) hne]
    simpa only [hA, or_false] using K.deterministic i j hij ha

/-- A successful candidate is forbidden by the existing root-free residual
safety event, irrespective of the arbitrary graph on the nonretained side. -/
theorem mixedSuccess_not_safe
    (K : SubcriticalResidualStarWitness p R I center) (hcard : Fintype.card I = k + 1)
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : Finset (SubcriticalActiveCoordinate D eta R₀))
    (hS : S ∈ mixedSuccessEvent K.present K.absent) :
    subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L) (mvec := mvec) S ∉
      subcriticalResidualSafeAwayFromRootsEvent p R := by
  let e₀ : Fin (k + 1) ≃ I := Fintype.equivOfCardEq (by simp [hcard])
  let e : Fin (k + 1) ≃ I := (Equiv.swap 0 (e₀.symm center)).trans e₀
  have he : e 0 = center := by simp [e]
  let f : inducedStar k ↪g
      subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L) (mvec := mvec) S :=
    { toFun := fun i ↦ K.vertex (e i)
      inj' := K.vertex.injective.comp e.injective
      map_rel_iff' := by
        intro i j
        change (subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L)
          (mvec := mvec) S).Adj (K.vertex (e i)) (K.vertex (e j)) ↔
            (inducedStar k).Adj i j
        rw [K.mixedSuccess_realizes h H mvec S hS, SimpleGraph.starGraph_adj,
          inducedStar_adj, ← he]
        simp only [e.injective.eq_iff, ne_eq] }
  intro hsafe
  obtain ⟨i, j, hR⟩ := K.defect
  have hn := hsafe f (fun i ↦ K.away (e i)) (e.symm i) (e.symm j)
  change ¬ R.Adj (K.vertex (e (e.symm i))) (K.vertex (e (e.symm j))) at hn
  simp only [Equiv.apply_symm_apply] at hn
  exact hn hR

end SubcriticalResidualStarWitness
end InducedStars
