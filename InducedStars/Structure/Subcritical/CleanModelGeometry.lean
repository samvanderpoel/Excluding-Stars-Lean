import InducedStars.Structure.Subcritical.CleanModelCounting

/-!
# Finite induced-star obstruction for clean models

Only the finite regular-core blow-up theorem is used. A hypothetical star
lies wholly on the retained side or wholly inside the fixed remainder.
There is no graphon optimizer, concentration, or multiplicity input.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta delta : ℝ} {R₀ m : ℕ}
  {v : RetainedEdgeCountVector D eta R₀}

private theorem clean_samePart_retained {x y : V} (hs : D.SamePart x y)
    (hx : x ∈ D.retainedVertices eta R₀) : y ∈ D.retainedVertices eta R₀ := by
  obtain ⟨a, hxa, hya⟩ := hs
  exact (D.mem_retainedVertices_iff_of_mem_componentSupport
    (D.mem_componentSupport.mpr ⟨a.2, hya⟩)).mpr
      ((D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a.2, hxa⟩)).mp hx)

private theorem clean_activePair_retained {x y : V} (hs : D.ActivePair x y)
    (hx : x ∈ D.retainedVertices eta R₀) : y ∈ D.retainedVertices eta R₀ := by
  obtain ⟨i, a, b, _, hxa, hyb⟩ := hs
  exact (D.mem_retainedVertices_iff_of_mem_componentSupport
    (D.mem_componentSupport.mpr ⟨b, hyb⟩)).mpr
      ((D.mem_retainedVertices_iff_of_mem_componentSupport
        (D.mem_componentSupport.mpr ⟨a, hxa⟩)).mp hx)

theorem subcriticalCleanGraph_adj_iff
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v) (x y : V) :
    (subcriticalCleanGraph H S).Adj x y ↔
      (s(x, y) ∈ retainedCliquePotentialEdges D eta R₀ ∨
        (subcriticalRemainderGraphSpanningCoe H).Adj x y ∨
        s(x, y) ∈ subcriticalActiveSelectedEdges ((retainedEdgeChoiceModel v).sampleOutcome S)) ∧
      x ≠ y := by
  simp only [subcriticalCleanGraph, subcriticalActiveGraphFromOutcome,
    subcriticalActiveBernoulliGraphFromOutcome, subcriticalGraphFromActiveEdges_adj,
    subcriticalActiveFixedBlockModel, SimpleGraph.bot_adj, ne_eq,
    eq_iff_iff, iff_false, not_not]

theorem subcriticalCleanGraph_part_clique
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    {x y : V} (hx : x ∈ D.part a) (hy : y ∈ D.part a) (hne : x ≠ y) :
    (subcriticalCleanGraph H S).Adj x y := by
  apply (subcriticalCleanGraph_adj_iff H S x y).mpr
  exact ⟨Or.inl ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mpr
    ⟨hne, ⟨a, hx, hy⟩, D.part_subset_retainedVertices ha hx⟩), hne⟩

theorem subcriticalCleanGraph_retained_edge_allowed
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀)
    (hxy : (subcriticalCleanGraph H S).Adj x y) : D.SamePart x y ∨ D.ActivePair x y := by
  rcases (subcriticalCleanGraph_adj_iff H S x y).mp hxy |>.1 with hc | hH | hA
  · exact Or.inl ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mp hc).2.1
  · exact ((D.mem_nonretainedVertices eta R₀ x).mp
      (subcriticalRemainderGraphSpanningCoe_support H hH).1 hx).elim
  · exact Or.inr ((mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ x y).mp
      (subcriticalActiveSelectedEdges_subset _ hA)).1

theorem subcriticalCleanGraph_neighbor_retained
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀)
    (hxy : (subcriticalCleanGraph H S).Adj x y) : y ∈ D.retainedVertices eta R₀ := by
  rcases subcriticalCleanGraph_retained_edge_allowed H S hx hxy with hs | ha
  · exact clean_samePart_retained hs hx
  · exact clean_activePair_retained ha hx

theorem subcriticalCleanGraph_no_retained_nonretained
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀)
    (hy : y ∈ D.nonretainedVertices eta R₀) : ¬(subcriticalCleanGraph H S).Adj x y := by
  intro hxy
  exact (D.mem_nonretainedVertices eta R₀ y).mp hy
    (subcriticalCleanGraph_neighbor_retained H S hx hxy)

theorem subcriticalCleanGraph_inactive_parts
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {a b : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    (hne : a ≠ b) (hno : ¬D.ActivePart a b)
    {x y : V} (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    ¬(subcriticalCleanGraph H S).Adj x y := by
  intro hxy
  rcases subcriticalCleanGraph_retained_edge_allowed H S
    (D.part_subset_retainedVertices ha hx) hxy with hs | ha
  · exact hne ((D.samePart_iff_of_mem_parts hx hy).mp hs)
  · exact hno ((D.activePair_iff_of_mem_parts hx hy).mp ha)

theorem subcriticalCleanGraph_distinct_components
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {a b : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    (hne : a.1 ≠ b.1) {x y : V} (hx : x ∈ D.part a) (hy : y ∈ D.part b) :
    ¬(subcriticalCleanGraph H S).Adj x y :=
  subcriticalCleanGraph_inactive_parts H S ha (fun h ↦ hne (congrArg Sigma.fst h))
    (fun h ↦ hne (SubcriticalDivision.activePart_same_component h)) hx hy

theorem subcriticalCleanGraph_model_adj_iff_of_retained
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v)
    {x y : V} (hx : x ∈ D.retainedVertices eta R₀) :
    (subcriticalDivisionModelGraph (subcriticalCleanGraph H S) D).Adj x y ↔
      (subcriticalCleanGraph H S).Adj x y := by
  rw [subcriticalDivisionModelGraph_adj]
  constructor
  · rintro ⟨hne, hs | ha⟩
    · apply (subcriticalCleanGraph_adj_iff H S x y).mpr
      exact ⟨Or.inl ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mpr
        ⟨hne, hs, hx⟩), hne⟩
    · exact ha.2
  · intro hxy
    refine ⟨hxy.ne, ?_⟩
    exact (subcriticalCleanGraph_retained_edge_allowed H S hx hxy).elim
      Or.inl (fun ha ↦ Or.inr ⟨ha, hxy⟩)

/-- The construction has no ordinary defect incident with a retained vertex;
the arbitrary remainder need not be empty or have zero ordinary defect. -/
theorem subcriticalCleanGraph_retainedIncident_empty
    (H : SubcriticalRemainderGraph D eta R₀) (S : RetainedEdgeChoices v) :
    subcriticalRetainedIncidentDefectGraph (subcriticalCleanGraph H S) D eta R₀ = ⊥ := by
  apply bot_unique
  intro x y hxy
  have hno {x y : V}
      (hxy : (subcriticalDefectGraph (subcriticalCleanGraph H S) D).Adj x y)
      (hx : x ∈ D.retainedVertices eta R₀) : False := by
    have hh := (subcriticalDefectGraph_adj _ D x y).mp hxy |>.1
    have hne := (subcriticalCombinedDefectGraph_adj _ D x y).mp hh
    exact hne (propext (subcriticalCleanGraph_model_adj_iff_of_retained H S hx).symm)
  exact (hxy.2.elim (fun hx ↦ hno hxy.1 hx) (fun hy ↦ hno hxy.1.symm hy)).elim

/-- The finite regular-core obstruction proves induced-star-freeness of
the retained part; the actual induced-free remainder supplies the other piece. -/
theorem subcriticalCleanModelGraph_inducedFree
    (hk : 3 ≤ k) (H : SubcriticalRemainderGraph D eta R₀)
    (hH : ¬Regularity.InducedEmbeds (inducedStar k) H) (S : RetainedEdgeChoices v) :
    ¬Regularity.InducedEmbeds (inducedStar k) (subcriticalCleanGraph H S) := by
  rintro ⟨f⟩
  by_cases hcenter : f 0 ∈ D.retainedVertices eta R₀
  · have hall (i : Fin (k + 1)) : f i ∈ D.retainedVertices eta R₀ := by
      by_cases hi : i = 0
      · simpa only [hi] using hcenter
      · exact subcriticalCleanGraph_neighbor_retained H S hcenter
          (f.map_rel_iff.mpr (inducedStar_center_adj_of_ne hi))
    let g : inducedStar k ↪g subcriticalDivisionModelGraph (subcriticalCleanGraph H S) D :=
      { toFun := f
        inj' := f.injective
        map_rel_iff' := by
          intro i j
          exact (subcriticalCleanGraph_model_adj_iff_of_retained H S (hall i)).trans
            f.map_rel_iff }
    exact isSubcriticalRegularBlowup_not_inducedEmbeds_inducedStar hk _
      (subcriticalDivisionModelGraph_isRegularBlowup _ D) ⟨g⟩
  · have hall (i : Fin (k + 1)) : f i ∈ D.nonretainedVertices eta R₀ := by
      apply (D.mem_nonretainedVertices eta R₀ (f i)).mpr
      intro hi
      by_cases hi0 : i = 0
      · exact hcenter (hi0 ▸ hi)
      · exact hcenter (subcriticalCleanGraph_neighbor_retained H S hi
          (f.map_rel_iff.mpr (inducedStar_center_adj_of_ne hi0)).symm)
    let g : inducedStar k ↪g H :=
      { toFun := fun i ↦ ⟨f i, hall i⟩
        inj' := fun i j hij ↦ f.injective (congrArg Subtype.val hij)
        map_rel_iff' := by
          intro i j
          have hh := congrArg (fun Q : SubcriticalRemainderGraph D eta R₀ ↦
            Q.Adj ⟨f i, hall i⟩ ⟨f j, hall j⟩) (subcriticalCleanGraph_remainder H S)
          exact (Iff.of_eq hh).symm.trans f.map_rel_iff }
    exact hH ⟨g⟩

theorem subcriticalCleanModelGraphFinset_inducedFree
    (hk : 3 ≤ k) {G : SimpleGraph V}
    (hG : G ∈ subcriticalCleanModelGraphFinset D eta R₀ m delta) :
    ¬Regularity.InducedEmbeds (inducedStar k) G := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hG
  exact subcriticalCleanModelGraph_inducedFree hk d.2.1.val
    ((mem_subcriticalCleanRemainderGraphFinset d.2.1.val d.1.val).mp d.2.1.property).1 d.2.2.2

end InducedStars
