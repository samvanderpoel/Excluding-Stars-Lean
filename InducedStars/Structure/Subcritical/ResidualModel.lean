import InducedStars.Structure.Subcritical.ProfileProbability

/-!
# Root-free residual defects in the active model

The compatible rooted and leftover patterns disappear on pairs avoiding all
profile roots. This is the exact deterministic interface for the four residual
matching placements; in particular missing same-part defects retain their
negative polarity. No condition on the nonretained remainder is needed.
-/

noncomputable section
open Finset Set
open scoped Classical
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {F : Finset (SimpleGraph V)} {p : SubcriticalProfile D eta R₀ theta}
  {TB R L : SimpleGraph V}

theorem SubcriticalCompatibleDefectTriple.rooted_incident_roots
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    {x y : V} (hxy : TB.Adj x y) : x ∈ p.roots ∨ y ∈ p.roots := by
  obtain ⟨G, hG, rfl, _, _⟩ := h
  have hp := (mem_subcriticalProfileClassGraphFinset.mp hG).2
  rw [hp.roots_eq]
  rcases (subcriticalRootedDefectGraph_adj G D eta R₀ theta alpha x y).mp hxy with h | h
  · exact Or.inl (subcriticalRecordedRootNeighbors_root_and_nonroot
      G D eta R₀ theta alpha x y h).1
  · exact Or.inr (subcriticalRecordedRootNeighbors_root_and_nonroot
      G D eta R₀ theta alpha y x h).1

theorem SubcriticalCompatibleDefectTriple.adj_away_roots
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    {x y : V} (hx : x ∉ p.roots) (hy : y ∉ p.roots) :
    (TB ⊔ R ⊔ L).Adj x y ↔ R.Adj x y := by
  have hb : ¬ TB.Adj x y := fun he ↦ (h.rooted_incident_roots he).elim hx hy
  have hl : ¬ L.Adj x y := fun he ↦ (h.leftover_incident_roots he).elim hx hy
  simp [SimpleGraph.sup_adj, hb, hl]

theorem SubcriticalCompatibleDefectTriple.valid
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L) :
    IsSubcriticalRetainedDefectPattern D eta R₀ (TB ⊔ R ⊔ L) := by
  obtain ⟨G, _, hG⟩ := h.decomposition.1
  rw [← hG]
  exact subcriticalRetainedIncidentDefectGraph_valid G D eta R₀

theorem SubcriticalCompatibleDefectTriple.residual_valid
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L) :
    IsSubcriticalRetainedDefectPattern D eta R₀ R := by
  intro x y hxy
  exact h.valid (Or.inl (Or.inr hxy))

/-- With a retained endpoint, the arbitrary nonretained graph contributes
no edge. Thus the exact model is clique-or-active status toggled by `R`. -/
theorem subcriticalResidualModel_adj_away_roots
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate)
    {x y : V} (hx : x ∉ p.roots) (hy : y ∉ p.roots)
    (hret : x ∈ D.retainedVertices eta R₀ ∨ y ∈ D.retainedVertices eta R₀)
    (hne : x ≠ y) :
    (subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L) S).Adj x y ↔
      ((D.SamePart x y ∨ s(x, y) ∈ subcriticalActiveSelectedEdges S) ≠ R.Adj x y) := by
  have hH : ¬ (subcriticalRemainderGraphSpanningCoe H).Adj x y := by
    intro he
    obtain ⟨hxn, hyn⟩ := subcriticalRemainderGraphSpanningCoe_support H he
    exact hret.elim ((D.mem_nonretainedVertices eta R₀ x).mp hxn)
      ((D.mem_nonretainedVertices eta R₀ y).mp hyn)
  have hC : s(x, y) ∈ retainedCliquePotentialEdges D eta R₀ ↔ D.SamePart x y := by
    rw [mk_mem_retainedCliquePotentialEdges_iff]
    constructor
    · exact fun h ↦ h.2.1
    · intro hs
      refine ⟨hne, hs, ?_⟩
      rcases hret with hx | hy
      · exact hx
      · obtain ⟨a, hxa, hya⟩ := hs
        rw [D.mem_retainedVertices_iff_of_mem_componentSupport
          (D.mem_componentSupport.mpr ⟨a.2, hya⟩)] at hy
        exact (D.mem_retainedVertices_iff_of_mem_componentSupport
          (D.mem_componentSupport.mpr ⟨a.2, hxa⟩)).mpr hy
  simp only [subcriticalActiveBernoulliGraphFromOutcome,
    subcriticalGraphFromActiveEdges_adj, hC, hH, false_or,
    h.adj_away_roots hx hy]
  exact and_iff_left hne

/-- Active coordinates are individual unordered vertex pairs, not merely
part-pair labels. Membership recovers the sampled Bernoulli bit exactly. -/
theorem subcriticalResidualModel_active_coordinate
    (h : SubcriticalCompatibleDefectTriple F alpha p TB R L)
    (H : SubcriticalRemainderGraph D eta R₀)
    (mvec : RetainedEdgeCountVector D eta R₀)
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate)
    (e : (subcriticalActiveFixedBlockModel mvec).Coordinate) :
    e.2.1 ∈ finiteGraphEdges
        (subcriticalActiveBernoulliGraphFromOutcome H (TB ⊔ R ⊔ L) S) ↔ e ∈ S := by
  have he : e.2.1 ∈ retainedActiveEdgeUniverse D eta R₀ :=
    (mem_retainedActiveEdgeUniverse D eta R₀ e.2.1).mpr ⟨e.1, e.2.2⟩
  have hh := congrArg (fun E ↦ e.2.1 ∈ E)
    (subcriticalGraphFromActiveEdges_active_edges H (TB ⊔ R ⊔ L) h.valid
      (subcriticalActiveSelectedEdges_subset S))
  simp only [Finset.mem_inter, he, and_true] at hh
  change e.2.1 ∈ finiteGraphEdges
    (subcriticalGraphFromActiveEdges H (TB ⊔ R ⊔ L) (subcriticalActiveSelectedEdges S)) ↔ _
  rw [hh]
  constructor
  · rintro he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.mp he
    exact (subcriticalActiveCoordinate_val_injective mvec hfe) ▸ hf
  · exact fun he ↦ Finset.mem_image.mpr ⟨e, he, rfl⟩

end InducedStars
