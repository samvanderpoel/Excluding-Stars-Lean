import InducedStars.Structure.Subcritical.ActiveModelsRealization

/-! # Exact recovery of finite graphs by the retained active model -/

noncomputable section
open Finset Set
open scoped BigOperators Classical symmDiff
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical fixed-count sample consists of the actual active edges. -/
def subcriticalActualActiveSample (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (eta : ℝ) (R₀ : ℕ) :
    (subcriticalActiveFixedBlockModel (actualRetainedEdgeCountVector G D eta R₀)).Sample :=
  fun e ↦ ⟨(actualRetainedActiveEdges G D eta R₀ e).subtype
    (fun z ↦ z ∈ retainedActivePotentialEdges D eta R₀ e), by
      apply Finset.mem_powersetCard.mpr
      refine ⟨Finset.subset_univ _, ?_⟩
      change ((actualRetainedActiveEdges G D eta R₀ e).subtype
        (fun z ↦ z ∈ retainedActivePotentialEdges D eta R₀ e)).card =
          (actualRetainedEdgeCountVector G D eta R₀).count e
      rw [Finset.card_subtype]
      have hf : (actualRetainedActiveEdges G D eta R₀ e).filter
          (fun z ↦ z ∈ retainedActivePotentialEdges D eta R₀ e) =
            actualRetainedActiveEdges G D eta R₀ e :=
        Finset.filter_eq_self.mpr (fun _ hz ↦ (Finset.mem_inter.mp hz).1)
      rw [hf]
      exact actualRetainedActiveEdges_card G D eta R₀ e⟩

theorem subcriticalActualActiveSample_selected (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (e : RetainedActivePair D eta R₀) :
    (subcriticalActiveFixedBlockModel (actualRetainedEdgeCountVector G D eta R₀)).selectedInBlock
      (subcriticalActualActiveSample G D eta R₀) e =
        actualRetainedActiveEdges G D eta R₀ e := by
  change ((actualRetainedActiveEdges G D eta R₀ e).subtype
    (fun z ↦ z ∈ retainedActivePotentialEdges D eta R₀ e)).map
      (Function.Embedding.subtype _) = _
  exact Finset.subtype_map_of_mem (fun _ hz ↦ (Finset.mem_inter.mp hz).1)

theorem subcriticalActualActiveSample_selected_all (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    subcriticalActiveSelectedEdges
      ((subcriticalActiveFixedBlockModel (actualRetainedEdgeCountVector G D eta R₀)).sampleOutcome
        (subcriticalActualActiveSample G D eta R₀)) =
      actualRetainedActiveEdgeUniverse G D eta R₀ := by
  rw [subcriticalActiveSelectedEdges_sample_eq, actualRetainedActiveEdgeUniverse_eq_biUnion]
  congr 1
  funext e
  exact subcriticalActualActiveSample_selected G D eta R₀ e

theorem subcriticalRemainderGraph_edges (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    finiteGraphEdges (subcriticalRemainderGraphSpanningCoe
      (subcriticalRemainderGraph G D eta R₀)) =
      finiteGraphEdges G ∩ nonretainedPotentialEdges D eta R₀ := by
  ext z
  induction z using Sym2.inductionOn with
  | _ x y =>
    simp only [mk_mem_finiteGraphEdges, subcriticalRemainderGraph_adj,
      Finset.mem_inter, mk_mem_nonretainedPotentialEdges_iff]
    exact ⟨fun h ↦ ⟨h.1, h.2.1, h.2.2, h.1.ne⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2.1⟩⟩

/-- Exact recovery, for every finite graph, with no induced-free or
closeness hypothesis. -/
theorem subcriticalActiveGraphFromOutcome_actual (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ) :
    subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀)
      (subcriticalRetainedIncidentDefectGraph G D eta R₀)
      (subcriticalActualActiveSample G D eta R₀) = G := by
  have hedge : finiteGraphEdges
      (subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀)
        (subcriticalRetainedIncidentDefectGraph G D eta R₀)
        (subcriticalActualActiveSample G D eta R₀)) = finiteGraphEdges G := by
    unfold subcriticalActiveGraphFromOutcome subcriticalActiveBernoulliGraphFromOutcome
    have hA : actualRetainedActiveEdgeUniverse G D eta R₀ ⊆
        retainedActiveEdgeUniverse D eta R₀ := Finset.inter_subset_left
    rw [subcriticalActualActiveSample_selected_all,
      subcriticalGraphFromActiveEdges_edges _ _ hA,
      subcriticalRemainderGraph_edges, subcriticalRetainedIncidentDefectGraph_edges]
    ext z
    simp only [retainedMissingCliqueEdges, retainedPresentDefectEdges,
      actualRetainedActiveEdgeUniverse, Finset.mem_symmDiff, Finset.mem_union,
      Finset.mem_inter, Finset.mem_sdiff]
    tauto
  ext x y
  exact Iff.of_eq (by simpa only [mk_mem_finiteGraphEdges] using
    (congrArg (fun E ↦ s(x, y) ∈ E) hedge))

/-- No valid defect changes an active coordinate, and no deterministic
clique or remainder edge occupies one. -/
theorem subcriticalGraphFromActiveEdges_active_edges {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {A : Finset (Sym2 V)} (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    finiteGraphEdges (subcriticalGraphFromActiveEdges H T A) ∩
      retainedActiveEdgeUniverse D eta R₀ = A := by
  rw [subcriticalGraphFromActiveEdges_edges H T hA]
  ext z
  have hC : z ∈ retainedActiveEdgeUniverse D eta R₀ →
      z ∉ retainedCliquePotentialEdges D eta R₀ := fun ha hc ↦
    Finset.disjoint_left.mp (retainedCliquePotentialEdges_disjoint_active D eta R₀) hc ha
  have hH : z ∈ retainedActiveEdgeUniverse D eta R₀ →
      z ∉ finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) := fun ha hh ↦
    Finset.disjoint_left.mp (retainedActiveEdgeUniverse_disjoint_nonretained D eta R₀)
      ha (subcriticalRemainderEdges_subset H hh)
  have hQ : z ∈ retainedActiveEdgeUniverse D eta R₀ → z ∉ finiteGraphEdges T := fun ha ht ↦
    Finset.disjoint_left.mp hT.disjoint_active ht ha
  have hsub : z ∈ A → z ∈ retainedActiveEdgeUniverse D eta R₀ := fun hz ↦ hA hz
  simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_union]
  tauto

theorem subcriticalActiveCoordinate_val_injective {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (mvec : RetainedEdgeCountVector D eta R₀) :
    Function.Injective (fun e : (subcriticalActiveFixedBlockModel mvec).Coordinate ↦ e.2.1) := by
  intro e f h
  change e.2.1 = f.2.1 at h
  have hi : e.1 = f.1 := by
    by_contra hne
    exact Finset.disjoint_left.mp (retainedActivePotentialEdges_disjoint D eta R₀ hne)
      e.2.2 (h.symm ▸ f.2.2)
  rcases e with ⟨i, x⟩
  rcases f with ⟨j, y⟩
  dsimp only at hi h
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext h)

/-- A fixed active sample is uniquely determined by the graph it realizes. -/
theorem subcriticalActiveGraphFromOutcome_injective {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    Function.Injective (fun S : (subcriticalActiveFixedBlockModel mvec).Sample ↦
      subcriticalActiveGraphFromOutcome H T S) := by
  intro S U heq
  have hE := congrArg (fun G ↦ finiteGraphEdges G ∩ retainedActiveEdgeUniverse D eta R₀) heq
  simp only [subcriticalActiveGraphFromOutcome, subcriticalActiveBernoulliGraphFromOutcome,
    subcriticalGraphFromActiveEdges_active_edges H T hT (subcriticalActiveSelectedEdges_subset _)] at hE
  apply (subcriticalActiveFixedBlockModel mvec).sampleOutcome_injective
  exact (Finset.image_injective (subcriticalActiveCoordinate_val_injective mvec)) hE

theorem subcriticalActiveGraphFromOutcome_actual_unique (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (eta : ℝ) (R₀ : ℕ)
    (S : (subcriticalActiveFixedBlockModel (actualRetainedEdgeCountVector G D eta R₀)).Sample) :
    subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀)
        (subcriticalRetainedIncidentDefectGraph G D eta R₀) S = G ↔
      S = subcriticalActualActiveSample G D eta R₀ := by
  constructor
  · intro h
    exact subcriticalActiveGraphFromOutcome_injective _ _
      (subcriticalRetainedIncidentDefectGraph_valid G D eta R₀) _
        (h.trans (subcriticalActiveGraphFromOutcome_actual G D eta R₀).symm)
  · rintro rfl
    exact subcriticalActiveGraphFromOutcome_actual G D eta R₀

/-- Retained clique defects delete, rather than add, their edges. -/
theorem subcriticalGraphFromActiveEdges_clique_adj {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (A : Finset (Sym2 V)) {x y : V}
    (hc : s(x, y) ∈ retainedCliquePotentialEdges D eta R₀) :
    (subcriticalGraphFromActiveEdges H T A).Adj x y ↔ ¬ T.Adj x y := by
  have hne := ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mp hc).1
  simp [subcriticalGraphFromActiveEdges_adj, hc, hne]

/-- The model leaves every nonretained-side edge exactly as specified by `H`. -/
theorem subcriticalGraphFromActiveEdges_nonretained_edges {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {A : Finset (Sym2 V)} (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀) :
    finiteGraphEdges (subcriticalGraphFromActiveEdges H T A) ∩
      nonretainedPotentialEdges D eta R₀ =
        finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) := by
  rw [subcriticalGraphFromActiveEdges_edges H T hA]
  ext z
  have hC : z ∈ nonretainedPotentialEdges D eta R₀ →
      z ∉ retainedCliquePotentialEdges D eta R₀ := fun hn hc ↦
    Finset.disjoint_left.mp (retainedCliquePotentialEdges_disjoint_nonretained D eta R₀) hc hn
  have hAA : z ∈ nonretainedPotentialEdges D eta R₀ → z ∉ A := fun hn ha ↦
    Finset.disjoint_left.mp (retainedActiveEdgeUniverse_disjoint_nonretained D eta R₀) (hA ha) hn
  have hQ : z ∈ nonretainedPotentialEdges D eta R₀ → z ∉ finiteGraphEdges T := fun hn ht ↦
    Finset.disjoint_left.mp hT.disjoint_nonretained ht hn
  have hsub : z ∈ finiteGraphEdges (subcriticalRemainderGraphSpanningCoe H) →
      z ∈ nonretainedPotentialEdges D eta R₀ := fun hz ↦ subcriticalRemainderEdges_subset H hz
  simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_union]
  tauto

/-- A valid non-clique defect is a positive edge in the realized graph. -/
theorem subcriticalGraphFromActiveEdges_positive_adj {D : SubcriticalDivision k V}
    {eta : ℝ} {R₀ : ℕ} (H : SubcriticalRemainderGraph D eta R₀)
    (T : SimpleGraph V) (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {A : Finset (Sym2 V)} (hA : A ⊆ retainedActiveEdgeUniverse D eta R₀)
    {x y : V} (ht : T.Adj x y) (hc : ¬ D.SamePart x y) :
    (subcriticalGraphFromActiveEdges H T A).Adj x y := by
  have hTmem := (mk_mem_finiteGraphEdges T x y).mpr ht
  have hC : s(x, y) ∉ retainedCliquePotentialEdges D eta R₀ :=
    fun h ↦ hc ((mk_mem_retainedCliquePotentialEdges_iff D eta R₀ x y).mp h).2.1
  have hH : ¬ (subcriticalRemainderGraphSpanningCoe H).Adj x y := fun hh ↦
    Finset.disjoint_left.mp hT.disjoint_nonretained hTmem
      (subcriticalRemainderEdges_subset H ((mk_mem_finiteGraphEdges _ x y).mpr hh))
  have hAA : s(x, y) ∉ A := fun ha ↦ Finset.disjoint_left.mp hT.disjoint_active hTmem (hA ha)
  simp [subcriticalGraphFromActiveEdges_adj, hC, hH, hAA, ht, ht.ne]

end InducedStars
