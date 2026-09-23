import InducedStars.Structure.Subcritical.ResidualStarCandidates
import InducedStars.Structure.Subcritical.ResidualCandidateEvents

/-!
# Deterministic semantics of the four actual residual-star constructions

Paper: the four placements in `lemma:residual-matching-estimate-K1k`.
The only residual edge in a selection is its designated matching edge.
The remaining deterministic pairs and all random pairs therefore have
the exact induced-star polarity, rather than ordinary-star containment.
Endpoint cleaning excludes every prescribed endpoint before free vertices are selected.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars
namespace SubcriticalHomogeneousResidualMatching

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta theta : ℝ}
  {R : SimpleGraph (Fin n)} {B : Finset (Fin n)}

theorem endpoints_adj (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : R.Adj (M.firstEndpoint e) (M.secondEndpoint e) := by
  have h := M.isMatching.1 e.val e.property
  simpa only [M.edge_eq_endpoints e, SimpleGraph.mem_edgeSet] using h

theorem own_active_freeParent (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    {x y : Fin n} (hx : x ∈ D.part M.placement.leftPart)
    (t : SubcriticalCoreNeighbor D M.placement.leftPart.1 M.placement.leftPart.2)
    (hy : y ∈ D.part (subcriticalResidualFreeParent M.placement.leftPart (some t))) :
    D.ActivePair x y := by
  exact ⟨M.placement.leftPart.1, M.placement.leftPart.2, t.val, t.property, hx, hy⟩

theorem endpoints_samePart_iff (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : D.SamePart (M.firstEndpoint e) (M.secondEndpoint e) ↔
      M.placement.IsInternal := by
  constructor
  · intro hs
    by_contra hc
    have hy : M.secondEndpoint e ∈ D.part M.placement.leftPart := by
      obtain ⟨a, hx, hy⟩ := hs
      rwa [← D.mem_part_unique (M.firstEndpoint_mem e) hx] at hy
    exact M.placement.right_not_mem_freeParent_of_not_internal hc
      (M.secondEndpoint_mem e) none hy
  · intro hc
    exact ⟨_, M.firstEndpoint_mem e,
      M.placement.right_mem_own_of_internal hc (M.secondEndpoint_mem e)⟩

theorem endpoints_nonactive (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : ¬ D.ActivePair (M.firstEndpoint e) (M.secondEndpoint e) := by
  by_cases hc : M.placement.IsInternal
  · exact SubcriticalDivision.not_activePair_of_samePart ((M.endpoints_samePart_iff e).mpr hc)
  · rintro ⟨i, a, b, hab, hx, hy⟩
    have he := D.mem_part_unique (M.firstEndpoint_mem e) (b := ⟨i, a⟩) hx
    have hbad := M.placement.right_not_mem_freeParent_of_not_internal hc
      (M.secondEndpoint_mem e)
    revert hbad
    rw [he]
    intro hbad
    exact hbad (some ⟨b, hab⟩) hy

theorem first_selection_no_defect
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : ¬R.Adj (M.firstEndpoint e) (f.val t) :=
  (DenseGraph.mem_endpointCleanTarget R _ _ _ _).mp (M.selection_mem_cleanTarget e f t) |>.2.1

theorem second_selection_no_defect
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole) : ¬R.Adj (M.secondEndpoint e) (f.val t) :=
  (DenseGraph.mem_endpointCleanTarget R _ _ _ _).mp (M.selection_mem_cleanTarget e f t) |>.2.2

theorem selections_no_defect (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (s t : M.FreeRole) (hst : s ≠ t) :
    ¬R.Adj (f.val s) (f.val t) :=
  (DenseGraph.mem_defectFreeSelections _ R f.val).mp f.property |>.2 s t hst

theorem first_selection_samePart_none
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : D.SamePart (M.firstEndpoint e) (f.val none) :=
  ⟨_, M.firstEndpoint_mem e, M.selection_mem_part e f none⟩

theorem second_selection_samePart_none
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (hc : M.placement.IsInternal) :
    D.SamePart (M.secondEndpoint e) (f.val none) :=
  ⟨_, M.placement.right_mem_own_of_internal hc (M.secondEndpoint_mem e),
    M.selection_mem_part e f none⟩

theorem second_selection_not_samePart
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (hc : ¬M.placement.IsInternal) (t : M.FreeRole) :
    ¬D.SamePart (M.secondEndpoint e) (f.val t) := by
  rintro ⟨a, hy, hz⟩
  have he := D.mem_part_unique hz (M.selection_mem_part e f t)
  rw [he] at hy
  exact M.placement.right_not_mem_freeParent_of_not_internal hc (M.secondEndpoint_mem e) t hy

theorem selections_not_samePart
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (s t : M.FreeRole) (hst : s ≠ t) :
    ¬D.SamePart (f.val s) (f.val t) := by
  rw [D.samePart_iff_of_mem_parts (M.selection_mem_part e f s) (M.selection_mem_part e f t)]
  exact fun h ↦ hst (subcriticalResidualFreeParent_injective _ h)

theorem endpoints_deterministic (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) :
    ((D.SamePart (M.firstEndpoint e) (M.secondEndpoint e) ≠
      R.Adj (M.firstEndpoint e) (M.secondEndpoint e)) ↔
      (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inl 0) (Sum.inl 1)) := by
  rw [M.endpoints_samePart_iff e]
  by_cases hc : M.placement.IsInternal <;>
    simp [M.endpoints_adj e, candidateCenter, hc, SimpleGraph.starGraph_adj]

theorem first_selection_deterministic
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole)
    (hn : ¬D.ActivePair (M.firstEndpoint e) (f.val t)) :
    ((D.SamePart (M.firstEndpoint e) (f.val t) ≠ R.Adj (M.firstEndpoint e) (f.val t)) ↔
      (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inl 0) (Sum.inr t)) := by
  cases t with
  | none =>
      by_cases hc : M.placement.IsInternal <;>
        simp [M.first_selection_samePart_none e f, M.first_selection_no_defect e f,
          candidateCenter, hc, SimpleGraph.starGraph_adj]
  | some t =>
      exact (hn (M.own_active_freeParent (M.firstEndpoint_mem e) t
        (M.selection_mem_part e f (some t)))).elim

theorem second_selection_deterministic
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.FreeRole)
    (hn : ¬D.ActivePair (M.secondEndpoint e) (f.val t)) :
    ((D.SamePart (M.secondEndpoint e) (f.val t) ≠ R.Adj (M.secondEndpoint e) (f.val t)) ↔
      (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inl 1) (Sum.inr t)) := by
  by_cases hc : M.placement.IsInternal
  · cases t with
    | none =>
        simp [M.second_selection_samePart_none e f hc, M.second_selection_no_defect e f,
          candidateCenter, hc, SimpleGraph.starGraph_adj]
    | some t =>
        exact (hn (M.own_active_freeParent
          (M.placement.right_mem_own_of_internal hc (M.secondEndpoint_mem e)) t
          (M.selection_mem_part e f (some t)))).elim
  · simp [M.second_selection_not_samePart e f hc t, M.second_selection_no_defect e f,
      candidateCenter, hc, SimpleGraph.starGraph_adj]

theorem selections_deterministic
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (s t : M.FreeRole) (hst : s ≠ t)
    (hn : ¬D.ActivePair (f.val s) (f.val t)) :
    ((D.SamePart (f.val s) (f.val t) ≠ R.Adj (f.val s) (f.val t)) ↔
      (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inr s) (Sum.inr t)) := by
  have hs := M.selections_not_samePart e f s t hst
  have hr := M.selections_no_defect e f s t hst
  by_cases hc : M.placement.IsInternal
  · cases s with
    | none =>
        cases t with
        | none => exact (hst rfl).elim
        | some t =>
            exact (hn (M.own_active_freeParent (M.selection_mem_part e f none) t
              (M.selection_mem_part e f (some t)))).elim
    | some s =>
        cases t with
        | none =>
            exact (hn ((D.activePair_comm _ _).mpr
              (M.own_active_freeParent (M.selection_mem_part e f none) s
                (M.selection_mem_part e f (some s))))).elim
        | some t => simp [hs, hr, candidateCenter, hc, SimpleGraph.starGraph_adj]
  · simp [hs, hr, candidateCenter, hc, SimpleGraph.starGraph_adj]

theorem selectionVertex_deterministic
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (s t : M.Role) (hst : s ≠ t)
    (hn : ¬D.ActivePair (M.selectionVertex e f s) (M.selectionVertex e f t)) :
    ((D.SamePart (M.selectionVertex e f s) (M.selectionVertex e f t) ≠
      R.Adj (M.selectionVertex e f s) (M.selectionVertex e f t)) ↔
      (SimpleGraph.starGraph M.candidateCenter).Adj s t) := by
  cases s with
  | inl s =>
      cases t with
      | inl t =>
          fin_cases s <;> fin_cases t
          · exact (hst rfl).elim
          · exact M.endpoints_deterministic e
          · change (D.SamePart (M.secondEndpoint e) (M.firstEndpoint e) ≠
                R.Adj (M.secondEndpoint e) (M.firstEndpoint e)) ↔
                (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inl 1) (Sum.inl 0)
            simpa only [D.samePart_comm (M.secondEndpoint e) (M.firstEndpoint e),
              R.adj_comm (M.secondEndpoint e) (M.firstEndpoint e),
              (SimpleGraph.starGraph M.candidateCenter).adj_comm (Sum.inl 1) (Sum.inl 0)]
              using M.endpoints_deterministic e
          · exact (hst rfl).elim
      | inr t =>
          fin_cases s
          · exact M.first_selection_deterministic e f t hn
          · exact M.second_selection_deterministic e f t hn
  | inr s =>
      cases t with
      | inl t =>
          fin_cases t
          · have hh := M.first_selection_deterministic e f s
              (fun ha ↦ hn ((D.activePair_comm _ _).mp ha))
            change (D.SamePart (f.val s) (M.firstEndpoint e) ≠
                R.Adj (f.val s) (M.firstEndpoint e)) ↔
                (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inr s) (Sum.inl 0)
            simpa only [
              D.samePart_comm (f.val s) (M.firstEndpoint e),
              R.adj_comm (f.val s) (M.firstEndpoint e),
              (SimpleGraph.starGraph M.candidateCenter).adj_comm (Sum.inr s) (Sum.inl 0)] using hh
          · have hh := M.second_selection_deterministic e f s
              (fun ha ↦ hn ((D.activePair_comm _ _).mp ha))
            change (D.SamePart (f.val s) (M.secondEndpoint e) ≠
                R.Adj (f.val s) (M.secondEndpoint e)) ↔
                (SimpleGraph.starGraph M.candidateCenter).Adj (Sum.inr s) (Sum.inl 1)
            simpa only [
              D.samePart_comm (f.val s) (M.secondEndpoint e),
              R.adj_comm (f.val s) (M.secondEndpoint e),
              (SimpleGraph.starGraph M.candidateCenter).adj_comm (Sum.inr s) (Sum.inl 1)] using hh
      | inr t => exact M.selections_deterministic e f s t (fun h ↦ hst (congrArg Sum.inr h)) hn

/-- Every actual clean selection is an induced-star witness for the active
random model; no probabilistic premise appears in this construction. -/
def selectionWitness {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e : M.Edge) (f : M.Selection e) :
    SubcriticalResidualStarWitness p R M.Role M.candidateCenter where
  vertex := M.selectionEmbedding e f
  away := M.selectionVertex_away e f
  retained_pair := M.selectionVertex_retained_pair e f
  deterministic := M.selectionVertex_deterministic e f
  defect := ⟨Sum.inl 0, Sum.inl 1, M.endpoints_adj e⟩

end SubcriticalHomogeneousResidualMatching
end InducedStars
