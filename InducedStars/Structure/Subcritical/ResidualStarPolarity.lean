import InducedStars.Structure.Subcritical.ResidualStarWitnesses

/-!
# Global polarity and matching-anchor separation of actual residual stars

The same coordinate never has opposite requirements in two candidates.
Internal-placement centers are precisely the unused vertices of the own
part; all other centers are precisely the first endpoints of the matching.
This one global center zone determines the polarity for the whole family.
This verifies the global (not candidate-dependent) flip used uniformly over the whole matching.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars
namespace SubcriticalHomogeneousResidualMatching

variable {k n R₀ : ℕ} {D : SubcriticalDivision k (Fin n)} {eta theta : ℝ}
  {R : SimpleGraph (Fin n)} {B : Finset (Fin n)}

theorem first_mem_endpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : M.firstEndpoint e ∈ DenseGraph.matchingEndpoints M.edges :=
  (DenseGraph.mem_matchingEndpoints _ _).mpr ⟨e.val, e.property, M.firstEndpoint_mem_edge e⟩

theorem second_mem_endpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : M.secondEndpoint e ∈ DenseGraph.matchingEndpoints M.edges :=
  (DenseGraph.mem_matchingEndpoints _ _).mpr ⟨e.val, e.property, M.secondEndpoint_mem_edge e⟩

theorem firstEndpoints_subset_endpoints
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :
    M.firstEndpoints ⊆ DenseGraph.matchingEndpoints M.edges := by
  intro x hx
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx
  exact M.first_mem_endpoints e

theorem first_mem_firstEndpoints (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) : M.firstEndpoint e ∈ M.firstEndpoints :=
  Finset.mem_image.mpr ⟨e, Finset.mem_attach _ e, rfl⟩

theorem second_not_mem_firstEndpoints
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) (e : M.Edge) :
    M.secondEndpoint e ∉ M.firstEndpoints := by
  intro he
  obtain ⟨d, _, hde⟩ := Finset.mem_image.mp he
  have hed : e = d := by
    apply Subtype.ext
    by_contra hne
    have he : M.secondEndpoint e ∈ (e.val : Set (Fin n)) := by
      rw [M.edge_eq_endpoints e]; simp
    have hd : M.firstEndpoint d ∈ (d.val : Set (Fin n)) := by
      rw [M.edge_eq_endpoints d]; simp
    exact Set.disjoint_left.mp (M.isMatching.2 e.property d.property hne) he (hde ▸ hd)
  subst d
  exact M.first_ne_second e hde

def selectionImage (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) : Finset (Fin n) :=
  Finset.univ.image (M.selectionVertex e f)

/-- A candidate meets the full matching endpoint set in exactly its own
two designated endpoints. -/
theorem selectionImage_inter_endpoints
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) :
    M.selectionImage e f ∩ DenseGraph.matchingEndpoints M.edges =
      {M.firstEndpoint e, M.secondEndpoint e} := by
  ext x
  constructor
  · rintro hx
    obtain ⟨hx, he⟩ := Finset.mem_inter.mp hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    cases t with
    | inl t => fin_cases t <;> simp [selectionVertex]
    | inr t => exact (M.selection_not_mem_endpoints e f t he).elim
  · intro hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
        ⟨Sum.inl 0, Finset.mem_univ _, rfl⟩, M.first_mem_endpoints e⟩
    · have hx' : x = M.secondEndpoint e := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
        ⟨Sum.inl 1, Finset.mem_univ _, rfl⟩, M.second_mem_endpoints e⟩

/-- Different matching anchors yield different actual vertex images,
not merely different tags in a sigma type. -/
theorem edge_eq_of_selectionImage_eq
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e d : M.Edge) (f : M.Selection e) (g : M.Selection d)
    (h : M.selectionImage e f = M.selectionImage d g) : e = d := by
  apply Subtype.ext
  by_contra hne
  have he : M.firstEndpoint e ∈ (e.val : Set (Fin n)) := by
    rw [M.edge_eq_endpoints e]; simp
  have hp : M.firstEndpoint e ∈
      ({M.firstEndpoint d, M.secondEndpoint d} : Finset (Fin n)) := by
    rw [← M.selectionImage_inter_endpoints d g, ← h]
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr
      ⟨Sum.inl 0, Finset.mem_univ _, rfl⟩, M.first_mem_endpoints e⟩
  have hd : M.firstEndpoint e ∈ (d.val : Set (Fin n)) := by
    rw [M.edge_eq_endpoints d]
    simpa using hp
  exact Set.disjoint_left.mp (M.isMatching.2 e.property d.property hne) he hd

theorem selection_eq_of_selectionImage_eq
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f g : M.Selection e)
    (h : M.selectionImage e f = M.selectionImage e g) : f = g := by
  apply Subtype.ext
  funext t
  have hm : f.val t ∈ M.selectionImage e g := by
    rw [← h]
    exact Finset.mem_image.mpr ⟨Sum.inr t, Finset.mem_univ _, rfl⟩
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hm
  cases s with
  | inl s =>
      fin_cases s
      · exact (M.first_ne_selection e f t hs).elim
      · exact (M.second_ne_selection e f t hs).elim
  | inr s =>
      change g.val s = f.val t at hs
      have hts := subcriticalResidualFreeParent_injective M.placement.leftPart
        (D.mem_part_unique (M.selection_mem_part e f t)
          (by simpa only [hs] using M.selection_mem_part e g s))
      simpa only [hts] using hs.symm

def centerZone (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) : Finset (Fin n) :=
  if M.placement.IsInternal then
    D.part M.placement.leftPart \ DenseGraph.matchingEndpoints M.edges
  else M.firstEndpoints

theorem selectionVertex_mem_centerZone_iff
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B)
    (e : M.Edge) (f : M.Selection e) (t : M.Role) :
    M.selectionVertex e f t ∈ M.centerZone ↔ t = M.candidateCenter := by
  by_cases hc : M.placement.IsInternal
  · cases t with
    | inl t =>
        fin_cases t <;>
          simp [selectionVertex, centerZone, candidateCenter, hc,
            M.first_mem_endpoints e, M.second_mem_endpoints e]
    | inr t =>
        cases t with
        | none =>
            have hm := M.selection_mem_part e f none
            change f.val none ∈ D.part M.placement.leftPart at hm
            simp [selectionVertex, centerZone, candidateCenter, hc,
              M.selection_not_mem_endpoints e f, hm]
        | some t =>
            have hnot : f.val (some t) ∉ D.part M.placement.leftPart := by
              intro hh
              have hsame : D.SamePart (M.firstEndpoint e) (f.val (some t)) :=
                ⟨_, M.firstEndpoint_mem e, hh⟩
              exact SubcriticalDivision.not_activePair_of_samePart hsame
                (M.own_active_freeParent (M.firstEndpoint_mem e) t
                  (M.selection_mem_part e f (some t)))
            simp [selectionVertex, centerZone, candidateCenter, hc, hnot]
  · cases t with
    | inl t =>
        fin_cases t <;>
          simp [selectionVertex, centerZone, candidateCenter, hc,
            M.first_mem_firstEndpoints e, M.second_not_mem_firstEndpoints e]
    | inr t =>
        have hn : f.val t ∉ M.firstEndpoints :=
          fun h ↦ M.selection_not_mem_endpoints e f t (M.firstEndpoints_subset_endpoints h)
        simp [selectionVertex, centerZone, candidateCenter, hc, hn]

/-- One fixed coordinate-polarity set for every anchor and every clean
selection in this homogeneous matching. -/
def positiveCoordinates (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :
    Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun a ↦ ∃ x ∈ M.centerZone, x ∈ a.2.1

theorem present_subset_positiveCoordinates {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e : M.Edge) (f : M.Selection e) :
    (M.selectionWitness e f).present ⊆ M.positiveCoordinates := by
  intro a ha
  obtain ⟨i, j, hij, hstar⟩ := ((M.selectionWitness e f).mem_present a).mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases (SimpleGraph.starGraph_adj.mp hstar).2 with hi | hj
  · refine ⟨M.selectionVertex e f i, (M.selectionVertex_mem_centerZone_iff e f i).mpr hi, ?_⟩
    rw [hij]
    exact Sym2.mem_mk_left _ _
  · refine ⟨M.selectionVertex e f j, (M.selectionVertex_mem_centerZone_iff e f j).mpr hj, ?_⟩
    rw [hij]
    exact Sym2.mem_mk_right _ _

theorem absent_disjoint_positiveCoordinates {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e : M.Edge) (f : M.Selection e) :
    Disjoint (M.selectionWitness e f).absent M.positiveCoordinates := by
  apply Finset.disjoint_left.mpr
  intro a ha hp
  obtain ⟨i, j, hij, hne, hstar⟩ := ((M.selectionWitness e f).mem_absent a).mp ha
  obtain ⟨x, hx, hxa⟩ := (Finset.mem_filter.mp hp).2
  rw [hij] at hxa
  rcases Sym2.mem_iff.mp hxa with hxi | hxj
  · change x = M.selectionVertex e f i at hxi
    have hi := (M.selectionVertex_mem_centerZone_iff e f i).mp (hxi ▸ hx)
    exact hstar (SimpleGraph.starGraph_adj.mpr ⟨hne, Or.inl hi⟩)
  · change x = M.selectionVertex e f j at hxj
    have hj := (M.selectionVertex_mem_centerZone_iff e f j).mp (hxj ▸ hx)
    exact hstar (SimpleGraph.starGraph_adj.mpr ⟨hne, Or.inr hj⟩)

/-- Global compatibility is proved for distinct candidates as well as for
each individual event; a per-event polarity flip would not suffice. -/
theorem selections_globalPolarity {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e d : M.Edge) (f : M.Selection e) (g : M.Selection d) :
    Disjoint (M.selectionWitness e f).present (M.selectionWitness d g).absent :=
  (M.absent_disjoint_positiveCoordinates d g).symm.mono_left
    (M.present_subset_positiveCoordinates e f)

def globalFlip (M : SubcriticalHomogeneousResidualMatching D eta R₀ R B) :
    Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ \ M.positiveCoordinates

theorem present_disjoint_globalFlip {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e : M.Edge) (f : M.Selection e) :
    Disjoint (M.selectionWitness e f).present M.globalFlip := by
  apply Finset.disjoint_left.mpr
  intro a ha hg
  exact (Finset.mem_sdiff.mp hg).2 (M.present_subset_positiveCoordinates e f ha)

theorem absent_subset_globalFlip {p : SubcriticalProfile D eta R₀ theta}
    (M : SubcriticalHomogeneousResidualMatching D eta R₀ R p.roots)
    (e : M.Edge) (f : M.Selection e) :
    (M.selectionWitness e f).absent ⊆ M.globalFlip := by
  intro a ha
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
    fun hp ↦ Finset.disjoint_left.mp (M.absent_disjoint_positiveCoordinates e f) ha hp⟩

end SubcriticalHomogeneousResidualMatching
end InducedStars
