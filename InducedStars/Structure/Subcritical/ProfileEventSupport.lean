import InducedStars.Structure.Subcritical.ProfileExponents
import InducedStars.Structure.Subcritical.ActiveModelsRecovery
import DenseGraph.FiniteModels.BernoulliEvents

/-!
# Coordinate supports of profile events

Paper: the independence step in `lemma:fixed-profile-probability-K1k`.
Residual safety tests only induced stars whose entire image avoids
the profile roots. Tail targets delete every root. These two restrictions
give the literal disjoint-coordinate independence proved here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Set
open scoped BigOperators Classical
open DenseGraph.FiniteBernoulliProduct

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta : ℝ} {R₀ : ℕ}

/-- The exact coordinates from a root into one trimmed target. -/
def subcriticalTailCoordinates (p : SubcriticalProfile D eta R₀ theta)
    (v : V) (a : D.PartIndex) : Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun e ↦ ∃ y ∈ D.part a \ p.roots, e.2.1 = s(v, y)

/-- A common support for all tail events at one root. -/
def subcriticalRootTailCoordinates (p : SubcriticalProfile D eta R₀ theta)
    (v : V) : Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun e ↦ ∃ y ∉ p.roots, e.2.1 = s(v, y)

/-- All random coordinates whose two endpoints avoid every profile root. -/
def subcriticalResidualCoordinates (p : SubcriticalProfile D eta R₀ theta) :
    Finset (SubcriticalActiveCoordinate D eta R₀) :=
  Finset.univ.filter fun e ↦ ∀ x ∈ e.2.1, x ∉ p.roots

private theorem selectedEdges_mem_congr
    {S U A : Finset (SubcriticalActiveCoordinate D eta R₀)}
    (h : S ∩ A = U ∩ A) {z : Sym2 V}
    (hz : ∀ e : SubcriticalActiveCoordinate D eta R₀, e.2.1 = z → e ∈ A) :
    z ∈ S.image (fun e ↦ e.2.1) ↔ z ∈ U.image (fun e ↦ e.2.1) := by
  have hagree (e : SubcriticalActiveCoordinate D eta R₀) (he : e ∈ A) :
      e ∈ S ↔ e ∈ U := by
    simpa only [Finset.mem_inter, he, and_true] using Finset.ext_iff.mp h e
  simp only [Finset.mem_image]
  exact ⟨fun ⟨e, he, heq⟩ ↦ ⟨e, (hagree e (hz e heq)).mp he, heq⟩,
    fun ⟨e, he, heq⟩ ↦ ⟨e, (hagree e (hz e heq)).mpr he, heq⟩⟩

theorem subcriticalTailDegree_eq_of_agree
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex)
    {S U : Finset (SubcriticalActiveCoordinate D eta R₀)}
    (h : S ∩ subcriticalTailCoordinates p v a =
      U ∩ subcriticalTailCoordinates p v a) :
    subcriticalTailDegree p v a S = subcriticalTailDegree p v a U := by
  unfold subcriticalTailDegree
  congr 1
  apply Finset.filter_congr
  intro y hy
  exact selectedEdges_mem_congr h (fun e he ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ e, y, hy, he⟩)

theorem subcriticalTailEvent_supportedOn
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ)
    (v : V) (a : D.PartIndex) (t : SubcriticalTailDirection) :
    EventSupportedOn (subcriticalTailEvent p alpha v a t)
      (subcriticalTailCoordinates p v a) := by
  intro S U h
  have heq := subcriticalTailDegree_eq_of_agree p v a h
  cases t <;> simp only [subcriticalTailEvent, Finset.mem_filter, Finset.mem_univ,
    true_and, heq]

theorem subcriticalTailCoordinates_subset_root
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (a : D.PartIndex) :
    subcriticalTailCoordinates p v a ⊆ subcriticalRootTailCoordinates p v := by
  intro e he
  obtain ⟨y, hy, heq⟩ := (Finset.mem_filter.mp he).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, y, (Finset.mem_sdiff.mp hy).2, heq⟩

theorem subcriticalRootTailEvent_supportedOn
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) (v : V) :
    EventSupportedOn (subcriticalRootTailEvent p alpha v)
      (subcriticalRootTailCoordinates p v) := by
  intro S U hagree
  simp only [subcriticalRootTailEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  apply forall_congr'
  intro a
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro _
  exact ((subcriticalTailEvent_supportedOn p alpha v a t).mono
    (subcriticalTailCoordinates_subset_root p v a)) S U hagree

/-- Deleting all roots from targets makes different root-coordinate sets
disjoint, even when their active blocks coincide. -/
theorem subcriticalRootTailCoordinates_disjoint
    (p : SubcriticalProfile D eta R₀ theta) {v w : V}
    (hv : v ∈ p.roots) (hw : w ∈ p.roots) (hne : v ≠ w) :
    Disjoint (subcriticalRootTailCoordinates p v) (subcriticalRootTailCoordinates p w) := by
  rw [Finset.disjoint_left]
  intro e he hf
  obtain ⟨x, hx, heq⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨y, hy, hfq⟩ := (Finset.mem_filter.mp hf).2
  have heq' := (Sym2.mk_eq_mk_iff (p := (v, x)) (q := (w, y))).mp
    (heq.symm.trans hfq)
  simp only [Prod.mk.injEq, Prod.swap_prod_mk] at heq'
  rcases heq' with ⟨hvw, _⟩ | ⟨hvy, _⟩
  · exact hne hvw
  · exact hy (hvy ▸ hv)

theorem subcriticalRootTailCoordinates_disjoint_residual
    (p : SubcriticalProfile D eta R₀ theta) {v : V} (hv : v ∈ p.roots) :
    Disjoint (subcriticalRootTailCoordinates p v) (subcriticalResidualCoordinates p) := by
  rw [Finset.disjoint_left]
  intro e he hf
  obtain ⟨y, _, heq⟩ := (Finset.mem_filter.mp he).2
  exact (Finset.mem_filter.mp hf).2 v (heq ▸ Sym2.mem_mk_left v y) hv

/-- Realized adjacency away from the roots depends only on the residual
coordinate support; deterministic defects need not be valid for this fact. -/
theorem subcriticalActiveGraph_adj_eq_of_agree_away_roots
    (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    {mvec : RetainedEdgeCountVector D eta R₀}
    {S U : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate}
    (h : S ∩ subcriticalResidualCoordinates p = U ∩ subcriticalResidualCoordinates p)
    {x y : V} (hx : x ∉ p.roots) (hy : y ∉ p.roots) :
    (subcriticalActiveBernoulliGraphFromOutcome H T S).Adj x y ↔
      (subcriticalActiveBernoulliGraphFromOutcome H T U).Adj x y := by
  have heq := selectedEdges_mem_congr h (z := s(x, y)) (by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ e, ?_⟩
    simpa only [he, Sym2.mem_iff, forall_eq_or_imp, forall_eq] using And.intro hx hy)
  simp only [subcriticalActiveBernoulliGraphFromOutcome,
    subcriticalGraphFromActiveEdges_adj, subcriticalActiveSelectedEdges,
    Finset.mem_image] at heq ⊢
  apply and_congr _ Iff.rfl
  exact Iff.of_eq (congrArg (fun q : Prop ↦ q ≠ T.Adj x y)
    (propext (or_congr Iff.rfl (or_congr Iff.rfl heq))))

/-- Root-avoiding safety is invariant under agreement of the induced graphs
away from the roots. This retains arbitrary induced star embeddings. -/
theorem subcriticalResidualSafeAwayFromRoots_congr
    (p : SubcriticalProfile D eta R₀ theta) (R : SimpleGraph V)
    {G G' : SimpleGraph V}
    (h : ∀ x ∉ p.roots, ∀ y ∉ p.roots, G.Adj x y ↔ G'.Adj x y) :
    G ∈ subcriticalResidualSafeAwayFromRootsEvent p R ↔
      G' ∈ subcriticalResidualSafeAwayFromRootsEvent p R := by
  have transfer {G₁ G₂ : SimpleGraph V}
      (hadj : ∀ x ∉ p.roots, ∀ y ∉ p.roots, G₁.Adj x y ↔ G₂.Adj x y)
      (hsafe : G₁ ∈ subcriticalResidualSafeAwayFromRootsEvent p R) :
      G₂ ∈ subcriticalResidualSafeAwayFromRootsEvent p R := by
    intro f hf
    let f' : inducedStar k ↪g G₁ :=
      { toFun := f
        inj' := f.injective
        map_rel_iff' := by
          intro i j
          exact (hadj (f i) (hf i) (f j) (hf j)).trans f.map_rel_iff }
    exact hsafe f' hf
  exact ⟨transfer h, transfer (fun x hx y hy ↦ (h x hx y hy).symm)⟩

/-- The pulled-back residual event uses only active pairs whose
two endpoints avoid every profile root. -/
theorem subcriticalResidualSafeEvent_supportedOn
    (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (T R : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    EventSupportedOn
      (subcriticalActiveGraphEvent H T mvec (subcriticalResidualSafeAwayFromRootsEvent p R))
      (subcriticalResidualCoordinates p) := by
  intro S U hagree
  simp only [subcriticalActiveGraphEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact subcriticalResidualSafeAwayFromRoots_congr p R
    (fun x hx y hy ↦ subcriticalActiveGraph_adj_eq_of_agree_away_roots p H T hagree hx hy)

theorem subcriticalAllTailEvents_eq_intersection
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ) :
    subcriticalAllTailEvents p alpha =
      eventIntersection p.retainedRoots (subcriticalRootTailEvent p alpha) := by
  ext S
  simp only [subcriticalAllTailEvents, eventIntersection, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- Full exact independence of all root tails and the root-avoiding residual
event. The remainder and deterministic defects are arbitrary here. -/
theorem subcriticalTailResidual_probability_eq_prod
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (TB R L : SimpleGraph V)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    (subcriticalActiveBernoulliModel mvec).eventProbability
      (subcriticalAllTailEvents p alpha ∩
        subcriticalActiveGraphEvent H (TB ⊔ R ⊔ L) mvec
          (subcriticalResidualSafeAwayFromRootsEvent p R)) =
      (∏ v ∈ p.retainedRoots, subcriticalRootTailProbability p alpha v mvec) *
        subcriticalResidualSafeProbability p H TB R L mvec := by
  have htail := EventSupportedOn.eventIntersection p.retainedRoots
    (subcriticalRootTailEvent p alpha) (subcriticalRootTailCoordinates p)
    (fun v _ ↦ subcriticalRootTailEvent_supportedOn p alpha v)
  have hdis : Disjoint (p.retainedRoots.biUnion (subcriticalRootTailCoordinates p))
      (subcriticalResidualCoordinates p) := by
    rw [Finset.disjoint_biUnion_left]
    intro v hv
    exact subcriticalRootTailCoordinates_disjoint_residual p (Finset.mem_union_left _ hv)
  have hpair : Set.PairwiseDisjoint (↑p.retainedRoots) (subcriticalRootTailCoordinates p) := by
    intro v hv w hw hne
    exact subcriticalRootTailCoordinates_disjoint p
      (Finset.mem_union_left _ hv) (Finset.mem_union_left _ hw) hne
  rw [subcriticalAllTailEvents_eq_intersection,
    (subcriticalActiveBernoulliModel mvec).eventProbability_inter_eq_mul_of_disjoint_support
      htail (subcriticalResidualSafeEvent_supportedOn p H (TB ⊔ R ⊔ L) R mvec) hdis,
    (subcriticalActiveBernoulliModel mvec).eventProbability_intersection_eq_prod
      p.retainedRoots (subcriticalRootTailEvent p alpha) (subcriticalRootTailCoordinates p)
      (fun v _ ↦ subcriticalRootTailEvent_supportedOn p alpha v) hpair]
  rfl

/-- Literal graph-side relaxed tails, with the original full part size on
the right-hand side and the root-deleted target inside the degree. -/
def subcriticalProfileTailGraphEvent (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) : Set (SimpleGraph V) :=
  {G | ∀ v ∈ p.retainedRoots, ∀ a t, p.tails v a = some t → match t with
    | .upper => (1 - 2 * alpha) * (D.part a).card ≤
        (degreeInFinset G v (D.part a \ p.roots) : ℝ)
    | .lower => (degreeInFinset G v (D.part a \ p.roots) : ℝ) ≤
        2 * alpha * (D.part a).card}

/-- The exact probability event for a fixed profile. Root-avoiding residual safety restricts only
the residual star witnesses to the complement of the roots. -/
def subcriticalProfileProbabilityEvent (p : SubcriticalProfile D eta R₀ theta)
    (alpha : ℝ) (R : SimpleGraph V) : Set (SimpleGraph V) :=
  subcriticalProfileTailGraphEvent p alpha ∩ subcriticalResidualSafeAwayFromRootsEvent p R

/-- A labeled tail lies entirely in active coordinates, so valid fixed
defects and the deterministic remainder leave its sampled degree unchanged. -/
theorem subcriticalTailDegree_eq_realized_degree
    (p : SubcriticalProfile D eta R₀ theta)
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    {mvec : RetainedEdgeCountVector D eta R₀}
    (S : Finset (subcriticalActiveFixedBlockModel mvec).Coordinate)
    {v : V} {a : D.PartIndex} {t : SubcriticalTailDirection}
    (ht : p.tails v a = some t) :
    subcriticalTailDegree p v a S =
      degreeInFinset (subcriticalActiveBernoulliGraphFromOutcome H T S)
        v (D.part a \ p.roots) := by
  obtain ⟨hv, hactive⟩ := p.tails_valid v a t ht
  unfold subcriticalTailDegree degreeInFinset
  congr 1
  apply Finset.filter_congr
  intro y hy
  have hA : s(v, y) ∈ retainedActiveEdgeUniverse D eta R₀ :=
    (mk_mem_retainedActiveEdgeUniverse_iff D eta R₀ v y).mpr
      ⟨(D.activePair_iff_of_mem_parts
        (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
        (Finset.mem_sdiff.mp hy).1).mpr hactive, p.retainedRoots_subset hv⟩
  have heq := Finset.ext_iff.mp (subcriticalGraphFromActiveEdges_active_edges H T hT
    (subcriticalActiveSelectedEdges_subset S)) s(v, y)
  simp only [Finset.mem_inter, hA, and_true, mk_mem_finiteGraphEdges] at heq
  simp only [subcriticalActiveBernoulliGraphFromOutcome,
    subcriticalGraphFromActiveEdges_adj, subcriticalActiveSelectedEdges,
    Finset.mem_image] at heq ⊢
  exact heq.symm

/-- Equality of graph tails and outcome tails. This records the independence
of tail probabilities from the valid deterministic data `H,T`. -/
theorem subcriticalProfileTailGraphEvent_pullback
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (T : SimpleGraph V)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalActiveGraphEvent H T mvec (subcriticalProfileTailGraphEvent p alpha) =
      subcriticalAllTailEvents p alpha := by
  ext S
  simp only [subcriticalActiveGraphEvent, subcriticalProfileTailGraphEvent,
    subcriticalAllTailEvents, subcriticalRootTailEvent, Finset.mem_filter,
    Finset.mem_univ, true_and, Set.mem_setOf_eq]
  apply forall₂_congr
  intro v _
  apply forall_congr'
  intro a
  apply forall_congr'
  intro t
  apply imp_congr_right
  intro ht
  have heq := subcriticalTailDegree_eq_realized_degree p H T hT S ht
  cases t <;> simp only [subcriticalTailEvent, Finset.mem_filter,
    Finset.mem_univ, true_and, heq]

theorem subcriticalProfileProbabilityEvent_pullback
    (p : SubcriticalProfile D eta R₀ theta) (alpha : ℝ)
    (H : SubcriticalRemainderGraph D eta R₀) (T R : SimpleGraph V)
    (hT : IsSubcriticalRetainedDefectPattern D eta R₀ T)
    (mvec : RetainedEdgeCountVector D eta R₀) :
    subcriticalActiveGraphEvent H T mvec (subcriticalProfileProbabilityEvent p alpha R) =
      subcriticalAllTailEvents p alpha ∩ subcriticalActiveGraphEvent H T mvec
        (subcriticalResidualSafeAwayFromRootsEvent p R) := by
  rw [← subcriticalProfileTailGraphEvent_pullback p alpha H T hT mvec]
  ext S
  simp only [subcriticalActiveGraphEvent, subcriticalProfileProbabilityEvent,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff, Finset.mem_inter]

/-- Close-geometry size bounds give the exact root-deletion reserve for
every labeled tail target. An active neighbor belongs to the same retained
component as its root, so it is one of the visible parts covered by `hpart`. -/
theorem subcriticalProfile_tailTrim_of_geometry
    (p : SubcriticalProfile D eta R₀ theta) {alpha rho : ℝ}
    (halpha : 0 ≤ alpha)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (hpart : ∀ a ∈ D.visiblePartIndices theta,
      theta * (Fintype.card V : ℝ) / 2 ≤ ((D.part a).card : ℝ))
    (hroot : (p.roots.card : ℝ) ≤ rho * Fintype.card V)
    (hrho : rho ≤ alpha * theta / 2) :
    ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card := by
  intro v a t ht
  obtain ⟨hv, hactive⟩ := p.tails_valid v a t ht
  have hcomponent := SubcriticalDivision.activePart_same_component hactive
  have ha : a ∈ D.retainedPartIndices eta R₀ := by
    apply (D.mem_retainedPartIndices eta R₀ a).mpr
    rw [← hcomponent]
    exact (D.mem_retainedPartIndices eta R₀ _).mp
      (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  calc
    (p.roots.card : ℝ) ≤ rho * Fintype.card V := hroot
    _ ≤ (alpha * theta / 2) * Fintype.card V :=
      mul_le_mul_of_nonneg_right hrho (Nat.cast_nonneg _)
    _ = alpha * (theta * Fintype.card V / 2) := by ring
    _ ≤ alpha * (D.part a).card := mul_le_mul_of_nonneg_left (hpart a (hret ha)) halpha

/-- Every realized profile satisfies its relaxed graph-tail event once the
root set is at most `alpha` times each labeled target. -/
theorem RealizesSubcriticalProfile.mem_tailGraphEvent
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta} {alpha : ℝ}
    (h : RealizesSubcriticalProfile G alpha p) (halpha : 0 ≤ alpha)
    (htrim : ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card) :
    G ∈ subcriticalProfileTailGraphEvent p alpha := by
  intro v hv a t ht
  obtain ⟨hv', hactive⟩ := p.tails_valid v a t ht
  have hlabel := h.tail_labels v hv' a hactive
  cases t with
  | upper =>
      exact subcriticalUpperTail_trimmed G v (D.part a) p.roots
        (htrim v a .upper ht) (hlabel.1.mp ht)
  | lower =>
      exact subcriticalLowerTail_trimmed G v (D.part a) p.roots
        halpha (hlabel.2.mp ht)

/-- One-way containment only: induced-free profile graphs satisfy all
relaxed tails and root-avoiding residual safety. -/
theorem RealizesSubcriticalProfile.mem_probabilityEvent
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta} {alpha : ℝ}
    (h : RealizesSubcriticalProfile G alpha p) (halpha : 0 ≤ alpha)
    (htrim : ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G) (R : SimpleGraph V) :
    G ∈ subcriticalProfileProbabilityEvent p alpha R :=
  ⟨h.mem_tailGraphEvent halpha htrim,
    subcriticalResidualSafeAwayFromRoots_of_induced_free p R G hfree⟩

/-- Actual profile graphs are exact fixed-model outcomes satisfying the
probability event; no converse realization claim is made. -/
theorem subcriticalProfileGraph_actual_probabilityEvent
    (F : Finset (SimpleGraph V)) (p : SubcriticalProfile D eta R₀ theta)
    {alpha : ℝ} {G : SimpleGraph V}
    (hG : G ∈ subcriticalProfileClassGraphFinset F alpha p) (halpha : 0 ≤ alpha)
    (htrim : ∀ v a t, p.tails v a = some t →
      (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G) :
    subcriticalActiveGraphFromOutcome (subcriticalRemainderGraph G D eta R₀)
        (subcriticalRetainedIncidentDefectGraph G D eta R₀)
        (subcriticalActualActiveSample G D eta R₀) = G ∧
      G ∈ subcriticalProfileProbabilityEvent p alpha
        (subcriticalResidualDefectGraph G D eta R₀ theta alpha) :=
  ⟨subcriticalActiveGraphFromOutcome_actual G D eta R₀,
    (mem_subcriticalProfileClassGraphFinset.mp hG).2.mem_probabilityEvent halpha htrim hfree _⟩

end InducedStars
