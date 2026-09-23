import InducedStars.Structure.Subcritical.LocalRowData
import InducedStars.Structure.Subcritical.Nonlow

/-!
# Exact local non-low budgets

Paper: Claim `claim:local-nonlow-budget-K1k`. Actual global part indices
are counted, retaining recorded zero rows. The only graph-theoretic input
is the finite deterministic non-low theorem (proved by restricted free-vertex counting).
-/

noncomputable section
open Finset
open scoped Classical

namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}

theorem subcriticalActivePartIndices_card (a : D.PartIndex) :
    (Finset.univ.filter (D.ActivePart a)).card = k - 2 := by
  have heq : Finset.univ.filter (D.ActivePart a) =
      ((D.core a.1).graph.neighborFinset a.2).image
        (fun j ↦ (⟨a.1, j⟩ : D.PartIndex)) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ⟨i, u, v, ha, rfl, hadj⟩
      cases ha
      exact ⟨v, hadj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨a.1, a.2, j, rfl, rfl, hj⟩
  rw [heq, Finset.card_image_of_injective]
  · exact (D.core a.1).degree_eq a.2
  · intro x y h
    simpa using h

theorem subcriticalActiveNeighborIndices_card
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (subcriticalActiveNeighborIndices p v hv).card = k - 2 :=
  subcriticalActivePartIndices_card _

theorem subcriticalNeighborIndices_card_eq
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalLowerNeighborIndices p v hv).card +
      (subcriticalMediumNeighborIndices p v hv).card = k - 2 := by
  rw [subcriticalNeighborIndices_card_decomposition, subcriticalActiveNeighborIndices_card]

theorem RealizesSubcriticalProfile.retained_row_iff
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots)
    (a : D.PartIndex) : a ∈ subcriticalProfileRowIndices p v ↔
      a ∈ D.eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  rw [mem_subcriticalProfileRowIndices, h.retained_rows v hv]
  have he : D.EligibleProfileTarget eta R₀ theta v a ↔
      a ∈ D.eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) := by
    constructor
    · rintro ⟨hv', ha⟩
      exact ha
    · intro ha
      exact ⟨_, ha⟩
  simp only [he]
  split_ifs with hc
  · exact ⟨fun _ ↦ hc, fun _ ↦ rfl⟩
  · constructor
    · intro hf
      cases hf
    · intro hf
      exact False.elim (hc hf)

theorem RealizesSubcriticalProfile.outside_row_iff
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.outsideRoots)
    (a : D.PartIndex) : a ∈ subcriticalProfileRowIndices p v ↔
      a ∈ D.retainedPartIndices eta R₀ ∧
        4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
  rw [mem_subcriticalProfileRowIndices, h.outside_rows v hv]
  split_ifs <;> simp_all

theorem subcriticalActiveNeighbor_visible
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {a : D.PartIndex} (ha : a ∈ subcriticalActiveNeighborIndices p v hv) :
    a ∈ D.visiblePartIndices theta := by
  have hc := SubcriticalDivision.activePart_same_component
    ((mem_subcriticalActiveNeighborIndices p v hv a).mp ha)
  apply hret
  rw [D.mem_retainedPartIndices, ← hc]
  exact (D.mem_retainedPartIndices eta R₀ _).mp
    (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))

theorem subcriticalUpperMedium_disjoint
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots) :
    Disjoint (subcriticalUpperNeighborIndices p v hv)
      (subcriticalMediumNeighborIndices p v hv) := by
  apply Finset.disjoint_left.mpr
  intro a hu hm
  have hu' := (mem_subcriticalUpperNeighborIndices p v hv a).mp hu
  have hm' := (mem_subcriticalMediumNeighborIndices p v hv a).mp hm
  rw [hu'.2] at hm'
  cases hm'.2

theorem RealizesSubcriticalProfile.active_rows_disjoint
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots) :
    Disjoint (subcriticalActiveNeighborIndices p v hv) (subcriticalProfileRowIndices p v) := by
  apply Finset.disjoint_left.mpr
  intro a ha hr
  have he := ((D.mem_eligibleVisibleTargets eta R₀ theta v
    (p.retainedRoots_subset hv) a).mp ((h.retained_row_iff v hv a).mp hr).1).2.2
  exact he ((mem_subcriticalActiveNeighborIndices p v hv a).mp ha)

theorem RealizesSubcriticalProfile.upperMediumRows_subset_nonlow
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots)
    (halpha : 0 ≤ alpha) (halphaHalf : alpha ≤ 1 / 2)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta) :
    subcriticalUpperNeighborIndices p v hv ∪ subcriticalMediumNeighborIndices p v hv ∪
      subcriticalProfileRowIndices p v ⊆ subcriticalNonlowVisibleParts G D alpha theta v := by
  intro a ha
  apply (mem_subcriticalNonlowVisibleParts G D alpha theta v a).mpr
  rcases Finset.mem_union.mp ha with ha | ha
  · rcases Finset.mem_union.mp ha with ha | ha
    · have ht := (h.upperNeighborIndices_iff v hv a).mp ha
      refine ⟨subcriticalActiveNeighbor_visible p v hv hret (by simp [ht.1]), ?_⟩
      have hn : (0 : ℝ) ≤ (D.part a).card := Nat.cast_nonneg _
      nlinarith
    · have ht := (mem_subcriticalMediumNeighborIndices p v hv a).mp ha
      refine ⟨subcriticalActiveNeighbor_visible p v hv hret (by simp [ht.1]), ?_⟩
      have hl : ¬ (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card := by
        intro hl
        have he := (h.tail_labels v hv a ht.1).2.mpr hl
        rw [ht.2] at he
        cases he
      exact (lt_of_not_ge hl).le
  · have ht := (h.retained_row_iff v hv a).mp ha
    refine ⟨((D.mem_eligibleVisibleTargets eta R₀ theta v
      (p.retainedRoots_subset hv) a).mp ht.1).1, ?_⟩
    have hn : (0 : ℝ) ≤ alpha * (D.part a).card := mul_nonneg halpha (Nat.cast_nonneg _)
    linarith [ht.2]

theorem RealizesSubcriticalProfile.own_not_mem_localCountedParts
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots) :
    D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv) ∉
      subcriticalUpperNeighborIndices p v hv ∪ subcriticalMediumNeighborIndices p v hv ∪
        subcriticalProfileRowIndices p v := by
  intro ha
  rcases Finset.mem_union.mp ha with ha | ha
  · have hact : D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
        (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) := by
      rcases Finset.mem_union.mp ha with ha | ha
      · exact ((mem_subcriticalUpperNeighborIndices p v hv _).mp ha).1
      · exact ((mem_subcriticalMediumNeighborIndices p v hv _).mp ha).1
    simpa only [D.activePart_mk_mk, SimpleGraph.irrefl] using hact
  · exact ((D.mem_eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) _).mp
      ((h.retained_row_iff v hv _).mp ha).1).2.1 rfl

theorem subcriticalLocalCountedParts_card
    {G : SimpleGraph V} {p : SubcriticalProfile D eta R₀ theta}
    (h : RealizesSubcriticalProfile G alpha p) (v : V) (hv : v ∈ p.retainedRoots) :
    (subcriticalUpperNeighborIndices p v hv ∪ subcriticalMediumNeighborIndices p v hv ∪
      subcriticalProfileRowIndices p v).card =
      (subcriticalUpperNeighborIndices p v hv).card +
        (subcriticalMediumNeighborIndices p v hv).card +
        (subcriticalProfileInsideRows p v hv).card +
        (subcriticalProfileOutsideRows p v hv).card := by
  have hd : Disjoint (subcriticalUpperNeighborIndices p v hv ∪
      subcriticalMediumNeighborIndices p v hv) (subcriticalProfileRowIndices p v) :=
    (h.active_rows_disjoint v hv).mono_left (by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact Finset.filter_subset _ _ ha
      · exact Finset.sdiff_subset ha)
  rw [Finset.card_union_of_disjoint hd,
    Finset.card_union_of_disjoint (subcriticalUpperMedium_disjoint p v hv),
    ← subcriticalProfileRows_card_decomposition p v hv]
  omega

section Finite
variable {n : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ} {R₀ : ℕ}

/-- Paper: Claim `claim:local-nonlow-budget-K1k`, both ordinary exact
cardinality inequalities, proved from genuine finite close geometry. -/
theorem subcriticalLocalNonlowBudget
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaHalf : alpha ≤ 1 / 2)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.retainedRoots) :
    (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalMediumNeighborIndices p v hv).card +
      (subcriticalProfileInsideRows p v hv).card +
      (subcriticalProfileOutsideRows p v hv).card ≤ k - 1 ∧
    (subcriticalProfileInsideRows p v hv).card +
      (subcriticalProfileOutsideRows p v hv).card ≤
        (subcriticalLowerNeighborIndices p v hv).card + 1 := by
  have hb := (Finset.card_le_card
    (h.upperMediumRows_subset_nonlow v hv halpha.le halphaHalf hret)).trans
    (subcriticalNonlowVisibleParts_card_le hk R hfree homega halpha htheta hdelta hscale v)
  rw [subcriticalLocalCountedParts_card h v hv] at hb
  have hc := subcriticalNeighborIndices_card_eq p v hv
  exact ⟨hb, by omega⟩

/-- Paper: Claim `claim:local-nonlow-budget-K1k`, strengthened by the
additional distinct non-low own part. No divisibility or asymptotic error. -/
theorem subcriticalLocalNonlowBudget_of_own_degree
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (halphaHalf : alpha ≤ 1 / 2)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (h : RealizesSubcriticalProfile G alpha p)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hown : alpha * (D.part (D.retainedVertexPart eta R₀ v
        (p.retainedRoots_subset hv))).card ≤
      (degreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v
        (p.retainedRoots_subset hv))) : ℝ)) :
    (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalMediumNeighborIndices p v hv).card +
      (subcriticalProfileInsideRows p v hv).card +
      (subcriticalProfileOutsideRows p v hv).card ≤ k - 2 ∧
    (subcriticalProfileInsideRows p v hv).card +
      (subcriticalProfileOutsideRows p v hv).card ≤
        (subcriticalLowerNeighborIndices p v hv).card := by
  have hins : insert (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
      (subcriticalUpperNeighborIndices p v hv ∪ subcriticalMediumNeighborIndices p v hv ∪
        subcriticalProfileRowIndices p v) ⊆ subcriticalNonlowVisibleParts G D alpha theta v := by
    apply Finset.insert_subset
    · exact (mem_subcriticalNonlowVisibleParts G D alpha theta v _).mpr
        ⟨hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv)), hown⟩
    · exact h.upperMediumRows_subset_nonlow v hv halpha.le halphaHalf hret
  have hb := (Finset.card_le_card hins).trans
    (subcriticalNonlowVisibleParts_card_le hk R hfree homega halpha htheta hdelta hscale v)
  rw [Finset.card_insert_of_notMem (h.own_not_mem_localCountedParts v hv),
    subcriticalLocalCountedParts_card h v hv] at hb
  have hc := subcriticalNeighborIndices_card_eq p v hv
  constructor <;> omega

end Finite
end InducedStars
