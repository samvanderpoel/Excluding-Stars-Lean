import InducedStars.Structure.Subcritical.LocalRootExclusions
import InducedStars.Structure.Subcritical.LocalInternalCompanions

/-!
# Strict local cardinal reserves

The paper's exceptional configurations are excluded using the actual
finite relocation identities. The high-negative nonadjacent comparison
retains every lost lower row. These auxiliary cardinality interfaces are not used by unified compensation.
-/

noncomputable section
open Finset
open scoped Classical
namespace InducedStars

variable {k n R₀ : ℕ} {hk : 3 ≤ k} {G : SimpleGraph (Fin n)}
  {D : SubcriticalDivision k (Fin n)} {L : AdmissibleBlockSequence k}
  {omega eta theta alpha delta epsilon : ℝ}

/-- A high-negative root has at least two upper/high-inside targets.
This packages exactly the sparse and two relocation exclusions. -/
theorem subcriticalHighNegative_upper_high_card_two_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (ha4 : alpha ≤ 1 / 4) (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta, 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hB : ∀ a ∈ D.visiblePartIndices theta, (p.roots.card : ℝ) ≤ alpha * (D.part a).card)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n), subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hsource : 2 ≤ (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ)) :
    2 ≤ (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card := by
  let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hvis : a ∈ D.visiblePartIndices theta :=
    hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have hown := (subcriticalOwn_highNegative_degree_bounds G v (D.part a) p.roots
    halpha.le ha4 (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
    (by linarith [htrim a hvis]) (by simpa only [hp.own_counts v hv] using hI)).1
  by_contra hn
  have hc : (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card ≤ 1 := by omega
  by_cases hu : (subcriticalUpperNeighborIndices p v hv).Nonempty
  · obtain ⟨r, hr⟩ := hu
    have huc : (subcriticalUpperNeighborIndices p v hv).card ≤ 1 := by omega
    have hunique : ∀ b ∈ subcriticalUpperNeighborIndices p v hv, b = r :=
      fun b hb ↦ Finset.card_le_one.mp huc b hb r hr
    have hh : subcriticalProfileHighInsideRows p alpha v hv = ∅ := by
      apply Finset.card_eq_zero.mp
      have := Finset.card_pos.mpr ⟨r, hr⟩
      omega
    have hadj := (subcriticalUniqueUpper_noHigh_adjacencies R hfree homega halpha ha5
      htheta hdelta hscale hret hp htrim v hv hown r hunique hh).2
    exact subcriticalHighNegative_upper_relocation_impossible hp hk halpha.le hsmall
      hminimal v hv r hr hunique (fun b hb ↦ subcriticalActivePart_symm (hadj b hb))
      hsource hbalance (hB a hvis) hI
  · have hu0 : subcriticalUpperNeighborIndices p v hv = ∅ := Finset.not_nonempty_iff_eq_empty.mp hu
    obtain ⟨s, hs⟩ := subcriticalHighNegative_active_nonlow_nonempty hp hk halpha.le
      hsmall hminimal v hv hsource hbalance (hB a hvis) hI
    have hsM : s ∈ subcriticalMediumNeighborIndices p v hv := by simpa [hu0] using hs
    obtain ⟨r, hr, _⟩ := subcriticalMediumNeighbor_highInside_of_noUpper R hfree homega
      halpha ha5 htheta hdelta hscale hret hp htrim v hv hown hu0 hsM
    have hhc : (subcriticalProfileHighInsideRows p alpha v hv).card ≤ 1 := by omega
    have hunique : ∀ b ∈ subcriticalProfileHighInsideRows p alpha v hv, b = r :=
      fun b hb ↦ Finset.card_le_one.mp hhc b hb r hr
    have hadj : ∀ b ∈ subcriticalMediumNeighborIndices p v hv, D.ActivePart r b := by
      intro b hb
      obtain ⟨c, hc, hbc⟩ := subcriticalMediumNeighbor_highInside_of_noUpper R hfree homega
        halpha ha5 htheta hdelta hscale hret hp htrim v hv hown hu0 hb
      exact hunique c hc ▸ subcriticalActivePart_symm hbc
    obtain ⟨hrIn, hrHigh⟩ := (mem_subcriticalProfileHighInsideRows p alpha v hv r).mp hr
    have hrRow : r ∈ subcriticalProfileRowIndices p v :=
      (mem_subcriticalProfileRowIndices p v r).mpr
        ((mem_subcriticalProfileInsideRows p v hv r).mp hrIn).1
    have hallowed := (D.mem_eligibleVisibleTargets eta R₀ theta v
      (p.retainedRoots_subset hv) r).mp ((hp.retained_row_iff v hv r).mp hrRow).1
    have hrnot : r ∉ D.closedPartIndices a := by
      intro h
      rcases (D.mem_closedPartIndices_iff a r).mp h with he | he
      · exact hallowed.2.1 he
      · exact hallowed.2.2 he
    exact subcriticalHighNegative_nonadjacent_relocation_impossible hp hk halpha.le
      hsmall hminimal v hv r hrnot hu0 hadj hsource hbalance (hB a hvis)
      (hB r hallowed.1) hI (by simpa only [hp.rowCount_eq_degree_of_mem hrRow] using hrHigh)

/-- A medium own row either has a small stored missing count or has the
strict two-target reserve. No entropy conclusion is assumed. -/
theorem subcriticalMediumNegative_small_or_upper_high_card_two_le
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta, 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n), subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hsource : 2 ≤ (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hIlo : 2 * alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ))
    (hIhi : ((p.ownCount v).val : ℝ) ≤ (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card) :
    ((p.ownCount v).val : ℝ) ≤ 2 * alpha * k *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card ∨
    2 ≤ (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card := by
  let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hvis : a ∈ D.visiblePartIndices theta :=
    hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have hbounds := subcriticalOwn_medium_degree_bounds G v (D.part a) p.roots halpha.le
    (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
    (Finset.mem_union_left _ hv) (by linarith [htrim a hvis])
    (by simpa only [hp.own_counts v hv] using hIlo)
    (by simpa only [hp.own_counts v hv] using hIhi)
  by_cases hc : 2 ≤ (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card
  · exact Or.inr hc
  left
  by_contra hlarge
  obtain ⟨r, hr⟩ := subcriticalMediumOwn_upper_nonempty R hfree homega halpha
    htheta hdelta hscale hret hp v hv hbounds.1 hbounds.2.1
  have huc : (subcriticalUpperNeighborIndices p v hv).card ≤ 1 := by omega
  have hunique : ∀ b ∈ subcriticalUpperNeighborIndices p v hv, b = r :=
    fun b hb ↦ Finset.card_le_one.mp huc b hb r hr
  have hh : subcriticalProfileHighInsideRows p alpha v hv = ∅ := by
    apply Finset.card_eq_zero.mp
    have := Finset.card_pos.mpr ⟨r, hr⟩
    omega
  have hadj := (subcriticalUniqueUpper_noHigh_adjacencies R hfree homega halpha ha5
    htheta hdelta hscale hret hp htrim v hv hbounds.2.2 r hunique hh).2
  exact subcriticalLargeOwn_upper_relocation_impossible hp hk halpha.le hminimal v hv r
    hr hunique (fun b hb ↦ subcriticalActivePart_symm (hadj b hb)) hsource hbalance
    (lt_of_not_ge hlarge)

/-- A high-degree bad root has a strict scalar reserve: an upper/high
target, or a strict deficit in the inside-row versus lower-label budget. -/
theorem subcriticalHighDegree_strict_card_reserve
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hfree : ¬ Regularity.InducedEmbeds (inducedStar k) G)
    (homega : omega ≤ 1) (halpha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (htheta : 0 < theta) (hdelta : delta ≤ subcriticalRowCountingTolerance k)
    (hscale : 8 ≤ alpha * theta * n)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (htrim : ∀ a ∈ D.visiblePartIndices theta, 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : Fin n) (hv : v ∈ p.retainedRoots)
    (hB : (p.roots.card : ℝ) + 1 ≤ alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : ((p.ownCount v).val : ℝ) < 2 * alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card) :
    1 ≤ (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card ∨
    (subcriticalProfileInsideRows p v hv).card < (subcriticalLowerNeighborIndices p v hv).card := by
  let a := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hdegree := subcriticalOwn_highDegree_lower G v (D.part a) p.roots halpha.le
    (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hB
    (by simpa only [hp.own_counts v hv] using hI)
  have hown : alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ) := by
    have hN : (0 : ℝ) ≤ (D.part a).card := Nat.cast_nonneg _
    nlinarith
  have hc := (subcriticalLocalNonlowBudget_of_own_degree R hfree homega halpha
    (by linarith) htheta hdelta hscale hret hp v hv hown).2
  by_cases ht : 1 ≤ (subcriticalUpperNeighborIndices p v hv).card +
      (subcriticalProfileHighInsideRows p alpha v hv).card
  · exact Or.inl ht
  right
  have hu : subcriticalUpperNeighborIndices p v hv = ∅ := Finset.card_eq_zero.mp (by omega)
  have hh : subcriticalProfileHighInsideRows p alpha v hv = ∅ := Finset.card_eq_zero.mp (by omega)
  have hi := subcriticalInsideRows_empty_of_noUpper_noHigh R hfree homega halpha ha5
    htheta hdelta hscale hret hp htrim v hv hu hh
  have hrows := hp.highDegree_rows_nonempty v hv halpha.le (by linarith) hI
  have hrowsCard := Finset.card_pos.mpr hrows
  have hsplit := subcriticalProfileRows_card_decomposition p v hv
  have hiCard : (subcriticalProfileInsideRows p v hv).card = 0 := by rw [hi]; simp
  omega

end InducedStars
