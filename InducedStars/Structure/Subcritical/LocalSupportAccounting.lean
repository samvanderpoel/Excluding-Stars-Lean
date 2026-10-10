import InducedStars.Structure.Subcritical.LocalSupport
import InducedStars.Structure.Subcritical.LocalRowCompanions

/-!
# Profile rows inside the full-degree support

Recorded positive rows and active upper/medium rows are disjoint targets.
Every full-degree high target is either the own part, an upper tail, or a
recorded high row. These two inclusions give the unified entropy coefficient.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}

/-- The two cardinality comparisons needed for the common component exponent. -/
theorem subcriticalUnifiedRootCounts
    (hp : RealizesSubcriticalProfile G alpha p) (ha : 0 < alpha) (ha5 : 5 * alpha ≤ 1)
    (hret : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    (htrim : ∀ a ∈ D.visiblePartIndices theta, 2 * (p.roots.card : ℝ) ≤ (D.part a).card)
    (v : V) (hv : v ∈ p.retainedRoots) :
    let own := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
    let H := subcriticalHighTargets G D alpha theta v own.1
    let M := subcriticalMediumTargets G D alpha theta v own.1
    (subcriticalProfileInsideRows p v hv).card +
        (subcriticalUpperNeighborIndices p v hv).card +
        (subcriticalMediumNeighborIndices p v hv).card +
        (if own ∈ H ∪ M then 1 else 0) ≤ H.card + M.card ∧
      H.card ≤ (subcriticalUpperNeighborIndices p v hv).card +
        (subcriticalProfileHighInsideRows p alpha v hv).card +
        (if own ∈ H then 1 else 0) := by
  dsimp only
  let own := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  let H := subcriticalHighTargets G D alpha theta v own.1
  let M := subcriticalMediumTargets G D alpha theta v own.1
  let U := subcriticalUpperNeighborIndices p v hv
  let Q := subcriticalMediumNeighborIndices p v hv
  let J := subcriticalProfileInsideRows p v hv
  let C := U ∪ Q ∪ J
  have hvis : own ∈ D.visiblePartIndices theta :=
    hret (D.retainedVertexPart_mem_retained eta R₀ v (p.retainedRoots_subset hv))
  have hvisible (a : D.PartIndex) (hai : a.1 = own.1) : a ∈ D.visiblePartIndices theta :=
    (D.mem_visiblePartIndices theta a).mpr (hai ▸ (D.mem_visiblePartIndices theta own).mp hvis)
  have hCcard : C.card = U.card + Q.card + J.card := by
    have hd : Disjoint (U ∪ Q) J := (hp.active_rows_disjoint v hv).mono
      (by
        intro a haC
        rcases Finset.mem_union.mp haC with hu | hm
        · exact Finset.filter_subset _ _ hu
        · exact Finset.sdiff_subset hm)
      (Finset.filter_subset _ _)
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_union_of_disjoint (subcriticalUpperMedium_disjoint p v hv)]
  have hown : own ∉ C := by
    intro h
    apply hp.own_not_mem_localCountedParts v hv
    rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.filter_subset _ _ h)
  have hC : C ⊆ H ∪ M := by
    intro a haC
    rcases Finset.mem_union.mp haC with haC | hj
    · rcases Finset.mem_union.mp haC with hu | hm
      · obtain ⟨hact, hd⟩ := (hp.upperNeighborIndices_iff v hv a).mp hu
        have hai := (SubcriticalDivision.activePart_same_component hact).symm
        exact Finset.mem_union_left _ ((mem_subcriticalHighTargets G D alpha theta v own.1 a).mpr
          ⟨hvisible a hai, hai, hd⟩)
      · obtain ⟨hact, ht⟩ := (mem_subcriticalMediumNeighborIndices p v hv a).mp hm
        have hai := (SubcriticalDivision.activePart_same_component hact).symm
        have hlo : alpha * (D.part a).card < (degreeInFinset G v (D.part a) : ℝ) := by
          apply lt_of_not_ge
          intro hh
          have hx := (hp.tail_labels v hv a hact).2.mpr hh
          rw [ht] at hx
          cases hx
        have hhi : (degreeInFinset G v (D.part a) : ℝ) < (1 - alpha) * (D.part a).card := by
          apply lt_of_not_ge
          intro hh
          have hx := (hp.tail_labels v hv a hact).1.mpr hh
          rw [ht] at hx
          cases hx
        exact Finset.mem_union_right _ ((mem_subcriticalMediumTargets G D alpha theta v own.1 a).mpr
          ⟨hvisible a hai, hai, hlo, hhi⟩)
    · obtain ⟨hr, hai⟩ := (mem_subcriticalProfileInsideRows p v hv a).mp hj
      have hd := hp.recorded_row_full_lower ((mem_subcriticalProfileRowIndices p v a).mpr hr)
      have hN : (0 : ℝ) < (D.part a).card := by exact_mod_cast (D.part_nonempty a).card_pos
      exact subcriticalDensitySupport_mem_of_degree_gt G D v own.1 a (hvisible a hai) hai
        (by nlinarith [mul_pos ha hN])
  have hH : H.erase own ⊆ U ∪ subcriticalProfileHighInsideRows p alpha v hv := by
    intro a haH
    obtain ⟨hne, haH⟩ := Finset.mem_erase.mp haH
    obtain ⟨hvisA, hai, hd⟩ := (mem_subcriticalHighTargets G D alpha theta v own.1 a).mp haH
    by_cases hact : D.ActivePart own a
    · exact Finset.mem_union_left _ ((hp.upperNeighborIndices_iff v hv a).mpr ⟨hact, hd⟩)
    · have hallowed : D.EligibleProfileTarget eta R₀ theta v a := by
        refine ⟨p.retainedRoots_subset hv, ?_⟩
        exact (D.mem_eligibleVisibleTargets eta R₀ theta v (p.retainedRoots_subset hv) a).mpr
          ⟨hvisA, hne, hact⟩
      obtain ⟨hr, hh⟩ := hp.high_allowed_recorded ha.le ha5 (htrim a hvisA)
        (Or.inl ⟨hv, hallowed⟩) hd
      exact Finset.mem_union_right _ ((mem_subcriticalProfileHighInsideRows p alpha v hv a).mpr
        ⟨(mem_subcriticalProfileInsideRows p v hv a).mpr
          ⟨(mem_subcriticalProfileRowIndices p v a).mp hr, hai⟩, hh⟩)
  constructor
  · have hcount : C.card + (if own ∈ H ∪ M then 1 else 0) ≤ (H ∪ M).card := by
      by_cases hs : own ∈ H ∪ M
      · have hh := Finset.card_le_card (Finset.insert_subset hs hC)
        rw [Finset.card_insert_of_notMem hown] at hh
        simpa only [if_pos hs] using hh
      · simpa only [if_neg hs, Nat.add_zero] using Finset.card_le_card hC
    rw [hCcard, Finset.card_union_of_disjoint
      (subcriticalHighMediumTargets_disjoint G D alpha theta v own.1)] at hcount
    change U.card + Q.card + J.card + (if own ∈ H ∪ M then 1 else 0) ≤
      H.card + M.card at hcount
    change J.card + U.card + Q.card + (if own ∈ H ∪ M then 1 else 0) ≤ H.card + M.card
    omega
  · have hh := (Finset.card_le_card hH).trans (Finset.card_union_le _ _)
    change H.card ≤ U.card + (subcriticalProfileHighInsideRows p alpha v hv).card +
      (if own ∈ H then 1 else 0)
    by_cases ho : own ∈ H
    · have hc := Finset.card_erase_add_one ho
      simp only [if_pos ho]
      omega
    · rw [Finset.erase_eq_of_notMem ho] at hh
      simpa only [if_neg ho, Nat.add_zero] using hh

end InducedStars
