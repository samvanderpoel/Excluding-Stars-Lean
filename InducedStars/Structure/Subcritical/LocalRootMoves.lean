import InducedStars.Structure.Subcritical.LocalRootGeometry

/-!
# Exact retained-root relocations

Rows enter and leave the active neighborhood according to the actual core.
For a nonadjacent target, the old own part becomes inactive. Every lost row remains explicit in the exact identity used by the unified zero-deficit placement argument.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact combined-defect degree: close rows are the own part and the
actual active core neighbors. Own missing edges replace own present edges. -/
theorem subcriticalDefect_degree_add_closed_degree_eq
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {v : V} {a : D.PartIndex} (hv : v ∈ D.part a) :
    (subcriticalCombinedDefectGraph G D).degree v +
        degreeInFinset G v (D.closedPartVertices a) =
      G.degree v + complementDegreeInFinset G v (D.part a) := by
  let N := D.closedPartVertices a
  let C := (D.part a).filter fun y ↦ y ≠ v ∧ ¬ G.Adj v y
  have heq : (subcriticalCombinedDefectGraph G D).neighborFinset v =
      (G.neighborFinset v \ N) ∪ C := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, subcriticalCombinedDefectGraph_adj_iff,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter, N, C,
      D.mem_closedPartVertices_iff hv]
    have hs : D.SamePart v y ↔ y ∈ D.part a := by
      constructor
      · rintro ⟨b, hvb, hyb⟩
        rwa [D.mem_part_unique hvb hv] at hyb
      · intro hy
        exact ⟨a, hv, hy⟩
    have hne : G.Adj v y → v ≠ y := SimpleGraph.Adj.ne
    have hne' : (v ≠ y) ↔ (y ≠ v) := ne_comm
    rw [hs]
    tauto
  have hdis : Disjoint (G.neighborFinset v \ N) C := by
    apply Finset.disjoint_left.mpr
    intro y hy hC
    exact (Finset.mem_sdiff.mp hy).2
      (D.part_subset_closedPartVertices a (Finset.mem_filter.mp hC).1)
  have hc := congrArg Finset.card heq
  rw [Finset.card_union_of_disjoint hdis, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset v) N
  have hinter : (G.neighborFinset v ∩ N).card = degreeInFinset G v N := by
    congr 1
    ext y
    simp [degreeInFinset, and_comm]
  rw [hinter, SimpleGraph.card_neighborFinset_eq_degree] at hp
  change (subcriticalCombinedDefectGraph G D).degree v + degreeInFinset G v N =
    G.degree v + C.card
  omega

/-- Disjoint division parts make the close-row degree sum exact. -/
theorem degreeInFinset_closedParts_eq_sum (G : SimpleGraph V)
    (D : SubcriticalDivision k V) (v : V) (a : D.PartIndex) :
    degreeInFinset G v (D.closedPartVertices a) =
      ∑ b ∈ D.closedPartIndices a, degreeInFinset G v (D.part b) := by
  have heq : (D.closedPartVertices a).filter (G.Adj v) =
      (D.closedPartIndices a).biUnion fun b ↦ (D.part b).filter (G.Adj v) := by
    ext y
    simp only [Finset.mem_filter, SubcriticalDivision.closedPartVertices, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨b, hb, hy⟩, hG⟩
      exact ⟨b, hb, hy, hG⟩
    · rintro ⟨b, hb, hy, hG⟩
      exact ⟨⟨b, hb, hy⟩, hG⟩
  rw [degreeInFinset, heq, Finset.card_biUnion]
  · rfl
  · intro b _ c _ hbc
    exact (D.part_disjoint hbc).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- Moving the root does not change its present degree into the target's
closed rows: only memberships of the root itself change, and there is no loop. -/
theorem subcriticalMove_closed_degree_eq
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (target : D.PartIndex) (hvalid) :
    degreeInFinset G v ((D.moveVertex v (some target) hvalid).closedPartVertices target) =
      degreeInFinset G v (D.closedPartVertices target) := by
  unfold degreeInFinset
  congr 1
  ext y
  by_cases hy : y = v
  · subst y
    simp
  · have hpart : ∀ b : D.PartIndex,
        y ∈ (D.moveVertex v (some target) hvalid).part b ↔ y ∈ D.part b :=
      fun b ↦ D.moveVertex_mem_part_of_ne v (some target) hvalid hy b
    simp only [Finset.mem_filter, SubcriticalDivision.closedPartVertices, Finset.mem_biUnion]
    change ((∃ b : D.PartIndex, b ∈ D.closedPartIndices target ∧
      y ∈ (D.moveVertex v (some target) hvalid).part b) ∧ G.Adj v y) ↔ _
    simp only [hpart]

/-- Exact relocation identity before cancelling the common close rows. -/
theorem subcriticalDefectCost_movePartToPart_closed_identity
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) :
    subcriticalDefectCost G (D.movePartToPart v source target hv hsource) +
        complementDegreeInFinset G v (D.part source) +
        (∑ b ∈ D.closedPartIndices target, degreeInFinset G v (D.part b)) =
      subcriticalDefectCost G D + complementDegreeInFinset G v (D.part target) +
        (∑ b ∈ D.closedPartIndices source, degreeInFinset G v (D.part b)) := by
  let E := D.movePartToPart v source target hv hsource
  have hvE : v ∈ E.part target := by simp [E, SubcriticalDivision.movePartToPart]
  have hcost := subcriticalDefectCost_moveVertex G D v (some target)
    (fun b _ ↦ D.erase_nonempty_of_source hv hsource b)
  have hold := subcriticalDefect_degree_add_closed_degree_eq G D hv
  have hnew := subcriticalDefect_degree_add_closed_degree_eq G E hvE
  have hcomp : complementDegreeInFinset G v (E.part target) =
      complementDegreeInFinset G v (D.part target) := by
    simp [E, SubcriticalDivision.movePartToPart, SubcriticalDivision.movedPart]
  have hclosed : degreeInFinset G v (E.closedPartVertices target) =
      degreeInFinset G v (D.closedPartVertices target) :=
    subcriticalMove_closed_degree_eq G D v target _
  rw [hcomp, hclosed] at hnew
  rw [degreeInFinset_closedParts_eq_sum] at hold hnew
  change subcriticalDefectCost G E + (subcriticalCombinedDefectGraph G D).degree v =
    subcriticalDefectCost G D + (subcriticalCombinedDefectGraph G E).degree v at hcost
  change subcriticalDefectCost G E + _ + _ = _
  omega

/-- Exact cost change: new active/clique rows supply gains, while old
active/clique rows lost at the destination supply losses. This identity
works whether or not source and destination are core-adjacent. -/
theorem subcriticalDefectCost_movePartToPart_row_identity
    (G : SimpleGraph V) (D : SubcriticalDivision k V) (v : V)
    (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) :
    subcriticalDefectCost G (D.movePartToPart v source target hv hsource) +
        complementDegreeInFinset G v (D.part source) +
        (∑ b ∈ D.closedPartIndices target \ D.closedPartIndices source,
          degreeInFinset G v (D.part b)) =
      subcriticalDefectCost G D + complementDegreeInFinset G v (D.part target) +
        (∑ b ∈ D.closedPartIndices source \ D.closedPartIndices target,
          degreeInFinset G v (D.part b)) := by
  have h := subcriticalDefectCost_movePartToPart_closed_identity G D v source target hv hsource
  have hs := Finset.sum_sdiff (f := fun b ↦ degreeInFinset G v (D.part b))
    (Finset.inter_subset_left : D.closedPartIndices source ∩ D.closedPartIndices target ⊆ _)
  have ht := Finset.sum_sdiff (f := fun b ↦ degreeInFinset G v (D.part b))
    (Finset.inter_subset_right : D.closedPartIndices source ∩ D.closedPartIndices target ⊆ _)
  simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at hs ht
  omega

/-- Minimality leaves a concrete lost-row budget. No assertion that an
eligible old-own row becomes active is used. -/
theorem subcriticalMinimal_relocation_row_budget
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) :
    complementDegreeInFinset G v (D.part source) +
        (∑ b ∈ D.closedPartIndices target \ D.closedPartIndices source,
          degreeInFinset G v (D.part b)) ≤
      complementDegreeInFinset G v (D.part target) +
        (∑ b ∈ D.closedPartIndices source \ D.closedPartIndices target,
          degreeInFinset G v (D.part b)) := by
  have h := subcriticalDefectCost_movePartToPart_row_identity G D v source target hv hsource
  have hm := hminimal (D.movePartToPart v source target hv hsource)
  omega

/-- A bounded lost-row degree costs at most one copy per old closed part. -/
theorem subcriticalMinimal_relocation_bounded_loss
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) (B : ℝ) (hB : 0 ≤ B)
    (hlost : ∀ b ∈ D.closedPartIndices source \ D.closedPartIndices target,
      (degreeInFinset G v (D.part b) : ℝ) ≤ B) :
    (complementDegreeInFinset G v (D.part source) : ℝ) ≤
      complementDegreeInFinset G v (D.part target) + (k - 1 : ℕ) * B := by
  have h := subcriticalMinimal_relocation_row_budget G D hminimal v source target hv hsource
  have h' : complementDegreeInFinset G v (D.part source) ≤
      complementDegreeInFinset G v (D.part target) +
        ∑ b ∈ D.closedPartIndices source \ D.closedPartIndices target,
          degreeInFinset G v (D.part b) := by omega
  have hsum := Finset.sum_le_sum hlost
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard : (D.closedPartIndices source \ D.closedPartIndices target).card ≤ k - 1 := by
    simpa only [D.card_closedPartIndices hk source] using
      Finset.card_le_card (Finset.sdiff_subset :
        D.closedPartIndices source \ D.closedPartIndices target ⊆ D.closedPartIndices source)
  have hc : ((D.closedPartIndices source \ D.closedPartIndices target).card : ℝ) * B ≤
      (k - 1 : ℕ) * B := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB
  have hr : (complementDegreeInFinset G v (D.part source) : ℝ) ≤
      complementDegreeInFinset G v (D.part target) +
        ∑ b ∈ D.closedPartIndices source \ D.closedPartIndices target,
          (degreeInFinset G v (D.part b) : ℝ) := by exact_mod_cast h'
  linarith

/-- At a unique upper target, every lost active row is lower once all
medium neighbors stay active. This is the finite division comparison used
in both upper-target exceptional cases of the paper. -/
theorem subcriticalMinimal_upper_relocation_complement_le
    {G : SimpleGraph V} {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
    {p : SubcriticalProfile D eta R₀ theta}
    (hp : RealizesSubcriticalProfile G alpha p) (hk : 3 ≤ k) (ha : 0 ≤ alpha)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (hv : v ∈ p.retainedRoots) (target : D.PartIndex)
    (htarget : target ∈ subcriticalUpperNeighborIndices p v hv)
    (hunique : ∀ b ∈ subcriticalUpperNeighborIndices p v hv, b = target)
    (hmedium : ∀ b ∈ subcriticalMediumNeighborIndices p v hv, D.ActivePart target b)
    (hsource : 2 ≤ (D.part
      (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card) :
    (complementDegreeInFinset G v
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) : ℝ) ≤
      2 * alpha * k *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card := by
  let source := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  let N := ((D.part source).card : ℝ)
  have hvP : v ∈ D.part source := D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  have hactive := (mem_subcriticalUpperNeighborIndices p v hv target).mp htarget |>.1
  have hreverse : D.ActivePart target source := by
    obtain ⟨i, a, b, ha, hb, hab⟩ := hactive
    exact ⟨i, b, a, hb, ha, hab.symm⟩
  have hsourceTarget : source ∈ D.closedPartIndices target :=
    D.mem_closedPartIndices_of_activePart hreverse
  have htargetScale : ((D.part target).card : ℝ) ≤ 2 * N :=
    hbalance target (SubcriticalDivision.activePart_same_component hactive).symm
  have htargetNot : v ∉ D.part target := by
    intro ht
    exact D.not_activePair_self v ((D.activePair_iff_of_mem_parts hvP ht).mpr hactive)
  have htargetSum : (degreeInFinset G v (D.part target) : ℝ) +
      complementDegreeInFinset G v (D.part target) = (D.part target).card := by
    exact_mod_cast degreeInFinset_add_complementDegreeInFinset_of_notMem G v
      (D.part target) htargetNot
  have htargetHigh := (hp.upperNeighborIndices_iff v hv target).mp htarget |>.2
  have htargetComp : (complementDegreeInFinset G v (D.part target) : ℝ) ≤ 2 * alpha * N := by
    nlinarith
  have hbound := subcriticalMinimal_relocation_bounded_loss hk G D hminimal v source target
    hvP hsource (2 * alpha * N) (by dsimp [N]; positivity) (by
      intro b hb
      obtain ⟨hb, hbnot⟩ := Finset.mem_sdiff.mp hb
      have hbactive : D.ActivePart source b := by
        rcases (D.mem_closedPartIndices_iff source b).mp hb with hsame | hact
        · exact (hbnot (hsame ▸ hsourceTarget)).elim
        · exact hact
      have hbU : b ∉ subcriticalUpperNeighborIndices p v hv := by
        intro h
        exact hbnot (hunique b h ▸ D.self_mem_closedPartIndices target)
      have hbM : b ∉ subcriticalMediumNeighborIndices p v hv := by
        intro h
        exact hbnot (D.mem_closedPartIndices_of_activePart (hmedium b h))
      have hbL : b ∈ subcriticalLowerNeighborIndices p v hv := by
        have hp := subcriticalNeighborIndices_partition p v hv
        have hbA : b ∈ subcriticalActiveNeighborIndices p v hv :=
          (mem_subcriticalActiveNeighborIndices p v hv b).mpr hbactive
        rw [← hp] at hbA
        simpa [hbU, hbM] using hbA
      have hlow := (hp.lowerNeighborIndices_iff v hv b).mp hbL |>.2
      have hscale := hbalance b (SubcriticalDivision.activePart_same_component hbactive).symm
      dsimp [N]
      nlinarith)
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (show k - 1 + 1 = k by omega)
  change (complementDegreeInFinset G v (D.part source) : ℝ) ≤ 2 * alpha * k * N
  nlinarith

/-- For a nonadjacent destination the old own row is a lost row, and the
target's present row is an actual gain. The old own part is inactive at the new location, and all remaining lost rows stay explicit. -/
theorem subcriticalMinimal_nonadjacent_relocation_row_budget
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card)
    (htarget : target ∉ D.closedPartIndices source) :
    complementDegreeInFinset G v (D.part source) + degreeInFinset G v (D.part target) ≤
      complementDegreeInFinset G v (D.part target) + degreeInFinset G v (D.part source) +
        (∑ b ∈ (D.closedPartIndices source \ D.closedPartIndices target).erase source,
          degreeInFinset G v (D.part b)) := by
  have hsourceNot : source ∉ D.closedPartIndices target := by
    intro h
    apply htarget
    rcases (D.mem_closedPartIndices_iff target source).mp h with heq | hact
    · subst target
      exact D.self_mem_closedPartIndices source
    · apply D.mem_closedPartIndices_of_activePart
      obtain ⟨i, a, b, ha, hb, hab⟩ := hact
      exact ⟨i, b, a, hb, ha, hab.symm⟩
  have hs : source ∈ D.closedPartIndices source \ D.closedPartIndices target :=
    Finset.mem_sdiff.mpr ⟨D.self_mem_closedPartIndices source, hsourceNot⟩
  have ht : target ∈ D.closedPartIndices target \ D.closedPartIndices source :=
    Finset.mem_sdiff.mpr ⟨D.self_mem_closedPartIndices target, htarget⟩
  have hgain := Finset.single_le_sum
    (f := fun b ↦ degreeInFinset G v (D.part b)) (fun b _ ↦ Nat.zero_le _) ht
  have hloss := Finset.add_sum_erase
    (D.closedPartIndices source \ D.closedPartIndices target)
    (fun b ↦ degreeInFinset G v (D.part b)) hs
  have h := subcriticalMinimal_relocation_row_budget G D hminimal v source target hv hsource
  omega

/-- The valid move to sparse bounds the own missing row by all old close
present rows. This exact finite inequality excludes all-low high-negative roots. -/
theorem subcriticalMinimal_sparse_row_budget
    (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) :
    complementDegreeInFinset G v (D.part source) ≤
      ∑ b ∈ D.closedPartIndices source, degreeInFinset G v (D.part b) := by
  let E := D.movePartToSparse v source hv hsource
  have hcost := subcriticalDefectCost_moveVertex G D v none
    (fun b _ ↦ D.erase_nonempty_of_source hv hsource b)
  have hmin := hminimal E
  have hvE : v ∈ E.sparse := (D.moveVertex_mem_sparse_self v none _).mpr rfl
  have hnew := subcriticalCombinedDefectGraph_degree_of_sparse G E hvE
  have hold := subcriticalDefect_degree_add_closed_degree_eq G D hv
  rw [degreeInFinset_closedParts_eq_sum] at hold
  change subcriticalDefectCost G E + (subcriticalCombinedDefectGraph G D).degree v =
    subcriticalDefectCost G D + (subcriticalCombinedDefectGraph G E).degree v at hcost
  omega

end InducedStars
