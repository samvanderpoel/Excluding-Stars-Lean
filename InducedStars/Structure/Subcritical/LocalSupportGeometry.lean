import InducedStars.Structure.Subcritical.LocalSupport
import InducedStars.Structure.Subcritical.LocalRootMoves

/-!
# Placement optimality for the zero-deficit support

The sparse placement excludes empty own-component support. In the unique-high
configuration every lost row outside the old own part is low, so the exact
placement identity forces a small own missing row.
-/

noncomputable section
open Finset
open scoped Classical BigOperators
namespace InducedStars
variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

private theorem closedPart_same_component (D : SubcriticalDivision k V)
    {a b : D.PartIndex} (h : b ∈ D.closedPartIndices a) : b.1 = a.1 := by
  rcases (D.mem_closedPartIndices_iff a b).mp h with h | h
  · exact congrArg Sigma.fst h
  · exact (SubcriticalDivision.activePart_same_component h).symm

/-- A low own-component support contradicts the admissible sparse placement. -/
theorem subcriticalOwnDensitySupport_nonempty
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    {alpha theta : ℝ} (ha : 0 < alpha)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (hminimal : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (own : D.PartIndex) (hv : v ∈ D.part own)
    (hsource : 2 ≤ (D.part own).card) (hloop : 1 ≤ alpha * (D.part own).card)
    (hvis : own ∈ D.visiblePartIndices theta)
    (hbalance : ∀ b : D.PartIndex, b.1 = own.1 →
      ((D.part b).card : ℝ) ≤ 2 * (D.part own).card) :
    (subcriticalDensitySupport G D alpha theta v own.1).Nonempty := by
  by_contra hnone
  have hlow (b : D.PartIndex) (hbi : b.1 = own.1) :
      (degreeInFinset G v (D.part b) : ℝ) ≤ alpha * (D.part b).card := by
    apply le_of_not_gt
    intro hb
    apply hnone
    refine ⟨b, subcriticalDensitySupport_mem_of_degree_gt G D v own.1 b ?_ hbi hb⟩
    exact (D.mem_visiblePartIndices theta b).mpr
      (hbi ▸ (D.mem_visiblePartIndices theta own).mp hvis)
  have hbudget := subcriticalMinimal_sparse_row_budget G D hminimal v own hv hsource
  have hsum := Finset.sum_le_sum (s := D.closedPartIndices own)
    (fun b hb ↦ (hlow b (closedPart_same_component D hb)).trans
      (mul_le_mul_of_nonneg_left (hbalance b (closedPart_same_component D hb)) ha.le))
  simp only [Finset.sum_const, nsmul_eq_mul, D.card_closedPartIndices hk own] at hsum
  have hbR : (complementDegreeInFinset G v (D.part own) : ℝ) ≤
      ∑ b ∈ D.closedPartIndices own, (degreeInFinset G v (D.part b) : ℝ) := by
    exact_mod_cast hbudget
  have hfull : (degreeInFinset G v (D.part own) : ℝ) +
      complementDegreeInFinset G v (D.part own) + 1 = (D.part own).card := by
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v (D.part own) hv
  have hsmallN := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg (D.part own).card)
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (show k - 1 + 1 = k by omega)
  have hN : (0 : ℝ) < (D.part own).card := by exact_mod_cast (D.part_nonempty own).card_pos
  nlinarith [hlow own rfl]

/-- Saturation of the non-low budget makes every target outside the unique
high target's closed neighborhood low, including other components. -/
theorem subcriticalZeroDeficit_outside_closed_low
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {alpha theta : ℝ}
    (ha : alpha ≤ 1 / 2) (v : V) (i : Fin D.componentCount) (t : D.PartIndex)
    (hH : subcriticalHighTargets G D alpha theta v i = {t})
    (hM : subcriticalMediumTargets G D alpha theta v i = Finset.univ.filter (D.ActivePart t))
    (hS : (subcriticalDensitySupport G D alpha theta v i).card = k - 1)
    (hbudget : (subcriticalNonlowVisibleParts G D alpha theta v).card ≤ k - 1)
    (a : D.PartIndex) (hvis : a ∈ D.visiblePartIndices theta)
    (hout : a ∉ D.closedPartIndices t) :
    (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card := by
  have heq : subcriticalDensitySupport G D alpha theta v i =
      subcriticalNonlowVisibleParts G D alpha theta v :=
    Finset.eq_of_subset_of_card_le (subcriticalDensitySupport_subset_nonlow G D ha v i)
      (by omega)
  by_contra hh
  have hm : a ∈ subcriticalNonlowVisibleParts G D alpha theta v :=
    (mem_subcriticalNonlowVisibleParts G D alpha theta v a).mpr ⟨hvis, (lt_of_not_ge hh).le⟩
  rw [← heq, subcriticalDensitySupport, hH, hM] at hm
  rcases Finset.mem_union.mp hm with hm | hm
  · have h := Finset.mem_singleton.mp hm
    exact hout (h ▸ D.self_mem_closedPartIndices t)
  · exact hout (D.mem_closedPartIndices_of_activePart (Finset.mem_filter.mp hm).2)

/-- The unique high target cannot be the own part of a retained bad root. -/
theorem subcriticalZeroDeficit_high_ne_own
    (G : SimpleGraph V) (D : SubcriticalDivision k V) {eta theta alpha : ℝ} {R₀ : ℕ}
    {p : SubcriticalProfile D eta R₀ theta} (hp : RealizesSubcriticalProfile G alpha p)
    (ha : 0 < alpha) (v : V) (hv : v ∈ p.retainedRoots)
    (t : D.PartIndex)
    (hhigh : (1 - alpha) * (D.part t).card ≤ (degreeInFinset G v (D.part t) : ℝ))
    (hlow : ∀ a ∈ D.visiblePartIndices theta, a ∉ D.closedPartIndices t →
      (degreeInFinset G v (D.part a) : ℝ) ≤ alpha * (D.part a).card) :
    t ≠ D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv) := by
  intro ht
  subst t
  have hb : v ∈ subcriticalBadRetainedRoots G D eta R₀ theta alpha := by
    rwa [← hp.retained_roots]
  obtain ⟨hvret, hbad⟩ := (mem_subcriticalBadRetainedRoots G D eta R₀ theta alpha v).mp hb
  rcases hbad with ⟨a, haS, had⟩ | had
  · obtain ⟨hvis, hne, hact⟩ := (D.mem_eligibleVisibleTargets eta R₀ theta v hvret a).mp haS
    have hnot : a ∉ D.closedPartIndices (D.retainedVertexPart eta R₀ v hvret) := by
      intro hh
      rcases (D.mem_closedPartIndices_iff _ a).mp hh with hh | hh
      · exact hne hh
      · exact hact hh
    have hh := hlow a hvis hnot
    have hN : (0 : ℝ) < (D.part a).card := by exact_mod_cast (D.part_nonempty a).card_pos
    nlinarith [mul_pos ha hN]
  · have hfull : (degreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) : ℝ) +
        complementDegreeInFinset G v (D.part (D.retainedVertexPart eta R₀ v hvret)) + 1 =
          (D.part (D.retainedVertexPart eta R₀ v hvret)).card := by
      exact_mod_cast subcriticalOwn_degree_complement_add_one G v _
        (D.mem_retainedVertexPart eta R₀ v hvret)
    have hN : (0 : ℝ) < (D.part (D.retainedVertexPart eta R₀ v hvret)).card := by
      exact_mod_cast (D.part_nonempty _).card_pos
    nlinarith [mul_pos ha hN]

/-- One placement comparison handles both adjacency relations between the
old own part and the high target. All lost rows except the own row are low. -/
theorem subcriticalZeroDeficit_own_complement_le
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V) {alpha : ℝ}
    (ha : 0 ≤ alpha)
    (hminimal : ∀ E : SubcriticalDivision k V,
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (own t : D.PartIndex) (hv : v ∈ D.part own)
    (hsource : 2 ≤ (D.part own).card) (hne : t ≠ own)
    (hhigh : (1 - alpha) * (D.part t).card ≤ (degreeInFinset G v (D.part t) : ℝ))
    (hT : ((D.part t).card : ℝ) ≤ 2 * (D.part own).card)
    (hdev : ((D.part own).card : ℝ) - (D.part t).card ≤ 2 * alpha * (D.part own).card)
    (hlost : ∀ b ∈ (D.closedPartIndices own \ D.closedPartIndices t).erase own,
      (degreeInFinset G v (D.part b) : ℝ) ≤ 2 * alpha * (D.part own).card) :
    (complementDegreeInFinset G v (D.part own) : ℝ) ≤
      4 * alpha * k * (D.part own).card := by
  have htNot : v ∉ D.part t := fun ht ↦ hne (D.mem_part_unique ht hv)
  have hfullT : (degreeInFinset G v (D.part t) : ℝ) +
      complementDegreeInFinset G v (D.part t) = (D.part t).card := by
    exact_mod_cast degreeInFinset_add_complementDegreeInFinset_of_notMem G v (D.part t) htNot
  have hcompT : (complementDegreeInFinset G v (D.part t) : ℝ) ≤
      2 * alpha * (D.part own).card := by nlinarith
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (show k - 1 + 1 = k by omega)
  have hN : (0 : ℝ) ≤ (D.part own).card := Nat.cast_nonneg _
  by_cases hclosed : own ∈ D.closedPartIndices t
  · have hh := subcriticalMinimal_relocation_bounded_loss hk G D hminimal v own t hv hsource
      (2 * alpha * (D.part own).card) (by positivity) (by
        intro b hb
        exact hlost b (Finset.mem_erase.mpr ⟨by
          intro h
          subst b
          exact (Finset.mem_sdiff.mp hb).2 hclosed, hb⟩))
    nlinarith
  · have htclosed : t ∉ D.closedPartIndices own := by
      intro ht
      apply hclosed
      rcases (D.mem_closedPartIndices_iff own t).mp ht with h | h
      · exact h ▸ D.self_mem_closedPartIndices own
      · obtain ⟨i, a, b, rfl, rfl, hab⟩ := h
        exact D.mem_closedPartIndices_of_activePart ⟨i, b, a, rfl, rfl, hab.symm⟩
    have hb := subcriticalMinimal_nonadjacent_relocation_row_budget G D hminimal
      v own t hv hsource htclosed
    have hsum := Finset.sum_le_sum hlost
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    have hc : ((D.closedPartIndices own \ D.closedPartIndices t).erase own).card ≤ k - 1 := by
      simpa only [D.card_closedPartIndices hk own] using Finset.card_le_card
        ((Finset.erase_subset _ _).trans (Finset.sdiff_subset :
          D.closedPartIndices own \ D.closedPartIndices t ⊆ D.closedPartIndices own))
    have hsum' := hsum.trans (mul_le_mul_of_nonneg_right
      (show (((D.closedPartIndices own \ D.closedPartIndices t).erase own).card : ℝ) ≤
        (k - 1 : ℕ) by exact_mod_cast hc) (show 0 ≤ 2 * alpha * (D.part own).card by positivity))
    have hbR : (complementDegreeInFinset G v (D.part own) : ℝ) +
        degreeInFinset G v (D.part t) ≤ complementDegreeInFinset G v (D.part t) +
        degreeInFinset G v (D.part own) +
        ∑ b ∈ (D.closedPartIndices own \ D.closedPartIndices t).erase own,
          (degreeInFinset G v (D.part b) : ℝ) := by exact_mod_cast hb
    have hfull : (degreeInFinset G v (D.part own) : ℝ) +
        complementDegreeInFinset G v (D.part own) + 1 = (D.part own).card := by
      exact_mod_cast subcriticalOwn_degree_complement_add_one G v _ hv
    have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith

end InducedStars
