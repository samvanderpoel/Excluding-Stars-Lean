import InducedStars.Structure.Subcritical.LocalRootMoves

/-!
# Finite high-negative root exclusions

The all-low active-neighbor case is ruled out by a valid move to sparse.
The nonadjacent high-target case retains every lost lower row, including
the equality branch with a nonempty lower set. These auxiliary exclusions are retained for compatibility; the current compensation proof uses the unified support deficit.
-/

noncomputable section
open Finset
open scoped BigOperators Classical
namespace InducedStars

variable {k : ℕ} {V : Type*} [Fintype V] [DecidableEq V]

/-- Under minimality a removable high-missing source cannot have only
small present degrees on its active rows. -/
theorem subcriticalMinimal_allLow_highMissing_impossible
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) (alpha : ℝ) (ha : 0 ≤ alpha)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (hcomp : (1 - 3 * alpha) * (D.part source).card ≤
      (complementDegreeInFinset G v (D.part source) : ℝ))
    (hrows : ∀ b ∈ (D.closedPartIndices source).erase source,
      (degreeInFinset G v (D.part b) : ℝ) ≤ 2 * alpha * (D.part source).card) : False := by
  let N := ((D.part source).card : ℝ)
  have hbudget := subcriticalMinimal_sparse_row_budget G D hminimal v source hv hsource
  have hsum := Finset.sum_le_sum hrows
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((D.closedPartIndices source).erase source).card ≤ k - 1 := by
    simpa only [D.card_closedPartIndices hk source] using
      Finset.card_le_card (Finset.erase_subset _ _ :
        (D.closedPartIndices source).erase source ⊆ D.closedPartIndices source)
  have hsum' : (∑ b ∈ (D.closedPartIndices source).erase source,
      (degreeInFinset G v (D.part b) : ℝ)) ≤ (k - 1 : ℕ) * (2 * alpha * N) :=
    hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))
  have hsplit := Finset.add_sum_erase (D.closedPartIndices source)
    (fun b ↦ degreeInFinset G v (D.part b)) (D.self_mem_closedPartIndices source)
  have hbudgetR : (complementDegreeInFinset G v (D.part source) : ℝ) ≤
      degreeInFinset G v (D.part source) +
        ∑ b ∈ (D.closedPartIndices source).erase source,
          (degreeInFinset G v (D.part b) : ℝ) := by
    rw [← hsplit] at hbudget
    exact_mod_cast hbudget
  have hfull : (degreeInFinset G v (D.part source) : ℝ) +
      complementDegreeInFinset G v (D.part source) + 1 = N := by
    dsimp [N]
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v (D.part source) hv
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (show k - 1 + 1 = k by omega)
  rw [← hkR] at hsmall
  have hsmallN := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ N by dsimp [N]; positivity)
  change (1 - 3 * alpha) * N ≤ _ at hcomp
  nlinarith

/-- A nonadjacent target with high present degree cannot coexist with a
high-missing source if every other lost row is small.
The target gain is retained, not dropped from the exact move identity. -/
theorem subcriticalMinimal_nonadjacent_highRows_impossible
    (hk : 3 ≤ k) (G : SimpleGraph V) (D : SubcriticalDivision k V)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (source target : D.PartIndex) (hv : v ∈ D.part source)
    (hsource : 2 ≤ (D.part source).card) (htarget : target ∉ D.closedPartIndices source)
    (alpha : ℝ) (ha : 0 ≤ alpha) (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (hcomp : (1 - 3 * alpha) * (D.part source).card ≤
      (complementDegreeInFinset G v (D.part source) : ℝ))
    (hdegree : (1 - 3 * alpha) * (D.part target).card ≤
      (degreeInFinset G v (D.part target) : ℝ))
    (hrows : ∀ b ∈ (D.closedPartIndices source \ D.closedPartIndices target).erase source,
      (degreeInFinset G v (D.part b) : ℝ) ≤ 2 * alpha * (D.part source).card) : False := by
  let N := ((D.part source).card : ℝ)
  let T := ((D.part target).card : ℝ)
  have hbudget := subcriticalMinimal_nonadjacent_relocation_row_budget G D hminimal
    v source target hv hsource htarget
  have hsum := Finset.sum_le_sum hrows
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  have hc : ((D.closedPartIndices source \ D.closedPartIndices target).erase source).card ≤ k - 1 := by
    simpa only [D.card_closedPartIndices hk source] using
      Finset.card_le_card ((Finset.erase_subset _ _).trans (Finset.sdiff_subset :
        D.closedPartIndices source \ D.closedPartIndices target ⊆ D.closedPartIndices source))
  have hsum' : (∑ b ∈ (D.closedPartIndices source \ D.closedPartIndices target).erase source,
      (degreeInFinset G v (D.part b) : ℝ)) ≤ (k - 1 : ℕ) * (2 * alpha * N) :=
    hsum.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity))
  have hbudgetR : (complementDegreeInFinset G v (D.part source) : ℝ) +
      degreeInFinset G v (D.part target) ≤
      complementDegreeInFinset G v (D.part target) + degreeInFinset G v (D.part source) +
        ∑ b ∈ (D.closedPartIndices source \ D.closedPartIndices target).erase source,
          (degreeInFinset G v (D.part b) : ℝ) := by exact_mod_cast hbudget
  have htargetNot : v ∉ D.part target := by
    intro ht
    exact htarget ((D.mem_part_unique ht hv) ▸ D.self_mem_closedPartIndices source)
  have hfull : (degreeInFinset G v (D.part source) : ℝ) +
      complementDegreeInFinset G v (D.part source) + 1 = N := by
    dsimp [N]
    exact_mod_cast subcriticalOwn_degree_complement_add_one G v (D.part source) hv
  have hfullT : (degreeInFinset G v (D.part target) : ℝ) +
      complementDegreeInFinset G v (D.part target) = T := by
    dsimp [T]
    exact_mod_cast degreeInFinset_add_complementDegreeInFinset_of_notMem G v
      (D.part target) htargetNot
  have hkR : ((k - 1 : ℕ) : ℝ) + 1 = k := by exact_mod_cast (show k - 1 + 1 = k by omega)
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hsmallT : 12 * alpha ≤ 1 := by nlinarith
  rw [← hkR] at hsmall
  have hsmallN := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ N by dsimp [N]; positivity)
  have hsmallT := mul_le_mul_of_nonneg_right hsmallT (show 0 ≤ T by dsimp [T]; positivity)
  change (1 - 3 * alpha) * N ≤ _ at hcomp
  change (1 - 3 * alpha) * T ≤ _ at hdegree
  nlinarith

section Profile

variable {G : SimpleGraph V} {D : SubcriticalDivision k V} {eta theta alpha : ℝ} {R₀ : ℕ}
  {p : SubcriticalProfile D eta R₀ theta}

/-- The high-negative case has an actual nonlow active-neighbor row.
The all-low alternative is contradicted by the finite sparse move. -/
theorem subcriticalHighNegative_active_nonlow_nonempty
    (hp : RealizesSubcriticalProfile G alpha p) (hk : 3 ≤ k) (ha : 0 ≤ alpha)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (hv : v ∈ p.retainedRoots)
    (hsource : 2 ≤ (D.part
      (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hB : (p.roots.card : ℝ) ≤ alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ)) :
    (subcriticalUpperNeighborIndices p v hv ∪ subcriticalMediumNeighborIndices p v hv).Nonempty := by
  let source := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  by_contra hempty
  have hnone : ∀ b, b ∉ subcriticalUpperNeighborIndices p v hv ∧
      b ∉ subcriticalMediumNeighborIndices p v hv := by
    intro b
    have hnot : b ∉ subcriticalUpperNeighborIndices p v hv ∪
        subcriticalMediumNeighborIndices p v hv := fun hb ↦ hempty ⟨b, hb⟩
    simpa using hnot
  apply subcriticalMinimal_allLow_highMissing_impossible hk G D hminimal v source
    (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hsource alpha ha hsmall
  · apply subcriticalOwn_highNegative_strong_complement G v (D.part source) p.roots ha hB
    simpa only [hp.own_counts v hv] using hI
  · intro b hb
    obtain ⟨hbne, hb⟩ := Finset.mem_erase.mp hb
    have hab : D.ActivePart source b := by
      rcases (D.mem_closedPartIndices_iff source b).mp hb with heq | hab
      · exact (hbne heq).elim
      · exact hab
    have hbA := (mem_subcriticalActiveNeighborIndices p v hv b).mpr hab
    rw [← subcriticalNeighborIndices_partition p v hv] at hbA
    have hbL : b ∈ subcriticalLowerNeighborIndices p v hv := by
      simpa [(hnone b).1, (hnone b).2] using hbA
    have hlow := (hp.lowerNeighborIndices_iff v hv b).mp hbL |>.2
    have hs := hbalance b (SubcriticalDivision.activePart_same_component hab).symm
    nlinarith

/-- All upper and medium rows stay closed at the destination, so any
other lost active row is lower. This purely finite classification is what
retains and bounds the extra lost rows. -/
theorem subcriticalLostClosedRow_lower
    (p : SubcriticalProfile D eta R₀ theta) (v : V) (hv : v ∈ p.retainedRoots)
    (target : D.PartIndex)
    (hupper : ∀ b ∈ subcriticalUpperNeighborIndices p v hv, b ∈ D.closedPartIndices target)
    (hmedium : ∀ b ∈ subcriticalMediumNeighborIndices p v hv, b ∈ D.closedPartIndices target)
    {b : D.PartIndex}
    (hb : b ∈ (D.closedPartIndices
      (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ D.closedPartIndices target).erase
        (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) :
    b ∈ subcriticalLowerNeighborIndices p v hv := by
  obtain ⟨hbne, hb⟩ := Finset.mem_erase.mp hb
  obtain ⟨hb, hbnot⟩ := Finset.mem_sdiff.mp hb
  have hab : D.ActivePart (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) b := by
    rcases (D.mem_closedPartIndices_iff _ b).mp hb with heq | hab
    · exact (hbne heq).elim
    · exact hab
  have hbA := (mem_subcriticalActiveNeighborIndices p v hv b).mpr hab
  rw [← subcriticalNeighborIndices_partition p v hv] at hbA
  rcases Finset.mem_union.mp hbA with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact (hbnot (hupper b h)).elim
    · exact h
  · exact (hbnot (hmedium b h)).elim

/-- High-negative own count and a high nonadjacent target contradict
minimality whenever all medium rows stay active. Lower rows need not be
empty: their full finite loss is charged in the preceding row budget. -/
theorem subcriticalHighNegative_nonadjacent_relocation_impossible
    (hp : RealizesSubcriticalProfile G alpha p) (hk : 3 ≤ k) (ha : 0 ≤ alpha)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
    (hminimal : ∀ E : SubcriticalDivision k V, subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (v : V) (hv : v ∈ p.retainedRoots) (target : D.PartIndex)
    (htarget : target ∉ D.closedPartIndices
      (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)))
    (hupper : subcriticalUpperNeighborIndices p v hv = ∅)
    (hmedium : ∀ b ∈ subcriticalMediumNeighborIndices p v hv, D.ActivePart target b)
    (hsource : 2 ≤ (D.part
      (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hbalance : ∀ b : D.PartIndex,
      b.1 = (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)).1 →
      ((D.part b).card : ℝ) ≤ 2 *
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hB : (p.roots.card : ℝ) ≤ alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hBT : (p.roots.card : ℝ) ≤ alpha * (D.part target).card)
    (hI : (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ))
    (hhigh : (1 - 2 * alpha) * (D.part target \ p.roots).card ≤
      (degreeInFinset G v (D.part target \ p.roots) : ℝ)) : False := by
  let source := D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)
  apply subcriticalMinimal_nonadjacent_highRows_impossible hk G D hminimal v source target
    (D.mem_retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) hsource htarget alpha ha hsmall
  · apply subcriticalOwn_highNegative_strong_complement G v (D.part source) p.roots ha hB
    simpa only [hp.own_counts v hv] using hI
  · exact subcriticalTrim_high_degree_lower G v (D.part target) p.roots ha hBT hhigh
  · intro b hb
    have hbL := subcriticalLostClosedRow_lower p v hv target
      (by simp [hupper]) (fun b hb ↦ D.mem_closedPartIndices_of_activePart (hmedium b hb)) hb
    have hlow := (hp.lowerNeighborIndices_iff v hv b).mp hbL
    have hscale := hbalance b (SubcriticalDivision.activePart_same_component hlow.1).symm
    nlinarith [hlow.2]

/-- The remaining medium exceptional configuration is impossible once the
stored own count exceeds the explicit upper-relocation budget. -/
theorem subcriticalLargeOwn_upper_relocation_impossible
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
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : 2 * alpha * k *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card <
        ((p.ownCount v).val : ℝ)) : False := by
  have hbound := subcriticalMinimal_upper_relocation_complement_le hp hk ha hminimal
    v hv target htarget hunique hmedium hsource hbalance
  have hIle : ((p.ownCount v).val : ℝ) ≤ complementDegreeInFinset G v
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) := by
    rw [hp.own_counts v hv]
    exact_mod_cast (subcriticalComplement_trim_bounds G v
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))) p.roots).1
  linarith

/-- High-negative own count automatically exceeds the upper-relocation
budget under the common scalar reserve. This closes its unique-upper case. -/
theorem subcriticalHighNegative_upper_relocation_impossible
    (hp : RealizesSubcriticalProfile G alpha p) (hk : 3 ≤ k) (ha : 0 ≤ alpha)
    (hsmall : (4 * (k : ℝ) + 8) * alpha ≤ 1)
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
        (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hB : (p.roots.card : ℝ) ≤ alpha *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))).card)
    (hI : (1 - 2 * alpha) *
      (D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv)) \ p.roots).card ≤
        ((p.ownCount v).val : ℝ)) : False := by
  let P := D.part (D.retainedVertexPart eta R₀ v (p.retainedRoots_subset hv))
  have hbound := subcriticalMinimal_upper_relocation_complement_le hp hk ha hminimal
    v hv target htarget hunique hmedium hsource hbalance
  have hlo := subcriticalOwn_highNegative_strong_complement G v P p.roots ha hB
    (by simpa only [hp.own_counts v hv] using hI)
  have hNnat : 0 < P.card := lt_of_lt_of_le (by omega : 0 < 2) hsource
  have hN : (0 : ℝ) < P.card := by exact_mod_cast hNnat
  have hsmallN := mul_le_mul_of_nonneg_right hsmall hN.le
  change (complementDegreeInFinset G v P : ℝ) ≤ 2 * alpha * k * P.card at hbound
  nlinarith

end Profile
end InducedStars
