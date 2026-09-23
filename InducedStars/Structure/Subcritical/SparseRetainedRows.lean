import InducedStars.Structure.Subcritical.DivisionMoveBounds
import InducedStars.Structure.Subcritical.DonorSource
import InducedStars.Structure.Subcritical.RowConstraints
import InducedStars.Structure.Subcritical.RetainedMembership

/-! # Finite sparse retained-row geometry

The elementary comparisons are stated with their exact source nonemptiness
conditions. The paper-facing assembly additionally uses the singleton-safe
singleton-safe comparison; it never treats an empty source part as a valid division.
-/

noncomputable section
open Finset Set
open scoped BigOperators Classical
namespace InducedStars

variable {k n R₀ : ℕ} {G : SimpleGraph (Fin n)} {D : SubcriticalDivision k (Fin n)}
  {eta theta alpha : ℝ}

/-- Quantitative parameter reserves for the singleton-safe sparse-row
comparison. All parameters depend only on `k`, `R₀`, and the retained cutoff. -/
structure SubcriticalSparseRowParameters (k R₀ : ℕ) (eta : ℝ) where
  alpha : ℝ
  theta : ℝ
  alpha_pos : 0 < alpha
  alpha_quarter : alpha ≤ 1 / 4
  alpha_budget : alpha * (1 + 2 * ((k - 1 : ℕ) : ℝ)) ≤ 1 / 2
  theta_pos : 0 < theta
  retained_visible : theta ≤ eta / (2 * (R₀ : ℝ))
  relocation_reserve : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ))

/-- One explicit permitted hierarchy is `α = 1/(8k)` and
`θ = η/(80kR₀)`. No finite graph enters these choices. -/
theorem exists_subcriticalSparseRowParameters
    (k : ℕ) (hk : 3 ≤ k) (R₀ : ℕ) (hR₀ : 1 ≤ R₀)
    (eta : ℝ) (heta : 0 < eta) :
    Nonempty (SubcriticalSparseRowParameters k R₀ eta) := by
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hR : (1 : ℝ) ≤ R₀ := by exact_mod_cast hR₀
  have hkpos : (0 : ℝ) < k := by linarith
  have hRpos : (0 : ℝ) < R₀ := by linarith
  have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
  refine ⟨⟨1 / (8 * k), eta / (80 * k * R₀), by positivity, ?_, ?_,
    by positivity, ?_, ?_⟩⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mpr
    nlinarith
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * k)).mpr
    nlinarith
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 80 * k * R₀)
      (by positivity : (0 : ℝ) < 2 * R₀)).mpr
    have hden : 2 * (R₀ : ℝ) ≤ 80 * k * R₀ := by nlinarith
    exact mul_le_mul_of_nonneg_left hden heta.le
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 80 * k * R₀)
      (by positivity : (0 : ℝ) < 2 * R₀)).mpr
    have hpos : 0 ≤ (eta * k * R₀ : ℝ) := by positivity
    nlinarith

/-- The literal conclusions of the sparse retained-row lemma, with the
non-low witness explicitly belonging to the component containing `v`. -/
def SubcriticalSparseRetainedRowBudget
    (G : SimpleGraph (Fin n)) (D : SubcriticalDivision k (Fin n))
    (eta theta alpha : ℝ) (R₀ : ℕ) : Prop :=
  ∀ v : Fin n, v ∈ D.nonretainedVertices eta R₀ →
    (∃ a ∈ D.retainedPartIndices eta R₀,
      4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) →
    v ∉ D.sparse ∧
      (∀ a : D.PartIndex, v ∈ D.part a →
        ∃ b : D.PartIndex, b.1 = a.1 ∧
          b ∈ subcriticalNonlowVisibleParts G D alpha theta v) ∧
      ((subcriticalNonlowVisibleParts G D alpha theta v) ∩
        D.retainedPartIndices eta R₀).card ≤ k - 2

/-- A high retained row supplies a weak-high row in the same retained
component, using the completed deterministic companion theorem. -/
theorem subcriticalRetainedHighRow_has_high_target
    (C : SubcriticalRowConstraints G D alpha theta) (halpha : 0 ≤ alpha)
    (hretvis : D.retainedPartIndices eta R₀ ⊆ D.visiblePartIndices theta)
    {v : Fin n} (hv : v ∈ D.nonretainedVertices eta R₀)
    {a : D.PartIndex} (ha : a ∈ D.retainedPartIndices eta R₀)
    (hrow : 4 * alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) :
    ∃ b : D.PartIndex, b ∈ D.retainedPartIndices eta R₀ ∧ b.1 = a.1 ∧
      (1 - alpha) * (D.part b).card ≤ (degreeInFinset G v (D.part b) : ℝ) := by
  by_cases hh : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
  · exact ⟨a, ha, rfl, hh⟩
  have hvout : v ∉ subcriticalCoreNeighborUnion D a.1 a.2 := by
    intro h
    obtain ⟨b, _, hvb⟩ := (mem_subcriticalCoreNeighborUnion D a.1 a.2 v).mp h
    have hb : (⟨a.1, b⟩ : D.PartIndex) ∈ D.retainedPartIndices eta R₀ := by
      simpa only [D.mem_retainedPartIndices] using (D.mem_retainedPartIndices eta R₀ a).mp ha
    exact (D.mem_nonretainedVertices eta R₀ v).mp hv (D.part_subset_retainedVertices hb hvb)
  obtain ⟨b, _, hb⟩ := C.medium_companion a.1
    ((D.mem_visiblePartIndices theta a).mp (hretvis ha)) a.2 v hvout
    (by
      change alpha * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)
      have hnon : (0 : ℝ) ≤ (D.part a).card := by positivity
      nlinarith)
    (le_of_not_ge hh)
  refine ⟨⟨a.1, b⟩, ?_, rfl, hb⟩
  simpa only [D.mem_retainedPartIndices] using (D.mem_retainedPartIndices eta R₀ a).mp ha

theorem subcritical_not_sparse_of_high_target
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (halpha : alpha < 1 / 2) (v : Fin n) (a : D.PartIndex)
    (hrow : (1 - alpha) * (D.part a).card ≤ (degreeInFinset G v (D.part a) : ℝ)) :
    v ∉ D.sparse := by
  apply subcritical_not_sparse_of_majority_row G D hminimal v a
  have hpos : (0 : ℝ) < (D.part a).card := by exact_mod_cast (D.part_nonempty a).card_pos
  have hlt : ((D.part a).card : ℝ) < 2 * degreeInFinset G v (D.part a) := by nlinarith
  exact_mod_cast hlt

/-- A removable source in a nonvisible component cannot compete with a
sufficiently large weak-high target. This lemma has no graphon input. -/
theorem subcritical_source_visible_of_high_target
    (hk : 3 ≤ k)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (htheta : 0 ≤ theta) (halpha : alpha ≤ 1 / 4)
    {v : Fin n} (a : D.PartIndex) (hv : v ∈ D.part a) (hsource : 2 ≤ (D.part a).card)
    (b : D.PartIndex)
    (hrow : (1 - alpha) * (D.part b).card ≤ (degreeInFinset G v (D.part b) : ℝ))
    (hlarge : 2 * ((k - 1 : ℕ) : ℝ) * theta * n < (D.part b).card) :
    a.1 ∈ D.visibleComponentIndices theta := by
  by_contra hnv
  have hparts : ∀ c : D.PartIndex, c.1 = a.1 → ((D.part c).card : ℝ) ≤ theta * n := by
    intro c hc
    have hnlarge : ¬ ∃ j, theta * n ≤ ((D.parts a.1 j).card : ℝ) := by
      simpa only [D.mem_visibleComponentIndices, Fintype.card_fin] using hnv
    rcases c with ⟨j, u⟩
    dsimp only at hc
    subst j
    exact (lt_of_not_ge (fun h ↦ hnlarge ⟨u, h⟩)).le
  have hmodel := subcriticalModel_degree_le_of_part_bound hk G D a hv Finset.univ
    (theta * n) (fun j ↦ hparts ⟨a.1, j⟩ rfl)
  rw [degreeInFinset_univ_eq_degree] at hmodel
  have hgain := subcriticalMinimal_target_gain_le_model_degree G D hminimal v b
    (fun c _ ↦ D.erase_nonempty_of_source hv hsource c)
  have hgain' : 2 * (degreeInFinset G v (D.part b) : ℝ) ≤
      (D.part b).card + (subcriticalDivisionModelGraph G D).degree v := by exact_mod_cast hgain
  have hcard : (0 : ℝ) ≤ (D.part b).card := by positivity
  nlinarith

/-- The sparse-placement comparison forces a non-low row in the source
component once that component is visible and the source is removable. -/
theorem subcritical_visible_source_has_nonlow
    (hk : 3 ≤ k)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (halpha : 0 ≤ alpha)
    (hsmall : alpha * (1 + 2 * ((k - 1 : ℕ) : ℝ)) ≤ 1 / 2)
    {v : Fin n} (a : D.PartIndex) (hv : v ∈ D.part a)
    (hsource : 4 ≤ (D.part a).card)
    (hvis : a.1 ∈ D.visibleComponentIndices theta)
    (hbalance : ∀ b : D.PartIndex, b.1 = a.1 → (D.part b).card ≤ (2 : ℝ) * (D.part a).card) :
    ∃ b : D.PartIndex, b.1 = a.1 ∧ b ∈ subcriticalNonlowVisibleParts G D alpha theta v := by
  by_contra hnone
  have hlow (b : D.PartIndex) (hb : b.1 = a.1) :
      (degreeInFinset G v (D.part b) : ℝ) < alpha * (D.part b).card := by
    apply lt_of_not_ge
    intro h
    apply hnone
    exact ⟨b, hb, (mem_subcriticalNonlowVisibleParts G D alpha theta v b).mpr
      ⟨(D.mem_visiblePartIndices theta b).mpr (hb ▸ hvis), h⟩⟩
  have hsum : (∑ b ∈ D.closedPartIndices a, (degreeInFinset G v (D.part b) : ℝ)) ≤
      ((k - 1 : ℕ) : ℝ) * (2 * alpha * (D.part a).card) := by
    calc
      _ ≤ ∑ _b ∈ D.closedPartIndices a, 2 * alpha * (D.part a).card := by
        apply Finset.sum_le_sum
        intro b hb
        have hsame : b.1 = a.1 := by
          obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
          rfl
        have hlo := (hlow b hsame).le
        have hbal := mul_le_mul_of_nonneg_left (hbalance b hsame) halpha
        nlinarith
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, D.card_closedPartIndices hk a]
  have hbudget := subcriticalMinimal_own_part_card_le_closed_degrees G D hminimal v a hv (by omega)
  have hbR : ((D.part a).card : ℝ) ≤ (degreeInFinset G v (D.part a) : ℝ) +
      (∑ b ∈ D.closedPartIndices a, (degreeInFinset G v (D.part b) : ℝ)) + 1 := by
    exact_mod_cast hbudget
  have hown := (hlow a rfl).le
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg (D.part a).card)
  have hc : (4 : ℝ) ≤ (D.part a).card := by exact_mod_cast hsource
  nlinarith

/-- One non-low visible part outside the retained indices improves the
retained-row count by exactly one. -/
theorem subcritical_retained_nonlow_card_le_of_own_witness
    (C : SubcriticalRowConstraints G D alpha theta) {v : Fin n}
    (hv : v ∈ D.nonretainedVertices eta R₀) (a : D.PartIndex) (hva : v ∈ D.part a)
    {b : D.PartIndex} (hb : b ∈ subcriticalNonlowVisibleParts G D alpha theta v)
    (hba : b.1 = a.1) :
    ((subcriticalNonlowVisibleParts G D alpha theta v) ∩ D.retainedPartIndices eta R₀).card ≤ k - 2 := by
  have hbn : b ∉ D.retainedPartIndices eta R₀ := by
    intro hbr
    have har : a ∈ D.retainedPartIndices eta R₀ := by
      simpa only [D.mem_retainedPartIndices, hba] using hbr
    exact (D.mem_nonretainedVertices eta R₀ v).mp hv (D.part_subset_retainedVertices har hva)
  have hproper : (subcriticalNonlowVisibleParts G D alpha theta v ∩
      D.retainedPartIndices eta R₀) ⊂ subcriticalNonlowVisibleParts G D alpha theta v := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hmem := heq.symm ▸ hb
    exact hbn (Finset.mem_inter.mp hmem).2
  have hlt := Finset.card_lt_card hproper
  have hcard := C.nonlow v
  omega

/-- Donor branch. A high retained target forces the source part to
be removable whenever its component contains any non-singleton donor. The
donor swap and subsequent relocation are actual valid divisions. -/
theorem subcriticalHighTarget_source_card_ge_two_of_donor
    (hk : 3 ≤ k) {L : AdmissibleBlockSequence k} {omega delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (homega : omega ≤ 1)
    (halpha : alpha ≤ 1 / 4)
    (hreserve : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)))
    (hscale : 8 ≤ theta * n)
    {v : Fin n} (hv : v ∈ D.nonretainedVertices eta R₀)
    (a : D.PartIndex) (hva : v ∈ D.part a)
    (hdonor : ∃ j : Fin (D.core a.1).order, 2 ≤ (D.parts a.1 j).card)
    (b : D.PartIndex) (hb : b ∈ D.retainedPartIndices eta R₀)
    (hrow : (1 - alpha) * (D.part b).card ≤ (degreeInFinset G v (D.part b) : ℝ)) :
    2 ≤ (D.part a).card := by
  have htarget : b.1 ≠ a.1 := by
    intro hba
    have ha : a ∈ D.retainedPartIndices eta R₀ := by
      simpa only [D.mem_retainedPartIndices, hba] using hb
    exact (D.mem_nonretainedVertices eta R₀ v).mp hv
      (D.part_subset_retainedVertices ha hva)
  have hvis : a.1 ∈ D.visibleComponentIndices theta := by
    by_contra hnv
    have hparts : ∀ j : Fin (D.core a.1).order,
        ((D.parts a.1 j).card : ℝ) ≤ theta * n := by
      intro j
      have hnlarge : ¬ ∃ j, theta * n ≤ ((D.parts a.1 j).card : ℝ) := by
        simpa only [D.mem_visibleComponentIndices, Fintype.card_fin] using hnv
      exact (lt_of_not_ge (fun h ↦ hnlarge ⟨j, h⟩)).le
    obtain ⟨j, hj⟩ := hdonor
    have hgain := subcriticalMinimal_donor_target_gain_le hk G D hminimal
      a.1 a.2 j v hva hj b htarget (theta * n) hparts
    have htarget := R.retainedPart_card_lower_bound hR₀ heta hb
    have hreserveN := mul_le_mul_of_nonneg_right hreserve (Nat.cast_nonneg n)
    rw [div_mul_eq_mul_div] at hreserveN
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hpos : 0 < theta * n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hscale
    have hless : 10 * ((k - 1 : ℕ) : ℝ) < 20 * (k : ℝ) := by linarith
    have hmul := mul_lt_mul_of_pos_right hless hpos
    have hcard : (0 : ℝ) ≤ (D.part b).card := by positivity
    nlinarith
  have hlower := R.visible_part_card_ge_half homega a
    ((D.mem_visiblePartIndices theta a).mpr hvis)
  have hcard : (2 : ℝ) ≤ (D.part a).card := by linarith
  exact_mod_cast hcard

/-- Finite assembly for a removable source. The nonemptiness premise is
explicit and will be discharged by the singleton-safe comparison, not hidden. -/
theorem subcriticalSparseRetainedRowBudget_of_removable_source
    (hk : 3 ≤ k) {L : AdmissibleBlockSequence k} {omega delta epsilon : ℝ}
    (R : SubcriticalCloseStructureResult hk G D L R₀ omega eta theta alpha delta epsilon)
    (C : SubcriticalRowConstraints G D alpha theta)
    (hminimal : ∀ E : SubcriticalDivision k (Fin n),
      subcriticalDefectCost G D ≤ subcriticalDefectCost G E)
    (hR₀ : 1 ≤ R₀) (heta : 0 ≤ eta) (htheta : 0 < theta)
    (homega : omega ≤ 1) (halpha : 0 ≤ alpha) (halphaQuarter : alpha ≤ 1 / 4)
    (hsmall : alpha * (1 + 2 * ((k - 1 : ℕ) : ℝ)) ≤ 1 / 2)
    (hcutoff : theta ≤ eta / (2 * (R₀ : ℝ)))
    (hreserve : 20 * (k : ℝ) * theta ≤ eta / (2 * (R₀ : ℝ)))
    (hscale : 8 ≤ theta * n) {v : Fin n}
    (hv : v ∈ D.nonretainedVertices eta R₀)
    (a : D.PartIndex) (hva : v ∈ D.part a) (hsource : 2 ≤ (D.part a).card)
    (hhigh : ∃ t ∈ D.retainedPartIndices eta R₀,
      4 * alpha * (D.part t).card ≤ (degreeInFinset G v (D.part t) : ℝ)) :
    v ∉ D.sparse ∧
      (∃ b : D.PartIndex, b.1 = a.1 ∧ b ∈ subcriticalNonlowVisibleParts G D alpha theta v) ∧
      ((subcriticalNonlowVisibleParts G D alpha theta v) ∩ D.retainedPartIndices eta R₀).card ≤ k - 2 := by
  obtain ⟨t, ht, hrow⟩ := hhigh
  obtain ⟨b, hbret, _, hrowb⟩ := subcriticalRetainedHighRow_has_high_target C halpha
    (D.retainedPartIndices_subset_visiblePartIndices hR₀ htheta.le hcutoff) hv ht hrow
  have hnotSparse := subcritical_not_sparse_of_high_target hminimal
    (by linarith : alpha < 1 / 2) v b hrowb
  have hlarge : 2 * ((k - 1 : ℕ) : ℝ) * theta * n < (D.part b).card := by
    have htarget := R.retainedPart_card_lower_bound hR₀ heta hbret
    have hreserveN := mul_le_mul_of_nonneg_right hreserve (Nat.cast_nonneg n)
    rw [div_mul_eq_mul_div] at hreserveN
    have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
    have hk1 : ((k - 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.sub_le k 1
    have hpos : 0 < theta * n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 8) hscale
    have hless : 2 * ((k - 1 : ℕ) : ℝ) < 20 * (k : ℝ) := by linarith
    have hmul := mul_lt_mul_of_pos_right hless hpos
    nlinarith
  have hvis := subcritical_source_visible_of_high_target hk hminimal htheta.le
    halphaQuarter a hva hsource b hrowb hlarge
  have hsourceFour : 4 ≤ (D.part a).card := by
    have hlower := R.visible_part_card_ge_half homega a
      ((D.mem_visiblePartIndices theta a).mpr hvis)
    have hcard : (4 : ℝ) ≤ (D.part a).card := by linarith
    exact_mod_cast hcard
  have hbal (c : D.PartIndex) (hc : c.1 = a.1) :
      (D.part c).card ≤ (2 : ℝ) * (D.part a).card := by
    rcases c with ⟨j, u⟩
    dsimp only at hc
    subst j
    have h := R.visible_component_ratio a.1 hvis u a.2
    have hpos : (0 : ℝ) ≤ (D.part a).card := by positivity
    change ((D.parts a.1 u).card : ℝ) ≤ 2 * (D.part a).card
    change ((D.parts a.1 u).card : ℝ) ≤ (1 + omega) * (D.part a).card at h
    nlinarith
  obtain ⟨c, hca, hc⟩ := subcritical_visible_source_has_nonlow hk hminimal halpha hsmall
    a hva hsourceFour hvis hbal
  exact ⟨hnotSparse, ⟨c, hca, hc⟩,
    subcritical_retained_nonlow_card_le_of_own_witness C hv a hva hc hca⟩

end InducedStars
